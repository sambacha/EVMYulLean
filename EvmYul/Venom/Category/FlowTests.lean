module

public import EvmYul.Venom.Category.BridgeTestHarness
public meta import EvmYul.Venom.Category.BridgeTestHarness
public import EvmYul.Venom.Category.FuncFlow
public meta import EvmYul.Venom.Category.FuncFlow

@[expose] public meta section

/-!
# Tests of the dominance order of the flow quiver (P1.1)

`Flow.lean` proves P1.1 for dominance on any flow quiver (`Dom.refl`, `Dom.trans`, `Dom.antisymm`
on reachable vertices, `Dom.chain`, `entry_dom`) and `FuncFlow.lean` identifies it with the
`Dominance.lean` relation (`dominates_iff_dom`). These tests check the same laws, and the computed
dominator tree, against a **brute-force oracle** written from the definition (`a` dominates a
reachable `v` iff `v` is unreachable once `a` is removed). Each section names the `TESTING.md`
rule it applies.

1. **§1 Unit checks.** On a diamond with a back edge: the entry dominates everything, the join is
   dominated by neither arm, the loop head dominates the loop body and not conversely.
2. **§2 Random functions (counted, A2).** On the random functions of `BridgeTestHarness.lean`
   (loops, parallel slots, missing labels, unreachable blocks): reflexivity, transitivity,
   antisymmetry on reachable blocks, the chain property of the dominators of each reachable block,
   the entry least, and `dominatesB` of the computed tree equal to the oracle. The number of
   functions with a cycle (where antisymmetry is not implied by acyclicity) and with a dominator
   chain of length at least 3 is printed and thresholded.
3. **§3 Canaries (E1).** Reachability in place of dominance is not antisymmetric; the dominators of
   `v` together with the predecessors of `v` are not a chain.
-/

namespace EvmYul.Venom.Category.FlowTests

open EvmYul.Venom.Cfg EvmYul.Venom.Dominance EvmYul.Venom.Category EvmYul.Venom.Category.BridgeTests
  Plausible Plausible.Decorations

/-- Successor labels (oracle side). -/
def succsO (f : Func) (u : Label) : List Label :=
  match f.find? u with
  | some b => b.succs
  | none => []

/-- Labels reachable from `src` without passing through `a` (fixpoint by iteration). -/
def reachFromAvoid (f : Func) (src a : Label) : List Label :=
  let n := f.blocks.length + 1
  let start := if src = a then [] else [src]
  (List.range n).foldl (fun acc _ =>
    acc ++ ((acc.flatMap (succsO f)).filter fun v => v ≠ a ∧ v ∉ acc).dedup) start

/-- Reachable from the entry. -/
def reachO (f : Func) : List Label := reachFromAvoid f f.entry "⊥ not a label"

/-- Oracle dominance on reachable blocks. -/
def domO (f : Func) (a v : Label) : Bool := v ∈ reachO f && v ∉ reachFromAvoid f f.entry a

/-- The oracle's dominators of `v`. -/
def domsO (f : Func) (v : Label) : List Label := (reachO f).filter (domO f · v)

/-- Do all pairs of a list satisfy `r` one way or the other? -/
def isChain (r : Label → Label → Bool) (l : List Label) : Bool :=
  l.all fun a => l.all fun b => r a b || r b a

/-- The laws of P1.1 for a relation `r` on the reachable blocks of `f`. -/
def lawsHold (f : Func) (r : Label → Label → Bool) : Bool :=
  let R := reachO f
  R.all (fun v => r v v && r f.entry v) &&
  R.all (fun a => R.all fun b => R.all fun c => !(r a b && r b c) || r a c) &&
  R.all (fun a => R.all fun b => !(r a b && r b a) || a == b) &&
  R.all (fun v => isChain r (R.filter (r · v)))

/-- The computed tree agrees with the oracle on all reachable pairs. -/
def treeAgrees (f : Func) : Bool :=
  let t := computeDomTree f
  checkTree f t && (reachO f).all fun a => (reachO f).all fun v => dominatesB t a v == domO f a v

/-- Does `f` have a cycle through reachable blocks? -/
def hasCycle (f : Func) : Bool :=
  (reachO f).any fun u => (succsO f u).any fun v => u ∈ reachFromAvoid f v "⊥ not a label"

/-- A diamond `e → (l | r) → j`, with a loop `j → h → j` and exit `h → x`. -/
def diamondLoop : Func := { name := "dl", entry := "e", blocks := [
  ⟨"e", [I .sub [.lit 1, .lit 0] ["c"], I .jnz [.var "c", .lbl "l", .lbl "r"]]⟩,
  ⟨"l", [I .jmp [.lbl "j"]]⟩,
  ⟨"r", [I .jmp [.lbl "j"]]⟩,
  ⟨"j", [I .jmp [.lbl "h"]]⟩,
  ⟨"h", [I .jnz [.var "c", .lbl "j", .lbl "x"]]⟩,
  ⟨"x", [I .stop []]⟩] }

/-- §1 unit checks. -/
def unitChecks : List (String × Bool) :=
  let f := diamondLoop
  [("the entry dominates every block", ["e", "l", "r", "j", "h", "x"].all (domO f "e")),
   ("neither arm dominates the join", !domO f "l" "j" && !domO f "r" "j"),
   ("the loop head j dominates h and x; h does not dominate j",
      domO f "j" "h" && domO f "j" "x" && !domO f "h" "j"),
   ("the dominators of x are the chain e, j, h, x", domsO f "x" == ["e", "j", "h", "x"]),
   ("the laws of P1.1 hold and the computed tree is exact", lawsHold f (domO f) && treeAgrees f)]

/-- **Canary relation**: reachability (every block reaching `v`). -/
def reachesO (f : Func) (a v : Label) : Bool := v ∈ reachO f && v ∈ reachFromAvoid f a "⊥"

/-- **Canary relation**: dominators of `v`, or predecessors of `v`. -/
def domOrPred (f : Func) (a v : Label) : Bool :=
  domO f a v || (a ∈ reachO f && v ∈ succsO f a)

/-- Run everything; throws on the first failure. -/
def runAll : IO Unit := do
  -- §1
  for (name, ok) in unitChecks do
    unless ok do throw <| IO.userError s!"§1 unit check failed: {name}"
  IO.println s!"§1 dominance: {unitChecks.length} unit checks passed"
  -- §2
  expectHolds "§2 random functions: dominance is a partial order, entry least, dominators a chain"
    (∀ (n k₀ : Nat) (bs : List (Nat × Nat × Nat × Nat)),
      lawsHold (funcOf n k₀ bs) (domO (funcOf n k₀ bs)) = true)
  expectHolds "§2 random functions: the computed dominator tree is accepted and exact"
    (∀ (n k₀ : Nat) (bs : List (Nat × Nat × Nat × Nat)), treeAgrees (funcOf n k₀ bs) = true)
  let fs := (List.range 300).map detFunc
  let cyc := (fs.filter hasCycle).length
  let longChain := (fs.filter fun f => (reachO f).any fun v => (domsO f v).length ≥ 3).length
  IO.println s!"§2 coverage (300 functions): with a cycle {cyc}; with a dominator chain of length \
    ≥ 3 {longChain}"
  unless cyc ≥ 30 ∧ longChain ≥ 30 do
    throw <| IO.userError "§2 coverage: a region is empty or too small (A2)"
  -- §3
  expectRefuted "§3 canary: reachability satisfies the laws of P1.1"
    (∀ (n k₀ : Nat) (bs : List (Nat × Nat × Nat × Nat)),
      lawsHold (funcOf n k₀ bs) (reachesO (funcOf n k₀ bs)) = true)
  expectRefuted "§3 canary: dominators together with predecessors form a chain"
    (∀ (n k₀ : Nat) (bs : List (Nat × Nat × Nat × Nat)),
      lawsHold (funcOf n k₀ bs) (domOrPred (funcOf n k₀ bs)) = true)

#eval runAll

end EvmYul.Venom.Category.FlowTests
