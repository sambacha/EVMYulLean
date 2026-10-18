module

public import EvmYul.Venom.Category.BridgeTestHarness
public meta import EvmYul.Venom.Category.BridgeTestHarness
public import EvmYul.Venom.Category.CfgNormalization
public meta import EvmYul.Venom.Category.CfgNormalization
public import EvmYul.Venom.Text
public meta import EvmYul.Venom.Text

@[expose] public meta section

/-!
# Tests of critical-edge splitting, and of the normal form of D1.3

`CfgNormalization.lean` splits critical edges as Vyper's `CFGNormalization` does;
`Normalization.lean` proves the abstract facts (subdivision has no critical edge; it commutes with
the semantics; D1.3's per-vertex condition is a different property, `vertexNormal_ne_noCritical`).
Each section names the `TESTING.md` rule it applies.

1. **§1 Unit checks.** A diamond whose join is reached by a `jnz` has one critical edge; after
   `normalize` it has none, the split block is named `p_split_b` and the join's φ reads from it;
   the parallel slots of `jnz c, @a, @a` are not split (Vyper's `cfg_out` is a set); the five-block
   counterexample of `Normalization.lean` as a Venom function has no critical edge but fails D1.3.
   The recorded Vyper 0.4.3 output for `store.vy` has no critical edge.
2. **§2 Random functions (counted, A2).** `normalize` leaves no critical edge, and it does not change
   `run`: a finished run of `f` with fuel `n` is the run of `normalize f` with fuel `2n`, and back.
   The number of functions with critical edges, and of normalized functions that still fail D1.3
   (so D1.3 is not the pass's postcondition), are printed and must be non-zero.
3. **§3 Canaries (E1).** Splitting without redirecting the φs changes the semantics; checking D1.3
   instead of the critical edges claims that `normalize` fails.
-/

namespace EvmYul.Venom.Category.CfgNormalizationTests

open EvmYul.Venom.Cfg EvmYul.Venom.Category EvmYul.Venom.Category.BridgeTests
  EvmYul.Venom.Text Plausible Plausible.Decorations

/-- A diamond `a → (b | c)`, `b → d`, `c → d`, with `a → d` directly as well (critical: `a` has
two successors and `d` has three predecessors). -/
def diamond : Func := { name := "d", entry := "a", blocks := [
  ⟨"a", [I .sub [.lit 0, .lit 0] ["c"], I .jnz [.var "c", .lbl "b", .lbl "d"]]⟩,
  ⟨"b", [I .sub [.lit 7, .lit 0] ["y"], I .jmp [.lbl "d"]]⟩,
  ⟨"c", [I .sub [.lit 8, .lit 0] ["y"], I .jmp [.lbl "d"]]⟩,
  ⟨"d", [I .phi [.lbl "a", .var "c", .lbl "b", .var "y", .lbl "c", .var "y"] ["w"],
         I .sstore [.var "w"], I .stop []]⟩] }

/-- `jnz %c, @x, @x`: two slots, one successor label. -/
def parallel : Func := { name := "p", entry := "a", blocks := [
  ⟨"a", [I .sub [.lit 1, .lit 0] ["c"], I .jnz [.var "c", .lbl "x", .lbl "x"]]⟩,
  ⟨"z", [I .jmp [.lbl "x"]]⟩,
  ⟨"x", [I .stop []]⟩] }

/-- The counterexample `p₁, p₂ → b → s₁, s₂` of `Normalization.lean` as a Venom function. -/
def five : Func := { name := "five", entry := "e", blocks := [
  ⟨"e", [I .sub [.lit 1, .lit 0] ["c"], I .jnz [.var "c", .lbl "p1", .lbl "p2"]]⟩,
  ⟨"p1", [I .jmp [.lbl "b"]]⟩,
  ⟨"p2", [I .jmp [.lbl "b"]]⟩,
  ⟨"b", [I .jnz [.var "c", .lbl "s1", .lbl "s2"]]⟩,
  ⟨"s1", [I .stop []]⟩,
  ⟨"s2", [I .revert []]⟩] }

/-- Does a run halt? -/
def haltsWithTrace (r : Result (List Word)) (ws : List Nat) : Bool :=
  match r with
  | .halted s => s.map BitVec.toNat == ws
  | _ => false

/-- §1 unit checks; each must be `true`. -/
def unitChecks (store : Func) : List (String × Bool) :=
  let nd := normalize diamond
  [("diamond: exactly one critical edge, a → d", criticalEdges diamond == [("a", "d")]),
   ("diamond normalized: no critical edge, the block a_split_d exists and jumps to d",
      criticalEdges nd == [] &&
      (nd.find? "a_split_d").any fun b => b.insts.map (·.op) == [.jmp] && b.succs == ["d"]),
   ("diamond normalized: d's φ reads its operand for the split block",
      (nd.find? "d").any fun b => b.phis.any fun i => i.args.contains (.lbl "a_split_d") &&
        !i.args.contains (.lbl "a")),
   ("diamond: c = 0, so the edge a → d is taken and run stores 0, before and after normalization",
      haltsWithTrace (run (σ := List Word) diamond 10 "" "a" EvmYul.Venom.Cfg.Env.empty []) [0] &&
      haltsWithTrace (run (σ := List Word) nd 10 "" "a" EvmYul.Venom.Cfg.Env.empty []) [0]),
   ("jnz %c, @x, @x is not critical (successor sets), so normalize leaves it alone",
      criticalEdges parallel == [] && (normalize parallel).blocks.length == 3),
   ("the five-block flow: no critical edge, but b fails D1.3 (two predecessors, two successors)",
      criticalEdges five == [] && !vertexNormalB five),
   ("store.vy (Vyper 0.4.3 output): no critical edge", criticalEdges store == [])]

/-- `run` after normalization with twice the fuel agrees with `run` before, in both directions,
whenever the run finishes. -/
def preserves (norm : Func → Func) (f : Func) (n : Nat) : Bool :=
  let r := run (σ := List Word) f n "" f.entry EvmYul.Venom.Cfg.Env.empty []
  let r' := run (σ := List Word) (norm f) (2 * n) "" (norm f).entry EvmYul.Venom.Cfg.Env.empty []
  let same : Result (List Word) → Result (List Word) → Bool
    | .halted s, .halted s' => s == s'
    | .reverted s, .reverted s' => s == s'
    | .fault, .fault => true
    | .fuelOut, _ => true
    | _, _ => false
  same r r' &&
    (match r' with
     | .fuelOut => true
     | _ => same (run (σ := List Word) f (2 * n) "" f.entry EvmYul.Venom.Cfg.Env.empty []) r')

/-- **Canary**: split without redirecting the φs of the target. -/
def splitEdgeNoPhi (f : Func) (pb : Label × Label) : Func :=
  let (p, b) := pb
  let s := splitLabel p b
  { f with blocks := (f.blocks.map fun blk =>
      if blk.label = p then
        { blk with insts := match blk.insts.reverse with
          | [] => []
          | t :: rest => (relabel b s t :: rest).reverse }
      else blk) ++ [⟨s, [⟨.jmp, [.lbl b], []⟩]⟩] }

/-- **Canary**: normalization without the φ redirection. -/
def normalizeNoPhi (f : Func) : Func := (criticalEdges f).foldl splitEdgeNoPhi f

/-- Random functions with φs on every non-entry block (so that a missed φ redirection shows). -/
def funcOfPhi (n k₀ : Nat) (bs : List (Nat × Nat × Nat × Nat)) : Func :=
  funcOf n k₀ (bs.map fun (k, t₁, t₂, q) => (k, t₁, t₂, q - q % 3))

/-- Run everything; throws on the first failure. -/
def runAll : IO Unit := do
  let text ← IO.FS.readFile "docs/research/venom/store_bb_runtime_0.4.3.txt"
  let some store := parseFunc? text | throw <| IO.userError "§1: the store.vy fixture does not parse"
  -- §1
  let checks := unitChecks store
  for (name, ok) in checks do
    unless ok do throw <| IO.userError s!"§1 unit check failed: {name}"
  IO.println s!"§1 normalization: {checks.length} unit checks passed"
  -- §2
  expectHolds "§2 random functions: normalize leaves no critical edge"
    (∀ (n k₀ : Nat) (bs : List (Nat × Nat × Nat × Nat)),
      (criticalEdges (normalize (funcOf n k₀ bs))).isEmpty = true)
  expectHolds "§2 random functions: run (normalize f) (2n) = run f n on finished runs, both ways"
    (∀ (n k₀ : Nat) (bs : List (Nat × Nat × Nat × Nat)) (fuel : Nat),
      preserves normalize (funcOf n k₀ bs) (fuel % 12) = true)
  let fs := (List.range 300).map detFunc
  let crit := (fs.filter fun f => !(criticalEdges f).isEmpty).length
  let stillNotD13 := (fs.filter fun f => !vertexNormalB (normalize f)).length
  let finished := (fs.filter fun f =>
    match run (σ := List Word) f 12 "" f.entry EvmYul.Venom.Cfg.Env.empty [] with
    | .fuelOut => false | _ => true).length
  IO.println s!"§2 coverage (300 functions): with a critical edge {crit}; normalized but failing \
    D1.3 {stillNotD13}; finishing within fuel 12 {finished}"
  unless crit ≥ 30 ∧ stillNotD13 ≥ 10 ∧ finished ≥ 100 do
    throw <| IO.userError "§2 coverage: a region is empty or too small (A2)"
  -- §3
  expectRefuted "§3 canary: splitting without redirecting the φs preserves run"
    (∀ (n k₀ : Nat) (bs : List (Nat × Nat × Nat × Nat)) (fuel : Nat),
      preserves normalizeNoPhi (funcOfPhi n k₀ bs) (fuel % 12) = true)
  expectRefuted "§3 canary: D1.3 holds after normalize"
    (∀ (n k₀ : Nat) (bs : List (Nat × Nat × Nat × Nat)),
      vertexNormalB (normalize (funcOf n k₀ bs)) = true)
  IO.println "normalization: standing caveat (D1): run is compared on one trace machine; the \
    abstract simulation is subdivSim in Normalization.lean"

#eval runAll

end EvmYul.Venom.Category.CfgNormalizationTests
