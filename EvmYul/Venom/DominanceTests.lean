module

public import EvmYul.Venom.Dominance
public meta import EvmYul.Venom.Dominance
public import EvmYul.Venom.Text
public meta import EvmYul.Venom.Text
public import EvmYul.Testing.Counted
public meta import EvmYul.Testing.Counted
public import Plausible
public meta import Plausible

@[expose] public meta section

/-!
# Tests of the dominator tree and the strict-SSA check

`Dominance.lean` computes dominator trees (untrusted), checks them as certificates (`checkTree`,
proved sound by `checkTree_sound`) and checks strict SSA (`checkSSA_sound`). These tests compare
everything with a **brute-force oracle** written here from the definition: `a` dominates a reachable
`v` iff `v` cannot be reached from the entry when `a` is removed. Each section names the
`TESTING.md` rule it applies.

1. **§1 Unit checks (concrete facts).** The recorded Vyper output for `store.vy` (parsed by
   `Text.lean`) has the tree `selector_bucket_0, selector_bucket_1 ← __main_entry` and
   `6_then, 9_if_exit ← selector_bucket_0`, and is strict SSA; a use of a variable from the other
   bucket is rejected. A loop with phis on its back edge is strict SSA. Wrong certificates are rejected.
2. **§2 Random graphs (counted, A2).** For random graphs of up to 7 blocks (loops, unreachable blocks,
   jumps to missing labels): the computed tree is accepted, and for every reachable `v` and every
   label `a`, `dominatesB` equals the oracle (both directions: the computed tree is exact).
3. **§3 Soundness against mutated certificates.** Re-parenting one node of the computed tree: when
   `checkTree` accepts (the new parent is still a dominator) every claimed dominance holds in the
   oracle; how many mutants are accepted and rejected is printed.
4. **§4 Strict SSA (counted).** On random graphs with one definition per block and uses of other
   blocks' variables, `checkSSA` equals the oracle's strict-SSA verdict.
5. **§5 Canaries (E1).** A tree check without the edge condition, dominator sets computed with a
   union instead of an intersection, and an SSA check that ignores phis must each be refuted.
-/

namespace EvmYul.Venom.DominanceTests

open EvmYul.Venom EvmYul.Venom.Cfg EvmYul.Venom.Text EvmYul.Venom.Dominance Plausible
  Plausible.Decorations

/-! ## The oracle -/

/-- Successors by label (the first block with the label, as `run`), written independently. -/
def succsO (f : Func) (u : Label) : List Label :=
  match f.blocks.find? (·.label == u) with
  | some b => b.succs
  | none => []

/-- Breadth-first search from the entry with `a` removed: the labels reached. -/
def reachAvoidO (f : Func) (a : Label) : List Label :=
  if f.entry = a then [] else
  (List.range (f.blocks.length + 2)).foldl (fun seen _ =>
    seen ++ ((seen.flatMap (succsO f)).filter (fun v => v ≠ a ∧ v ∉ seen)).eraseDups) [f.entry]

/-- Reachable labels (nothing removed). -/
def reachO (f : Func) : List Label := reachAvoidO f "⊥ not a label"

/-- **The dominance oracle**: `v` is unreachable once `a` is removed. -/
def domO (f : Func) (a v : Label) : Bool := v ∉ reachAvoidO f a

/-- Every claim of the tree (`a` ancestor-or-self of a reachable `v`) holds in the oracle, and with
`exact` also every oracle fact is claimed. -/
def treeMatchesOracle (f : Func) (t : DomTree) (exact : Bool) : Bool :=
  let labels := f.entry :: f.blocks.map (·.label)
  (reachO f).all fun v => labels.all fun a =>
    if dominatesB t a v then domO f a v else !exact || !domO f a v

/-! ## Fixtures -/

/-- `%x = op args`. -/
def I (op : Op) (args : List Cfg.Operand) (outs : List Var := []) : Inst := ⟨op, args, outs⟩

/-- The summing loop (as in `EvmMachineTests.lean`): phis on the back edge `body → head`. -/
def sumLoop : Func := { name := "sum", entry := "entry", blocks := [
  ⟨"entry", [I .calldataload [.lit 0] ["n"], I .jmp [.lbl "head"]]⟩,
  ⟨"head", [I .phi [.lbl "entry", .var "n", .lbl "body", .var "i2"] ["i"],
            I .phi [.lbl "entry", .lit 0, .lbl "body", .var "acc2"] ["acc"],
            I .jnz [.var "i", .lbl "body", .lbl "exit"]]⟩,
  ⟨"body", [I .add [.var "acc", .var "i"] ["acc2"], I .sub [.var "i", .lit 1] ["i2"],
            I .jmp [.lbl "head"]]⟩,
  ⟨"exit", [I .sstore [.lit 0, .var "acc"], I .stop []]⟩] }

/-- A diamond `a → b, c → d`. -/
def diamond : Func := { name := "d", entry := "a", blocks := [
  ⟨"a", [I .callvalue [] ["x"], I .jnz [.var "x", .lbl "b", .lbl "c"]]⟩,
  ⟨"b", [I .add [.var "x", .lit 1] ["y"], I .jmp [.lbl "d"]]⟩,
  ⟨"c", [I .add [.var "x", .lit 2] ["z"], I .jmp [.lbl "d"]]⟩,
  ⟨"d", [I .phi [.lbl "b", .var "y", .lbl "c", .var "z"] ["w"], I .sstore [.lit 0, .var "w"],
         I .stop []]⟩] }

/-- Replace the operands of instruction `k` of block `l`. -/
def setArgs (f : Func) (l : Label) (k : Nat) (args : List Cfg.Operand) : Func :=
  { f with blocks := f.blocks.map fun b =>
    if b.label = l then { b with insts := b.insts.zipIdx.map fun (i, j) =>
      if j = k then { i with args := args } else i } else b }

/-- §1 unit checks; each must be `true`. -/
def unitChecks (store : Func) : List (String × Bool) :=
  let ts := domTree? store
  let t := ts.getD ⟨[]⟩
  let tl := domTree? sumLoop
  let td := computeDomTree diamond
  [("store.vy: the computed tree is accepted by checkTree", ts.isSome),
   ("store.vy: parents bucket_0, bucket_1 ← __main_entry; 6_then, 9_if_exit ← selector_bucket_0",
      t.parent "selector_bucket_0" == some "__main_entry" &&
      t.parent "selector_bucket_1" == some "__main_entry" &&
      t.parent "6_then" == some "selector_bucket_0" &&
      t.parent "9_if_exit" == some "selector_bucket_0" && t.parent "__main_entry" == none),
   ("store.vy: selector_bucket_0 dominates 6_then; selector_bucket_1 does not (both in the oracle)",
      dominatesB t "selector_bucket_0" "6_then" && domO store "selector_bucket_0" "6_then" &&
      !dominatesB t "selector_bucket_1" "6_then" && !domO store "selector_bucket_1" "6_then"),
   ("store.vy: the tree matches the oracle exactly", treeMatchesOracle store t true),
   ("store.vy is strict SSA (%2 from the entry is used in every bucket)", checkSSA store t),
   ("store.vy with 6_then reading %42 of selector_bucket_1: rejected (bucket_1 does not dominate)",
      !checkSSA (setArgs store "6_then" 4 [.var "42", .var "20"]) t),
   ("store.vy with a use before its definition in the same block: rejected",
      !checkSSA (setArgs store "6_then" 1 [.var "20"]) t),
   ("sum loop: tree head ← entry, body ← head, exit ← head, accepted",
      tl.any fun t => t.parent "head" == some "entry" && t.parent "body" == some "head" &&
        t.parent "exit" == some "head"),
   ("sum loop: strict SSA, φ source acc2 for body defined in body (body dominates body)",
      tl.any (checkSSA sumLoop)),
   ("sum loop: a φ source for entry defined in body is rejected",
      tl.any fun t => !checkSSA (setArgs sumLoop "head" 0
        [.lbl "entry", .var "i2", .lbl "body", .var "i2"]) t),
   ("diamond: d's parent is a; neither b nor c dominates d", td.parent "d" == some "a" &&
      !domO diamond "b" "d" && !domO diamond "c" "d"),
   ("diamond: the certificate d ← b is rejected", !checkTree diamond ⟨[("b", "a"), ("c", "a"),
      ("d", "b")]⟩),
   ("diamond: a certificate giving the entry a parent is rejected",
      !checkTree diamond ⟨[("a", "b"), ("b", "a"), ("c", "a"), ("d", "a")]⟩),
   ("diamond: a certificate missing c is rejected (c is reached from a tree node)",
      !checkTree diamond ⟨[("b", "a"), ("d", "a")]⟩),
   ("diamond: φ w = phi @b, y, @c, z is strict SSA; w = y outside the φ is not",
      checkSSA diamond td && !checkSSA (setArgs diamond "d" 1 [.lit 0, .var "y"]) td)]

/-! ## Random graphs -/

/-- Label of block `j`. -/
def lab (j : Nat) : Label := "b" ++ toString j

/-- A random graph of `n + 1 ≤ 7` blocks; block `j` defines `v_j` and uses `v_{u_j}`, in either order
(strict SSA only if `u_j` is a dominator, or `j` itself with the definition first), and ends in `jmp`, `jnz` or `stop`. The first
target runs forward (`j + 1` or `j + 2`, so trees get deep), the second anywhere up to `n + 1` (back
edges, and a jump to a missing label). With `phi`, block `j` also opens with
`%p_j = phi @b_{q}, %v_{q'}`. -/
def graphOf (n : Nat) (bs : List (Nat × Nat × Nat × Nat)) (phi : Bool := false) : Func :=
  let m := n % 7 + 1
  let blk (j : Nat) : Block :=
    let (k, t₁, t₂, u) := bs.getD j (j, j + 1, j + 2, 0)
    let term := match k % 4 with
      | 0 => I .jmp [.lbl (lab ((j + 1 + t₁ % 2) % (m + 1)))]
      | 1 | 2 => I .jnz [.var ("v" ++ toString j), .lbl (lab ((j + 1 + t₁ % 2) % (m + 1))),
                         .lbl (lab (t₂ % (m + 1)))]
      | _ => I .stop []
    let phis := if phi ∧ j > 0 then [I .phi [.lbl (lab (u % m)), .var ("v" ++ toString (t₂ % m))]
      ["p" ++ toString j]] else []
    let defV := I .callvalue [] ["v" ++ toString j]
    let useW := I .add [.var ("v" ++ toString (u % m)), .lit 1] ["w" ++ toString j]
    ⟨lab j, phis ++ (if t₁ / 2 % 2 = 1 then [useW, defV] else [defV, useW]) ++ [term]⟩
  ⟨"g", lab 0, (List.range m).map blk⟩

/-- Dominance as the SSA check uses it: the oracle on reachable blocks; on an unreachable block
(where every label dominates vacuously) only the block itself, since the check is conservative
there and accepts only definitions from the same block. -/
def domR (f : Func) (d v : Label) : Bool :=
  if v ∈ reachO f then domO f d v else decide (d = v)

/-- The oracle's strict-SSA verdict for `graphOf` programs (one definition per variable there):
every use is defined earlier in its block or in another block that dominates it, every φ source in
a block that dominates the predecessor. -/
def ssaO (f : Func) : Bool :=
  let defBlk (x : Var) : Option (Label × Nat) :=
    f.blocks.findSome? fun b =>
      (b.insts.zipIdx.find? fun (i, _) => x ∈ i.outs).map fun ik => (b.label, ik.2)
  f.blocks.all fun b => b.insts.zipIdx.all fun (i, k) =>
    if i.op = .phi then
      (phiVarSources i.args).all fun (p, x) => match defBlk x with
        | some (d, _) => domR f d p
        | none => false
    else i.args.all fun
      | .var x => (match defBlk x with
        | some (d, j) => if d = b.label then decide (j < k) else domR f d b.label
        | none => false)
      | _ => true

/-- Re-parent node `v` of a tree to `p`. -/
def reparent (t : DomTree) (v p : Label) : DomTree :=
  ⟨t.idom.map fun (x, q) => if x = v then (x, p) else (x, q)⟩

/-- A mutated certificate. For even `j`, a node whose parent is not the entry is re-parented to the
entry (a coarser but true dominator: the check must accept it); otherwise node number `i` is
re-parented to label number `j / 2` (usually not a dominator: the check must reject it). -/
def mutant (f : Func) (i j : Nat) : DomTree :=
  let t := computeDomTree f
  let deep := t.idom.filter fun (_, p) => p ≠ f.entry
  if j % 2 = 0 ∧ !deep.isEmpty then reparent t (deep.getD (i % deep.length) ("", "")).1 f.entry
  else match t.idom with
    | [] => t
    | ids => reparent t (ids.getD (i % ids.length) ("", "")).1 (lab (j / 2 % (f.blocks.length + 1)))

/-! ## §5 Canary support -/

/-- `checkTree` without the edge condition (only the root condition and that targets have
parents). -/
def checkTreeNoEdge (f : Func) (t : DomTree) : Bool :=
  (t.parent f.entry).isNone &&
    (f.entry :: t.idom.map Prod.fst).all fun u => (succsO f u).all fun v =>
      v == f.entry || (t.parent v).isSome

/-- Dominator sets with a union at joins (the classic sign error). -/
def domSetsUnion (f : Func) : List (Label × List Label) :=
  let reach := reachable f
  let init := reach.map fun v => (v, if v = f.entry then [f.entry] else [])
  let round (d : List (Label × List Label)) : List (Label × List Label) :=
    reach.map fun v =>
      if v = f.entry then (v, [f.entry]) else
      let ps := (predsOf f reach v).flatMap fun p => (d.lookup p).getD []
      (v, (v :: ps).eraseDups)
  (List.range (reach.length + 1)).foldl (fun d _ => round d) init

/-- `dominatesB` read off union dominator sets. -/
def domUnion (f : Func) (a v : Label) : Bool := ((domSetsUnion f).lookup v).any (a ∈ ·)

/-- The first version of `useOk`: a definition in the same block was also accepted through
`dominatesB` (every block dominates itself), so a use **before** the definition passed. -/
def useOkLoose (f : Func) (t : DomTree) (l : Label) (k : Nat) (x : Var) : Bool :=
  match defSite f x with
  | some (d, j) => (decide (d = l) && decide (j < k)) || dominatesB t d l
  | none => false

/-- `checkSSA` with `useOkLoose`. -/
def checkSSALoose (f : Func) (t : DomTree) : Bool :=
  decide ((f.blocks.flatMap fun b => b.insts.flatMap (·.outs)).Nodup) &&
  f.blocks.all fun b => b.insts.zipIdx.all fun (i, k) =>
    if i.op = .phi then
      (phiVarSources i.args).all fun (p, x) =>
        match defSite f x with
        | some (d, _) => dominatesB t d p
        | none => false
    else (varsOf i.args).all (useOkLoose f t b.label k)

/-- `checkSSA` that skips φ instructions. -/
def checkSSANoPhi (f : Func) (t : DomTree) : Bool :=
  checkSSA { f with blocks := f.blocks.map fun b =>
    { b with insts := b.insts.filter (·.op != .phi) } } t

/-! ## Running -/

/-- Seeded configuration (`TESTING.md` E3). -/
def cfg : Configuration := { numInst := 300, maxSize := 30, randomSeed := some 20261015,
                             quiet := true }

/-- Fail the build on a counterexample or on too few valid inputs (counts printed). -/
def expectHolds (name : String) (p : Prop)
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] : IO Unit :=
  discard <| EvmYul.CountedTesting.holdsCore cfg name p' (EvmYul.CountedTesting.defaultMinValid cfg)

/-- Mutation test: fail the build unless a counterexample is found (counts printed). -/
def expectRefuted (name : String) (p : Prop)
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] : IO Unit :=
  discard <| EvmYul.CountedTesting.refutedCore cfg name p'

/-- A deterministic pseudo-random number. -/
def mixD (x : Nat) : Nat := (x + 1) * 0x9E3779B97F4A7C15 % 2 ^ 61

/-- Deterministic graphs for the coverage lines. -/
def detGraph (i : Nat) (phi : Bool := false) : Func :=
  graphOf (mixD i % 7) ((List.range 7).map fun j =>
    (mixD (i * 7 + j) % 4, mixD (i + j * 3) % 9, mixD (i * j + 1) % 9, mixD (i + 5 * j) % 9)) phi

/-- Run everything; throws on the first failure. -/
def runAll : IO Unit := do
  let text ← IO.FS.readFile "docs/research/venom/store_bb_runtime_0.4.3.txt"
  let some store := parseFunc? text | throw <| IO.userError "§1: the store.vy fixture does not parse"
  -- §1
  let checks := unitChecks store
  for (name, ok) in checks do
    unless ok do throw <| IO.userError s!"§1 unit check failed: {name}"
  IO.println s!"§1 dominance: {checks.length} unit checks passed"
  -- §2
  expectHolds "§2 random graphs: the computed tree is accepted and equals the oracle exactly"
    (∀ (n : Nat) (bs : List (Nat × Nat × Nat × Nat)),
      (match domTree? (graphOf n bs) with
       | some t => treeMatchesOracle (graphOf n bs) t true
       | none => false) = true)
  let gs := (List.range 300).map fun i => detGraph i
  let unreach := (gs.filter fun f => (reachO f).length < f.blocks.length).length
  let loops := (gs.filter fun f => (reachO f).any fun v => (succsO f v).any fun w =>
    dominatesB (computeDomTree f) w v).length
  let deep := (gs.filter fun f => (computeDomTree f).idom.any fun (_, p) => p ≠ f.entry).length
  IO.println s!"§2 coverage (300 graphs): with an unreachable block {unreach}, with a back edge (to a \
    dominator) {loops}, with a parent other than the entry {deep}"
  unless unreach ≥ 30 ∧ loops ≥ 30 ∧ deep ≥ 30 do
    throw <| IO.userError "§2 coverage: a region is empty or too small (A2)"
  -- §3
  expectHolds "§3 re-parented certificates: whenever checkTree accepts, every claim holds"
    (∀ (n : Nat) (bs : List (Nat × Nat × Nat × Nat)) (i j : Nat),
      (!checkTree (graphOf n bs) (mutant (graphOf n bs) i j) ||
        treeMatchesOracle (graphOf n bs) (mutant (graphOf n bs) i j) false) = true)
  let ms := (List.range 300).map fun i => (detGraph i, mutant (detGraph i) (mixD i) (mixD (i + 1)))
  let acc := (ms.filter fun (f, t) => checkTree f t ∧ t ≠ computeDomTree f).length
  let rej := (ms.filter fun (f, t) => !checkTree f t).length
  IO.println s!"§3 coverage (300 mutants): changed and still accepted (re-parented to a dominator) \
    {acc}, rejected {rej}"
  unless acc ≥ 20 ∧ rej ≥ 50 do
    throw <| IO.userError "§3 coverage: the accepted or the rejected region is too small (A2)"
  -- §4
  expectHolds "§4 strict SSA: checkSSA = the oracle's verdict (uses and φ sources)"
    (∀ (n : Nat) (bs : List (Nat × Nat × Nat × Nat)) (phi : Bool),
      (match domTree? (graphOf n bs phi) with
       | some t => checkSSA (graphOf n bs phi) t == ssaO (graphOf n bs phi)
       | none => false) = true)
  let ss := (List.range 300).map fun i => detGraph i (i % 2 == 0)
  let ok := (ss.filter ssaO).length
  IO.println s!"§4 coverage (300 graphs): strict SSA {ok}, not {300 - ok}"
  unless ok ≥ 30 ∧ 300 - ok ≥ 30 do
    throw <| IO.userError "§4 coverage: a verdict is too rare (A2)"
  -- §5
  expectRefuted "§5 canary: a tree check without the edge condition is unsound"
    (∀ (n : Nat) (bs : List (Nat × Nat × Nat × Nat)) (i j : Nat),
      (!checkTreeNoEdge (graphOf n bs) (mutant (graphOf n bs) i j) ||
        treeMatchesOracle (graphOf n bs) (mutant (graphOf n bs) i j) false) = true)
  expectRefuted "§5 canary: dominator sets with a union at joins"
    (∀ (n : Nat) (bs : List (Nat × Nat × Nat × Nat)),
      ((reachO (graphOf n bs)).all fun v => (reachO (graphOf n bs)).all fun a =>
        domUnion (graphOf n bs) a v == domO (graphOf n bs) a v) = true)
  expectRefuted "§5 canary: the first useOk (a later definition in the same block accepted)"
    (∀ (n : Nat) (bs : List (Nat × Nat × Nat × Nat)),
      (match domTree? (graphOf n bs) with
       | some t => checkSSALoose (graphOf n bs) t == ssaO (graphOf n bs)
       | none => false) = true)
  expectRefuted "§5 canary: an SSA check that ignores phis"
    (∀ (n : Nat) (bs : List (Nat × Nat × Nat × Nat)),
      (match domTree? (graphOf n bs true) with
       | some t => checkSSANoPhi (graphOf n bs true) t == ssaO (graphOf n bs true)
       | none => false) = true)
  IO.println "dominance: standing caveat (D1): the oracle is a breadth-first search written here; the \
    soundness of the check itself is the theorem checkTree_sound"

#eval runAll

end EvmYul.Venom.DominanceTests
