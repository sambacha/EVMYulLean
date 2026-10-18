module

public import EvmYul.Yul.Gas.ConventionTestHarness
public meta import EvmYul.Yul.Gas.ConventionTestHarness
public import EvmYul.Yul.Gas.Functions.OracleTestHarness
public meta import EvmYul.Yul.Gas.Functions.OracleTestHarness
@[expose] public meta section

/-!
# The testing conventions (`TESTING.md` B5, D–G) applied to the Yul gas layer

Built by `lake build EvmYulGasTests`. Continues `ConventionTests.lean` (groups A–C) with oracles
(D), meta-properties of the suite itself (E), Lean-specific rigor (F), the computed detection
budget of the Plausible suites (B5) and the printed detection surface (G2). Every check is
deterministic: the corpus is fixed, and the Plausible runs use the fixed seed of `ycfg`.
-/

namespace EvmYul.Yul.GasTests.ConventionMetaTests

open Plausible Plausible.Decorations Ast Relational Gas LoopsTests NestedLoopsTests ConventionTests
open EvmYul.Testing.EvmFixtures
  CompleteTests

/-! ## D1: an oracle by a different route — unrolling

For a straight-line, break-free body, a loop of `k` iterations is computed three ways: by the
single-loop meter `loopG` (`Loops.lean`), by the nested-loop meter `execL` (`NestedLoops.lean`) and
by the **loop-free** meter `execG` (`Metered.lean`) on the *unrolled* program
`(body ++ post)^k`, plus `k + 1` exit tests priced from the Yellow Paper constants directly
(`LT` = G_verylow 3, `JUMPI` = G_high 10, `JUMPDEST` = 1). The unrolled route shares no loop code
with the other two, so a fault in either loop driver shows up as a disagreement. -/

/-- The unrolled program's statements. -/
def unrolled (k : ℕ) (body : List Stmt) : List Stmt :=
  (List.replicate k (body ++ lPost)).flatten

/-- The unrolling oracle: full observation and gas. -/
def unrollOracle (k : ℕ) (init : List ℕ) (body : List Stmt) : String × ℕ :=
  let o := blockG cancun (unrolled k body) (startState init)
  (obsFull o.1, o.2 + (k + 1) * (3 + 10 + 1))

/-- The two loop meters, observed. -/
def loopRoutes (k : ℕ) (init : List ℕ) (body : List Stmt) : (String × ℕ) × Option (String × ℕ) :=
  let lo := loopG cancun 1000 (lCond k) lPost body (startState init)
  ((obsFull lo.res, lo.gas),
   (execL cancun k (.For (lCond k) lPost body) (startState init)).map fun o => (obsFull o.1, o.2))

/-- Mutant loop meter for E1: the post block is not charged. -/
def noPostGas (k : ℕ) (init : List ℕ) (body : List Stmt) : ℕ :=
  (loopRoutes k init body).1.2 - k * gasB cancun lPost

#eval show IO Unit from do
  let mut n := 0
  for (i, ns) in corpus 80 do
    for k in boundChoices do
      let body := lBody true (noBreak ns)
      let (lo, el) := loopRoutes k i body
      let u := unrollOracle k i body
      check s!"D1: loopG = unrolled execG (k = {k})" (lo == u)
      check s!"D1: execL = unrolled execG (k = {k})" (el == some u)
      n := n + 1
  IO.println s!"D1 diverse derivation: loopG, execL and unrolled execG agree on {n} loops \
    (full observation and gas)"

/-! ## D2: round trips as directional (Galois) laws, exhaustively at the boundary

The Yul builtin ↔ EVM opcode correspondence: `ofEVM ∘ toEVM = some` on all 80 builtins (no
information lost), and `toEVM ∘ ofEVM ⊑ id` on **all 256** decoded EVM bytes (the adversarial side:
PUSH/DUP/SWAP/JUMP… have no Yul builtin and must map to `none`, never to a wrong builtin). -/

#eval show IO Unit from do
  check "D2: ofEVM (toEVM op) = some op for all 80 builtins"
    (allPrims.all fun op => ofEVM (toEVM op) == some op)
  -- undefined bytes all decode to `INVALID`, so the distinct decoded operations are compared
  let ops := decodedOps.eraseDups
  let back := ops.filterMap fun w => (ofEVM w).map fun op => (w, op)
  check "D2: ofEVM w = some op → toEVM op = w on all decoded bytes"
    (back.all fun (w, op) => toEVM op == w)
  check "D2: the image of ofEVM is exactly the 80 builtins" (back.length == allPrims.length)
  IO.println s!"D2 Galois laws: 80 builtins round-trip; {decodedOps.length} EVM bytes = \
    {ops.length} distinct operations, {back.length} with a builtin, {ops.length - back.length} \
    correctly unmapped"

/-! ## D3: golden corpus (recorded before any refactor)

Each entry pins the gas and a hash of the **full** observation (C3: hash the whole observable state,
not selected fields). A behaviour change must edit this table in the same change, marked
`GOLDEN-CHANGE` with a reason.

The hashes are a regression snapshot: they detect change, not correctness. The gas values are
not taken on trust from the meters they pin: every one is re-derived below by the counting oracle
of `FunctionOracleTestHarness`, which shares no metering code with `execL` or `runF` (it rewrites
the program so that every builtin and branch adds its price to a transient-storage counter, and runs
the result on the unmetered reference interpreter). An entry whose program ends in an error has no
final state and hence no counter; for those the oracle must return `none` and the meter an error. -/

/-- Loop-free / nested programs: `(name, program, gas, hash of obsFull)`, metered by `execL 20`. -/
def goldenLoops : List (String × Stmt × ℕ × UInt64) :=
  [("threeAdds", threeAdds, 9, 2164731397093606266),
   ("guarded 2", guarded 2, 19, 10146044737136225840),
   ("guarded 9", guarded 9, 14, 10605576756710413732),
   ("p1", p1, 74, 16600968470034078228),
   ("p34", p34, 347, 8754049063622203868),
   ("p33", p33, 287, 614901708344349517),
   ("pBreak", pBreak, 107, 11157833768211450989),
   ("p222", p222, 360, 2944884584090605889),
   ("wall program", genProg false [2 ^ 256 - 1, 1, 2 ^ 255, 0] (List.range 30), 62,
     2818210400395222591),
   ("straight program", genProg true [5, 7, 11, 13] ((List.range 30).map (· * 7)), 113,
     3921204902459665405),
   ("nested 3x4 generated", nestProg 3 4 false [5, 7, 11, 13] [1, 2, 3, 4, 5, 6, 7], 941,
     5115548147933337715)]

/-- Programs with user calls, metered by `runF` with budgets `(9, 8)`. -/
def goldenFns : List (String × Stmt × ℕ × UInt64) :=
  [("fact 5", pFact 5, 250, 4121079534768834365),
   ("twice 3", pTwice, 69, 10508955057609955635),
   ("sumTo 4", pSum, 115, 15430090028176410141),
   ("even 4", pEven, 187, 7406910987974698418),
   ("missing", pMissing, 21, 13431977735815460035),
   ("loop calling sumTo", pLoopCall, 350, 12661288873623566900),
   ("generated calls", genFProg false [] (List.range 40), 49, 15496303966070417168)]

/-- Entries marked `GOLDEN-CHANGE` (none since recording). -/
def goldenChanges : List (String × String) := []

/-- Fuel for the counting oracle on the golden programs (ample: the oracle turns every builtin
into a call, so it needs far more fuel than the meters' budgets). -/
def goldenOracleFuel : ℕ := 100000

/-- Independent provenance of a golden gas value `g` for program `p`: the counting oracle either
measures exactly `g`, or yields no state at all, in which case the user-function meter must report
an error for `p` (an erroring program leaves no counter to read). -/
def goldenAgreesWithOracle (p : Stmt) (g : ℕ) : Bool :=
  match OracleTests.oracle cancunFn true goldenOracleFuel p with
  | some (_, g') => g' == g
  | none => (runF cancunFn (some codeT) 9 8 p sF).any fun (r, _) => r matches .error _

/-- Does meter `M` reproduce the loop golden corpus? -/
def goldenLoopsOk (M : Meter) : Bool :=
  goldenLoops.all fun (_, p, g, h) => (M 20 p).map (fun o => (o.2, hash o.1)) == some (g, h)

/-- Does the user-function meter with cost model `c` reproduce the function golden corpus? -/
def goldenFnsOk (c : FnCostModel) : Bool :=
  goldenFns.all fun (_, p, g, h) =>
    (runF c (some codeT) 9 8 p sF).map (fun o => (o.2, hash (obsFull o.1))) == some (g, h)

#eval show IO Unit from do
  for (name, p, g, h) in goldenLoops do
    check s!"D3 golden: {name}" ((realMeter 20 p).map (fun o => (o.2, hash o.1)) == some (g, h))
  check "D3 golden: user-function programs" (goldenFnsOk cancunFn)
  for (name, p, g, _) in goldenLoops ++ goldenFns do
    check s!"D3 golden provenance: {name}" (goldenAgreesWithOracle p g)
  IO.println s!"D3 golden corpus: {goldenLoops.length + goldenFns.length} entries, \
    {goldenChanges.length} GOLDEN-CHANGE; every gas value re-derived by the counting oracle"

/-! ## E1: mutation adequacy per module (with an order-2 spot check)

Every mutant is run against the laws above; `MA = detected / planted` is printed per module. An
undetected mutant fails the build unless it is in `justifiedNeutral` with a reason. -/

/-- A planted mutant and whether some law of the suite rejects it. -/
structure Mutant where
  name : String
  module : String
  detected : Bool

/-- Cost-model mutant: `ADD` priced like `MUL` (G_low = 5). -/
def addAsLow : CostModel := { cancun with prim := fun op => if op == .ADD then 5 else cancun.prim op }

/-- Cost-model mutant: branches are free. -/
def freeBranch : FnCostModel := { cancunFn with branch := 0 }

/-- The meter with an arbitrary cost model, observed (for cost-model mutants). -/
def meterWith (c : CostModel) : Meter := fun n p =>
  (execL c n p s0).map fun o => (obsFull o.1, o.2)

/-- Loop-free corpus programs. -/
def flatProgs : List Stmt := (corpus 200).map fun (i, ns) => genProg false i ns

/-- Order-2 pair: exit test charged twice **and** the bound raised by the same 14 gas. -/
def mExitTwiceBound (n : ℕ) (p : Stmt) : ℕ := gasLS cancun n p + (if fragS p then 0 else 14)

/-- The catalogue. -/
def yulMutants : List Mutant :=
  let states := a4States
  [ ⟨"bound forgets if bodies", "Metered",
      flatProgs.any fun p => gasOf p > badGasS p⟩,
    ⟨"bound takes the cheapest switch branch", "Metered",
      flatProgs.any fun p => gasOf p > minGasS p⟩,
    ⟨"meter forgets memory writes", "Metered",
      flatProgs.any fun p => some (obsFull (clearMem (execG cancun p s0).1)) != execObs (fuelS p) p⟩,
    ⟨"cost model: ADD priced G_low", "CostModel",
      !(allPrims.all fun op => (yulFeeGroup op).staticCost?.isNone ||
        addAsLow.prim op == EVM.C' evmS (toEVM op)) || !goldenLoopsOk (meterWith addAsLow)⟩,
    ⟨"cost model: branches free", "CostModel",
      !goldenLoopsOk (meterWith freeBranch.toCostModel) || !goldenFnsOk freeBranch⟩,
    ⟨"loop exit test charged twice", "NestedLoops",
      states.any fun st => !(failing mExitTwice st).isEmpty⟩,
    ⟨"charge per unit of budget", "NestedLoops",
      states.any fun st => !(failing mBudget st).isEmpty⟩,
    ⟨"clamp instead of reject", "NestedLoops",
      nests.any fun x => match nStar x with
        | some n => !rejectsBelow mClamp (nestOf x) n
        | none => false⟩,
    ⟨"bound with one iteration fewer", "NestedLoops",
      states.any fun (p, _, n) => (realMeter n p).any fun o => o.2 > gasLS cancun (n - 1) p⟩,
    ⟨"inner loop charged once", "NestedLoops",
      (corpus 40).any fun (i, ns) => [(2, 3), (3, 3), (5, 2)].any fun (a, b) =>
        (mObs (maxIters a b) (nestProg a b true i (noBreak ns))).any fun o =>
          o.2 > onceBound (maxIters a b) a b (lBody true (noBreak ns))⟩,
    ⟨"post block not charged", "Loops",
      (corpus 40).any fun (i, ns) => [2, 5].any fun k =>
        noPostGas k i (lBody true (noBreak ns)) != (unrollOracle k i (lBody true (noBreak ns))).2⟩,
    ⟨"bound without call overhead", "Functions",
      fnCorpus.any fun (i, ns) => (mObsF 9 8 (genFProg false i ns)).any fun o =>
        o.2 > gasF noCallModel tblT 9 8 (genFProg false i ns)⟩,
    ⟨"fixed call depth 3", "Functions",
      (List.range 8).any fun k => (mObsF 0 3 (pFact k)).map (·.1) != eObsF 3000 (pFact k)⟩,
    ⟨"callees charged as if they made no calls", "Functions",
      fnCorpus.any fun (i, ns) => (mObsF 8 7 (genFProg false i ns)).any fun o =>
        o.2 > flatBound 8 (genFProg false i ns)⟩,
    -- order-2: the two faults mask each other for the bound conjunct C₁; the golden corpus and the
    -- unrolling oracle (different routes) still see the meter fault
    ⟨"order-2: exit charged twice + bound raised by 14", "NestedLoops",
      !(states.all fun (p, _, n) => (mExitTwice n p).all (·.2 ≤ mExitTwiceBound n p)) ||
        !goldenLoopsOk mExitTwice⟩ ]

/-- Undetected mutants that are semantically neutral, with the reason (none at present). -/
def justifiedNeutral : List (String × String) := []

#eval show IO Unit from do
  let ms := yulMutants
  let mods := (ms.map (·.module)).eraseDups
  let mut lines := #[]
  for m in mods do
    let xs := ms.filter (·.module == m)
    lines := lines.push s!"{m}: MA = {(xs.filter (·.detected)).length}/{xs.length}"
  for m in ms do
    unless m.detected || justifiedNeutral.any (·.1 == m.name) do
      throw <| IO.userError s!"E1: undetected, unjustified mutant [{m.module}] {m.name}"
  -- the order-2 pair is masked for the bound conjunct alone (K2 evidence): only another route sees it
  check "E1 order-2: the pair is invisible to the bound conjunct alone"
    (a4States.all fun (p, _, n) => (mExitTwice n p).all (·.2 ≤ mExitTwiceBound n p))
  IO.println s!"E1 Yul mutation adequacy per module: {String.intercalate ", " lines.toList}; \
    order-2 pair masked for C₁, caught by the golden corpus"

/-- The counterexample Plausible reports for `p` under the Yul suites' fixed-seed `ycfg`. -/
def yCounterexample (p : Prop) (p' : Decorations.DecorationsOf p := by mk_decorations)
    [Testable p'] : IO (Option (List String)) := do
  match ← Testable.checkIO p' ycfg with
  | .failure _ xs _ => pure (some xs)
  | _ => pure none

/-! ### Harness self-test: the counted-law runner can fail

`countedLaw` must reject a violated law, a law whose antecedent never holds non-trivially (A2:
decorative), and a law with too few valid samples; otherwise every count it prints is worthless. -/

#eval show IO Unit from do
  let xs := List.range 50
  let violated ← (countedLaw "seed: violated" xs (fun _ => true) (fun _ => true) (· < 49)).toBaseIO
  let decorative ← (countedLaw "seed: decorative" xs (fun _ => true) (fun _ => false)
    (fun _ => true)).toBaseIO
  let scarce ← (countedLaw "seed: scarce" xs (· == 3) (fun _ => true) (fun _ => true)
    (minValid := 2)).toBaseIO
  let fine ← (countedLaw "seed: fine" xs (· % 2 == 0) (· > 10) (· < 50)).toBaseIO
  check "harness self-test: violated, decorative and scarce laws are rejected; a sound law passes"
    (violated matches .error _ && decorative matches .error _ && scarce matches .error _ &&
      fine matches .ok _)
  IO.println "harness self-test: countedLaw rejects violated / decorative / scarce laws"

/-! ## E2: shrinking stays inside the precondition

A shrinker for `∀ x, P x → Q x` must map the subtype `{x // P x}` to itself. `shrinkPre` filters its
candidates by `P` (soundness proved below), and the minimiser reports how much of its budget was
spent on candidates outside the feasible set, and whether the final counterexample sits on the
feasibility edge (every further shrink leaves `P`), which deserves extra suspicion. -/

/-- Shrink candidates: drop one element, or halve one element. -/
def shrinkCands (ns : List ℕ) : List (List ℕ) :=
  (List.range ns.length).map ns.eraseIdx ++
    (List.range ns.length).filterMap fun i =>
      let v := ns.getD i 0
      if v = 0 then none else some (ns.set i (v / 2))

/-- Candidates that keep the precondition. -/
def shrinkPre (pre : List ℕ → Bool) (ns : List ℕ) : List (List ℕ) := (shrinkCands ns).filter pre

/-- **Shrinker soundness**: every candidate satisfies the precondition. -/
theorem shrinkPre_sound {pre : List ℕ → Bool} {ns x : List ℕ} (h : x ∈ shrinkPre pre ns) :
    pre x = true := (List.mem_filter.mp h).2

/-- Greedy minimisation of a counterexample to `law` under `pre`: `(result, steps, discarded)`,
where `discarded` counts candidates rejected for violating `pre`. -/
def minimize (pre law : List ℕ → Bool) : ℕ → List ℕ → List ℕ × ℕ × ℕ
  | 0, ns => (ns, 0, 0)
  | fuel + 1, ns =>
    let cands := shrinkCands ns
    let disc := (cands.filter fun c => !pre c).length
    match (shrinkPre pre ns).find? fun c => !law c with
    | none => (ns, 0, disc)
    | some c => let (r, s, d) := minimize pre law fuel c; (r, s + 1, d + disc)

#eval show IO Unit from do
  -- the refuted conjecture "programs of ≥ 3 statements without `if` that end normally are charged
  -- exactly the static bound" (false: `switch` branches differ in cost). The precondition is
  -- restrictive: halving a statement number often turns it into an `if` (residue 2 mod 9).
  let init : List ℕ := [5, 7, 11, 13]
  let pre := fun ns : List ℕ =>
    ns.length ≥ 3 && ns.all (· % 9 != 2) && endsOk (genProg false init ns)
  let law := fun ns => gasOf (genProg false init ns) == gasS cancun (genProg false init ns)
  let some start := (corpus 300).map (·.2) |>.find? fun ns => pre ns && !law ns
    | throw <| IO.userError "E2: no counterexample to the refuted law"
  let (m, steps, disc) := minimize pre law 200 start
  check "E2: the minimal counterexample satisfies the precondition" (pre m)
  check "E2: … and still refutes the law" (!law m)
  check "E2: the shrinker met infeasible candidates (the precondition was exercised)" (disc > 0)
  check "E2: every accepted candidate kept the precondition"
    ((shrinkPre pre m).all pre && (shrinkPre pre start).all pre)
  let edge := (shrinkCands m).all fun c => !pre c || law c
  let outside := ((shrinkCands m).filter fun c => !pre c).length
  IO.println s!"E2 shrinking: {start} ↦ {m} in {steps} steps; {disc} candidates discarded for \
    leaving the precondition; final: {outside}/{(shrinkCands m).length} neighbours infeasible, \
    locally minimal={edge}"
  -- Plausible's own shrinker on a guarded Yul property keeps the guard
  match ← yCounterexample (∀ init ns : List ℕ, endsOk (genProg false init ns) →
      gasOf (genProg false init ns) = gasS cancun (genProg false init ns)) with
  | some xs =>
    check s!"E2: Plausible's shrunk counterexample carries its guard: {xs}"
      (xs.any fun x => x.startsWith "guard:")
  | none => throw <| IO.userError "E2: expected a counterexample"

/-! ## E3: randomized tests are reproducible -/

/-- The counterexample Plausible reports for a refuted Yul property under `ycfg`. -/
def yulCounterexample : IO (Option (List String)) :=
  yCounterexample (∀ init ns : List ℕ, gasOf (genProg false init ns) ≤ minGasS (genProg false init ns))

#eval show IO Unit from do
  let a ← yulCounterexample
  let b ← yulCounterexample
  check "E3: a Yul counterexample exists" a.isSome
  check "E3: same seed, same counterexample" (a == b)
  IO.println s!"E3 reproducibility: two runs of a seeded Yul property give {a}"

/-! ## F1: exhaustive single-statement sweep

`genStmt_periodic` proves that every statement the generator can produce is `genStmt s n` for some
`n < 1872`. The sweep runs every one of them (both `straight` settings) after each of the five
boundary-heavy initialisations: 18720 programs, no sampling. -/

#eval show IO Unit from do
  let mut total := 0
  let mut straightOk := 0
  for straight in [false, true] do
    for init in initChoices do
      for n in List.range stmtPeriod do
        let p := genProg straight init [n]
        let r := (execG cancun p s0).1
        check s!"F1: interpreter = meter (n = {n})" (execObs (fuelS p) p == some (obsFull r))
        check s!"F1: FragBoundLaw (n = {n})" (decide (FragBoundLaw p s0))
        check s!"F1: enough fuel (n = {n})" (execObs (enoughFuel [n]) p).isSome
        if straight && endsOk p then
          check s!"F1: exactness (n = {n})" (gasOf p == gasS cancun p)
          straightOk := straightOk + 1
        total := total + 1
  IO.println s!"F1 exhaustive sweep: {total} programs (every generated statement × 5 inits); \
    exactness exercised on {straightOk}"

/-! ## F2: lawfulness through the interpreter

The interpreter runs in `Except Yul.Exception`, a lawful monad. The meter threads gas with
`addGas`, a monoid action (proved below). Sequencing of statement blocks is the Kleisli
composition that both run: it must be associative with the empty block as unit — checked through
the interpreter and the meter, with continuations that read state and branch (`if`/`switch`). -/

example : LawfulMonad (Except Yul.Exception) := inferInstance

theorem addGas_zero_left (o : Option (Res × ℕ)) : addGas 0 o = o := by
  rcases o with _ | ⟨r, g⟩ <;> simp [addGas]

theorem addGas_addGas (a b : ℕ) (o : Option (Res × ℕ)) :
    addGas a (addGas b o) = addGas (a + b) o := by
  rcases o with _ | ⟨r, g⟩ <;> simp [addGas, Nat.add_assoc]

#eval show IO Unit from do
  let mut n := 0
  for (i, ns) in corpus 150 do
    let ini := (List.range 4).map fun j => Stmt.Let [vr j] (some (lit (i.getD j j)))
    let a := ns.take 2 |>.map (genStmt false)
    let b := (ns.drop 2).take 3 |>.map (genStmt false)
    let c := ns.drop 5 |>.map (genStmt false)
    let left : Stmt := .Block (ini ++ [.Block [.Block a, .Block b], .Block c])
    let right : Stmt := .Block (ini ++ [.Block a, .Block [.Block b, .Block c]])
    let unitL : Stmt := .Block (ini ++ [.Block [], .Block a])
    let unitR : Stmt := .Block (ini ++ [.Block a, .Block []])
    let plain : Stmt := .Block (ini ++ [.Block a])
    check "F2: associativity (meter)" (realMeter 0 left == realMeter 0 right)
    check "F2: associativity (interpreter)" (execObs 300 left == execObs 300 right)
    check "F2: left/right unit (meter)"
      (realMeter 0 unitL == realMeter 0 plain && realMeter 0 unitR == realMeter 0 plain)
    check "F2: left/right unit (interpreter)"
      (execObs 300 unitL == execObs 300 plain && execObs 300 unitR == execObs 300 plain)
    n := n + 1
  IO.println s!"F2 monad laws through the interpreter: associativity and units on {n} programs \
    with branching statements; addGas action laws proved"

/-! ## F3: the tested statement is the proved statement

`FragBoundLaw`, `NestedBoundLaw`, `GasMonoLaw` and `FnBoundLaw` are single definitions, proved by
the theorems below and decided — the same definitions — on the corpora. -/

example := fragBoundLaw_holds
example := nestedBoundLaw_holds
example := gasMonoLaw_holds
example := fnBoundLaw_holds

#eval show IO Unit from do
  check "F3: FragBoundLaw decided on the corpus" (flatProgs.all fun p => decide (FragBoundLaw p s0))
  check "F3: NestedBoundLaw and GasMonoLaw decided on the corpus"
    (nests.all fun x => (List.range 6).all fun n =>
      decide (NestedBoundLaw n (nestOf x) s0) && decide (GasMonoLaw n 3 (nestOf x) s0))
  check "F3: FnBoundLaw decided on the corpus"
    (fnCorpus.all fun (i, ns) => (List.range 4).all fun d =>
      decide (FnBoundLaw 9 d (genFProg false i ns)))
  IO.println "F3 shared statements: 4 laws proved and decided on the same definitions"

/-! ## B5: computed detection budget of the Plausible suites

The Yul Plausible suites draw `List ℕ` with `ycfg` (200 instances, sizes shrinking from 40). Below,
the same generator is sampled with the same seed and size schedule, and for each statement kind of
`genStmt` the per-draw probability `p̂` that a program contains it is estimated. The probability
of hitting the kind at least once in one run is `1 − (1 − p̂)^200`. A kind is *covered by sampling*
only if that is `≥ 0.99`, i.e. `n·p̂ ≥ ln 100 ≈ 4.61` draws expected; every other kind must be
covered deterministically — and all kinds are, by the F1 sweep. -/

/-- `ycfg.numInst` lists from Plausible's generator, with Plausible's size schedule and seed. -/
def plausibleLists : IO (List (List ℕ)) :=
  runRandWith (ycfg.randomSeed.getD 0) do
    let n := ycfg.numInst
    let mut out := []
    for i in List.range n do
      let size := (n - i - 1) * ycfg.maxSize / n
      let xs ← (Arbitrary.arbitrary : Gen (List ℕ)).resize (fun _ => size)
      out := xs :: out
    return out

/-- Statement kinds of `genStmt false`: the nine residues, with `break` split out of residue 8. -/
def kindOf (n : ℕ) : ℕ := if n % 9 = 8 ∧ (n / 9) % 13 = 0 then 9 else n % 9

#eval show IO Unit from do
  let xs ← plausibleLists
  let n := xs.length
  let names := ["let+add", "let+mul", "if", "switch", "iszero", "pop", "mstore", "mload",
    "and", "break"]
  let mut lines := #[]
  let mut sampled := 0
  for k in List.range 10 do
    let hits := (xs.filter fun ns => ns.any fun m => kindOf m == k).length
    let p : ℚ := hits / n
    let det := 1 - (1 - p) ^ n
    -- every kind is covered by the exhaustive F1 sweep (genStmt_periodic), sampled or not
    check s!"B5: kind {names.getD k ""} is in the F1 domain"
      ((List.range stmtPeriod).any fun m => kindOf m == k)
    if det ≥ 99 / 100 then sampled := sampled + 1
    lines := lines.push s!"{names.getD k ""}: n·p̂={hits} P≈{(det * 1000).floor}/1000"
  IO.println s!"B5 detection budget of the Yul Plausible suites (n = {n}): \
    {String.intercalate ", " lines.toList}; {sampled}/10 kinds covered by sampling (P ≥ 0.99), \
    all 10 covered exhaustively by F1"

/-! ## G2: detection surface of the Yul gas layer -/

#eval IO.println "G2 Yul detection surface: A1/A2/A3/A4/B1/B3/C1–C4 lines (ConventionTests), \
  D1–D3, E1–E3, F1–F3, B5 lines above. CAVEAT: every check is internal to the specification \
  (the Yul semantics and the Cancun cost model). The 11-gas branch and 21-gas call are measured \
  on the EVM semantics as strict floors of their lowerings (LoweringTests); which lowering solc \
  emits is not checked here; see docs/CONJECTURES.md K6, K11–K13."

end EvmYul.Yul.GasTests.ConventionMetaTests
