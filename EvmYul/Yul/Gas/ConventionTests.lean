module

public import EvmYul.Yul.Gas.ConventionTestHarness
public meta import EvmYul.Yul.Gas.ConventionTestHarness
@[expose] public meta section

/-!
# The testing conventions (`TESTING.md` A–C) applied to the Yul gas layer

Built by `lake build EvmYulGasTests`; every check runs during elaboration and a failure fails the
build. The earlier Yul suites (`Tests`, `LoopsTests`, `NestedLoopsTests`, `CompleteTests`) were
written before the conventions were applied to the Yul layer; the audit in `docs/TEST_AUDIT.md`
lists what they lacked. This module closes the gaps of groups A–C; `ConventionMetaTests.lean`
closes D–G. All checks are **deterministic** (the corpus comes from a fixed LCG, see
`Gas/ConventionTestHarness.lean`), so none can be flaky (E3).

Every law prints `total / valid / interesting` counts (rule 0.5, A2).
-/

namespace EvmYul.Yul.GasTests.ConventionTests

open Ast Relational Gas LoopsTests NestedLoopsTests CompleteTests
open EvmYul.Testing.EvmFixtures

/-! ## A1: the ∀∃ budget-witness law, two-tier

Universal generator: every nested corpus program × fuel `{0, 5, 40, 120, bigFuel}` — independent of
the solver, and including fuels at which the interpreter *does* run out (so the precondition is not
drawn from the solver's comfort zone). Checker soundness is the theorem `budgetWitnessOk_sound`;
the law itself is `budgetWitness_exists`. Every universal sample the solver does not solve must be
excluded by the independent reason "the interpreter ran out of fuel" (precondition false). -/

#eval show IO Unit from do
  let mut universal := 0
  let mut excluded := 0
  let mut solved := 0
  let mut nontrivial := 0
  for x in nests do
    for f in [0, 5, 40, 120, bigFuel x] do
      universal := universal + 1
      match execObs f (nestOf x) with
      | none => excluded := excluded + 1
      | some _ =>
        match solveBudget (nestOf x) f with
        | some n => solved := solved + 1; if n ≥ 2 then nontrivial := nontrivial + 1
        | none => throw <| IO.userError s!"A1: no budget witness found for {repr x} at fuel {f}"
  check "A1: the universal generator reaches states where the precondition fails" (excluded > 0)
  check "A1: the solver needs a non-trivial witness (budget ≥ 2) at least once" (nontrivial > 0)
  check "A1: every sample is solved or excluded" (solved + excluded == universal)
  IO.println s!"A1 ∀∃ budget-witness law (nested loops): universal={universal} solved={solved} \
    excluded(out of fuel)={excluded} witness≥2={nontrivial}"

#eval show IO Unit from do
  let mut universal := 0
  let mut excluded := 0
  let mut solved := 0
  let mut deep := 0
  for (init, ns) in fnCorpus do
    let p := genFProg false init ns
    for f in [3, 30, fnFuel ns] do
      universal := universal + 1
      match execObs f p (some codeT) sF with
      | none => excluded := excluded + 1
      | some _ =>
        match solveFn p f with
        | some (_, d) => solved := solved + 1; if d ≥ 3 then deep := deep + 1
        | none => throw <| IO.userError s!"A1: no (n, d) witness for {ns} at fuel {f}"
  check "A1 (functions): precondition fails somewhere" (excluded > 0)
  check "A1 (functions): a call depth ≥ 3 is needed somewhere" (deep > 0)
  IO.println s!"A1 ∀∃ budget-witness law (user functions): universal={universal} solved={solved} \
    excluded(out of fuel)={excluded} depth≥3={deep}"

#eval show IO Unit from do
  -- `straight ∧ ends normally → gas = gasS`; interesting: the bound is not trivially 0.
  let _ ← countedLaw "A2 exactness on straight-line programs"
    (corpus 300) (fun (i, ns) => endsOk (genProg true i ns))
    (fun (i, ns) => gasS cancun (genProg true i ns) > 0)
    (fun (i, ns) => gasOf (genProg true i ns) == gasS cancun (genProg true i ns)) (minValid := 100)
  -- `execL n ≠ none → gas ≤ gasLS n`, at budgets n*, n*+1; interesting: n is exactly the threshold.
  let states := nests.flatMap fun x => match nStar x with
    | some n => [(x, n, true), (x, n + 1, false)]
    | none => []
  let _ ← countedLaw "A2 nested bound (NestedBoundLaw)" states
    (fun (x, n, _) => (realMeter n (nestOf x)).isSome) (fun (_, _, atThreshold) => atThreshold)
    (fun (x, n, _) => decide (NestedBoundLaw n (nestOf x) s0)) (minValid := 100)
  -- Temporal: □(break executed → ◇ loop exits), checked as "a body with a top-level break runs at
  -- most once". The antecedent is non-trivial only when the condition would still allow more
  -- iterations (k ≥ 2): there `break`, not the condition, ends the loop.
  let loops := (corpus 300).flatMap fun (i, ns) => boundChoices.map fun k => (k, i, ns)
  let _ ← countedLaw "A2 temporal □(break → ◇exit), horizon k ≤ 11"
    loops (fun (k, _, ns) => k ≥ 1 && hasTopBreak (lBody false ns)) (fun (k, _, _) => k ≥ 2)
    (fun (k, i, ns) => (mLoop k false i ns).iters ≤ 1) (minValid := 20)

/-! ## A3: liveness is bounded — the horizon is stated and shown to matter

Every Yul result in this repository is *bounded*: loop bounds `< 12`, iteration budget `≤ 20`,
interpreter fuel `≤ nestFuel`. The witness below is the folklore conjecture in executable form:
for every horizon `k ≤ 10`, the meter with budget `k` passes every corpus program whose loops need
at most `k` iterations, yet fails on the program that needs `k + 1`. So no test of horizon `k`
establishes unbounded liveness. The fuel hypothesis (the "fairness" side) is tested separately. -/

#eval show IO Unit from do
  for k in List.range 11 do
    let passes := nests.all fun x => match nStar x with
      | some n => n > k || (realMeter k (nestOf x)).isSome
      | none => true
    let witness := nestWith (k + 1) 1 [0, 0, 0, 0] addBody
    check s!"A3: budget {k} passes every corpus program needing ≤ {k}" passes
    check s!"A3: budget {k} fails at horizon {k + 1}"
      ((realMeter k witness).isNone && (realMeter (k + 1) witness).isSome)
  let fuelOk := nests.all fun x => (execObs (bigFuel x) (nestOf x)).isSome
  check "A3: the fuel hypothesis holds separately (nestFuel never runs out)" fuelOk
  IO.println s!"A3 horizon: loop bounds < 12, budget ≤ 20, fuel ≤ nestFuel; for each k ≤ 10 the \
    budget-k meter passes all corpus programs needing ≤ k and fails at k + 1 \
    (bounded liveness only); fuel hypothesis checked on {nests.length} programs"

#eval show IO Unit from do
  let states := a4States
  check "A4: the real meter satisfies every conjunct on every state"
    (states.all fun st => (failing realMeter st).isEmpty)
  let mut lines := #[]
  for (name, M, i) in [("dropMem", mDropMem, 0), ("exitTwice", mExitTwice, 1),
      ("budget", mBudget, 2)] do
    let unique := (states.filter fun st => failing M st == [i]).length
    check s!"A4: conjunct C{i} is the unique killer of mutant {name} on some state" (unique > 0)
    lines := lines.push s!"{name}→C{i} on {unique}"
  IO.println s!"A4 meter invariant conjunct liveness: {String.intercalate ", " lines.toList}; \
    states={states.length}"

#eval show IO Unit from do
  let mut nProbes := 0
  let mut fProbes := 0
  for x in nests.take 60 do
    let p := nestOf x
    let some n := nStar x | throw <| IO.userError "B1: no least budget"
    let some e := execObs (bigFuel x) p | throw <| IO.userError "B1: out of fuel"
    check "B1: n* reproduces the interpreter" ((realMeter n p).map (·.1) == some e)
    check "B1: n* + 1 gives the same answer" (realMeter (n + 1) p == realMeter n p)
    if n > 0 then
      check "B1: n* − 1 is rejected" (realMeter (n - 1) p).isNone
    nProbes := nProbes + 1
    let some f := fStar p (bigFuel x) | throw <| IO.userError "B1: no least fuel"
    check "B1: f* and f* + 1 agree with the meter"
      (execObs f p == some e && execObs (f + 1) p == some e)
    if f > 0 then check "B1: f* − 1 runs out of fuel" (execObs (f - 1) p).isNone
    fProbes := fProbes + 1
  -- tight runs: the bound is attained, so `bound − 1` is violated (the bound is not loose)
  let tight := (corpus 40).filterMap fun (i, ns) =>
    let p := nestProg 3 3 true i (noBreak ns)
    (realMeter 3 p).map fun (_, g) => (g, gasLS cancun 3 p)
  check "B1: tight runs hit gasLS exactly and exceed gasLS − 1"
    (tight.all fun (g, b) => g == b && g > b - 1)
  let wall := (corpus 300).filter fun (i, _) => wallInit i
  check "B1: the corpus reaches the 2^256 wall" (wall.length > 0)
  check "B1: at the wall the interpreter (fuelS) and the meter agree on the full observation"
    (wall.all fun (i, ns) => execObs (fuelS (genProg false i ns)) (genProg false i ns) ==
      some (obsFull (execG cancun (genProg false i ns) s0).1))
  IO.println s!"B1 thresholds: n*±1 on {nProbes}, f*±1 on {fProbes}, tight bound on {tight.length}, \
    2^256-wall samples {wall.length}"

/-! ## B2 / B4: not applicable (stated, not skipped silently)

Every stage is exact (`ℕ`, `UInt256`), so the error-budget ledger has all `εᵢ = 0` (B2), and no
component claims to sample a distribution (B4). Both premises are checked mechanically by the
suite-wide lint SA7 in `Audits/TestSuite.lean` (no floating point, no decimal literal, no
global RNG in the gas library or any test file). -/

#eval IO.println "B2/B4: N/A — Yul gas arithmetic is exact (ε = 0 at every stage); no component \
  claims a target distribution (premises enforced by TestSuite SA7)"

#eval show IO Unit from do
  for (name, p, d) in [("depth 1", p1, 1), ("depth 2 (p34)", p34, 2), ("depth 3 (p222)", p222, 3)] do
    let g := (List.range 13).map fun n => gasLS cancun n p
    let dd := diffN g d
    let dd1 := diffN g (d + 1)
    check s!"B3: Δ^{d} gasLS constant and positive ({name})"
      (dd.all (· == dd.headD 0) && dd.headD 0 > 0)
    check s!"B3: Δ^{d + 1} gasLS = 0 ({name})" (dd1.all (· == 0))
  let mut probes := 0
  for (i, ns) in corpus 60 do
    let gs := (List.range 12).map fun k => (mLoop k true i (noBreak ns)).gas
    let L := iterG 0 true (noBreak ns)
    check "B3: local Lipschitz constant of loop gas in k is exactly loopIterGas"
      ((diffs gs).all (· == (L : ℤ)))
    probes := probes + 1
  IO.println s!"B3 local probing: Δ^d gasLS for depths 1–3 over n ∈ [0,12]; loop gas Δ_k = \
    loopIterGas on {probes} bodies × 11 adjacent pairs"

/-! ## C1: the invariant folded through every step; no dead ends

For a loop `for {} lt(i, k) {…} {body}` the prefix after `j` iterations is the loop with bound `j`
(the body never touches `i`). At every step: `gas(j) ≤ gas(j+1) ≤ gas(j) + loopIterGas` and
`gas(j) ≤ j · loopIterGas + loopExitGas` (the invariant at index `j`, not only at the end). No
dead end: from every reachable prefix the meter, given one more iteration of budget, continues. -/

#eval show IO Unit from do
  let mut steps := 0
  for (i, ns) in corpus 80 do
    for straight in [true, false] do
      let L := iterG 0 straight ns
      let gs := (List.range 12).map fun j => (mLoop j straight i ns).gas
      for j in List.range 11 do
        let a := gs.getD j 0
        let b := gs.getD (j + 1) 0
        check "C1: per-step increment within [0, loopIterGas]" (a ≤ b && b ≤ a + L)
        check "C1: invariant at every index" (a ≤ j * L + exitG j)
        let pj : Stmt := .Block [loopInit i, .For (lCond (j + 1)) lPost (lBody straight ns)]
        check "C1: no dead end (budget j+1 continues from prefix j)"
          (execL cancun (j + 1) pj s0).isSome
        steps := steps + 1
  IO.println s!"C1 per-step fold: {steps} steps checked (invariant, increment, no dead end)"

/-! ## C2: bisimulation up to the *full* observation

The earlier suites compared `obs` (outcome and `v0..v3`). That relation is blind to memory: the
mutant `clearMem` (a meter that forgets memory writes) agrees with the interpreter under `obs` on
every corpus program, and is caught only by `obsFull`. The agreement laws are therefore restated on
`obsFull`, and every final variable store is checked to bind only identifiers of `progIds` (so the
variable part of `obsFull` is complete). -/

#eval show IO Unit from do
  let progs := (corpus 300).map fun (i, ns) => genProg false i ns
  let mut blindOld := 0
  let mut caughtNew := 0
  for p in progs do
    let r := (execG cancun p s0).1
    check "C2: interpreter = meter on the full observation"
      (execObs (fuelS p) p == some (obsFull r))
    check "C2: the observation covers every bound variable"
      (match r with | .ok (.Ok _ vs) => scopedIn vs | _ => true)
    if obs (clearMem r) == obs r then blindOld := blindOld + 1
    if obsFull (clearMem r) != obsFull r then caughtNew := caughtNew + 1
  check "C2: the old relation `obs` is blind to the memory mutant on every program"
    (blindOld == progs.length)
  check "C2: the full observation catches the memory mutant" (caughtNew > 0)
  -- the same full-observation agreement for nested loops and user functions
  check "C2: nested loops agree on the full observation"
    (nests.all fun x => match nStar x with
      | some n => (realMeter n (nestOf x)).map (·.1) == execObs (bigFuel x) (nestOf x)
      | none => false)
  check "C2: user functions agree on the full observation"
    (fnCorpus.all fun (i, ns) =>
      ((runF cancunFn (some codeT) 9 8 (genFProg false i ns) sF).map (obsFull ·.1)) ==
        execObs (fnFuel ns) (genFProg false i ns) (some codeT) sF)
  IO.println s!"C2 observation: {progs.length} loop-free + {nests.length} nested + \
    {fnCorpus.length} function programs agree on obsFull; memory mutant invisible to obs on \
    {blindOld}, caught by obsFull on {caughtNew}"

#eval show IO Unit from do
  let mut chunks := 0
  let mut indep := 0
  let mut depDiffer := 0
  let mut pads := 0
  for (i, ns) in corpus 200 do
    let sts := progStmts i ns
    for cut in [0, 4, sts.length / 2 + 2, sts.length] do
      let o := seqG (sts.take cut) (sts.drop cut) s0
      check "C3: chunking" ((obsFull o.1, o.2) == runB sts)
      chunks := chunks + 1
    let r := lcgStream (ns.length + i.length + 99) 6
    let x := r.getD 0 0 % 4
    let y := r.getD 1 0 % 4
    let c1 := r.getD 2 0 % 50
    let c2 := r.getD 3 0 % 50
    let x' := (x + 1 + r.getD 4 0 % 3) % 4
    let y' := r.getD 5 0 % 4
    let s1 := asg x y .ADD c1
    let s2 := asg x' y' .MUL c2
    if x' != y && x != y' then
      check "C3: independent assignments commute (full observation and gas)"
        (runB (sts ++ [s1, s2]) == runB (sts ++ [s2, s1]))
      check "C3: independent assignments commute in the interpreter"
        (execObs 200 (.Block (sts ++ [s1, s2])) == execObs 200 (.Block (sts ++ [s2, s1])))
      indep := indep + 1
    -- negative control: `x := x + 1` and `x := x * 2` (same variable) do not commute in general
    let d1 := asg x x .ADD 1
    let d2 := asg x x .MUL 2
    if runB (sts ++ [d1, d2]) != runB (sts ++ [d2, d1]) then depDiffer := depDiffer + 1
    let padded := sts.flatMap fun st => [st, .Block []]
    check "C3: padding with empty blocks" (runB padded == runB sts)
    check "C3: padding in the interpreter" (execObs 400 (.Block padded) == execObs 400 (.Block sts))
    pads := pads + 1
  check "C3: independent pairs were exercised" (indep > 0)
  check "C3: the commutation check can fail (dependent pairs differ)" (depDiffer > 0)
  IO.println s!"C3 congruences: chunking {chunks}, independent commutations {indep} (dependent \
    pairs differing: {depDiffer}), padding {pads}; compared on full observation and gas"

#eval show IO Unit from do
  let mut rejections := 0
  let mut clampCaught := 0
  let mut clampBoundOk := true
  for x in nests do
    let some n := nStar x | throw <| IO.userError "C4: no least budget"
    check "C4: every budget below n* is rejected" (rejectsBelow realMeter (nestOf x) n)
    rejections := rejections + n
    if !rejectsBelow mClamp (nestOf x) n then clampCaught := clampCaught + 1
    clampBoundOk := clampBoundOk && (List.range n).all fun m =>
      (mClamp m (nestOf x)).all (·.2 ≤ gasLS cancun m (nestOf x))
  check "C4: the clamping mutant is caught by the rejection law" (clampCaught > 0)
  check "C4: … and is invisible to the bound law (so rejection must be tested)" clampBoundOk
  check "C4: the fragment checker rejects contract calls"
    (!fragLS (.ExprStmtCall (call .CALL [lit 0, lit 0, lit 0, lit 0, lit 0, lit 0, lit 0])))
  check "C4: a call of a missing function is an error, not a no-op"
    (mObsF 0 1 pMissing == some ("error", 21))
  IO.println s!"C4 rejection: {rejections} below-threshold budgets rejected; clamp mutant caught on \
    {clampCaught} programs (bound law alone: blind)"

end EvmYul.Yul.GasTests.ConventionTests
