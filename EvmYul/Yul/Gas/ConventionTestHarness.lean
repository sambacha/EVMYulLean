module

public import EvmYul.Yul.Gas.Functions.CompleteTestHarness
public meta import EvmYul.Yul.Gas.Functions.CompleteTestHarness
@[expose] public meta section

/-!
# Shared harness for the Yul gas convention tests (`TESTING.md` A–G)

This module holds what `ConventionTests.lean` and `ConventionMetaTests.lean` share:

* a **counted-law runner** that prints `total / valid / interesting` for every law (rule 0.5, A2)
  and fails when the antecedent is never non-trivially exercised;
* the **full observation** `obsFull` of a Yul result (C2): every variable a test program can bind,
  the active memory words and the memory bytes, the jump kind, and the error (including the state
  carried by `YulHalt`). The earlier suites compared only `obs` (outcome and four variables), a
  sampled-field relation that misses memory;
* a **deterministic corpus** of programs from a fixed linear congruential generator, with
  boundary-heavy initial values (`2^256 − 1`, `2^255`) and loop bounds (`0, 1, 2, 3, 5, 10, 11`);
* the **shared law statements** (F3): each is a `Prop`-valued definition, proved for all inputs here
  and decided — the very same definition — by the tests;
* the **two-tier ∀∃ checker** for the budget-witness law (A1), with its soundness proved.
-/

namespace EvmYul.Yul.GasTests.ConventionTests

open Plausible Ast Relational Gas LoopsTests NestedLoopsTests CompleteTests
open EvmYul.Testing.EvmFixtures

/-! ## Harness -/

/-- Throw a build error unless `b`. -/
def check (name : String) (b : Bool) : IO Unit :=
  unless b do throw <| IO.userError s!"[{name}] FAILED"

/-- Run a law over a sample (rule 0.5 / A2). `pre` is the law's antecedent, `interesting` marks the
samples where the antecedent holds *non-trivially*, `law` is the consequent. Fails on a violation, if
fewer than `minValid` samples satisfy `pre`, or if no valid sample is interesting. Prints the three
counts. Returns the number of interesting samples. -/
def countedLaw {X : Type} (name : String) (xs : List X) (pre interesting law : X → Bool)
    (minValid : ℕ := 1) : IO ℕ := do
  let valid := xs.filter pre
  let bad := valid.filter fun x => !law x
  unless bad.isEmpty do
    throw <| IO.userError s!"[{name}] VIOLATED on {bad.length} of {valid.length} valid samples"
  let intr := (valid.filter interesting).length
  IO.println s!"[{name}] total={xs.length} valid={valid.length} interesting={intr}"
  if valid.length < minValid then
    throw <| IO.userError s!"[{name}] only {valid.length} valid samples (need ≥ {minValid})"
  if intr = 0 then
    throw <| IO.userError s!"[{name}] antecedent never holds non-trivially (decorative law)"
  return intr

/-! ## Full observation (C2) -/

/-- Every identifier a test program can bind (`v0..v3`, loop counters, function locals). -/
def progIds : List Identifier := ["v0", "v1", "v2", "v3", "i", "j", "l", "x", "r", "n"]

/-- The value of every identifier of `progIds` (`none` when unbound). -/
def obsVars (vs : VarStore) : String :=
  toString (progIds.map fun x => (vs.lookup x).map (·.toNat))

/-- Is every bound variable in `progIds`? (If not, `obsVars` would be a sampled-field view.) -/
def scopedIn (vs : VarStore) : Bool := decide (vs.keys ⊆ progIds.toFinset)

/-- Machine state the fragment builtins can change: active words and memory bytes. -/
def obsShared (ss : SharedState .Yul) : String :=
  s!"aw={ss.activeWords.toNat} mem={ss.memory.data.toList}"

/-- Full observation of a Yul state. -/
def obsSt : State → String
  | .Ok ss vs => s!"Ok {obsVars vs} {obsShared ss} scoped={scopedIn vs}"
  | .Checkpoint (.Continue ss vs) => s!"Continue {obsVars vs} {obsShared ss}"
  | .Checkpoint (.Break ss vs) => s!"Break {obsVars vs} {obsShared ss}"
  | .Checkpoint (.Leave ss vs) => s!"Leave {obsVars vs} {obsShared ss}"
  | .OutOfFuel => "OutOfFuel-state"

/-- Full observation of a result. -/
def obsFull : Res → String
  | .ok s => "ok " ++ obsSt s
  | .error (.YulHalt s v) => s!"halt {v.toNat} " ++ obsSt s
  | .error e => "error " ++ reprStr e

/-- The interpreter's full observation, `none` when it runs out of fuel. -/
def execObs (fuel : ℕ) (p : Stmt) (co : Option YulContract := none) (s : State := s0) :
    Option String :=
  match exec fuel p co s with
  | .error .OutOfFuel => none
  | r => some (obsFull r)

/-- A meter, observed: budget ↦ program ↦ (full observation, gas). -/
abbrev Meter := ℕ → Stmt → Option (String × ℕ)

/-- The real nested-loop meter `execL` (Cancun), observed. -/
def realMeter : Meter := fun n p => (execL cancun n p s0).map fun (r, g) => (obsFull r, g)

/-! ## Deterministic corpus -/

/-- One step of a 64-bit linear congruential generator (Knuth's MMIX constants). -/
def lcgNext (s : ℕ) : ℕ := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- `n` pseudo-random values from `seed` (the high bits of successive LCG states). -/
def lcgStream (seed : ℕ) : ℕ → List ℕ
  | 0 => []
  | n + 1 => let s := lcgNext seed; s / 2 ^ 33 :: lcgStream s n

/-- `genStmt` is periodic with period 1872 (see `genStmt_periodic`), so statement numbers are drawn
from `[0, 1872)`, where every distinct generated statement occurs exactly once. -/
def stmtPeriod : ℕ := 1872

/-- Boundary-heavy initial values for `v0..v3`. -/
def initChoices : List (List ℕ) :=
  [[], [0, 0, 0, 0], [2 ^ 256 - 1, 1, 2 ^ 255, 0], [5, 7, 11, 13], [2 ^ 256 - 1, 2 ^ 256 - 1, 3, 2]]

/-- Sample `i` of the corpus: initial values and `i % 13` statement numbers. -/
def corpusEntry (i : ℕ) : List ℕ × List ℕ :=
  (initChoices.getD (i % initChoices.length) [],
   (lcgStream (i + 20261008) (i % 13)).map (· % stmtPeriod))

/-- The first `n` corpus samples. -/
def corpus (n : ℕ) : List (List ℕ × List ℕ) := (List.range n).map corpusEntry

/-- Does an initial-value list contain a value at the `2^256` wall? -/
def wallInit (init : List ℕ) : Bool := init.any (· ≥ 2 ^ 255)

/-- Boundary-heavy loop bounds (below the `NestedLoopsTests` limit of 12). -/
def boundChoices : List ℕ := [0, 1, 2, 3, 5, 10, 11]

/-- Nested-loop corpus: `(k₁, k₂, init, ns)`. -/
def nestCorpus (n : ℕ) : List (ℕ × ℕ × List ℕ × List ℕ) :=
  (List.range n).map fun i =>
    let (init, ns) := corpusEntry (i + 7919)
    (boundChoices.getD (i % 7) 0, boundChoices.getD ((i / 7) % 7) 0, init, ns)

/-- The nested program of a corpus entry. -/
def nestOf : ℕ × ℕ × List ℕ × List ℕ → Stmt
  | (k₁, k₂, init, ns) => nestProg k₁ k₂ false init ns

/-! ## F1: the statement generator is periodic, so `[0, 1872)` is exhaustive -/

theorem vr_add_four_mul (k j : ℕ) : vr (k + 4 * j) = vr k := by
  unfold vr; congr 2; omega

/-- **Coverage proof for the F1 sweep.** Every statement `genStmt` can produce is produced by some
`n < 1872`: the generator only reads `n % 9`, `(n / 9) % 4`, `(n / 36) % 4` and `(n / 9) % 13`. -/
theorem genStmt_periodic (straight : Bool) (n : ℕ) :
    genStmt straight (n + stmtPeriod) = genStmt straight n := by
  have h1 : (n + 1872) / 9 = n / 9 + 4 * 52 := by omega
  have h2 : (n / 9 + 4 * 52) / 4 = n / 9 / 4 + 4 * 13 := by omega
  have h3 : (n / 9 + 4 * 52) % 13 = n / 9 % 13 := by omega
  have h4 : (n + 1872) % 9 = n % 9 := by omega
  simp only [genStmt, stmtPeriod, h1, h2, h3, h4, vr_add_four_mul]

theorem genStmt_mod (straight : Bool) (n : ℕ) :
    genStmt straight (n % stmtPeriod) = genStmt straight n := by
  conv_rhs => rw [← Nat.mod_add_div n stmtPeriod]
  induction n / stmtPeriod with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ, ← Nat.add_assoc, genStmt_periodic, ih]

/-! ## F3: law statements, defined once, proved here, decided by the tests -/

/-- Loop-free bound (`execG_gas_le`). -/
def FragBoundLaw (st : Stmt) (s : State) : Prop := (execG cancun st s).2 ≤ gasS cancun st

instance (st : Stmt) (s : State) : Decidable (FragBoundLaw st s) := by
  unfold FragBoundLaw; infer_instance

theorem fragBoundLaw_holds (st : Stmt) (s : State) : FragBoundLaw st s := execG_gas_le cancun st s

/-- Nested-loop bound (`execL_gas_le`). -/
def NestedBoundLaw (n : ℕ) (st : Stmt) (s : State) : Prop :=
  match execL cancun n st s with
  | none => True
  | some (_, g) => g ≤ gasLS cancun n st

instance (n : ℕ) (st : Stmt) (s : State) : Decidable (NestedBoundLaw n st s) := by
  unfold NestedBoundLaw; split <;> infer_instance

theorem nestedBoundLaw_holds (n : ℕ) (st : Stmt) (s : State) : NestedBoundLaw n st s := by
  unfold NestedBoundLaw
  split
  · trivial
  · next h => exact execL_gas_le cancun n st s h

/-- Budget monotonicity, gas part (`execL_mono`): a run within budget `n` is charged the same gas
with budget `n + d`, and does not start failing. -/
def GasMonoLaw (n d : ℕ) (st : Stmt) (s : State) : Prop :=
  match execL cancun n st s, execL cancun (n + d) st s with
  | none, _ => True
  | some _, none => False
  | some (_, g), some (_, g') => g = g'

instance (n d : ℕ) (st : Stmt) (s : State) : Decidable (GasMonoLaw n d st s) := by
  unfold GasMonoLaw; split <;> infer_instance

theorem gasMonoLaw_holds (n d : ℕ) (st : Stmt) (s : State) : GasMonoLaw n d st s := by
  unfold GasMonoLaw
  split
  · trivial
  · next o h h' => exact absurd (execL_mono cancun (Nat.le_add_right n d) st s h) (by simp [h'])
  · next r g r' g' h h' =>
    have := execL_mono cancun (Nat.le_add_right n d) st s h
    rw [h'] at this
    simp only [Option.some.injEq, Prod.mk.injEq] at this
    exact this.2.symm

/-- User-function bound (`runF_gas_le`) for the test contract. -/
def FnBoundLaw (n d : ℕ) (st : Stmt) : Prop :=
  match runF cancunFn (some codeT) n d st sF with
  | none => True
  | some (_, g) => g ≤ gasF cancunFn tblT n d st

instance (n d : ℕ) (st : Stmt) : Decidable (FnBoundLaw n d st) := by
  unfold FnBoundLaw; split <;> infer_instance

theorem fnBoundLaw_holds (n d : ℕ) (st : Stmt) : FnBoundLaw n d st := by
  unfold FnBoundLaw
  split
  · trivial
  · next h => exact runF_gas_le cancunFn (tableCovers_some codeT) n d st sF h

/-! ## A1: two-tier checker for the budget-witness law

The law (`exec_eq_execL`): for every loop-fragment program `p` and fuel `f` on which the
interpreter does not run out of fuel, **there exists** a budget `n` at which `execL` returns the
interpreter's result. The tests draw `(p, f)` from an adversarial universal generator, search `n`
with an incomplete solver, and accept only witnesses the checker confirms. -/

/-- The witness relation, observationally: budget `n` reproduces the interpreter's result. -/
def BudgetWitness (p : Stmt) (f n : ℕ) : Prop :=
  ∃ r g, execL cancun n p s0 = some (r, g) ∧ obsFull r = obsFull (exec f p none s0)

/-- The checker. -/
def budgetWitnessOk (p : Stmt) (f n : ℕ) : Bool :=
  match execL cancun n p s0 with
  | some (r, _) => obsFull r == obsFull (exec f p none s0)
  | none => false

/-- **Checker soundness** (the only property the tests rely on): an accepted witness is a witness. -/
theorem budgetWitnessOk_sound {p : Stmt} {f n : ℕ} (h : budgetWitnessOk p f n = true) :
    BudgetWitness p f n := by
  unfold budgetWitnessOk at h
  split at h
  · next r g hr => exact ⟨r, g, hr, by simpa using h⟩
  · exact absurd h Bool.false_ne_true

/-- The ∀∃ law itself, proved: the solver may be incomplete, but a witness always exists. -/
theorem budgetWitness_exists {p : Stmt} {f : ℕ} (hf : fragLS p = true)
    (h : exec f p none s0 ≠ OOF) : ∃ n, BudgetWitness p f n := by
  obtain ⟨n, g, hn⟩ := exec_eq_execL cancun hf h
  exact ⟨n, _, g, hn, rfl⟩

/-- The (incomplete) solver: the least budget `≤ 20` the checker accepts. -/
def solveBudget (p : Stmt) (f : ℕ) : Option ℕ :=
  (List.range 21).find? fun n => budgetWitnessOk p f n

/-! ## Definitions of `ConventionTests` (moved here so that `ConventionMetaTests` imports this
harness instead of a test file; `GUIDELINES.md` Rule 3) -/

/-- Fuel that is enough for every nested corpus program (`NestedLoopsTests.nestFuel`). -/
def bigFuel (p : ℕ × ℕ × List ℕ × List ℕ) : ℕ := nestFuel p.2.2.2

/-- The nested corpus used by groups A–C. -/
def nests : List (ℕ × ℕ × List ℕ × List ℕ) := nestCorpus 147

/-- The least budget that reproduces the interpreter's result with enough fuel. -/
def nStar (x : ℕ × ℕ × List ℕ × List ℕ) : Option ℕ := solveBudget (nestOf x) (bigFuel x)

/-- The witness relation for user functions: budgets `(n, d)` reproduce the interpreter. -/
def FnWitness (p : Stmt) (f n d : ℕ) : Prop :=
  ∃ r g, runF cancunFn (some codeT) n d p sF = some (r, g) ∧
    obsFull r = obsFull (exec f p (some codeT) sF)

/-- Checker for `FnWitness`. -/
def fnWitnessOk (p : Stmt) (f n d : ℕ) : Bool :=
  match runF cancunFn (some codeT) n d p sF with
  | some (r, _) => obsFull r == obsFull (exec f p (some codeT) sF)
  | none => false

theorem fnWitnessOk_sound {p : Stmt} {f n d : ℕ} (h : fnWitnessOk p f n d = true) :
    FnWitness p f n d := by
  unfold fnWitnessOk at h
  split at h
  · next r g hr => exact ⟨r, g, hr, by simpa using h⟩
  · exact absurd h Bool.false_ne_true

/-- Incomplete solver: the first `(n, d)` with `n ≤ 9`, `d ≤ 8`, ordered by `n + d`. -/
def solveFn (p : Stmt) (f : ℕ) : Option (ℕ × ℕ) :=
  ((List.range 18).flatMap fun t => (List.range (t + 1)).map fun n => (n, t - n)).find? fun (n, d) =>
    n ≤ 9 && d ≤ 8 && fnWitnessOk p f n d

/-- Function-call corpus: statement numbers cover every `genFStmt` residue. -/
def fnCorpus : List (List ℕ × List ℕ) :=
  (List.range 60).map fun i =>
    ((corpusEntry i).1, (lcgStream (i + 4242) (i % 9)).map (· % (13 * stmtPeriod)))

/-! ## A2: antecedent coverage, propositional and temporal -/

/-- Does a body contain a top-level `break`? -/
def hasTopBreak (body : List Stmt) : Bool := body.any fun | .Break => true | _ => false

/-! ## A4: conjunct liveness of the compound meter invariant

`I(p, n) = C₀ ∧ C₁ ∧ C₂` with `C₀`: the meter's full observation equals the interpreter's, `C₁`:
gas `≤ gasLS n`, `C₂`: budget `n + 3` gives the same answer. Three planted mutants each break one
conjunct; each conjunct must be the *unique* killer on some state (so no conjunct is implied by the
others on the sample), and removing it would let its mutant through on those states. -/

/-- The three conjuncts of `I` for meter `M`, interpreter observation `e`, budget `n`. -/
def conjuncts (M : Meter) (e : String) (n : ℕ) (p : Stmt) : List Bool :=
  [ (M n p).all (·.1 == e),
    (M n p).all (·.2 ≤ gasLS cancun n p),
    (M n p).all fun o => M (n + 3) p == some o ]

/-- Clear the memory bytes of a result (a meter that forgets memory writes). -/
def clearMem : Res → Res
  | .ok (.Ok ss vs) => .ok (.Ok { ss with memory := .empty } vs)
  | r => r

/-- Mutant: forgets memory writes (breaks `C₀`). -/
def mDropMem : Meter := fun n p => (execL cancun n p s0).map fun (r, g) => (obsFull (clearMem r), g)

/-- Mutant: charges the outer loop's exit test (14 gas) twice (breaks `C₁` on tight runs). -/
def mExitTwice : Meter := fun n p =>
  (realMeter n p).map fun (o, g) => (o, if fragS p then g else g + 14)

/-- Mutant: charges one unit per unit of budget (breaks `C₂`). -/
def mBudget : Meter := fun n p =>
  (realMeter n p).map fun (o, g) => (o, if fragS p then g else g + n)

/-- A4 states: the corpus at budgets `n*`, `n* + 1`, `n* + 4`, plus tight straight-line `k × k`
nests at budget `k` (where the bound is attained). -/
def a4States : List (Stmt × String × ℕ) :=
  (nests.flatMap fun x => match nStar x, execObs (bigFuel x) (nestOf x) with
    | some n, some e => [n, n + 1, n + 4].map fun m => (nestOf x, e, m)
    | _, _ => []) ++
  ((corpus 40).flatMap fun (i, ns) => [1, 2, 5].filterMap fun k =>
    let p := nestProg k k true i (noBreak ns)
    (execObs (nestFuel ns) p).map fun e => (p, e, k))

/-- Indices of the conjuncts that fail. -/
def failing (M : Meter) (st : Stmt × String × ℕ) : List ℕ :=
  ((conjuncts M st.2.1 st.2.2 st.1).zipIdx.filter fun (b, _) => !b).map (·.2)

/-! ## B1: thresholds probed at `t − 1`, `t`, `t + 1`, computed exactly

Three thresholds: the least budget `n*`, the least fuel `f*` at which the interpreter does not run
out, and the static bound on tight runs. All are integers, so the neighbours are exact (no `t ± ε`
that could round back onto `t`). The `2^256` wall enters through the initial values. -/

/-- The least fuel `≤ bound` at which the interpreter does not run out. -/
def fStar (p : Stmt) (bound : ℕ) : Option ℕ :=
  (List.range (bound + 1)).find? fun f => (execObs f p).isSome

/-! ## B3: local probing — finite differences at adjacent points

`gasLS n` is a polynomial in the budget `n` whose degree is the loop-nesting depth: its `d`-th
finite difference is a positive constant and its `(d+1)`-th vanishes. The actual gas of a
straight-line loop, as a function of the iteration count `k`, has local Lipschitz constant exactly
`loopIterGas` at *every* adjacent pair (no blow-up anywhere in `[0, 11]`). -/

/-- Forward differences. -/
def diffs : List ℕ → List ℤ
  | a :: b :: rest => ((b : ℤ) - a) :: diffs (b :: rest)
  | _ => []

/-- Forward differences of an integer list. -/
def diffsZ : List ℤ → List ℤ
  | a :: b :: rest => (b - a) :: diffsZ (b :: rest)
  | _ => []

/-- `d`-fold forward difference. -/
def diffN (xs : List ℕ) : ℕ → List ℤ
  | 0 => xs.map (↑)
  | d + 1 => diffsZ (diffN xs d)

/-- A single loop. -/
def p1 : Stmt := .Block [loopInit [0, 0, 0, 0], .For (lCond 3) lPost addBody]

/-! ## C3: replay determinism as a congruence

(i) *Chunking*: running `a ++ b` equals running `a` and then `b` from its end state (gas adds up).
(ii) *Commuting independent events*: two assignments to different variables, neither reading the
other's target, commute (full observation and gas); a dependent pair does not, so the check can
fail. (iii) *Padding*: inserting empty blocks changes neither the full observation nor the gas,
and the interpreter agrees. -/

/-- Run `a`, then `b` from its end state if it ended normally. -/
def seqG (a b : List Stmt) (s : State) : Res × ℕ :=
  match blockG cancun a s with
  | (.ok (.Ok ss vs), g) => let o := blockG cancun b (.Ok ss vs); (o.1, g + o.2)
  | o => o

/-- The statements of `genProg` as a list. -/
def progStmts (i ns : List ℕ) : List Stmt := match genProg false i ns with
  | .Block sts => sts
  | st => [st]

/-- An assignment `x := op(y, c)`. -/
def asg (x y : ℕ) (op : PrimOp) (c : ℕ) : Stmt := .Let [vr x] (some (call op [.Var (vr y), lit c]))

/-- Observed result and gas of a block. -/
def runB (sts : List Stmt) : String × ℕ := let o := blockG cancun sts s0; (obsFull o.1, o.2)

/-! ## C4: the meter rejects; it never clamps

Below the least budget `n*` the meter must return `none` (reject), at **every** smaller budget, not
a truncated success. The planted mutant `mClamp` ("on overflow report success, gas clamped to the
bound") is caught by this law, while it still satisfies the bound law — so only the rejection test
distinguishes rejection from clamping. -/

/-- Mutant: clamps instead of rejecting. -/
def mClamp : Meter := fun n p => match realMeter n p with
  | some o => some o
  | none => (realMeter 20 p).map fun (o, _) => (o, gasLS cancun n p)

/-- The rejection law for meter `M` on program `p` with least budget `n`. -/
def rejectsBelow (M : Meter) (p : Stmt) (n : ℕ) : Bool :=
  (List.range n).all fun m => (M m p).isNone

end EvmYul.Yul.GasTests.ConventionTests
