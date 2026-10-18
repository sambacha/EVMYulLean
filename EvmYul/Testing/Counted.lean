module

public import Plausible
public meta import Plausible

@[expose] public meta section

/-!
# A Plausible runner that counts how often the precondition held (`TESTING.md` A2)

Plausible's `Testable.checkIO` returns only `success`, `gaveUp n` or `failure`. For an implication
`∀ x, P x → Q x` it discards every input with `¬ P x` (a guard failure is `gaveUp 1`), retries up
to `numRetries` times per sample, and reports `success` as soon as **one** sample got through: of
300 requested samples, 299 can be discarded and the run still "passes". The final result carries no
count, so the old harnesses could not print, let alone check, how many inputs the conclusion was
actually tested on.

`runCounted` re-implements Plausible's suite loop (`Testable.runSuiteAux`) on top of the same
per-input primitive, `Testable.runProp`, with the same sizes, the same retry policy and the same
random-number stream, and counts as it goes:

* `total`: inputs generated (retries included);
* `valid`: inputs on which every guard held, so the conclusion was evaluated;
* `discarded = total − valid`.

`checkCounted` turns this into a test verdict: it fails on a counterexample (with Plausible's shrunk
witness), and it fails when `valid < minValid`, by default **half of the requested samples**. A
property whose precondition rarely holds can therefore no longer pass silently; a suite that needs
a lower floor must say so at the call site.

Because the loop draws exactly the random numbers `runSuiteAux` draws, a property that has no
guard sees exactly the inputs it saw under `checkIO` (checked below: same first counterexample on
seeded mutants).
-/

namespace EvmYul.CountedTesting

open Plausible Plausible.Decorations

/-- What a counted run observed. -/
structure Counts where
  /-- Samples requested (`numInst`). -/
  samples : Nat
  /-- Inputs generated, retries after a failed guard included. -/
  total : Nat
  /-- Inputs on which every guard held (the conclusion was evaluated). -/
  valid : Nat
  /-- Plausible found a proof of the whole property (a closed decidable proposition). -/
  proved : Bool := false
  deriving Repr, DecidableEq

/-- Inputs rejected by a guard. -/
def Counts.discarded (c : Counts) : Nat := c.total - c.valid

instance : ToString Counts where
  toString c := s!"total={c.total} valid={c.valid} discarded={c.discarded}" ++
    (if c.proved then " (proved)" else "")

/-- Outcome of a counted run. -/
inductive Outcome where
  /-- No counterexample. -/
  | passed (c : Counts)
  /-- A counterexample (Plausible's shrunk witness, as printed by Plausible). -/
  | refuted (c : Counts) (witness : List String)
  deriving Repr

/-- One sample: up to `retries` inputs until the guards hold (Plausible's `retry`). Returns the
result of the last input and the number of inputs used. -/
def sample {p : Prop} (cmd : Gen (TestResult p)) : Nat → Nat → Gen (TestResult p × Nat)
  | 0, used => return (.gaveUp 1, used)
  | k + 1, used => do
    match ← cmd with
    | .gaveUp _ => sample cmd k (used + 1)
    | r => return (r, used + 1)

/-- The counted suite loop: `n` samples left, counts so far. Mirrors `Testable.runSuiteAux`. -/
def loop (p : Prop) [Testable p] (cfg : Configuration) : Nat → Counts → Gen Outcome
  | 0, c => return .passed c
  | n + 1, c => do
    let size (_ : Nat) := (cfg.numInst - n - 1) * cfg.maxSize / cfg.numInst
    let (r, used) ← sample ((Testable.runProp p cfg true).resize size) cfg.numRetries 0
    let c := { c with total := c.total + used }
    match r with
    | .success (.inl ()) => loop p cfg n { c with valid := c.valid + 1 }
    | .success (.inr _) => return .passed { c with valid := c.valid + 1, proved := true }
    | .gaveUp _ => loop p cfg n c
    | .failure _ xs _ => return .refuted { c with valid := c.valid + 1 } xs

/-- Run `p` with configuration `cfg` (seeded runs are reproducible), counting. -/
def runCounted (p : Prop) [Testable p] (cfg : Configuration) : IO Outcome :=
  let g := loop p cfg cfg.numInst { samples := cfg.numInst, total := 0, valid := 0 }
  match cfg.randomSeed with
  | none => Gen.run g 0
  | some seed => runRandWith seed g

/-- The default floor on `valid`: half of the requested samples. -/
def defaultMinValid (cfg : Configuration) : Nat := (cfg.numInst + 1) / 2

/-- A property test with counts on an already decorated property: prints
`[name] total=… valid=… discarded=…`; fails on a counterexample, and fails when fewer than
`minValid` inputs satisfied the guards (A2: a law that is mostly vacuous is a failing test, not a
passing one). The harnesses `expectHolds` / `yHolds` call this. -/
def holdsCore (cfg : Configuration) (name : String) (p : Prop) [Testable p]
    (minValid : Nat := defaultMinValid cfg) : IO Counts := do
  match ← runCounted p cfg with
  | .refuted c xs => throw <| IO.userError s!"[{name}] COUNTEREXAMPLE after {c}: {xs}"
  | .passed c =>
    unless c.proved || minValid ≤ c.valid do
      throw <| IO.userError
        s!"[{name}] VACUOUS: {c}; at least {minValid} valid inputs required (A2)"
    IO.println s!"[{name}] {c}"
    return c

/-- A mutation test with counts on an already decorated property: fails unless a counterexample is
found; prints how many inputs it took. The harnesses `expectRefuted` / `yRefuted` call this. -/
def refutedCore (cfg : Configuration) (name : String) (p : Prop) [Testable p] :
    IO (Counts × List String) := do
  match ← runCounted p cfg with
  | .refuted c xs =>
    IO.println s!"[{name}] refuted as expected after {c} by {xs}"
    return (c, xs)
  | .passed c => throw <| IO.userError s!"[{name}] expected a counterexample, none found ({c})"

/-- `holdsCore` on a plain proposition (decorated here for readable witnesses). -/
def checkCounted (cfg : Configuration) (name : String) (p : Prop)
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p']
    (minValid : Nat := defaultMinValid cfg) : IO Counts :=
  holdsCore cfg name p' minValid

/-- `refutedCore` on a plain proposition. -/
def refuteCounted (cfg : Configuration) (name : String) (p : Prop)
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] :
    IO (Counts × List String) :=
  refutedCore cfg name p'

/-! ## Antecedents the runner can see

Many laws are implications whose antecedent is hidden inside a Boolean, typically `o.all f` for an
`o : Option _` that is `none` when the interpreter ran out of fuel or a budget was exceeded. Plausible
counts such an input as a pass, so no runner can tell how often `f` was evaluated. `WhenSome o f`
states the same law (`∀ a, o = some a → f a`) but tells the runner that `o = none` is a failed guard:
the input is discarded, retried and counted. -/

/-- `o.all f` as a guarded law: for every `a`, `o = some a` implies `f a`. -/
def WhenSome {α : Type} (o : Option α) (f : α → Bool) : Prop := ∀ a, o = some a → f a = true

theorem whenSome_iff_all {α : Type} (o : Option α) (f : α → Bool) :
    WhenSome o f ↔ o.all f = true := by
  cases o <;> simp [WhenSome]

instance {α : Type} (o : Option α) (f : α → Bool) : Testable (WhenSome o f) where
  run _ _ :=
    match o with
    | none => return .gaveUp 1
    | some a =>
      if hf : f a = true then
        return .success (.inr fun b hb => by obtain rfl := Option.some.inj hb; exact hf)
      else
        return .failure (fun H => hf (H a rfl)) ["issue: the conclusion is false"] 0

/-! ## Self-tests: the counts are right and the runner can fail -/

/-- Configuration of the self-tests. -/
def selfCfg : Configuration := { numInst := 100, maxSize := 100, randomSeed := some 20261008,
                                 quiet := true }

#eval show IO Unit from do
  -- 1. No guard: every input is valid, and exactly one input per sample is drawn.
  let c ← checkCounted selfCfg "self-test: unguarded" (∀ n : Nat, n + 0 = n)
  unless c.total = 100 ∧ c.valid = 100 do
    throw <| IO.userError s!"self-test: unguarded counts wrong: {c}"
  -- 2. A guard that holds on a known fraction: `n % 4 = 0` on `n ≤ size`. The counts must add up,
  --    a substantial number of inputs must be discarded, and the conclusion was evaluated on
  --    every sample whose retries succeeded.
  let c ← checkCounted selfCfg "self-test: guard n % 4 = 0"
    (∀ n : Nat, n % 4 = 0 → n % 2 = 0)
  unless c.valid + c.discarded = c.total ∧ c.discarded ≥ c.valid ∧ c.valid ≥ 50 do
    throw <| IO.userError s!"self-test: guard counts implausible: {c}"
  -- 3. A guard that (almost) never holds must be reported as VACUOUS, not passed. Plausible's own
  --    runner returns `success` here, as soon as one sample gets through.
  let r ← (checkCounted selfCfg "self-test seed: guard n = 77"
    (∀ n : Nat, n = 77 → n = 77)).toBaseIO
  match r with
  | .error e =>
    unless (toString e).startsWith "[self-test seed: guard n = 77] VACUOUS" do
      throw <| IO.userError s!"self-test: wrong failure for a vacuous law: {e}"
  | .ok c => throw <| IO.userError s!"self-test: a vacuous law passed: {c}"
  --    ... whereas Plausible's own runner calls the same law a success (the gap this closes).
  let vacuous := NamedBinder "n" <| ∀ n : Nat, NamedBinder "h" <| n = 77 → n = 77
  match ← Testable.checkIO vacuous selfCfg with
  | .success _ => IO.println "self-test: Plausible's checkIO reports the vacuous law as a success"
  | _ => throw <| IO.userError "self-test: expected checkIO to report the vacuous law as success"
  -- 4. A false property is refuted, and the counterexample is a valid input.
  let (c, xs) ← refuteCounted selfCfg "self-test seed: n < 50"
    (∀ n : Nat, n < 50)
  unless c.valid ≥ 1 ∧ !xs.isEmpty do throw <| IO.userError "self-test: refutation not counted"
  -- 5. Same random stream as `checkIO`: on an unguarded false property both find the same witness.
  let p := NamedBinder "n" <| ∀ n : Nat, NamedBinder "m" <| ∀ m : Nat, n * m < 300
  let w ← match ← Testable.checkIO p selfCfg with
    | .failure _ xs _ => pure xs
    | _ => throw <| IO.userError "self-test: checkIO found no counterexample"
  let (_, w') ← refutedCore selfCfg "self-test seed: n * m < 300 (stream check)" p
  unless w = w' do
    throw <| IO.userError s!"self-test: counted runner diverged from checkIO: {w} vs {w'}"
  -- 6. `WhenSome`: `none` is a discarded input, not a pass; a false conclusion is refuted.
  let c ← checkCounted selfCfg "self-test: WhenSome (n even, half the inputs)"
    (∀ n : Nat, WhenSome (if n % 2 = 0 then some n else none) fun k => k % 2 == 0)
  unless c.discarded ≥ 20 ∧ c.valid = 100 do
    throw <| IO.userError s!"self-test: WhenSome guard not counted: {c}"
  let r ← (checkCounted selfCfg "self-test seed: WhenSome never some"
    (∀ n : Nat, WhenSome (if n = 1000 then some n else none) fun _ => true)).toBaseIO
  if r matches .ok _ then throw <| IO.userError "self-test: WhenSome on `none` only passed"
  discard <| refuteCounted selfCfg "self-test seed: WhenSome with a false conclusion"
    (∀ n : Nat, WhenSome (some n) fun k => k < 20)
  IO.println "CountedTesting self-tests: counts exact on unguarded laws, vacuous laws rejected, \
    refutations counted, same random stream as Plausible's checkIO"

end EvmYul.CountedTesting
