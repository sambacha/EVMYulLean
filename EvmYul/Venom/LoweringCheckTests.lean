module

public import EvmYul.Venom.LoweringCheckTestHarness
public meta import EvmYul.Venom.LoweringCheckTestHarness
public import EvmYul.Testing.Counted
public meta import EvmYul.Testing.Counted
public import Plausible
public meta import Plausible

@[expose] public meta section

/-!
# Tests of the lowering checker: SWAP/POP schedules, the freshness counterexample, canaries

`validateLowering_sound` proves the checker sound. These tests check what the proof does not
cover: that the checker is useful (it accepts the schedules a scheduler really emits) and that every
condition in it is needed. Each section names the `TESTING.md` rule it applies.

1. **§1 Unit checks.**
   * The proved compiler's output is accepted.
   * A `SWAP` schedule is accepted, and the same code without its `SWAP` is rejected.
   * A schedule that `POP`s dead values compiles `deepProg d` for `d` = 16, 40 and 100. The proved
     compiler rejects these programs because the operand is out of `DUP16`'s reach.
2. **§2 The freshness counterexample (falsification, proved by `decide`).** `naiveValidate` is the
   checker without its freshness condition. It accepts a lowering of a program that assigns `%1`
   twice, and that lowering returns different data (`naive_unsound`). The real checker rejects it
   (`validateLowering_rejects_stale`).
3. **§3 Counted properties (A2) over random fragment programs**, run over a test machine whose
   effects depend on the state:
   * S1 (completeness against the proved compiler): every compiled program is accepted.
   * S2 (padding): inserting `PUSH n; POP` pairs is accepted, the outcome, data and state are
     unchanged, and the gas grows by exactly `W_verylow + W_base` per pair.
   * S3 (`SWAP` scheduler): a scheduler that pushes binary operands in list order and fixes the order
     with `SWAP1` is accepted, and its outcome, data and state agree with the semantics.
   * S4 (soundness on stale-copy schedules): on programs that may assign a variable twice, a
     scheduler that loads the **oldest** copy of a variable is accepted only when that is
     correct.
4. **§4 Canaries (E1).**
   * The `SWAP` scheduler without its `SWAP`s is not always accepted.
   * The naive checker on stale-copy schedules is not sound.
   * An unbalanced `PUSH` inside the code is not always accepted. The same `PUSH` before
     everything is harmless, and a control property checks that it is accepted and correct.
-/

namespace EvmYul.Venom.LoweringCheckTests

open EvmYul.Venom Plausible Plausible.Decorations GasConstants

/-! ## §1 Unit checks -/

#guard (compiledS subProg).any fun c => validateLowering subProg c []
#guard validateLowering subProg subSwapped [] && sameObs subProg subSwapped
#guard !validateLowering subProg subUnswapped []
-- the rejection is not over-cautious: without the swap the stored value really differs
#guard !sameObs subProg subUnswapped
#guard [16, 40, 100].all fun d =>
  (compile (deepProg d)).isNone && validateLowering (deepProg d) (deepPopped d) [] &&
    sameObs (deepProg d) (deepPopped d)
-- the boundary of the proved scheme is unchanged: 15 still compiles
#guard (compile (deepProg 15)).isSome

/-! ## §2 The freshness counterexample -/

/-- The checker **without** the freshness condition (the first design). -/
def naiveValidate : Program → List SAsm → List Operand → Bool
  | p, .push n :: c, S => naiveValidate p c (.lit n :: S)
  | p, .dup k :: c, S =>
    decide (1 ≤ k ∧ k ≤ 16 ∧ k ≤ S.length) && naiveValidate p c (S.getD (k - 1) default :: S)
  | p, .swap k :: c, S =>
    decide (1 ≤ k ∧ k ≤ 16 ∧ k < S.length) && naiveValidate p c (swapTop k S)
  | p, .pop :: c, S =>
    match S with
    | [] => false
    | _ :: S' => naiveValidate p c S'
  | [], [], _ => true
  | [], .halt .stop :: _, _ => true
  | .pure d o args :: rest, .op o' :: c, S =>
    o == o' && args.length == o.arity && S.take o.arity == args &&
      naiveValidate rest c (.var d :: S.drop o.arity)
  | .eff dst e args :: rest, .eff e' :: c, S =>
    e == e' && args.length == e.arity && S.take e.arity == args &&
      match dst with
      | some d => e.produces && naiveValidate rest c (.var d :: S.drop e.arity)
      | none => !e.produces && naiveValidate rest c (S.drop e.arity)
  | .assert a :: rest, .assertJ :: c, a' :: S => a == a' && naiveValidate rest c S
  | .halt h args :: _, .halt h' :: _, S =>
    h == h' && args.length == h.arity && S.take h.arity == args
  | _, _, _ => false

/-- `%1 = add 1, 1; %1 = add 5, 5; return %1, %1` (not SSA: `%1` is assigned twice). -/
def redefProg : Program :=
  [.pure 1 .add [L 1, L 1], .pure 1 .add [L 5, L 5], .halt .ret [.var 1, .var 1]]

/-- Code that keeps the first `%1` (value 2) on the stack and returns it as the second word. -/
def redefCode : List SAsm :=
  [.push (word 1), .push (word 1), .op .add, .push (word 5), .push (word 5), .op .add, .halt .ret]

/-- **The naive checker is unsound.** It accepts `redefCode`, which returns `[10, 2]` where the
program returns `[10, 10]`. -/
theorem naive_unsound :
    naiveValidate redefProg redefCode [] = true ∧
      (runSAsm unitPrims redefCode [] () 0).map Final.data = some [word 10, word 2] ∧
      (run unitPrims redefProg Store.empty () 0).map Final.data = some [word 10, word 10] := by
  decide

/-- The real checker rejects the same pair: `%1` is defined while its old copy is on the stack. -/
theorem validateLowering_rejects_stale : validateLowering redefProg redefCode [] = false := by
  decide

/-! ## Running -/

/-- Seeded configuration (`TESTING.md` E3). -/
def cfg : Configuration := { numInst := 300, maxSize := 30, randomSeed := some 20261012,
                             quiet := true }

/-- Fail the build on a counterexample or on too few valid inputs (counts printed). -/
def expectHolds (name : String) (p : Prop)
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] : IO Unit :=
  discard <| EvmYul.CountedTesting.holdsCore cfg name p' (EvmYul.CountedTesting.defaultMinValid cfg)

/-- Mutation test: fail the build unless a counterexample is found (counts printed). -/
def expectRefuted (name : String) (p : Prop)
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] : IO Unit :=
  discard <| EvmYul.CountedTesting.refutedCore cfg name p'

/-- S1: the proved compiler's output is accepted. -/
def lawS1 (xs : List (ℕ × ℕ × ℕ × ℕ)) (t : ℕ) : Bool :=
  let p := decodeProg xs t false true
  match compiledS p with
  | some c => validateLowering p c [] && sameObs p c
  | none => true

/-- S2: padded compiled code is accepted, ends the same way, and costs exactly the padding more. -/
def lawS2 (xs : List (ℕ × ℕ × ℕ × ℕ)) (t : ℕ) (pos : List ℕ) : Bool :=
  let p := decodeProg xs t false false
  match compiledS p with
  | some c =>
    let (c', m) := pad pos c
    validateLowering p c' [] && sameObs p c' &&
      (match gasOf p c' with
       | (some g₁, some g₂) => g₁ == g₂ + m * (Gverylow + Gbase)
       | _ => false)
  | none => true

/-- S3: the `SWAP1` scheduler's output is accepted and ends the same way. -/
def lawS3 (xs : List (ℕ × ℕ × ℕ × ℕ)) (t : ℕ) : Bool :=
  let p := decodeProg xs t false true
  match lowerWith false true [] p with
  | some c => validateLowering p c [] && sameObs p c
  | none => true

/-- S4 / canary: on programs that may assign twice, a checker that accepts the oldest-copy
scheduler's output must be right. -/
def soundOnStale (check : Program → List SAsm → List Operand → Bool)
    (xs : List (ℕ × ℕ × ℕ × ℕ)) (t : ℕ) : Bool :=
  let p := decodeProg xs t true true
  match lowerWith true false [] p with
  | some c => !check p c [] || sameObs p c
  | none => true

/-- The scheduler and the compiler agree when nothing is swapped and the newest copy is loaded
(the harness is the compiler's scheme, `TESTING.md` D). -/
def harnessMatchesCompiler (xs : List (ℕ × ℕ × ℕ × ℕ)) (t : ℕ) : Bool :=
  let p := decodeProg xs t true true
  lowerWith false false [] p == compiledS p

/-- Run everything; throws on the first failure. -/
def runAll : IO Unit := do
  -- A2 coverage of the generators: how many programs compile, use the stack beyond 2 slots, revert,
  -- and (for S4) assign a variable twice while its old copy is live, and are accepted
  let gen := (List.range 300).map fun i =>
    ((List.range (i % 20)).map fun j => (i * 7 + j * 13, i + j * 5, i * j + 3, j * 11 + i), i)
  let progs := gen.map fun (xs, t) => decodeProg xs t false true
  let compiled := (progs.filter fun p => (compile p).isSome).length
  let reverted := (progs.filter fun p =>
    (run testPrims p Store.empty [] 0).any (·.outcome == .reverted)).length
  let stale := gen.map fun (xs, t) => decodeProg xs t true true
  let staleOk := (stale.filter fun p => match lowerWith true false [] p with
    | some c => validateLowering p c []
    | none => false).length
  let staleWrong := (stale.filter fun p => match lowerWith true false [] p with
    | some c => naiveValidate p c [] && !sameObs p c
    | none => false).length
  IO.println s!"§3 coverage (300 programs): compile {compiled}, revert {reverted}; \
    stale-copy schedules accepted by the checker {staleOk}, accepted by the naive checker and \
    wrong {staleWrong}"
  unless compiled ≥ 150 ∧ reverted ≥ 10 ∧ staleWrong ≥ 1 do
    throw <| IO.userError "§3 coverage: a generator region is empty or too small (A2)"
  -- §3
  expectHolds "§3 harness scheduler (newest copy, no swap) = the proved compiler"
    (∀ (xs : List (ℕ × ℕ × ℕ × ℕ)) (t : ℕ), harnessMatchesCompiler xs t = true)
  expectHolds "§3 S1 compiled code is accepted and agrees with the semantics"
    (∀ (xs : List (ℕ × ℕ × ℕ × ℕ)) (t : ℕ), (compile (decodeProg xs t false true)).isSome = true →
      lawS1 xs t = true)
  expectHolds "§3 S2 PUSH/POP padding: accepted, same result, gas + 5 per pair"
    (∀ (xs : List (ℕ × ℕ × ℕ × ℕ)) (t : ℕ) (pos : List ℕ),
      (compile (decodeProg xs t false false)).isSome = true → lawS2 xs t pos = true)
  expectHolds "§3 S3 SWAP1 scheduler: accepted and agrees with the semantics"
    (∀ (xs : List (ℕ × ℕ × ℕ × ℕ)) (t : ℕ),
      (lowerWith false true [] (decodeProg xs t false true)).isSome = true → lawS3 xs t = true)
  expectHolds "§3 S4 oldest-copy scheduler on non-SSA programs: accepted ⇒ correct"
    (∀ (xs : List (ℕ × ℕ × ℕ × ℕ)) (t : ℕ), soundOnStale validateLowering xs t = true)
  -- §4
  expectRefuted "§4 canary: the SWAP1 scheduler without its SWAPs is always accepted"
    (∀ (xs : List (ℕ × ℕ × ℕ × ℕ)) (t : ℕ),
      (match lowerWith false true [] (decodeProg xs t false true) with
       | some c => validateLowering (decodeProg xs t false true) (c.filter (· != .swap 1)) []
       | none => true) = true)
  expectRefuted "§4 canary: the checker without freshness is sound on oldest-copy schedules"
    (∀ (xs : List (ℕ × ℕ × ℕ × ℕ)) (t : ℕ), soundOnStale naiveValidate xs t = true)
  -- An extra item at the very bottom is harmless (DUP counts from the top, and a halt ignores what
  -- lies below its operands): the first version of this canary prepended the PUSH and was never
  -- refuted. Inside the code it shifts every later DUP by one.
  expectRefuted "§4 canary: an unbalanced PUSH inside the code is always accepted"
    (∀ (xs : List (ℕ × ℕ × ℕ × ℕ)) (t j : ℕ),
      (match compiledS (decodeProg xs t false true) with
       | some c =>
         let k := j % max c.length 1
         validateLowering (decodeProg xs t false true) (c.take k ++ .push (word 0) :: c.drop k) []
       | none => true) = true)
  -- … and the benign variant really is benign: accepted and correct on every program
  expectHolds "§4 control: an extra PUSH below everything is accepted and harmless"
    (∀ (xs : List (ℕ × ℕ × ℕ × ℕ)) (t : ℕ), (compile (decodeProg xs t false true)).isSome = true →
      (match compiledS (decodeProg xs t false true) with
       | some c => validateLowering (decodeProg xs t false true) (.push (word 0) :: c) [] &&
           sameObs (decodeProg xs t false true) (.push (word 0) :: c)
       | none => false) = true)

#eval runAll

end EvmYul.Venom.LoweringCheckTests
