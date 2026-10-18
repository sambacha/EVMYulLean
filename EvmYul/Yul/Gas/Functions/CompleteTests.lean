module

public import EvmYul.Yul.Gas.Functions.CompleteTestHarness
public meta import EvmYul.Yul.Gas.Functions.CompleteTestHarness
@[expose] public meta section

/-!
# Regression tests for Yul gas with user-defined functions (`Functions/Basic.lean`, `Functions/Complete.lean`)

These run **during `lake build EvmYulGasTests`**; any failing check fails the build.

The test contract `codeT` defines six functions: `inc`, `twice` (calls `inc` twice, depth 2), the
recursive `fact`, `sumTo` (a loop inside a function), and the mutually recursive `even`/`odd`. The
interpreter runs with code override `some codeT` from a state whose code owner has an account.

Caller programs are random lists of statements: the arithmetic/memory/`if`/`switch`/`break`
statements of `Gas/MeteredTests.lean` plus calls of `twice`, `fact(b mod 6)`, `sumTo(b mod 8)`, `inc` and, now
and then, of a function that does not exist.

1. **Unit tests**: gas, result and minimal budgets computed by hand (with `cancunFn.call = 21`).
2. **Property tests** (Plausible, fixed seed):
   * the interpreter, with random fuel, runs out of fuel or returns exactly what `runF` returns
     (mirrors `exec_complete_runF`), and with enough fuel it never runs out (non-vacuity);
   * every successful metered run costs at most `gasF` (mirrors `runF_gas_le`), and budgets
     `(8, 7)` always succeed (non-vacuity);
   * larger budgets give the same result and gas (mirrors `runF_mono`);
   * `fact(k)` needs call-depth budget exactly `k + 1`;
   * for straight-line, break-free programs calling only `inc` and `twice`, the gas is **exactly**
     `gasF` at depth 2 (the bound is attained);
   * on call-free programs `runF` is `execL` and `gasF` is `gasLS` (mirrors `runF_of_fragLS`,
     `gasF_of_fragLS`).
3. **Mutation tests**: Plausible must refute a bound with one call level fewer, a bound that leaves
   out the call overhead, a meter with a fixed depth budget of 3, reversed depth monotonicity, and a
   bound that charges every callee as if it made no calls.
-/

namespace EvmYul.Yul.GasTests.CompleteTests

open Plausible Ast Relational Gas LoopsTests
open EvmYul.Testing.EvmFixtures

/-- Named unit checks; each must evaluate to `true`. -/
def unitChecks : List (String × Bool) :=
  [ ("a user call costs PUSH + 2 JUMP + 2 JUMPDEST = 3 + 2 * (8 + 1) = 21", cancunFn.call == 21),
    ("fact(5) = 120, gas = 21 + 14 + 5 * 43 = 250", mObsF 8 6 (pFact 5) == some ("ok [120, 0, 0, 0]", 250)),
    ("fact(5): the interpreter agrees", eObsF 3000 (pFact 5) == some "ok [120, 0, 0, 0]"),
    ("fact(5): depth budget 6 suffices, 5 does not",
      (mObsF 8 6 (pFact 5)).isSome && (mObsF 8 5 (pFact 5)).isNone),
    ("fact(5): larger budgets give the same result and gas", mObsF 20 11 (pFact 5) == mObsF 8 6 (pFact 5)),
    ("fact(5): static bound at depth 6 = 21 + 6 * 43 = 279 (29 above the run: the deepest untaken branch)",
      gasF cancunFn tblT 8 6 (pFact 5) == 279),
    ("twice(3) = 5, gas = 21 + 2 * (21 + 3) = 69, depth 2", mObsF 0 2 pTwice == some ("ok [5, 0, 0, 0]", 69)),
    ("twice(3): depth budget 1 is too small", (mObsF 0 1 pTwice).isNone),
    ("twice(3): the bound at depth 2 is attained (69); at depth 1 it is 63, below the cost",
      gasF cancunFn tblT 0 2 pTwice == 69 && gasF cancunFn tblT 0 1 pTwice == 63),
    ("sumTo(4) = 6, gas = 21 + 4 * 20 + 14 = 115, iteration budget 4",
      mObsF 4 1 pSum == some ("ok [6, 0, 0, 0]", 115) && (mObsF 3 1 pSum).isNone),
    ("even(4) = 1 by mutual recursion, gas = 21 + 14 + 4 * 38 = 187, depth 5",
      mObsF 0 5 pEven == some ("ok [1, 0, 0, 0]", 187) && (mObsF 0 4 pEven).isNone),
    ("even(4): the interpreter agrees", eObsF 3000 pEven == some "ok [1, 0, 0, 0]"),
    ("a call of a missing function fails and costs only the call overhead (21)",
      mObsF 0 1 pMissing == some ("error", 21) && eObsF 3000 pMissing == some "error"),
    ("loop calling sumTo: v0 = 3 -> 3 -> 3 -> 3 (sumTo(3) = 3), gas = 3 * (14 + 95 + 3) + 14 = 350",
      mObsF 3 1 pLoopCall == some ("ok [3, 0, 0, 0]", 350)),
    ("loop calling sumTo: the interpreter agrees", eObsF 3000 pLoopCall == some "ok [3, 0, 0, 0]"),
    ("generated programs with calls are in the fragment, not in the call-free one",
      fragFS (genFProg false [] (List.range 60)) && !fragLS (genFProg false [] (List.range 60))),
    ("every function of the test contract is in the fragment",
      [fInc, fTwice, fFact, fSum, fEven, fOdd].all fun | .Def _ _ b => fragFB b)
  ]

/-- Run every check; throws on the first failure. -/
def runAll : IO Unit := do
  for (name, ok) in unitChecks do
    unless ok do throw <| IO.userError s!"unit check failed: {name}"
  IO.println s!"{unitChecks.length} unit checks passed"
  -- Mirrors `exec_complete_runF`.
  yHolds "exec with calls (random fuel) runs out of fuel or returns the metered result"
    (∀ f : ℕ, ∀ init ns : List ℕ,
      CountedTesting.WhenSome (eObsF (fuelAt f (fnFuel ns)) (genFProg false init ns)) fun o =>
        (mObsF 8 7 (genFProg false init ns)).map (·.1) == some o)
  -- Non-vacuity of the property above.
  yHolds "exec with enough fuel never runs out on programs with calls"
    (∀ init ns : List ℕ, (eObsF (fnFuel ns) (genFProg false init ns)).isSome)
  -- Mirrors `runF_gas_le`.
  yHolds "every metered run costs at most gasF"
    (∀ b e : ℕ, ∀ init ns : List ℕ,
      CountedTesting.WhenSome (mObsF (b % 10) (e % 9) (genFProg false init ns)) fun o =>
        o.2 ≤ gasF cancunFn tblT (b % 10) (e % 9) (genFProg false init ns))
  -- Non-vacuity: budgets (8, 7) always suffice.
  yHolds "budgets (8, 7) always suffice"
    (∀ init ns : List ℕ, (mObsF 8 7 (genFProg false init ns)).isSome)
  -- Mirrors `runF_mono`.
  yHolds "larger budgets give the same result and gas"
    (∀ b e b' e' : ℕ, ∀ init ns : List ℕ,
      CountedTesting.WhenSome (mObsF (b % 10) (e % 9) (genFProg false init ns)) fun o =>
        mObsF (b % 10 + b' % 4) (e % 9 + e' % 4) (genFProg false init ns) == some o)
  -- Minimal depth.
  yHolds "fact(k) needs call-depth budget exactly k + 1"
    (∀ k : ℕ, (mObsF 0 (k % 12 + 1) (pFact (k % 12))).isSome ∧
      (mObsF 0 (k % 12) (pFact (k % 12))).isNone)
  -- The bound is attained.
  yHolds "straight-line programs calling inc/twice are charged exactly gasF at depth 2"
    (∀ init ns : List ℕ,
      (mObsF 0 2 (genSProg init (noBreak ns))).map (·.2) ==
        some (gasF cancunFn tblT 0 2 (genSProg init (noBreak ns))))
  -- Mirrors `runF_of_fragLS` and `gasF_of_fragLS`.
  yHolds "on call-free programs runF is execL and gasF is gasLS"
    (∀ b e : ℕ, ∀ init ns : List ℕ,
      mObsF (b % 10) (e % 9) (genProg false init ns) ==
          ((execL cancun (b % 10) (genProg false init ns) sF).map fun (r, g) => (obs r, g)) ∧
        gasF cancunFn tblT (b % 10) (e % 9) (genProg false init ns) =
          gasLS cancun (b % 10) (genProg false init ns))
  IO.println "8 property suites passed"
  -- Mutation tests.
  yRefuted "mutant bound: one call level fewer"
    (∀ k : ℕ, (mObsF 0 (k % 12 + 1) (pFact (k % 12))).all fun o =>
      o.2 ≤ gasF cancunFn tblT 0 (k % 12) (pFact (k % 12)))
  yRefuted "mutant bound: no call overhead"
    (∀ init ns : List ℕ, (mObsF 8 7 (genFProg false init ns)).all fun o =>
      o.2 ≤ gasF noCallModel tblT 8 7 (genFProg false init ns))
  yRefuted "mutant meter: a call-depth budget of 3 matches the interpreter"
    (∀ k : ℕ, (eObsF 3000 (pFact (k % 8))).all fun o =>
      (mObsF 0 3 (pFact (k % 8))).map (·.1) == some o)
  yRefuted "mutant: depth monotonicity reversed"
    (∀ k e : ℕ, (mObsF 0 (e % 9 + 1) (pFact (k % 8))).isSome →
      (mObsF 0 (e % 9) (pFact (k % 8))).isSome)
  yRefuted "mutant bound: callees charged as if they made no calls"
    (∀ init ns : List ℕ, (mObsF 8 7 (genFProg false init ns)).all fun o =>
      o.2 ≤ flatBound 8 (genFProg false init ns))

#eval runAll

end EvmYul.Yul.GasTests.CompleteTests
