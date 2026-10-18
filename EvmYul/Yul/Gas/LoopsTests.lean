module

public import EvmYul.Yul.Gas.LoopsTestHarness
public meta import EvmYul.Yul.Gas.LoopsTestHarness
@[expose] public meta section

/-!
# Regression tests for Yul loop gas (`Loops.lean`)

These run **during `lake build EvmYulGasTests`**; any failing check fails the build.

The test loops count a variable `i` from `0` to `k` (`k < 12`):

```
for {} lt(i, k) { i := add(i, 1) } { body }
```

The body is a random list of generated statements (`genStmt` from `Gas/MeteredTests.lean`): arithmetic,
memory, `pop`, `break`, and (unless the loop is straight-line) `if` and `switch`. The body never
touches `i`, so a loop without `break` runs exactly `k` times.

1. **Unit tests**: concrete loops whose gas, iteration count and result are computed by hand.
2. **Property tests** (Plausible, fixed seed):
   * the interpreter, with random fuel, runs out of fuel or returns exactly what `loopG` returns
     (mirrors `exec_for_eq_loopG`), and with enough fuel it never runs out (non-vacuity);
   * gas ≤ iters · `loopIterGas` + `loopExitGas` (mirrors `loopG_gas_le`);
   * clean runs of straight-line loops are charged exactly that (mirrors `loopG_gas_eq`), and
     straight-line loops without `break` are clean and run `k` times (non-vacuity);
   * the iteration count never exceeds the budget (mirrors `loopG_iters_le`).
3. **Mutation tests**: Plausible must refute a bound without the exit term, a bound without the
   post block, a bound that charges one iteration fewer, exactness without the straight-line
   hypothesis, and a meter with a fixed small iteration budget.
-/

namespace EvmYul.Yul.GasTests.LoopsTests

open Plausible Ast Relational Gas
open EvmYul.Testing.EvmFixtures

/-- Named unit checks; each must evaluate to `true`. -/
def unitChecks : List (String × Bool) :=
  [ ("ten iterations: gas = 10 * (LT 3 + branch 11 + ADD 3 + ADD 3) + (LT 3 + branch 11) = 214",
      tenLoop.2.gas == 214),
    ("ten iterations: iters = 10, clean", tenLoop.2.iters == 10 && tenLoop.2.clean),
    ("ten iterations: v0 = 20 and i = 10",
      obsL tenLoop.2.res == "ok [20, 0, 0, 0] i=10"),
    ("ten iterations: interpreter agrees",
      (match exec 200 tenLoop.1 none (startState [0, 0, 0, 0]) with
        | .error .OutOfFuel => false
        | r => obsL r == obsL tenLoop.2.res)),
    ("ten iterations: static bound is attained",
      tenLoop.2.gas == 10 * loopIterGas cancun (lCond 10) lPost
        [.Let [vr 0] (some (call .ADD [.Var (vr 0), lit 2]))] + loopExitGas cancun (lCond 10)),
    ("break at once: one body run, not clean, gas = LT + branch = 14",
      breakLoop.iters == 1 && !breakLoop.clean && breakLoop.gas == 14),
    ("break at once: the loop ends normally with i = 0", obsL breakLoop.res == "ok [0, 1, 2, 3] i=0"),
    ("condition 0: no body run, clean, gas = branch = 11",
      zeroLoop.iters == 0 && zeroLoop.clean && zeroLoop.gas == 11),
    ("budget 0 reports out of fuel",
      (match (loopG cancun 0 (lCond 3) lPost [] (startState [])).res with
        | .error .OutOfFuel => true
        | _ => false)),
    ("loop bodies are in the fragment", fragB (lBody false (List.range 40)))
  ]

/-- Run every check; throws on the first failure. -/
def runAll : IO Unit := do
  for (name, ok) in unitChecks do
    unless ok do throw <| IO.userError s!"unit check failed: {name}"
  IO.println s!"{unitChecks.length} unit checks passed"
  -- Mirrors `exec_for_eq_loopG`.
  yHolds "exec on a loop (random fuel) runs out of fuel or returns the metered result"
    (∀ k f : ℕ, ∀ init ns : List ℕ,
      CountedTesting.WhenSome (eLoop (fuelAt f (loopFuel ns)) (k % 12) false init ns)
        (· == obsL (mLoop (k % 12) false init ns).res))
  -- Non-vacuity of the property above.
  yHolds "exec with enough fuel never runs out on the test loops"
    (∀ k : ℕ, ∀ init ns : List ℕ, (eLoop (loopFuel ns) (k % 12) false init ns).isSome)
  -- Mirrors `loopG_gas_le`.
  yHolds "loop gas <= iters * loopIterGas + loopExitGas"
    (∀ k : ℕ, ∀ init ns : List ℕ,
      (mLoop (k % 12) false init ns).gas ≤
        (mLoop (k % 12) false init ns).iters * iterG (k % 12) false ns + exitG (k % 12))
  -- Mirrors `loopG_gas_eq`.
  yHolds "clean runs of straight-line loops are charged exactly the bound"
    (∀ k : ℕ, ∀ init ns : List ℕ, (mLoop (k % 12) true init ns).clean →
      (mLoop (k % 12) true init ns).gas =
        (mLoop (k % 12) true init ns).iters * iterG (k % 12) true ns + exitG (k % 12))
  -- Non-vacuity of exactness: break-free straight loops are clean and run k times.
  yHolds "straight-line loops without break are clean and run k times"
    (∀ k : ℕ, ∀ init ns : List ℕ,
      (mLoop (k % 12) true init (noBreak ns)).clean ∧
        (mLoop (k % 12) true init (noBreak ns)).iters = k % 12)
  -- Mirrors `loopG_iters_le`.
  yHolds "iterations never exceed the budget"
    (∀ k b : ℕ, ∀ init ns : List ℕ,
      (loopG cancun (b % 15) (lCond (k % 12)) lPost (lBody false ns) (startState init)).iters ≤
        b % 15)
  IO.println "6 property suites passed"
  -- Mutation tests.
  yRefuted "mutant bound: no exit term"
    (∀ k : ℕ, ∀ init ns : List ℕ,
      (mLoop (k % 12) false init ns).gas ≤
        (mLoop (k % 12) false init ns).iters * iterG (k % 12) false ns)
  yRefuted "mutant bound: forgets the post block"
    (∀ k : ℕ, ∀ init ns : List ℕ,
      (mLoop (k % 12) false init ns).gas ≤
        (mLoop (k % 12) false init ns).iters * (iterG (k % 12) false ns - gasB cancun lPost) +
          exitG (k % 12))
  yRefuted "mutant bound: one iteration fewer"
    (∀ k : ℕ, ∀ init ns : List ℕ,
      (mLoop (k % 12) false init ns).gas ≤
        ((mLoop (k % 12) false init ns).iters - 1) * iterG (k % 12) false ns + exitG (k % 12))
  yRefuted "exactness without the straight-line hypothesis"
    (∀ k : ℕ, ∀ init ns : List ℕ, (mLoop (k % 12) false init ns).clean →
      (mLoop (k % 12) false init ns).gas =
        (mLoop (k % 12) false init ns).iters * iterG (k % 12) false ns + exitG (k % 12))
  yRefuted "mutant meter: an iteration budget of 3 matches the interpreter"
    (∀ k : ℕ, ∀ init ns : List ℕ,
      (eLoop (loopFuel ns) (k % 12) false init ns).all (· == obsL
        (loopG cancun 3 (lCond (k % 12)) lPost (lBody false ns) (startState init)).res))

#eval runAll

end EvmYul.Yul.GasTests.LoopsTests
