module

public import EvmYul.Yul.Gas.NestedLoopsTestHarness
public meta import EvmYul.Yul.Gas.NestedLoopsTestHarness
@[expose] public meta section

/-!
# Regression tests for nested-loop Yul gas (`NestedLoops.lean`)

These run **during `lake build EvmYulGasTests`**; any failing check fails the build.

The test programs nest two counting loops (`k₁, k₂ < 12`):

```
let v0..v3 := init   let i := 0   let j := 0
for {} lt(j, k₁) { j := add(j, 1) } {
  let i := 0
  for {} lt(i, k₂) { i := add(i, 1) } { body }
}
```

The inner body is a random list of generated statements (`genStmt` from `Gas/MeteredTests.lean`): arithmetic,
memory, `pop`, `break` (which leaves the inner loop only), and, unless the program is straight-line,
`if` and `switch`. The body never touches `i` or `j`.

1. **Unit tests**: concrete nested loops (two and three levels) whose gas, result and minimal
   iteration budget are computed by hand.
2. **Property tests** (Plausible, fixed seed):
   * the interpreter, with random fuel, runs out of fuel or returns exactly what `execL` returns
     (mirrors `exec_eq_execL`), and with enough fuel it never runs out (non-vacuity);
   * every successful metered run with budget `n` costs at most `gasLS n` (mirrors
     `execL_gas_le`), and budget `11` always succeeds (non-vacuity);
   * a run that fits in budget `n` gives the same result and gas with every larger budget (mirrors
     `execL_mono`);
   * the least successful budget is the largest per-entry iteration count;
   * for break-free straight-line bodies and `k₁ = k₂ = k`, the gas is **exactly** `gasLS k` (the
     bound is attained);
   * on loop-free programs `execL` is `execG` and `gasLS` is `gasS` (mirrors `execL_of_fragS`,
     `gasLS_of_fragS`).
3. **Mutation tests**: Plausible must refute a bound with one iteration fewer, a bound charging the
   inner loop once instead of once per outer iteration, a bound without the inner exit tests, a
   meter with a fixed small budget, and reversed budget monotonicity.
-/

namespace EvmYul.Yul.GasTests.NestedLoopsTests

open Plausible Ast Relational Gas LoopsTests
open EvmYul.Testing.EvmFixtures

/-- Named unit checks; each must evaluate to `true`. -/
def unitChecks : List (String × Bool) :=
  [ ("3x4: inner = 4 * 20 + 14 = 94, outer = 3 * (14 + 94 + 3) + 14 = 347 gas",
      (mObs 4 p34).map (·.2) == some 347),
    ("3x4: v0 = 24, i = 4 (`let i := 0` re-assigns the outer i), j = 3",
      (mObs 4 p34).map (·.1) == some "ok [24, 0, 0, 0] i=4 j=3"),
    ("3x4: the interpreter agrees", eObs 300 p34 == (mObs 4 p34).map (·.1)),
    ("3x4: budget 3 is too small, budget 4 suffices",
      (mObs 3 p34).isNone && (mObs 4 p34).isSome),
    ("3x4: a larger budget gives the same result and gas", mObs 9 p34 == mObs 4 p34),
    ("3x4: static bound with budget 4 = 4 * (14 + 94 + 3) + 14 = 458", gasLS cancun 4 p34 == 458),
    ("3x3: bound attained, gas = gasLS 3 = 287",
      (mObs 3 p33).map (·.2) == some 287 && gasLS cancun 3 p33 == 287),
    ("inner break at once: gas = 3 * (14 + 14 + 3) + 14 = 107",
      (mObs 3 pBreak).map (·.2) == some 107),
    ("inner break at once: v0 and i unchanged, j = 3",
      (mObs 3 pBreak).map (·.1) == some "ok [0, 0, 0, 0] i=0 j=3"),
    ("inner break at once: budget 3 (outer iterations) is needed, 2 is not",
      (mObs 2 pBreak).isNone),
    ("three levels: 2 * (14 + 2 * (14 + 54 + 3) + 14 + 3) + 14 = 360 gas, v0 = 16",
      mObs 2 p222 == some ("ok [16, 0, 0, 0] i=2 j=2", 360)),
    ("three levels: the interpreter agrees", eObs 300 p222 == (mObs 2 p222).map (·.1)),
    ("three levels: bound attained, gasLS 2 = 360", gasLS cancun 2 p222 == 360),
    ("nested programs are in the loop fragment",
      fragLS (nestProg 5 5 false [] (List.range 40)) && fragLS p222),
    ("nested programs are not in the loop-free fragment", !fragS p34),
    ("loop-free program: gasLS = gasS",
      gasLS cancun 7 (genProg false [] (List.range 40)) == gasS cancun (genProg false [] (List.range 40)))
  ]

/-- Run every check; throws on the first failure. -/
def runAll : IO Unit := do
  for (name, ok) in unitChecks do
    unless ok do throw <| IO.userError s!"unit check failed: {name}"
  IO.println s!"{unitChecks.length} unit checks passed"
  -- Mirrors `exec_eq_execL`.
  yHolds "exec on nested loops (random fuel) runs out of fuel or returns the metered result"
    (∀ k₁ k₂ f : ℕ, ∀ init ns : List ℕ,
      CountedTesting.WhenSome (eObs (fuelAt f (nestFuel ns)) (nestProg (k₁ % 12) (k₂ % 12) false init ns)) fun o =>
        (mObs 11 (nestProg (k₁ % 12) (k₂ % 12) false init ns)).map (·.1) == some o)
  -- Non-vacuity of the property above.
  yHolds "exec with enough fuel never runs out on nested loops"
    (∀ k₁ k₂ : ℕ, ∀ init ns : List ℕ,
      (eObs (nestFuel ns) (nestProg (k₁ % 12) (k₂ % 12) false init ns)).isSome)
  -- Mirrors `execL_gas_le`.
  yHolds "every metered run with budget n costs at most gasLS n"
    (∀ k₁ k₂ b : ℕ, ∀ init ns : List ℕ,
      CountedTesting.WhenSome (mObs (b % 14) (nestProg (k₁ % 12) (k₂ % 12) false init ns)) fun o =>
        o.2 ≤ gasLS cancun (b % 14) (nestProg (k₁ % 12) (k₂ % 12) false init ns))
  -- Non-vacuity: budget 11 always suffices for k₁, k₂ < 12.
  yHolds "budget 11 always suffices"
    (∀ k₁ k₂ : ℕ, ∀ init ns : List ℕ,
      (mObs 11 (nestProg (k₁ % 12) (k₂ % 12) false init ns)).isSome)
  -- Mirrors `execL_mono`.
  yHolds "a larger budget gives the same result and gas"
    (∀ k₁ k₂ b d : ℕ, ∀ init ns : List ℕ,
      CountedTesting.WhenSome (mObs (b % 14) (nestProg (k₁ % 12) (k₂ % 12) false init ns)) fun o =>
        mObs (b % 14 + d % 5) (nestProg (k₁ % 12) (k₂ % 12) false init ns) == some o)
  -- The least successful budget is the largest per-entry iteration count.
  yHolds "the least successful budget is the largest per-entry iteration count"
    (∀ k₁ k₂ : ℕ, ∀ init ns : List ℕ,
      (mObs (maxIters (k₁ % 12) (k₂ % 12))
        (nestProg (k₁ % 12) (k₂ % 12) false init (noBreak ns))).isSome ∧
      (maxIters (k₁ % 12) (k₂ % 12) = 0 ∨
        (mObs (maxIters (k₁ % 12) (k₂ % 12) - 1)
          (nestProg (k₁ % 12) (k₂ % 12) false init (noBreak ns))).isNone))
  -- The bound is attained.
  yHolds "break-free straight-line k x k loops are charged exactly gasLS k"
    (∀ k : ℕ, ∀ init ns : List ℕ,
      (mObs (k % 12) (nestProg (k % 12) (k % 12) true init (noBreak ns))).map (·.2) ==
        some (gasLS cancun (k % 12) (nestProg (k % 12) (k % 12) true init (noBreak ns))))
  -- Mirrors `execL_of_fragS` and `gasLS_of_fragS`.
  yHolds "on loop-free programs execL is execG and gasLS is gasS"
    (∀ b : ℕ, ∀ init ns : List ℕ,
      ((execL cancun (b % 14) (genProg false init ns) s0).map fun (r, g) => (obs r, g)) ==
          some (obs (execG cancun (genProg false init ns) s0).1,
            (execG cancun (genProg false init ns) s0).2) ∧
        gasLS cancun (b % 14) (genProg false init ns) = gasS cancun (genProg false init ns))
  IO.println "8 property suites passed"
  -- Mutation tests.
  yRefuted "mutant bound: one iteration fewer"
    (∀ k : ℕ, ∀ init ns : List ℕ,
      (mObs (k % 12) (nestProg (k % 12) (k % 12) true init (noBreak ns))).all fun o =>
        o.2 ≤ gasLS cancun (k % 12 - 1) (nestProg (k % 12) (k % 12) true init (noBreak ns)))
  yRefuted "mutant bound: the inner loop is charged once"
    (∀ k₁ k₂ : ℕ, ∀ init ns : List ℕ,
      (mObs (maxIters (k₁ % 12) (k₂ % 12))
        (nestProg (k₁ % 12) (k₂ % 12) true init (noBreak ns))).all fun o =>
        o.2 ≤ onceBound (maxIters (k₁ % 12) (k₂ % 12)) (k₁ % 12) (k₂ % 12)
          (lBody true (noBreak ns)))
  yRefuted "mutant bound: no inner exit tests"
    (∀ k : ℕ, ∀ init ns : List ℕ,
      (mObs (k % 12) (nestProg (k % 12) (k % 12) true init (noBreak ns))).all fun o =>
        o.2 ≤ gasLS cancun (k % 12) (nestProg (k % 12) (k % 12) true init (noBreak ns)) -
          (k % 12) * loopExitGas cancun (ltc ctr (k % 12)))
  yRefuted "mutant meter: an iteration budget of 3 matches the interpreter"
    (∀ k₁ k₂ : ℕ, ∀ init ns : List ℕ,
      (eObs (nestFuel ns) (nestProg (k₁ % 12) (k₂ % 12) false init ns)).all fun o =>
        (mObs 3 (nestProg (k₁ % 12) (k₂ % 12) false init ns)).map (·.1) == some o)
  yRefuted "mutant: budget monotonicity reversed"
    (∀ k₁ k₂ b : ℕ, ∀ init ns : List ℕ,
      (mObs (b % 14 + 1) (nestProg (k₁ % 12) (k₂ % 12) false init ns)).isSome →
        (mObs (b % 14) (nestProg (k₁ % 12) (k₂ % 12) false init ns)).isSome)

#eval runAll

end EvmYul.Yul.GasTests.NestedLoopsTests
