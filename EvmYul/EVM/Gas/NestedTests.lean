module

public import EvmYul.EVM.Gas.NestedTestHarness
public meta import EvmYul.EVM.Gas.NestedTestHarness
@[expose] public meta section

/-!
# Regression tests for nested frames (`GasNested`: K8 and K1)

`GasNested` proves that a nested frame (`Θ`, `Λ`, `Ξ`, `X`) never hands back more gas than it was
given, and that none of them, nor a whole transaction (`Υ`), runs out of fuel once the fuel exceeds
the gas by a small margin. The earlier tests (`StepFrameTests`) only used callees **without
code**, so the nested frame returned at once. These tests use callees that **run code**: an
infinite loop, a self-recursive CALL, SSTORE, RETURN, REVERT, CREATE and STOP.

Like `StepFrameTests`, these checks execute the interpreter (FFI), so they run in the compiled
executable `lake exe gasStepFrameTests`; `lake build EvmYulGasTests` type-checks them.

1. **Unit tests**: per callee program, `Θ` with fuel `g + 5` does not fail with `OutOfFuel`, and
   `gasLeft ≤ g` (`Θ_gasLeft_le`). Exact values pin the behaviour: the loop burns everything
   (`gasLeft = 0`), STOP returns everything (`gasLeft = g`, so the bound is tight), SSTORE costs at
   least 20000. A CALL step into a code-running callee strictly lowers the caller's gas
   (`step_CALL_gas_lt`). `Υ` with `transactionFuel` on a looping recipient does not run out of fuel.
2. **Property tests** (Plausible, 300 inputs, fixed seed): random callee program, random gas, random
   requested gas / value / balance: `Θ` with fuel `g + 5` (`Θ_ne_outOfFuel`, `Θ_gasLeft_le`); a
   spawning step with the `Z` charge and fuel `gas + 2` (`stepGasSoundZ`, `nestedFuelAdequateZ`);
   `Υ` with `transactionFuel` (`Υ_transactionFuel_ne_outOfFuel`).
3. **Coverage**: on a fixed grid, at least half of the CALL samples really execute callee code
   (the caller ends with less gas than after the same CALL into a STOP callee).
4. **Mutation tests** (must be refuted): "the callee returns strictly less than it was given"
   (refuted by STOP: the bound is tight), "fuel 3 suffices for `Θ`" and "fuel 5 suffices for `Υ`"
   (refuted by the loop: the fuel margin is necessary), and "the callee's consumption is not charged
   to the caller" (refuted by every callee that uses gas).
-/

namespace EvmYul

namespace EVM

namespace NestedTests

open GasMeter Plausible StepFrameTests
open EvmYul.Testing.EvmFixtures

/-! ## 1. Unit tests -/

def unitChecks : List (String × Bool) :=
  [ ("Θ: looping callee burns all 10000 gas", θGasLeft? progLoop 10000 == some 0),
    ("Θ: STOP callee returns all 10000 gas (bound is tight)", θGasLeft? progSTOP 10000 == some 10000),
    ("Θ: SSTORE callee spends at least 20000 of 50000",
      match θGasLeft? progSstore 50000 with | some g => g ≤ 30000 | none => false),
    ("Θ: RETURN callee returns less than given", match θGasLeft? progReturn 1000 with
      | some g => decide (g < 1000) | none => false),
    ("Θ: REVERT callee returns less than given", match θGasLeft? progRevert 1000 with
      | some g => decide (g < 1000) | none => false),
    ("Θ: self-recursive callee, 1000000 gas: no OutOfFuel, gasLeft ≤ g",
      θSpec progRecurse 1000000),
    ("Θ: nested CREATE, 100000 gas: no OutOfFuel, gasLeft ≤ g", θSpec progCreate 100000),
    ("Θ with fuel 3 on the loop: OutOfFuel (the margin matters)",
      match runΘ 3 progLoop 10000 with | .error .OutOfFuel => true | _ => false),
    ("CALL into the looping callee: the 5000 forwarded gas is burned",
      callBurn? 1 5000 100000 == some 5000),
    ("CALL into the STOP callee: nothing burned", callBurn? 0 5000 100000 == some 0),
    ("CALL into the self-recursive callee: gas strictly drops, no OutOfFuel",
      callSpec 5 200000 0 0 370000),
    ("Υ with transactionFuel, looping recipient, zero balance: no OutOfFuel",
      !isOutOfFuel (runΥ (transactionFuel (txOf 50000) ⟨0⟩) progLoop 50000)),
    ("Υ with fuel 5, looping recipient: OutOfFuel (the margin matters)",
      isOutOfFuel (runΥ 5 progLoop 50000)) ]

def runAll : IO Unit := do
  for (name, ok) in unitChecks do
    unless ok do throw <| IO.userError s!"nested unit check failed: {name}"
  IO.println s!"{unitChecks.length} nested-frame unit checks passed"
  unless callCoverage ≥ 42 do
    throw <| IO.userError s!"nested coverage too low: {callCoverage} of 84 CALLs ran callee code"
  IO.println s!"nested coverage: {callCoverage} of 84 grid CALLs ran callee code"
  expectHolds "Θ with fuel g+5: no OutOfFuel and gasLeft ≤ g (code-running callees)"
    (∀ k : Fin 7, ∀ g : ℕ, θSpec (prog k) (g % 200000) = true)
  expectHolds "CALL step into code-running callee: gas strictly drops, no OutOfFuel"
    (∀ k : Fin 7, ∀ gReq val bal g : ℕ, callSpec k gReq val bal g = true)
  expectHolds "Υ with transactionFuel never fails with OutOfFuel"
    (∀ k : Fin 7, ∀ gl : ℕ, υSpec k gl = true)
  IO.println "3 nested property suites passed (300 inputs each)"
  expectRefuted "mutant: the callee returns strictly less than it was given"
    (∀ k : Fin 7, ∀ g : ℕ, (θGasLeft? (prog k) (g % 50000 + 1)).all (· < g % 50000 + 1) = true)
  expectRefuted "mutant: fuel 3 suffices for Θ"
    (∀ k : Fin 7, ∀ g : ℕ, (runΘ 3 (prog k) (g % 50000 + 100) matches .error .OutOfFuel) = false)
  expectRefuted "mutant: fuel 5 suffices for Υ"
    (∀ k : Fin 7, ∀ gl : ℕ, isOutOfFuel (runΥ 5 (prog k) (gl % 60000)) = false)
  expectRefuted "mutant: the callee's consumption is not charged to the caller"
    (∀ k : Fin 7, ∀ gReq g : ℕ, callNoBurn k gReq g = true)

end NestedTests

end EVM

end EvmYul
