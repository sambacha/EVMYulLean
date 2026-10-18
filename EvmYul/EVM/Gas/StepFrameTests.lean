module

public import EvmYul.EVM.Gas.StepFrameTestHarness
public meta import EvmYul.EVM.Gas.StepFrameTestHarness
@[expose] public meta section

/-!
# Regression tests for the gas behaviour of `step` (`GasStepFrame`)

These checks *execute* the interpreter, and the interpreter's memory and hash primitives are C
functions reached through the FFI, which the elaborator cannot call while building. They therefore
run in a compiled executable: `lake exe gasStepFrameTests` (exit code 1 on any failure; run in CI).
`lake build EvmYulGasTests` compiles this module, so the checks always type-check.

1. **Unit tests** (named checks): `EvmYul.step` keeps the gas for concrete instructions, `EVM.step`
   deducts exactly the charge, stack underflow is an error other than `OutOfFuel`, zero fuel is
   `OutOfFuel`, and the fall-through case of `EvmYul.step` for CREATE returns the all-zero state.
2. **Property tests** (Plausible, 300 random inputs, fixed seed), mirroring `evmStep_gasSafe` and
   `step_some_gasSafe`: for a random instruction outside `spawnOps`, random small operands, random
   gas and a random charge that fits, the outcome is gas-safe.
3. **The spawning instructions** (executed mirror of `SpawnStepGasSoundZ` /
   `SpawnNestedFuelAdequateZ`, now proved in `GasNested`): on a fixed grid of 1350 CREATE /
   CREATE2 / CALL / CALLCODE / DELEGATECALL / STATICCALL states (at least 600 must pass `Z`, so the
   check is not vacuous) and on 300 random ones, with the charge from `Z` and fuel `gas + 2`.
4. **Mutation tests**: Plausible must refute (a) `EvmYul.step` gas safety with the `spawnOps`
   exclusion dropped (mirrors `not_gasSafe_CREATE`), (b) the spawning check with charge 0 instead of
   the `Z` charge (mirrors `not_stepGasSound`), and (c) "`EVM.step` leaves the gas unchanged" (a
   step that forgot the deduction), so the property tests above can fail.

Operands are kept small (below 4096) so memory-touching instructions stay cheap to execute.
-/

namespace EvmYul

namespace EVM

namespace StepFrameTests

open GasMeter Plausible EvmYul.Testing.EvmFixtures

/-! ## 1. Unit tests -/

/-- Named unit checks; each must evaluate to `true`. -/
def unitChecks : List (String × Bool) :=
  [ ("ADD keeps the gas",
      gasSafeB (u 77) (EvmYul.step (τ := .EVM) .ADD none (withGas (withStack [u 1, u 2]) 77))),
    ("ADD result and gas",
      match EvmYul.step (τ := .EVM) .ADD none (withGas (withStack [u 1, u 2]) 77) with
      | .ok s => s.gasAvailable == u 77 && s.stack == [u 3]
      | .error _ => false),
    ("EVM.step ADD deducts the charge 5",
      match step 1 5 (some (.ADD, none)) (withGas (withStack [u 1, u 2]) 77) with
      | .ok s => s.gasAvailable == u 72
      | .error _ => false),
    ("EVM.step MSTORE deducts the charge 3",
      match step 1 3 (some (.MSTORE, none)) (withGas (withStack [u 0, u 9]) 10) with
      | .ok s => s.gasAvailable == u 7
      | .error _ => false),
    ("EVM.step SSTORE deducts the charge 3",
      match step 1 3 (some (.SSTORE, none)) (withGas (withOwnerAccount (withStack [u 1, u 2])) 9)
      with
      | .ok s => s.gasAvailable == u 6
      | .error _ => false),
    ("stack underflow is StackUnderflow, not OutOfFuel",
      match step 1 5 (some (.ADD, none)) (withGas (withStack [u 1]) 77) with
      | .error .StackUnderflow => true
      | _ => false),
    ("zero fuel is OutOfFuel",
      match step 0 5 (some (.ADD, none)) (withGas (withStack [u 1, u 2]) 77) with
      | .error .OutOfFuel => true
      | _ => false),
    ("fall-through: EvmYul.step CREATE succeeds with gas 0",
      match EvmYul.step (τ := .EVM) .CREATE none (withGas (withStack [u 0, u 0, u 0]) 50) with
      | .ok s => s.gasAvailable == u 0
      | .error _ => false),
    ("fall-through: EvmYul.step CREATE is not gas-safe",
      !gasSafeB (u 50)
        (EvmYul.step (τ := .EVM) .CREATE none (withGas (withStack [u 0, u 0, u 0]) 50))) ]

/-! ## 3. Mutation tests (inside `runAll`) -/

/-- Run every check; throws on the first failure. The two mutants must be refuted: dropping the
`spawnOps` exclusion (CREATE takes the fall-through case to the all-zero state), and a step that
forgot to deduct the charge. -/
def runAll : IO Unit := do
  for (name, ok) in unitChecks do
    unless ok do throw <| IO.userError s!"unit check failed: {name}"
  IO.println s!"{unitChecks.length} unit checks passed"
  expectHolds "EvmYul.step is gas-safe outside spawnOps"
    (∀ o : AnyOp, ∀ a b c g : ℕ, ∀ p : Bool, evmStepSpec o a b c g p = true)
  expectHolds "EVM.step deducts exactly the charge outside spawnOps"
    (∀ o : AnyOp, ∀ a b c g k : ℕ, stepSpec o a b c g k = true)
  unless spawnCoverage ≥ 600 do
    throw <| IO.userError s!"spawn coverage too low: {spawnCoverage} of 1350 grid samples pass Z"
  IO.println s!"spawn coverage: {spawnCoverage} of 1350 grid samples pass Z"
  unless spawnGridFailures.isEmpty do
    throw <| IO.userError s!"spawn property fails on grid samples {spawnGridFailures}"
  IO.println "spawn property holds on all 1350 grid samples"
  expectRefuted "coverage: some random spawning instruction passes Z"
    (∀ k : Fin 6, ∀ gReq toN val bal g : ℕ, spawnReached k gReq toN val bal g = false)
  expectHolds "spawning instructions with Z charges: gas sound and no OutOfFuel (proved: GasNested)"
    (∀ k : Fin 6, ∀ gReq toN val bal g : ℕ, spawnSpec true k gReq toN val bal g = true)
  IO.println "3 property suites passed (300 inputs each)"
  expectRefuted "mutant: EvmYul.step is gas-safe for every instruction (spawnOps included)"
    (∀ o : AnyOp, ∀ a b c : ℕ,
      let s := smallState a b c 1000
      gasSafeB s.gasAvailable (EvmYul.step o.op none s) = true)
  expectRefuted "refuted hypothesis: spawning instructions with charge 0 (not_stepGasSound)"
    (∀ k : Fin 6, ∀ gReq toN val bal g : ℕ, spawnSpec false k gReq toN val bal g = true)
  expectRefuted "mutant: EVM.step leaves the gas unchanged (deduction forgotten)"
    (∀ o : AnyOp, ∀ a b c k : ℕ,
      let s := smallState a b c 1000
      let charge := k % 1001 + 1
      (o.op ∈ spawnOps ||
        gasSafeB s.gasAvailable (step 1 charge (some (o.op, none)) s)) = true)

end StepFrameTests

end EVM

end EvmYul
