module

public import EvmYul.EVM.Gas.StepFrameTests
public meta import EvmYul.EVM.Gas.StepFrameTests
public import EvmYul.EVM.Gas.NestedTests
public meta import EvmYul.EVM.Gas.NestedTests

/-!
# Entry point of `lake exe gasStepFrameTests`

Runs the executable checks of the step-frame and nested-call gas tests (`StepFrameTests`,
`NestedTests`) outside the elaborator, with the FFI primitives linked in.
-/
@[expose] public meta section

/-- `lake exe gasStepFrameTests`: run the executable checks of `StepFrameTests` and
`NestedTests`; exit code 1 on
any failure. -/
def main : IO UInt32 := do
  try
    EvmYul.EVM.StepFrameTests.runAll
    EvmYul.EVM.NestedTests.runAll
    IO.println "gasStepFrameTests: all checks passed"
    return 0
  catch e =>
    IO.eprintln s!"gasStepFrameTests: FAILED: {e}"
    return 1
