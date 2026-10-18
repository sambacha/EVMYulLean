module

public import EvmYul.FFI.Primitives
public meta import EvmYul.FFI.Primitives
public import EvmYul.EVM.Gas.StepFrameTests
public meta import EvmYul.EVM.Gas.StepFrameTests
public import EvmYul.EVM.Gas.NestedTests
public meta import EvmYul.EVM.Gas.NestedTests
@[expose] public meta section

/-!
# The interpreter-executing gas suites, run during `lake build EvmYulGasTests`

`StepFrameTests` and `NestedTests` execute the EVM interpreter, which reaches Keccak-256
through the FFI (`ffi.keccak256`, e.g. for `KECCAK256` and for `CREATE`/`CREATE2` addresses).
The elaborator cannot run an `@[extern]` declaration unless the native code is loaded, so these
suites used to run only in `lake exe gasStepFrameTests`.

The `EvmYulGasTests` library now loads the shared library `evmffi` (lakefile target
`evmFFIDynlib`: the C primitives plus the compiled wrapper module `EvmYul.FFI.Primitives`) through
`lean --load-dynlib`. This file runs both suites with `#eval`; an uncaught failure is an
elaboration error, so it fails the build exactly as the executable's exit code 1 did.

The first two checks are known-answer tests showing that the native primitives are really the
ones being run (not a stub): Keccak-256 of the empty string and of `"abc"`, from the Keccak team's
published test vectors (also the values every Ethereum client returns for `keccak256("")` and
`keccak256("abc")`).
-/

namespace EvmYul.EVM.FFIBuildTests

/-- Hex rendering of a byte array, lower case, no prefix. -/
def hex (b : ByteArray) : String :=
  String.join (b.toList.map fun x =>
    let d := "0123456789abcdef".toList
    String.ofList [d[(x.toNat / 16)]!, d[(x.toNat % 16)]!])

-- Keccak-256 of the empty input (Ethereum's `EMPTY_CODE_HASH`).
#guard hex (ffi.KEC .empty) ==
  "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"

-- Keccak-256 of `"abc"`.
#guard hex (ffi.KEC "abc".toUTF8) ==
  "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45"

#eval StepFrameTests.runAll
#eval NestedTests.runAll

end EvmYul.EVM.FFIBuildTests
