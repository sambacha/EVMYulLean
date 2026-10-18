# `EvmYul/EVM/`: The EVM

The EVM machine: bytecode decoding, instructions, state, the interpreter (`Semantics.lean`), the gas model (`Gas/`) and the precompiled contracts (`PrecompiledContracts/`).

## Files

The library children of this folder (layout check L13 keeps this list complete):

- `Decode.lean`: Bytecode decoding and jump destinations.
- `FrameOutcome.lean`: Named frame results (review O-3).
- `Instr.lean`: EVM instruction encoding.
- `PrimOps.lean`: EVM primitive operations as state transformers.
- `Semantics.lean`: The EVM interpreter.
- `State.lean`: EVM machine state.
- `StateOps.lean`: Operations on the EVM state.
- `Gas/`: EVM gas; see `Gas/README.md`.
- `PrecompiledContracts/`: Precompiled contracts; see `PrecompiledContracts/README.md`.
