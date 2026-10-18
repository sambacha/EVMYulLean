# `EvmYul/`: The EVM and Yul model

The library: the EVM and Yul machines, their shared state and instruction semantics, the gas model and its proofs, and the compiler front ends used as test oracles. Every subfolder has a parent file of the same name that imports its library modules (Rule 2) and a README like this one (Rule 10).

## Files

The library children of this folder (layout check L13 keeps this list complete):

- `ProofTags.lean`: Review tags for the proof-term audits.
- `EllipticCurves.lean`: secp256k1 signatures.
- `MachineState.lean`: Machine state shared by the EVM and Yul.
- `MachineStateOps.lean`: Operations on the machine state.
- `Operations.lean`: The operations of the EVM and of Yul.
- `PerformIO.lean`: Running `IO` inside pure code.
- `Pretty.lean`: Pretty printers.
- `Semantics.lean`: Instruction semantics shared by the EVM and Yul.
- `SelfDestruct.lean`: `SELFDESTRUCT` (EIP-6780): the effect shared by the EVM and Yul, and its lemmas.
- `SharedState.lean`: State shared by the EVM and Yul.
- `SharedStateOps.lean`: Operations on the shared state.
- `Stack.lean`: The machine stack.
- `UInt256.lean`: 256-bit words.
- `EVMException.lean`: Exceptions of the EVM model.
- `Toolchain.lean`: Toolchain upgrade check: the pure model.
- `EVM/`: The EVM; see `EVM/README.md`.
- `FFI/`: Foreign functions; see `FFI/README.md`.
- `Maps/`: Finite maps; see `Maps/README.md`.
- `Solc/`: solc fixtures; see `Solc/README.md`.
- `SpongeHash/`: Keccak; see `SpongeHash/README.md`.
- `State/`: World state; see `State/README.md`.
- `Venom/`: Venom; see `Venom/README.md`.
- `Vyper/`: Vyper fixtures; see `Vyper/README.md`.
- `Wheels/`: Basic types; see `Wheels/README.md`.
- `Yul/`: Yul; see `Yul/README.md`.
