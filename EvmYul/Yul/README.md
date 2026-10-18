# `EvmYul/Yul/`: Yul

The Yul language: syntax, state, the interpreter and its reasoning principles, the gas layer (`Gas/`) and the relational semantics with its WP calculus (`Relational/`).

## Files

The library children of this folder (layout check L13 keeps this list complete):

- `Ast.lean`: Yul abstract syntax.
- `Exception.lean`: Yul exceptions.
- `ExecLemmas.lean`: Lemmas about the Yul interpreter.
- `Interpreter.lean`: The Yul interpreter.
- `MachineState.lean`: Yul machine state.
- `PrimOps.lean`: Yul primitive operations as state transformers.
- `ReasoningPrinciple.lean`: Reasoning principles for Yul.
- `State.lean`: Yul state.
- `StateOps.lean`: Operations on the Yul state.
- `VarStore.lean`: Yul variable store.
- `YulNotation.lean`: Yul notation.
- `WellScoped.lean`: Well-scoped Yul programs.
- `SizeLemmas.lean`: Size lemmas for Yul syntax.
- `Gas/`: see `Gas/README.md`.
- `Relational/`: Relational Yul; see `Relational/README.md`.
