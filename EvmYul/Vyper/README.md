# `EvmYul/Vyper/`: Vyper fixtures

Vyper bytecode fixtures (V1): the fixture shape, the generated fixtures (do not edit; regenerate with `tools/vyper/`), the harness and the reference semantics.

## Files

The library children of this folder (layout check L13 keeps this list complete):

- `Fixture.lean`: The shape of a Vyper bytecode fixture (V1, `docs/VYPER_V1_PLAN.md`).
- `Fixtures.lean`: Vyper bytecode fixtures (generated; do not edit).
- `Harness.lean`: Running compiled Vyper contracts on this project's EVM (V1 harness).
- `Reference.lean`: Reference semantics of the Vyper corpus (V1 business assertions).
