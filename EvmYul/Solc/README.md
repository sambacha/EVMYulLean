# `EvmYul/Solc/`: solc fixtures

The solc Yul-lowering matrix: the fixture shape, the generated fixtures and corpus (do not edit; regenerate with `tools/solc/`), and the harness that runs them on both machines.

## Files

The library children of this folder (layout check L13 keeps this list complete):

- `Corpus.lean`: The solc corpus, read by the project's own Yul parser (generated; do not edit).
- `Fixture.lean`: The shape of a solc Yul-lowering fixture (`docs/SOLC_VYPER_PLAN.md`, Steps 2–3).
- `Fixtures.lean`: solc Yul-lowering fixtures (generated; do not edit).
- `Harness.lean`: Running solc output on the EVM, and its Yul source on the Yul model (solc matrix harness).
