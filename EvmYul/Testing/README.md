# `EvmYul/Testing/`: Test support

Shared test support: the counted Plausible runner (`TESTING.md` A2), the EVM fixtures and generators, and a reference model for map tests. Test-only: no library module imports it.

## Files

The library children of this folder (layout check L13 keeps this list complete):

- `Counted.lean`: A Plausible runner that counts how often the precondition held (`TESTING.md` A2).
- `EvmFixtures.lean`: Shared fixtures and generators for the EVM tests.
- `EvmFixturesTests.lean`: Self-checks of the shared EVM test fixtures (`EvmYul/Testing/EvmFixtures.lean`).
- `MapModel.lean`: Reference model for map tests.
