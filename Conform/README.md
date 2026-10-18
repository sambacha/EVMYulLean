# `Conform/`: Conformance runner

Runs the pinned `ethereum/tests` corpus against the EVM model (`lake exe conform`). It sits outside the library: no `EvmYul` module imports it (layout check L4), and it imports library folders through their parent files (L15).

## Files

The library children of this folder (layout check L13 keeps this list complete):

- `Exception.lean`: Conformance-runner exceptions.
- `Model.lean`: Data model of the Ethereum conformance tests.
- `TestParser.lean`: JSON parser for the conformance tests.
- `TestRunner.lean`: Conformance test runner.
- `Corpus.lean`: The pinned `ethereum/tests` conformance corpus.
- `Verdict.lean`: Verdict of a conformance run (review O-9).
