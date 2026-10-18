# `EvmYul/Yul/Relational/`: Relational Yul

A fuel-free, big-step semantics of Yul, the soundness of the interpreter with respect to it, and a weakest-precondition calculus.

## Files

The library children of this folder (layout check L13 keeps this list complete):

- `Examples.lean`: Worked examples for the Yul WP calculus.
- `PrimCallK.lean`: Fuel-free view of Yul primitive calls.
- `Semantics.lean`: Relational (big-step, fuel-free) semantics of Yul.
- `Soundness.lean`: The Yul interpreter is sound with respect to the relational semantics.
- `WP.lean`: A weakest-precondition calculus for Yul, sound with respect to the relational semantics.
