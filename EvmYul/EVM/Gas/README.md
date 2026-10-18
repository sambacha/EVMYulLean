# `EvmYul/EVM/Gas/`: EVM gas

The gas model of the EVM interpreter and the proofs about it: the cost tables and fork schedules, the meter, fuel and termination, and the laws about nested frames. The longer design notes live next to the modules: `STEP_FRAME.md` (gas behaviour of `step`) and `FORK_SCHEDULE.md` (fork schedule, cost/accounting split and invariants). Tests are imported by the test index `EVM/GasTests.lean`.

## Files

The library children of this folder (layout check L13 keeps this list complete):

- `CallReadings.lean`: MO-4 / decision D-1: three readings of the CALL gas cap, compared by proof.
- `Classification.lean`: Exhaustiveness of the per-operation cost function (issue S2).
- `Constants.lean`: Fee schedule constants (Yellow Paper, Appendix G).
- `Costs.lean`: Gas costs (Yellow Paper, Appendix G and H.1).
- `ExpByteLength.lean`: The byte length in the `EXP` cost (YP Appendix H.1).
- `FeeSchedule.lean`: Fee-schedule types (handoff WP-6, MO-10, PO-12) and the opcode/price parity theorem (PO-1).
- `ForkCost.lean`: The pure, total, fork-parameterised cost function and the accounting transformer.
- `ForkCostBridge.lean`: The split cost/accounting `Z` is the previous `Z`.
- `ForkCostLemmas.lean`: The Cancun instance of `ForkSchedule.cost` is the interpreter's cost.
- `ForkSchedule.lean`: Fork-indexed gas schedules (Frontier → Cancun / Prague / Osaka).
- `Fuel.lean`: Fuel (handoff C13, CE-9, PO-10).
- `HaltOrder.lean`: Reordering the exceptional-halting checks is behaviour-preserving.
- `Invariants.lean`: Core gas invariants of the split cost / accounting model.
- `Laws.lean`: Gas laws: shared statements, congruences and independent oracles.
- `Meter.lean`: Gas meter hardening.
- `Nested.lean`: Nested frames: gas returned and fuel adequacy (K8, K1).
- `NestedFuel.lean`: Nested frames: fuel adequacy at every frame (K8, K1).
- `Positivity.lean`: Every non-halting instruction costs gas, in every named fork.
- `StepFrame.lean`: Gas behaviour of `step` outside the spawning instructions.
- `Termination.lean`: Termination by well-founded recursion on gas.
- `Atomicity.lean`: Deduction atomicity of one instruction (handoff PO-3 / PO-4, meter level).
- `CallBoundary.lean`: The 63/64 rule at every call boundary, and order sensitivity of the cost.
- `ForkSchedulePins.lean`: Pins: every named fork, field by field.
- `Lemmas.lean`: Gas lemma battery (issue S1).
- `WarmAccess.lean`: Warm access costs (handoff WP-5 pilot).
