# Fork schedule, pure cost function, accounting transformer and core gas invariants

This note covers the follow-up request: split `Z`/`C'` into a total, pure cost function and a
separate accounting transformer; replace the flat `GasConstants` with a `ForkSchedule` record; and
prove the core invariants. Every claim below names the Lean declaration that proves or tests it.
`lake build EvmYul EvmYulGasTests Conform` builds everything, runs all tests, and runs the axiom
audit and the lints.

## Plan tree

Steps marked (C) are critical (later steps depend on them); (F) steps are flexible.

```
PLAN TREE:
Step 1: Fork parameterisation (C)
├─ Alt 1.1 [0.85]: flat literal record per fork + rfl pins (full record and EIP delta)
├─ Alt 1.2 [0.60]: record built by successive `{ prev with … }` updates (pins trivial, kernel slow)
└─ Alt 1.3 [0.35]: type class per fork (instance search on every cost call)
Step 2: Pure total cost (C)
├─ Alt 2.1 [0.80]: `instrCost? fs gas s w` reading operands with `stack[i]?`, guard first,
│                  `cost := guard → memory part → instruction part on post-memory gas`
├─ Alt 2.2 [0.55]: cost on the pre-state only (impossible for CALL: refuted by
│                  `call_cost_order_sensitive`)
└─ Alt 2.3 [0.40]: dependent cost with a stack-length proof argument
Step 3: Accounting transformer + executable equality (C)
├─ Alt 3.1 [0.80]: `chargeOp` (guard, guarded memory charge, fit check), `exceptionalHalt :=
│                  exceptionalHaltFs cancun`, propositional equality with the old body for all
│                  inputs
├─ Alt 3.2 [0.50]: keep the old body and prove the new model equal on the side (no single source)
└─ Alt 3.3 [0.30]: definitional (`rfl`) equality (blocked by the `!`-read vs `[i]?` rewrite)
Step 4: Invariants (C)
├─ Alt 4.1 [0.75]: per-family case lemmas plus a decidable price condition (`PositivePrices`)
│                  checked for all 13 forks by `decide`
├─ Alt 4.2 [0.50]: one monolithic `cases w <;> simp` (heartbeat blow-up)
└─ Alt 4.3 [0.30]: reflection over a cost table
Step 5: Termination (F)
├─ Alt 5.1 [0.60]: generic WF-on-gas machine + fuel adequacy for `X`'s loop under explicit
│                  hypotheses on the rest of the mutual block
├─ Alt 5.2 [0.25]: rewrite the mutual Θ/Λ/Ξ/X block with `termination_by` on gas
└─ Alt 5.3 [0.20]: fuel adequacy by induction over the whole block
Step 6: Tests (F)
├─ Alt 6.1 [0.85]: `#guard` unit tests per fork, Plausible properties mirroring each theorem,
│                  mutation tests that must be refuted
├─ Alt 6.2 [0.60]: unit tests only
└─ Alt 6.3 [0.40]: conformance fixtures only (no data available offline)

PATH SCORES:
A: [0.80] 1.1→2.1→3.1→4.1→5.1→6.1   (highest success probability)
B: [0.62] 1.2→2.1→3.2→4.1→5.1→6.2   (balanced)
C: [0.30] 1.3→2.3→3.3→4.3→5.2→6.3   (novel)

FINAL PLAN: Path A
Step 1 [C]: ForkSchedule.lean (13 forks), ForkSchedulePins.lean; GasConstants := cancun projections
Step 2 [C]: GasCost.lean: instrCost?, memoryCost?, guardOk, costParts, cost
Step 3 [C]: chargeOp, settleRefund; Semantics: exceptionalHalt := exceptionalHaltFs cancun;
            GasCostBridge.exceptionalHalt_eq_prev
Step 4 [C]: GasCostLemmas, GasPositivity, GasInvariants, GasCallBoundary
Step 5 [F]: GasTermination
Step 6 [F]: ForkScheduleTests; axiom audit and lints extended to every new module
```

Path A was executed. Step 5 is only partly done, as described below.

## 1. `ForkSchedule` (`EvmYul/EVM/Gas/ForkSchedule.lean`)

* `Fork`: Frontier, Homestead, Tangerine Whistle, Spurious Dragon, Byzantium, Petersburg (which also
  stands for Constantinople, whose SSTORE metering was reverted), Istanbul, Berlin, London,
  Shanghai, Cancun, Prague and Osaka.
* `ForkSchedule` contains:
  * every YP Appendix G price;
  * the flat pre-Berlin prices (`Gsload`, `Gbalance`, `Gextcode`, `Gextcodehash`, `Gcall`);
  * the EIP switches: `callGasRetention` (EIP-150), `eip2929`, `sstoreRule`,
    `selfdestructNewAccount`, `refundQuotient` (EIP-3529), `maxCodeSize`, `maxInitcodeSize`,
    `txDataFloorPerToken` (EIP-7623), `perEmptyAccountCost` (EIP-7702) and `txGasLimitCap`
    (EIP-7825).
* `GasConstants.X` is now `ForkSchedule.cancun.X`, so the interpreter's prices come from the record.
* Pins (`ForkSchedulePins.lean`, all `rfl`): `<fork>_def` gives the full literal record, and
  `<fork>_eq_prev` the EIP delta from the previous fork.

## 2. The pure cost and the accounting transformer (`EvmYul/EVM/Gas/ForkCost.lean`)

* `instrCost? fs gas s w : Option ℕ` reads operands with `stack[i]?`, so it has no `!` reads.
  `memoryCost? fs s w` is the memory-expansion part.
* `cost fs s w = (costParts fs s w).map (·.1 + ·.2)`. `costParts` checks `guardOk` first: the opcode
  must exist in the fork, be valid, and have its operands on the stack. Only then does it evaluate
  the memory part, and finally the instruction part on the gas left after the memory charge. So
  `cost` is `none` exactly when the guard fails (`cost_eq_none_iff`), and memory expansion is never
  evaluated before the guard.
* `gas` stays an argument because the YP's CALL cost depends on it. It cannot be removed:
  `call_cost_order_sensitive` gives, for every EIP-150 schedule, a CALL whose cost is
  `6300 + C_EXTRA` on pre-memory gas and `5670 + C_EXTRA` on post-memory gas.
  `instrCost?_gas_indep` shows that every other instruction ignores the argument.
* `chargeOp` is the accounting transformer: guard, guarded memory charge, and a check that the
  instruction part fits. Its normal form is `chargeOp_of_costParts`: a single guarded charge of
  `m + c`. `settleRefund` handles the end-of-transaction refund.
* **Executable path.** `Semantics.exceptionalHalt := exceptionalHaltFs cancun`, which is `chargeOp`
  followed by `haltChecks`. `exceptionalHalt_eq_prev` proves it equal to the previous definition
  for **every** input. The equality is propositional (`exceptionalHalt_eq_prev_fun` by funext), not
  `rfl`, because the old body used `!` reads. The conformance runner (`Conform/`) is unmodified and
  builds. Agreement with the old cost functions: `instrCost?_cancun` (= `C'`), `memoryCost?_cancun`
  (= `memoryExpansionCost`) and `costParts_cancun`.

## 3. Invariants

| Requirement | Theorem (file) |
|---|---|
| Z never fires spuriously | `exceptionalHaltFs_error_cases`, `exceptionalHaltFs_oog_sound` (soundness), `exceptionalHaltFs_ok_of` (completeness) (`GasInvariants`) |
| Accounting normal form | `chargeOp_of_costParts`, `chargeOp_ok_iff`, `chargeOp_oog_iff`, `chargeOp_ok_deduct` (`GasInvariants`) |
| Every non-halting instruction costs ≥ 1, in every fork | `instrCost?_ge_minCost`, `minCost_pos`, `instrCost?_pos`, `positivePrices_ofFork` (`GasPositivity`) |
| SELFDESTRUCT must be excluded | `frontier_selfdestruct_free` (`GasPositivity`) |
| Gas strictly decreases per non-halting step | `exceptionalHaltFs_charge_lt` (all schedules with positive prices), `exceptionalHalt_charge_lt` (interpreter) (`GasInvariants`) |
| refund ≤ ⌊used/5⌋ | `settleRefund_refund_le` (≤ used / quotient, every schedule), `settleRefund_refund_le_fifth` (London on), `settleRefund_refund_le_counter`, `settleRefund_le_limit`, `refundedGas_toNat_eq_settleRefund` (the interpreter's refund is `cancun.settleRefund`) (`GasInvariants`) |
| 63/64 rule at every call boundary | generic: `callGasCap_le_L`, `callGas_le`, `callCost_retains`, `callGas_lt_size` (no `UInt256` wrap); interpreter: `call_boundary_of_instrCost`, `call_boundary`, `staticcall_boundary`, `create_boundary` (`GasCallBoundary`) |
| Order sensitivity | `instrCost?_gas_indep`, `call_cost_order_sensitive` (`GasCallBoundary`) |
| UInt256 ↔ ℕ | `toNat_sub_ofNat_of_le`, `deductPrechecked_toNat`, `toNat_ofNat_of_lt`, used in `exceptionalHalt_ok_parts`, `call_boundary_of_instrCost`, `create_boundary` |
| Termination | `GasMachine.run` (fuel-free, `termination_by` gas), `GasMachine.runFuel_eq_run`, `runFuel_ne_oof`, `X_ne_outOfFuel` (`GasTermination`) |

## 4. What is not done

* **`X` still uses fuel, so OutOfFuel is not eliminated from the interpreter.** `X_ne_outOfFuel`
  proves that `X`'s own counter never runs out once fuel > gas + 2, under two hypotheses stated for
  the charge `Z` produced: `StepGasSoundZ` and `NestedFuelAdequateZ`. `GasStepFrame` proves both
  for every instruction except CREATE, CREATE2, CALL, CALLCODE, DELEGATECALL and STATICCALL
  (`step_some_gasSafe`), so `X_ne_outOfFuel_of_spawn` needs them only for those six; those six are
  now proved too (K8, `Gas/Nested.lean`), so `X_ne_outOfFuel_unconditional` has no hypotheses. The earlier charge-free hypotheses `StepGasSound` /
  `NestedFuelAdequate` were false (`not_stepGasSound`, `not_nestedFuelAdequate`), so the earlier
  form of the theorem was vacuous; see `STEP_FRAME.md`.
* **The conformance suite was not run**, because the fixture data is not available offline. The
  executable equality is proved (`exceptionalHalt_eq_prev`), and the `Conform` library builds.
* The interpreter still runs only the Cancun schedule. The other forks are fully priced in
  `ForkSchedule` and tested in `ForkScheduleTests`, but `Θ`/`Υ` take no fork argument.
* `D_J_aux` (a `partial def`) and the FFI hashes are in the trusted base (see `TCB.md`). No gas
  theorem depends on their values.

## 5. Tests (`EvmYul/EVM/Gas/ForkScheduleTests.lean`)

* Unit tests (`#guard`):
  * cold SLOAD 50/200/800/2100 across forks;
  * EXP byte price 10 vs 50;
  * BALANCE across forks;
  * PUSH0/TLOAD/SHL unavailable in earlier forks;
  * stack underflow and INVALID give `none`;
  * memory expansion inside `cost`;
  * CALL with and without the 63/64 rule (Frontier 1 000 040, Tangerine Whistle 98 449, Cancun
    98 479 = `C'`);
  * SSTORE and SELFDESTRUCT across forks;
  * `chargeOp` results (ok, OOG, underflow, invalid in Frontier) and `exceptionalHaltFs` per fork;
  * refunds with quotient 2 vs 5, and `refundedGas` = `cancun.settleRefund`.
* Plausible properties (300 inputs, fixed seed), one per theorem family:
  * Cancun agreement with `memoryExpansionCost + C'`, and `none` iff the guard fails;
  * the `chargeOp` normal form in every fork;
  * positivity in every fork;
  * gas independence outside the CALL family;
  * the refund bounds in every fork;
  * the 63/64 boundary in every EIP-150 fork.
* Mutation tests. Plausible must find a counterexample to each of these, which shows the
  properties above are not vacuous:
  * "SELFDESTRUCT always costs gas";
  * "CALL cost is independent of gas";
  * "a Cancun refund with quotient 2 respects used/5";
  * "a CALL without the 1/64 retention keeps (gas − extra)/64".
