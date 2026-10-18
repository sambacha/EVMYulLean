# Gas behaviour of `step`, and a correction to the fuel theorem

This round picks up the first open item of `FORK_SCHEDULE.md` §4: the two hypotheses of
`X_ne_outOfFuel` (`X`'s own fuel counter never runs out once fuel > gas + 2).

## Plan tree

```
PLAN TREE:
Step 1: Show that EvmYul.step never touches the gas (non-spawning opcodes)
├─ Alt 1.1 [0.80]: one GasSafe lemma per shared helper (execBinOp, unaryStateOp, log2Op, …),
│                  a per-family lemma naming each constructor's helper, no catch-all case
├─ Alt 1.2 [0.35]: one theorem, `cases op <;> first | exact … | …` over all helpers
└─ Alt 1.3 [0.20]: rewrite EvmYul.step so that it cannot write gasAvailable (changes the code)
Step 2: Lift to the interpreter's EVM.step (the charge is deducted exactly)
├─ Alt 2.1 [0.75]: unfold EVM.step once, `split`; spawning branches closed by `decide` on spawnOps
├─ Alt 2.2 [0.40]: prove an equation lemma per opcode
└─ Alt 2.3 [0.30]: refactor EVM.step into "deduct; dispatch"
Step 3: Feed the result into X_ne_outOfFuel
├─ Alt 3.1 [0.70]: restrict the hypotheses to decoded instructions, reduce them to spawnOps
├─ Alt 3.2 [0.40]: prove the whole mutual block by induction on gas (CALL/CREATE included)
└─ Alt 3.3 [0.30]: replace X by GasMachine.run
Step 4: Try to break the hypotheses (critical: a false hypothesis makes the theorem vacuous)
├─ Alt 4.1 [0.70]: kernel-evaluated CALL executions with extreme charges / fuel
├─ Alt 4.2 [0.50]: random executable search only
└─ Alt 4.3 [0.20]: argue on paper
Step 5: Tests that execute the interpreter
├─ Alt 5.1 [0.75]: compiled test executable (FFI primitives are unavailable while building)
├─ Alt 5.2 [0.30]: #eval in the build (crashes: no native FFI in the elaborator)
└─ Alt 5.3 [0.40]: kernel `decide` on small states only

PATH SCORES:
A: [0.74] 1.1→2.1→3.1→4.1→5.1
B: [0.45] 1.2→2.2→3.2→4.2→5.3
C: [0.28] 1.3→2.3→3.3→4.3→5.2

FINAL PLAN: Path A
Step 1 [C]: GasSafe for 21 helpers + 11 family lemmas (generated from EvmYul/Semantics.lean)
Step 2 [C]: step_some_gasSafe
Step 3 [F]: Z-restricted hypotheses, X_ne_outOfFuel_of_spawn
Step 4 [C]: not_stepGasSound / not_nestedFuelAdequate
Step 5 [F]: lake exe gasStepFrameTests (+ CI step)
```

Alt 1.2 was tried first: it ran out of heartbeats (all cases share one declaration's budget), and
elaborating `fun _ _ _ => rfl` before the helper's function argument was known caused `whnf`
timeouts. Splitting per family (Alt 1.1) and naming the function argument fixed both; the module
builds in about 8 s.

## Results (all in `EvmYul/EVM/Gas/StepFrame.lean`, no `sorry`, standard axioms only)

* `evmStep_gasSafe`: for every instruction outside `spawnOps`, `EvmYul.step` either succeeds with
  `gasAvailable` unchanged or fails with an error other than `OutOfFuel`.
* `step_some_gasSafe`: for those instructions, the interpreter's `EVM.step` with at least one unit
  of fuel either succeeds leaving exactly `gasAvailable − c` (`deductPrechecked`) or fails with an
  error other than `OutOfFuel`.
* `not_gasSafe_CREATE` / `evmStep_CREATE_eq_default`: the exclusion is necessary. `EvmYul.step`'s
  fall-through `| .EVM, _ => λ _ ↦ default` makes CREATE (and the other spawning opcodes)
  *succeed* with the all-zero state. `EVM.step` intercepts them, so the interpreter never reaches
  this case, but the fall-through is a latent hazard for any other caller of `EvmYul.step`.
* `stepGasSoundZ_of_spawn`, `nestedFuelAdequateZ_of_spawn`, `X_ne_outOfFuel_of_spawn`: the fuel
  theorem now assumes its two hypotheses only for the six spawning instructions.

### Correction: the earlier hypotheses were false

`StepGasSound` and `NestedFuelAdequate` (the hypotheses of the earlier `X_ne_outOfFuel`) quantify
over every charge `c ≤ gas`. Both are refuted by CALL executions that the kernel evaluates:

* `not_stepGasSound`: charge 0, gas 0, value 1 > balance 0. The CALL fails the balance check and
  returns the callee allowance (100) plus the 2300 stipend: gas goes from 0 to 2400.
* `not_nestedFuelAdequate`: fuel 2, gas 0. The CALL reaches `Θ` with fuel 0, which raises
  `OutOfFuel`.

So the earlier theorem was vacuous. The hypotheses are now stated only for charges that `Z`
(`exceptionalHalt`) produced (`StepGasSoundZ`, `NestedFuelAdequateZ`); `Z` rejects both witnesses
(`exceptionalHalt_callWitness_oog`). `X_ne_outOfFuel` keeps its name with the corrected
hypotheses; the old definitions are kept only so that their refutations stay checked.

## Tests (`EvmYul/EVM/Gas/StepFrameTests.lean`, `lake exe gasStepFrameTests`)

The interpreter's memory and hash primitives are FFI calls, which the elaborator cannot run (an
`#eval` of `EvmYul.step` aborts with "Could not find native implementation of external declaration
`ffi.ByteArray.zeroes`"). The checks therefore run as a compiled executable (exit code 1 on
failure), added to CI. Output of the run in this session:

```
9 unit checks passed
spawn coverage: 740 of 1350 grid samples pass Z
spawn conjecture holds on all 1350 grid samples
[coverage: some random spawning instruction passes Z] refuted as expected by [k := 5, …]
3 property suites passed (300 inputs each)
[mutant: EvmYul.step is gas-safe for every instruction (spawnOps included)] refuted as expected by [o := { byte := 245 }, …]
[refuted hypothesis: spawning instructions with charge 0 (not_stepGasSound)] refuted as expected by [k := 5, …]
[mutant: EVM.step leaves the gas unchanged (deduction forgotten)] refuted as expected by [o := { byte := 68 }, …]
gasStepFrameTests: all checks passed
```

A first version of the spawn check passed vacuously: random gas stayed below every CALL's cost,
so `Z` rejected every sample. It now draws gas from 30 000 up and the run fails unless at least 600
of 1350 grid samples pass `Z`.

## Build-time gates

`GasStepFrame` is added to the axiom audit (953 theorems), the unused-argument lint and the A5
proof-term audit. The three `rfl` pins (`step_zero_fuel`, `evmStep_CREATE_eq_default`,
`call_fuel2_outOfFuel`) are on the reviewed list, each paired with a property that needs real
reasoning.

## What remains

* **K8 — now proved** in `Gas/Nested.lean` (`spawnStepGasSoundZ`, `spawnNestedFuelAdequateZ`,
  `X_ne_outOfFuel_unconditional`, and K1 `Υ_ne_outOfFuel`). The paragraph below is the original
  analysis, kept for context. The two hypotheses for CREATE/CREATE2/CALL/CALLCODE/
  DELEGATECALL/STATICCALL. For CALL the code shows what is needed. The caller ends with
  `gas − c + g'`, where `g'` is either the allowance `callgas` (failed balance check; the cost
  formulas give `callgas ≤ c`, read from the code but not proved) or what `Θ` returns, so the open part is "a nested frame returns at most the gas it received" (and the
  CREATE analogue for `Λ`). That is the induction over the mutual block.
* The interpreter still runs only the Cancun schedule; the conformance suite has not been run here.
