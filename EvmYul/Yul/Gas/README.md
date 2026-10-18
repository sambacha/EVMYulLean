# Yul gas: a metered Yul semantics and a static bound (analysis §5, Approach B)

This document covers the Yul half of `EVMYulLean_Gas_Analysis.md`: issue **S6** ("Yul has a
`gasAvailable` field that is never updated") and **Approach B** ("gas-carrying Yul semantics … only
the *bound* flavor is realistically deliverable without modeling solc codegen"). Approach A (the
EVM meter) was delivered in earlier changes; see `docs/gas/PLAN.md` and `docs/gas/RESULTS.md`.

## 1. Plan tree

Scores are estimated success probabilities for this repository and toolchain (Lean 4.22.0 when written, now 4.28.0; no
network). C = critical step, F = flexible.

```
PLAN TREE:
Step 1: One cost table for both languages (no drift, analysis S2/B-"Cons")
├─ Alt 1.1 [0.9]: map each Yul builtin to its EVM twin (total, no wildcard) and reuse GasMeter.feeGroup
├─ Alt 1.2 [0.6]: a separate Yul fee table, kept equal to the EVM one by a differential test
└─ Alt 1.3 [0.3]: change Operation so that Yul and EVM share one constructor type
Step 2: A metered Yul semantics
├─ Alt 2.1 [0.4]: thread gas through the existing fuelled interpreter (breaks ~2,000 lines of proofs)
├─ Alt 2.2 [0.5]: a gas-indexed copy of the relational semantics (7 mutual relations)
└─ Alt 2.3 [0.8]: a fuel-free metered evaluator on a loop-free, call-free fragment, related to ExecR
Step 3: Relate the meter to the existing semantics
├─ Alt 3.1 [0.8]: soundness (evaluator ⇒ ExecR) and completeness (ExecR ⇒ evaluator) by syntax recursion
├─ Alt 3.2 [0.5]: prove the evaluator equal to `exec` directly by induction on fuel
└─ Alt 3.3 [0.3]: differential testing only
Step 4: A static gas bound
├─ Alt 4.1 [0.85]: syntactic bound (sum along code, max over branches), proved sound and tight
├─ Alt 4.2 [0.5]: loop bounds via invariants (needs `for`, i.e. the WP layer plus gas)
└─ Alt 4.3 [0.3]: bound via a compiled-bytecode model (needs a Yul→EVM compiler; F-2)
Step 5: Regression tests that cannot pass vacuously
├─ Alt 5.1 [0.9]: unit + Plausible properties mirroring each theorem + mutation tests, run at build
├─ Alt 5.2 [0.6]: an executable test driver (needs the FFI libraries linked)
└─ Alt 5.3 [0.4]: golden files only

PATH SCORES:
A: [0.81] 1.1 → 2.3 → 3.1 → 4.1 → 5.1   (highest success probability)
B: [0.45] 1.2 → 2.2 → 3.1 → 4.2 → 5.1   (balanced: loops, larger proof surface)
C: [0.10] 1.3 → 2.1 → 3.2 → 4.3 → 5.2   (novel: compiler-backed, open research per the analysis)

FINAL PLAN: Path A
Step 1 [C]: `toEVM` without wildcard + `yulFeeGroup := feeGroup ∘ toEVM`; prove agreement with C'.
Step 2 [C]: `execG` on the fragment (no `for`, no user calls, no CALL family); no fuel needed.
Step 3 [C]: `execG_sound`, `execG_complete`, hence `exec_eq_execG` for the real interpreter.
Step 4 [F]: `gasS` with `execG_gas_le` (sound) and `execG_gas_eq_of_ok` (exact on straight code).
Step 5 [F]: `EvmYul/Yul/Gas/MeteredTests.lean` in `lake build EvmYulGasTests`.
```

Review of the path before execution:
- *Counterexamples first*: the switch quirk (`switch_default_error_aborts`) means a naive meter that
  charges "the selected branch" must still model the default block's error; the evaluator follows
  `ExecR` exactly, and the gas convention for `switch` is stated in `Metered.lean`.
- *Conjecture → lemma*: "the bound is exact" is false with branches (refuted by a mutation test),
  so the exactness theorem carries the `Straight` hypothesis; the test suite shows the hypothesis is
  needed.
- *Proof obligations*: completeness needs determinism of builtins; it holds only off the CALL family
  (`primCallK_indep`), which is why the fragment excludes the CALL family.
- *Conventions*: same test harness style as `Yul/Relational/SemanticsTests.lean` (named unit checks, fixed-seed
  Plausible, `expectRefuted`-style mutants), same axiom audit, no `sorry`, no `native_decide`.

## 2. What was built

| File | Contents |
|---|---|
| `EvmYul/Yul/Gas/CostModel.lean` | `toEVM`, `ofEVM`, `toEVM_injective`, `yulFeeGroup`, `FeeGroup.floorCost`, `CostModel`, `cancun`, `cancun_prim_eq_C'`, `cancun_prim_le_C'` |
| `EvmYul/Yul/Gas/Metered.lean` | fragment (`fragS`, `InFragment`, `Straight`), metered evaluator `execG`, static bound `gasS`, `execG_gas_le`, `execG_gas_eq_of_ok` |
| `EvmYul/Yul/Gas/MeteredSound.lean` | `ArgsR` snoc lemmas, `execG_sound`, `execG_complete`, `execR_deterministic`, `exec_eq_execG`, `exec_gas_bound`, `exec_gas_exact` |
| `EvmYul/Yul/Gas/MeteredTests.lean` | 24 unit checks, 5 Plausible properties, 4 mutation tests (run by `lake build EvmYulGasTests`) |

### Main theorems (all proved, standard axioms only; checked by `Audits.GasAxioms`)

- `cancun_prim_eq_C'`: for every Yul builtin whose EVM twin has a state-independent price, the Yul
  price equals the EVM charge `C'` of the twin **in every EVM state**.
- `cancun_prim_le_C'`: for every Yul builtin and every EVM state, the Yul price is at most `C'` of
  the twin (for dynamically priced builtins the Yul model charges the state-independent floor).
- `execG_sound`: every result of `execG` that is not "out of fuel" is an `ExecR` run (any program).
- `execG_complete`: on the fragment, every `ExecR` run has exactly the result of `execG`.
- `exec_eq_execG`: on the fragment, every interpreter run that does not run out of fuel returns
  exactly `(execG c st s).1`.
- `exec_gas_bound`: on the fragment, every such run is charged at most `gasS c st` gas, for every
  start state and every cost model `c`.
- `exec_gas_exact`: on straight-line fragment programs, every run that ends normally is charged
  exactly `gasS c st`.

## 2a. Loops (`EvmYul/Yul/Gas/Loops.lean`)

A loop's gas depends on how many times its body runs, so no syntactic bound exists. For a
single-level loop `for {} cond {post} {body}` (condition, body and post block in the fragment),
the file adds a metered loop evaluator and bounds its gas in terms of the iteration count.

- `loopG c n cond post body s`: follows the interpreter's `loop` case by case, with an iteration
  budget `n`. It returns a `LoopOut`: result, gas, `iters` (how many times the body ran) and
  `clean` (every body and post block ended normally and the loop left through its condition).
  Gas convention as for `if`: the condition's builtins plus one `c.branch` per test.
- `loopIterGas = gasE cond + branch + gasB body + gasB post`, `loopExitGas = gasE cond + branch`.
- `loopG_gas_le`: gas ≤ `iters · loopIterGas + loopExitGas`, for every start state and budget.
- `loopG_gas_eq`: equality for clean runs of loops whose body and post block are straight-line.
- `loopG_iters_le`: `iters ≤ n`.
- `exec_for_eq_loopG`: every interpreter run of such a loop that does not run out of fuel returns
  exactly the result of `loopG` for some budget (proved by induction on the interpreter's fuel,
  using `exec_eq_execG` for the body and post block).
- `exec_for_gas_bound`: the combination for the interpreter.

Tests (`EvmYul/Yul/Gas/LoopsTests.lean`, in `lake build EvmYulGasTests`): 10 unit checks (a
ten-iteration counting loop costs exactly `10 · 20 + 14 = 214` gas under the Cancun model, an
immediate `break`, a constant-false condition, budget 0); 6 Plausible suites mirroring each theorem,
with non-vacuity checks (break-free straight loops are clean and run `k` times; with enough fuel
the interpreter never runs out); 5 mutants that must be refuted (no exit term, no post block, one
iteration fewer, exactness without the straight-line hypothesis, a fixed budget of 3).

## 2b. Nested loops (`EvmYul/Yul/Gas/NestedLoops.lean`)

§2a covers one loop level. This file covers every call-free program whose loops are nested
arbitrarily (`fragLS`: loops inside loop bodies, inside `if`/`switch` branches, and so on). The
bound is stated in terms of an iteration budget `n`, the largest number of body executions of any
single entry into any loop of the run.

- `execL c n st s : Option (Res × ℕ)`: a metered evaluator. Loops are run by `loopWith`, which
  follows `LoopR` case by case and allows `n` body executions per loop entry. `none` means some loop
  entry needs more than `n`.
- `gasLS c n st`: a static bound, polynomial in `n` with degree equal to the loop nesting depth.
  A loop costs `n · (gasE cond + branch + gasLB n body + gasLB n post) + gasE cond + branch`.
- `execL_gas_le`: `execL c n st s = some (r, g) → g ≤ gasLS c n st`.
- `execL_mono`: a run that fits in budget `n` gives the same result and gas with every larger
  budget. `execL_budget_indep`: two successful budgets give the same result and gas.
- `exec_complete_execL` / `exec_eq_execL`: every interpreter run that does not run out of fuel is
  an `execL` run for some budget. Proved by strong induction on the interpreter's fuel; `switch` uses
  `selectBranch_of_execSwitchCases`, which shows the selected branch is an interpreter run with less
  fuel.
- `exec_nested_gas_bound`: the result for the interpreter. Such a run has a budget `n` at which
  `execL` returns its result with gas `≤ gasLS c n st`, and every larger budget gives the same
  result and gas.
- `execL_of_fragS`, `gasLS_of_fragS`: on loop-free programs `execL` equals `execG` and `gasLS`
  equals `gasS`, for any budget. So this layer extends §2 without changing it.

Tests (`EvmYul/Yul/Gas/NestedLoopsTests.lean`, in `lake build EvmYulGasTests`). They use two nested
counting loops (`k₁, k₂ < 12`) with a random inner body.
- 16 unit checks, worked out by hand. Example: a 3×4 nest costs \(3\cdot(14+94+3)+14=347\) gas,
  needs budget 4 and fails with budget 3. A 3×3 nest costs exactly `gasLS 3 = 287`. A three-level
  2×2×2 nest costs exactly 360. The interpreter agrees with the meter.
- 8 Plausible suites:
  - interpreter agreement under random fuel, with a non-vacuity check (enough fuel never runs out);
  - the gas bound, with a non-vacuity check (budget 11 always succeeds);
  - budget monotonicity;
  - least budget = largest per-entry iteration count;
  - exactness for break-free straight-line \(k\times k\) nests;
  - agreement with `execG`/`gasS` on loop-free programs.
- 5 mutants, all refuted: one iteration fewer, the inner loop charged once instead of once per outer
  iteration, no inner exit tests, a fixed budget of 3, and reversed monotonicity.

## 2c. User-defined functions (`EvmYul/Yul/Gas/Functions/Basic.lean`, `Functions/Complete.lean`)

§2b covers call-free programs. This layer adds calls of user-defined Yul functions, including
recursive and mutually recursive ones, on top of arbitrarily nested loops (`fragFS`). Contract calls
(the CALL family) are still excluded.

Plan for this step (scores are estimated success probabilities; C = critical, F = flexible):

```
Step 1: A metered semantics with calls
├─ Alt 1.1 [0.8]: evaluator parametrised by a call runner; the runner at depth d runs bodies at depth d-1
├─ Alt 1.2 [0.4]: one evaluator by well-founded recursion on (depth, syntax)
└─ Alt 1.3 [0.3]: inline function bodies up to a depth (breaks on recursion)
Step 2: A static bound
├─ Alt 2.1 [0.85]: bound parametrised by per-function callee bounds, computed from a table by depth
├─ Alt 2.2 [0.4]: fixpoint over the call graph (only for non-recursive programs)
└─ Alt 2.3 [0.3]: bound per call site from the actual run (not static)
Step 3: Link to the interpreter
├─ Alt 3.1 [0.75]: strong induction on fuel over eval, exec and call at once
├─ Alt 3.2 [0.2]: induction on ExecR derivations (no `brecOn` for the mutual relations: not usable)
└─ Alt 3.3 [0.3]: differential tests only
Step 4: Tests
└─ Alt 4.1 [0.9]: unit + Plausible properties mirroring each theorem + mutants (same harness as §2b)

FINAL PLAN: 1.1 [C] → 2.1 [C] → 3.1 [C] → 4.1 [F]
```

Definitions:
- `FnCostModel` extends `CostModel` with `call`, the price of one user-function call. The Cancun
  instance `cancunFn` charges `PUSH` of the return label plus two `JUMP`s and two `JUMPDEST`s:
  `3 + 2 · (8 + 1) = 21`. Like `branch`, this is an assumption about compiled code.
- `evalF`, `argsF`, `execF`, `blockF`, `casesF`, `loopF`: a metered evaluator parametrised by a call
  runner `rc` and an iteration budget `n`. It mirrors the interpreter case by case, including the
  object-data builtins (`dataoffset`/`datasize` in expressions, `datacopy` in statements, charged 0).
- `callF c co n d`: the call runner with call-depth budget `d`. It looks the function up exactly
  as the interpreter does (`lookupFunction`) and runs its body with depth budget `d - 1`; at depth
  `0` it gives up (`none`).
- `runF c co n d st s := execF c (callF c co n d) n st s`.
- `gasFS c gc n st`: static bound given a bound `gc f` per call of `f`; `gasFn c tbl n d f` computes
  these bounds from a function table by depth; `gasF c tbl n d st` is the program's bound.
- `TableCovers co tbl`: the table contains every function the interpreter can look up;
  `tableCovers_some`: with code override `some code`, `code.functions.lookup` covers.
- `FunctionsInFragment co`: every function the interpreter can look up has its body in the fragment.

Results (all proved, standard axioms only):
- `runF_gas_le`: `runF c co n d st s = some (r, g) → g ≤ gasF c tbl n d st` for every covering table.
- `runF_mono`, `runF_budget_indep`: larger budgets (both `n` and `d`) give the same result and gas.
- `exec_complete_runF`: if `FunctionsInFragment co`, every interpreter run on a fragment program that
  does not run out of fuel is a `runF` run for some `n`, `d`.
- `exec_fn_gas_bound`: the result for the interpreter: such a run has budgets `n`, `d` at which `runF`
  returns its result with gas `≤ gasF c tbl n d st`, and all larger budgets give the same result and
  gas. `exec_fn_gas_bound_code` is the special case of a fixed contract (`co = some code`).
- `runF_of_fragLS`, `gasF_of_fragLS`: on call-free programs `runF` equals `execL` and `gasF` equals
  `gasLS`, for any call-depth budget and table. So this layer extends §2b without changing it.

Tests (`EvmYul/Yul/Gas/Functions/CompleteTests.lean`, in `lake build EvmYulGasTests`). The test contract
defines `inc`, `twice` (depth 2), the recursive `fact`, `sumTo` (a loop inside a function) and the
mutually recursive `even`/`odd`; random caller programs mix the statements of `Gas/MeteredTests.lean` with calls
of these functions and of a missing one.
- 17 unit checks, worked out by hand. Example: `fact(5)` returns 120 and costs
  \(21 + 14 + 5\cdot 43 = 250\) gas; it needs depth budget 6 and fails with 5; the static bound at
  depth 6 is \(21 + 6\cdot 43 = 279\) (the extra 29 is the recursive branch not taken at the deepest
  level). `twice(3)` costs exactly the bound, 69. `even(4)` (mutual recursion) costs 187. A call of a
  missing function fails and costs only the call overhead, 21. The interpreter agrees each time.
- 8 Plausible suites: interpreter agreement under random fuel (with a non-vacuity check), the gas
  bound (with a non-vacuity check: budgets `(8, 7)` always succeed), budget monotonicity, the minimal
  depth of `fact(k)` is `k + 1`, exactness for straight-line programs calling `inc`/`twice`, and
  agreement with `execL`/`gasLS` on call-free programs.
- 5 mutants, all refuted: one call level fewer, no call overhead in the bound, a fixed depth budget
  of 3, reversed depth monotonicity, and callees charged as if they made no calls.

### What is *not* claimed

- That solc compiles Yul control flow to a particular instruction sequence. `CostModel.branch`
  (Cancun instance: `JUMPI + JUMPDEST = 11`) is a model parameter; the theorems are generic in it.
- Dynamic gas (memory expansion, cold/warm access, copy words, log data, call forwarding). The
  Cancun model charges the state-independent floor of each builtin's price (`cancun_prim_le_C'`);
  the dynamic remainder is charged by the EVM layer.
- Contract calls (the CALL family): they need the callee contract's cost. Loops nested to any depth
  and user-defined functions (also recursive) are covered by §2a–§2c.
- A static bound on the call depth of recursive functions: like the iteration count, the bound of
  §2c is stated in terms of the depth the run needs.
- A static bound on the number of loop iterations. The loop bounds of §2a–§2c are stated in terms
  of the number of iterations of the run; bounding that number needs a ranking argument about the
  program's variables, which is not part of this layer.
- (Fuel adequacy of the interpreter on the fragment, conjecture K10, is now proved:
  `exec_eq_execG_of_fuel` in `FuelAdequacy.lean`.)

## 3. Verification

`lake build EvmYul EvmYulGasTests Conform` succeeds with no warnings. The Yul part of the test log
shows (counterexamples elided):

```
info: EvmYul/Yul/Gas/MeteredTests.lean: 30 unit checks passed
6 property suites passed
[mutant bound: forgets if bodies] refuted as expected by …
[mutant bound: cheapest switch branch] refuted as expected by …
[exactness without the straight-line hypothesis] refuted as expected by …
[mutant fuel: ignores nesting depth (statement count + 5)] refuted as expected by …
[mutant fuel: ignores block length (constant 30)] refuted as expected by …
[differential test against a mutated program (ADD -> SUB)] refuted as expected by …
info: EvmYul/Yul/Gas/LoopsTests.lean: 10 unit checks passed
6 property suites passed
[mutant bound: no exit term] refuted as expected by [k := 0, init := [], ns := [], issue: 14 ≤ 0 does not hold]
[mutant bound: forgets the post block] refuted as expected by …
[mutant bound: one iteration fewer] refuted as expected by …
[exactness without the straight-line hypothesis] refuted as expected by …
[mutant meter: an iteration budget of 3 matches the interpreter] refuted as expected by …
info: EvmYul/Yul/Gas/NestedLoopsTests.lean: 16 unit checks passed
8 property suites passed
[mutant bound: one iteration fewer] refuted as expected by …
[mutant bound: the inner loop is charged once] refuted as expected by [k₁ := 2, k₂ := 2, init := [], ns := [3], issue: false does not hold]
[mutant bound: no inner exit tests] refuted as expected by …
[mutant meter: an iteration budget of 3 matches the interpreter] refuted as expected by …
[mutant: budget monotonicity reversed] refuted as expected by …
info: EvmYul/Yul/Gas/Functions/CompleteTests.lean: 17 unit checks passed
8 property suites passed
[mutant bound: one call level fewer] refuted as expected by [k := 0, issue: false does not hold]
[mutant bound: no call overhead] refuted as expected by …
[mutant meter: a call-depth budget of 3 matches the interpreter] refuted as expected by [k := 3, …]
[mutant: depth monotonicity reversed] refuted as expected by …
[mutant bound: callees charged as if they made no calls] refuted as expected by …
axiom audit (PO-11): 1812 gas theorems use only propext/Classical.choice/Quot.sound
```

## Files

The library children of this folder (layout check L13 keeps this list complete):

- `CostModel.lean`: Yul gas, part 1: one cost table for both languages (analysis, Approach B, item 1).
- `CostMono.lean`: Yul gas is monotone in the cost model; the call-price hypothesis cannot be dropped.
- `FuelAdequacy.lean`: Yul gas, part 4: fuel adequacy of the interpreter on the fragment (conjecture K10).
- `Loops.lean`: Yul gas, part 5: gas bounds for `for` loops.
- `Metered.lean`: Yul gas, part 2: a metered Yul semantics and a static gas bound (analysis, Approach B).
- `NestedLoops.lean`: Yul gas, part 6: nested loops.
- `MeteredSound.lean`: Yul gas, part 3: the metered evaluator is the relational semantics.
- `Functions/`: Yul gas: user functions; see `Functions/README.md`.
