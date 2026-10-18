module

public import EvmYul.Yul.Gas.Functions.OracleTestHarness
public meta import EvmYul.Yul.Gas.Functions.OracleTestHarness
@[expose] public meta section

/-!
# A second, independent route to the gas of programs with user functions (D1, residual R-3)

`runF` (the metered semantics of `Functions/Basic.lean`) computes gas by structural recursion: each
evaluator returns a pair `(result, gas)` and adds up the gas of its parts, with the call runner
`callF` adding `call` plus the callee's gas. Every other check of user-function gas (the bound
`gasF`, the budget monotonicity, the golden values) goes through that same recursion or through
`gasF`, which is written in the same shape. A bug that both share, for example an inner call whose
gas is dropped, or a callee's branch charged at the wrong depth, would not be seen.

This file computes the same quantity a different way: **it rewrites the program so that it counts
its own gas, and runs the rewritten program on the reference interpreter `exec`**, which knows
nothing about gas.

* every builtin call `prim(args)` becomes a call of a wrapper function that first adds
  `c.prim prim` to a counter and then performs `prim`;
* every condition of an `if`, `switch` or `for` is wrapped in `__branch(cond)`, which adds
  `c.branch` and returns its argument;
* every user function gets `c.call` added as the first statement of its body.

The counter is transient-storage slot 0 (`tstore`/`tload`). It lives in the interpreter's shared
state, so it follows the interpreter's own control flow: across calls and returns, through `leave`,
`break` and `continue`, and in a `switch` (whose cases the interpreter evaluates separately) only the
selected case's additions survive. The meter is not consulted. Only the price table `c` is shared,
because both routes have to price the same cost model.

The comparison is made on runs where the interpreter returns a state (not on errors, since an error
carries no state to read the counter from). Checks:

1. **Unit tests**: the oracle reproduces the hand-computed gas of `CompleteTests` (fact, twice,
   sumTo, mutual recursion, a loop calling a function), and the rewrite is transparent (same
   variables as the original program).
2. **Property** (counted): on random programs with calls, whenever the interpreter returns a state,
   `runF` returns the same observation and **exactly** the counter's gas.
3. **Deterministic sweep**: 600 generated programs, with agreement and exclusion counts printed.
4. **Mutation tests**, so the comparison can fail: a meter that drops the gas of nested callees, a
   meter with the call price or the branch price one lower, and an oracle that forgets the call
   tick are all refuted.
-/

namespace EvmYul.Yul.GasTests.OracleTests

open Plausible Ast Relational Gas CompleteTests
open EvmYul.Testing.EvmFixtures

/-! ## 1. Unit tests -/

/-- Named unit checks; each must evaluate to `true`. -/
def unitChecks : List (String × Bool) :=
  [ ("wrapper names are reserved: no function of the test contract starts with `__`",
      fnListT.all fun fd => !fd.1.startsWith "__"),
    ("the rewrite is transparent: fact(5) still returns 120",
      (oracle cancunFn true 20000 (pFact 5)).map (·.1) == some "ok [120, 0, 0, 0]"),
    ("oracle: fact(5) costs 250 (hand value of CompleteTests)",
      (oracle cancunFn true 20000 (pFact 5)).map (·.2) == some 250),
    ("oracle: twice(3) costs 69", (oracle cancunFn true 20000 pTwice).map (·.2) == some 69),
    ("oracle: sumTo(4) costs 115", (oracle cancunFn true 20000 pSum).map (·.2) == some 115),
    ("oracle: even(4) costs 187 (mutual recursion)",
      (oracle cancunFn true 20000 pEven).map (·.2) == some 187),
    ("oracle: the loop calling sumTo costs 350",
      (oracle cancunFn true 20000 pLoopCall).map (·.2) == some 350),
    ("oracle and meter agree on the five hand-checked programs",
      [pFact 5, pTwice, pSum, pEven, pLoopCall].all fun p =>
        oracle cancunFn true 20000 p == meter cancunFn p),
    ("a call of a missing function is an error: no state, so no oracle value",
      (oracle cancunFn true 20000 pMissing).isNone),
    ("the counter starts at 0: a program of `let`s only costs 0",
      (oracle cancunFn true 100 (withInit [])).map (·.2) == some 0)
  ]

/-- Run every check; throws on the first failure. -/
def runAll : IO Unit := do
  for (name, ok) in unitChecks do
    unless ok do throw <| IO.userError s!"unit check failed: {name}"
  IO.println s!"{unitChecks.length} oracle unit checks passed"
  -- 2. The property: wherever the interpreter returns a state, the meter returns the same
  --    observation and exactly the counter's gas.
  yHolds "second route: runF gas = the self-counting program's counter on the interpreter"
    (∀ init ns : List ℕ,
      CountedTesting.WhenSome (oracle cancunFn true (oFuel ns) (genFProg false init ns)) fun o =>
        meter cancunFn (genFProg false init ns) == some o)
  -- ... and the rewrite never changes what the program computes.
  yHolds "the rewrite is transparent: same observation as the original program"
    (∀ init ns : List ℕ,
      CountedTesting.WhenSome (oracle cancunFn true (oFuel ns) (genFProg false init ns)) fun o =>
        eObsF (fnFuel ns) (genFProg false init ns) == some o.1)
  -- 3. Sweep.
  let mut agree := 0
  let mut excluded := 0
  let mut withCalls := 0
  for (init, ns) in corpus 600 do
    let p := genFProg false init ns
    match oracle cancunFn true (oFuel ns) p with
    | none => excluded := excluded + 1
    | some o =>
      unless meter cancunFn p == some o do
        throw <| IO.userError s!"oracle sweep: disagreement on init={init} ns={ns}: \
          oracle {o}, meter {meter cancunFn p}"
      agree := agree + 1
      if ns.any (fun n => n % 13 ≥ 9) then withCalls := withCalls + 1
  unless agree ≥ 300 ∧ withCalls ≥ 200 do
    throw <| IO.userError s!"oracle sweep too weak: agree={agree} withCalls={withCalls}"
  IO.println s!"D1 second route for user-function gas: the self-counting program on the \
    interpreter and runF agree exactly on {agree} of 600 programs ({withCalls} of them call user \
    functions); {excluded} excluded (the interpreter returned an error, so there is no state to read)"
  -- 4. Mutation tests.
  yRefuted "mutant meter: nested callees' gas dropped"
    (∀ init ns : List ℕ,
      CountedTesting.WhenSome (oracle cancunFn true (oFuel ns) (genFProg false init ns)) fun o =>
        meterFlat (genFProg false init ns) == some o)
  yRefuted "mutant meter: call price one lower"
    (∀ init ns : List ℕ,
      CountedTesting.WhenSome (oracle cancunFn true (oFuel ns) (genFProg false init ns)) fun o =>
        meter cheapCall (genFProg false init ns) == some o)
  yRefuted "mutant meter: branch price one lower"
    (∀ init ns : List ℕ,
      CountedTesting.WhenSome (oracle cancunFn true (oFuel ns) (genFProg false init ns)) fun o =>
        meter cheapBranch (genFProg false init ns) == some o)
  yRefuted "mutant oracle: the call tick forgotten"
    (∀ init ns : List ℕ,
      CountedTesting.WhenSome (oracle cancunFn false (oFuel ns) (genFProg false init ns)) fun o =>
        meter cancunFn (genFProg false init ns) == some o)

#eval runAll

end EvmYul.Yul.GasTests.OracleTests
