module

public import EvmYul.Yul.Gas.MeteredTestHarness
public meta import EvmYul.Yul.Gas.MeteredTestHarness
@[expose] public meta section

/-!
# Regression tests for Yul gas (`CostModel`, `Metered`, `MeteredSound`)

These run **during `lake build EvmYulGasTests`**; any failing check fails the build.

1. **Unit tests** (named checks, each must be `true`): the Cancun model's prices for a few builtins
   and for a branch; the price table against the EVM's `C'` for **every** Yul builtin (the list
   `allPrims` is checked to have 80 distinct entries, one per Yul builtin); concrete programs whose
   metered gas is computed by hand.
2. **Property tests** (Plausible, fixed seed) on random loop-free, call-free programs built from
   a list of numbers (`genProg`): arithmetic, `if`, `switch`, `pop`, `mstore`/`mload`, `break`.
   * the interpreter `exec`, with random fuel, either runs out of fuel or returns exactly what the
     metered evaluator returns (mirrors `exec_eq_execG`);
   * with enough fuel it never runs out (so the previous property is not vacuous). This is now a
     theorem, `genProg_fuel_adequate` (conjecture K10, proved via `exec_ne_OOF_of_fuel`); the
     property is kept as its executable mirror;
   * with exactly `fuelS` fuel the interpreter returns exactly the metered result (mirrors
     `exec_eq_execG_of_fuel`);
   * the metered gas is at most `gasS` (mirrors `execG_gas_le`);
   * on straight-line programs that end normally the metered gas equals `gasS` (mirrors
     `execG_gas_eq_of_ok`).
3. **Mutation tests**: Plausible must find a counterexample for a bound that forgets `if` bodies,
   a bound that takes the cheapest `switch` branch, "exactness" without the straight-line
   hypothesis, a differential test against a mutated program, and two mutants of the fuel measure
   (one ignoring nesting depth, one ignoring block length).
-/

namespace EvmYul.Yul.GasTests

open Plausible Plausible.Decorations EvmYul.Testing.EvmFixtures Ast Relational Gas

/-- Named unit checks; each must evaluate to `true`. -/
def unitChecks : List (String × Bool) :=
  [ ("cancun: ADD costs G_verylow = 3", cancun.prim .ADD == 3),
    ("cancun: MUL costs G_low = 5", cancun.prim .MUL == 5),
    ("cancun: ADDMOD costs G_mid = 8", cancun.prim .ADDMOD == 8),
    ("cancun: KECCAK256 floor is G_keccak256 = 30", cancun.prim .KECCAK256 == 30),
    ("cancun: SLOAD/SSTORE floor is G_warmaccess = 100",
      cancun.prim .SLOAD == 100 && cancun.prim .SSTORE == 100),
    ("cancun: CALL floor is G_warmaccess = 100", cancun.prim .CALL == 100),
    ("cancun: CREATE floor is G_create = 32000", cancun.prim .CREATE == 32000),
    ("cancun: STOP/RETURN/REVERT are free",
      cancun.prim .STOP == 0 && cancun.prim .RETURN == 0 && cancun.prim .REVERT == 0),
    ("cancun: a branch costs JUMPI + JUMPDEST = 11", cancun.branch == 11),
    ("allPrims lists 80 distinct builtins", allPrims.length == 80 && decide allPrims.Nodup),
    ("toEVM is injective on allPrims", decide (allPrims.map toEVM).Nodup),
    ("ofEVM inverts toEVM on allPrims", allPrims.all fun op => ofEVM (toEVM op) == some op),
    ("Yul price = EVM C' (EVM state with 8 zero stack words) for every static builtin",
      allPrims.all fun op => (yulFeeGroup op).staticCost?.isNone ||
        cancun.prim op == EVM.C' evmS (toEVM op)),
    ("Yul price <= EVM C' (EVM state with 8 zero stack words) for every builtin except SSTORE and
      SELFDESTRUCT (whose price reads an account that this state lacks; proved for all states by
      `cancun_prim_le_C'`)",
      (allPrims.filter (fun op => op != .SSTORE && op != .SELFDESTRUCT)).all fun op =>
        cancun.prim op ≤ EVM.C' evmS (toEVM op)),
    ("three ADDs: metered gas 9 = static bound", gasOf threeAdds == 9 && gasS cancun threeAdds == 9),
    ("three ADDs: v0 = 3", runMetered threeAdds == "ok [3, 0, 0, 0]"),
    ("guarded, taken: LT + branch + MUL = 3 + 11 + 5", gasOf (guarded 2) == 19),
    ("guarded, not taken: LT + branch = 3 + 11", gasOf (guarded 9) == 14),
    ("guarded: static bound 19 is attained by the taken branch",
      gasS cancun (guarded 9) == 19),
    ("for loops are outside the fragment", !fragS (.For (lit 1) [] [])),
    ("user function calls are outside the fragment",
      !fragS (.ExprStmtCall (.Call (.inr "f") []))),
    ("CALL is outside the fragment",
      !fragS (.ExprStmtCall (call .CALL [lit 0, lit 0, lit 0, lit 0, lit 0, lit 0, lit 0]))),
    ("generated programs are in the fragment", fragS (genProg false [1, 2] (List.range 40))),
    ("interpreter agrees on threeAdds", runExec 100 threeAdds == some (runMetered threeAdds)),
    ("fuel measure: a generated switch needs 12 (the bound of genStmt_safe_fuel is attained)",
      fuelS (genStmt false 3) == 12),
    ("fuel measure: threeAdds = deepest let (8) + one unit per statement (7)",
      fuelS threeAdds == 15),
    ("fuel measure grows with block length, not total size",
      fuelS (genProg false [] (List.range 100)) ≤ 117),
    ("generated programs use only builtins proved never to report OutOfFuel",
      safeS (genProg false [1, 2] (List.range 40))),
    ("CALLER is not (yet) in the proved-safe builtin list",
      !safeS (.ExprStmtCall (call .POP [call .CALLER []]))),
    ("interpreter with exactly fuelS fuel agrees on threeAdds",
      runExec (fuelS threeAdds) threeAdds == some (runMetered threeAdds))
  ]

/-- Run every check; throws on the first failure. -/
def runAll : IO Unit := do
  for (name, ok) in unitChecks do
    unless ok do throw <| IO.userError s!"unit check failed: {name}"
  IO.println s!"{unitChecks.length} unit checks passed"
  -- Mirrors `exec_eq_execG`.
  yHolds "exec (random fuel) runs out of fuel or returns the metered result"
    (∀ init ns : List ℕ, ∀ f : ℕ,
      CountedTesting.WhenSome (runExec (fuelAt f (enoughFuel ns)) (genProg false init ns))
        (· == runMetered (genProg false init ns)))
  -- Non-vacuity of the property above.
  yHolds "exec with enough fuel never runs out on generated programs"
    (∀ init ns : List ℕ, (runExec (enoughFuel ns) (genProg false init ns)).isSome)
  -- Mirrors `execG_gas_le`.
  yHolds "metered gas <= static bound"
    (∀ init ns : List ℕ, gasOf (genProg false init ns) ≤ gasS cancun (genProg false init ns))
  -- Mirrors `execG_gas_eq_of_ok`.
  yHolds "straight-line programs that end normally are charged exactly the static bound"
    (∀ init ns : List ℕ, endsOk (genProg true init ns) →
      gasOf (genProg true init ns) = gasS cancun (genProg true init ns))
  -- Non-vacuity of the exactness property.
  yHolds "straight-line programs without break end normally"
    (∀ init ns : List ℕ, endsOk (genProg true init (ns.map fun n => 9 * n + n % 8)))
  -- Mirrors `exec_eq_execG_of_fuel`: with exactly `fuelS` fuel the interpreter *is* the meter.
  yHolds "exec with fuelS fuel returns exactly the metered result"
    (∀ init ns : List ℕ, runExec (fuelS (genProg false init ns)) (genProg false init ns) ==
      some (runMetered (genProg false init ns)))
  IO.println "6 property suites passed"
  -- Mutation tests.
  yRefuted "mutant bound: forgets if bodies"
    (∀ init ns : List ℕ, gasOf (genProg false init ns) ≤ badGasS (genProg false init ns))
  yRefuted "mutant bound: cheapest switch branch"
    (∀ init ns : List ℕ, gasOf (genProg false init ns) ≤ minGasS (genProg false init ns))
  yRefuted "exactness without the straight-line hypothesis"
    (∀ init ns : List ℕ, endsOk (genProg false init ns) →
      gasOf (genProg false init ns) = gasS cancun (genProg false init ns))
  -- Mutants of the fuel measure: dropping either ingredient of `fuelS` is caught.
  yRefuted "mutant fuel: ignores nesting depth (statement count + 5)"
    (∀ init ns : List ℕ, (runExec (ns.length + 5) (genProg false init ns)).isSome)
  yRefuted "mutant fuel: ignores block length (constant 30)"
    (∀ init ns : List ℕ, (runExec 30 (genProg false init ns)).isSome)
  yRefuted "differential test against a mutated program (ADD -> SUB)"
    (∀ init ns : List ℕ,
      (runExec 1000 (genProg false init ns)).all (· == runMetered (mutateAdd (genProg false init ns))))

#eval runAll

end EvmYul.Yul.GasTests
