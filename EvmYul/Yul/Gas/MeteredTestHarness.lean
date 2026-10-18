module

public import EvmYul.Testing.EvmFixtures
public meta import EvmYul.Testing.EvmFixtures
public import EvmYul.Yul.ExecLemmas
public meta import EvmYul.Yul.ExecLemmas
public import EvmYul.Yul.Gas.MeteredSound
public meta import EvmYul.Yul.Gas.MeteredSound
public import EvmYul.Yul.Gas.FuelAdequacy
public meta import EvmYul.Yul.Gas.FuelAdequacy
public import EvmYul.Testing.Counted
public meta import EvmYul.Testing.Counted
@[expose] public meta section

/-!
# Test harness of `MeteredTests`

The definitions that `MeteredTests.lean` runs and that other test files reuse: generators,
observers, runners, mutants and the lemmas about them. They used to live in the test file itself,
which made other test files import a test file as a fixture library; `GUIDELINES.md` Rule 3 keeps
shared fixtures in a harness module instead (layout check L10). Every declaration keeps its name and
namespace.
-/

namespace EvmYul.Yul.GasTests

open Plausible Plausible.Decorations EvmYul.Testing.EvmFixtures Ast Relational Gas

/-- Fewer, smaller inputs than the EVM suite: every input runs the interpreter. -/
def ycfg : Configuration := { numInst := 200, maxSize := 40, randomSeed := some 20261007,
                              quiet := true }

/-- Random fuel for a program that provably needs at most `need` fuel. Plausible draws `f` from
`[0, size]` with `size ≤ ycfg.maxSize`, so `f % c` for a constant `c ≥ maxSize` is just `f`: the
random-fuel laws used to run with fuel `≤ 40`, where most generated programs run out of fuel (the
counted runner showed 84–96 % of inputs discarded). Scaling spreads the fuel over `[0, 2 · need]`,
so both sides of the out-of-fuel threshold are sampled. -/
def fuelAt (f need : ℕ) : ℕ := f * (2 * need) / ycfg.maxSize

/-- Fail the build on a counterexample, or when fewer than `minValid` inputs (default: half of the
samples) satisfied the property's guards; print `total/valid/discarded` (`CountedTesting`). -/
def yHolds (name : String) (p : Prop)
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p']
    (minValid : Nat := CountedTesting.defaultMinValid ycfg) : IO Unit :=
  discard <| CountedTesting.holdsCore ycfg name p' minValid

/-- Mutation test: fail the build unless a counterexample is found (counts printed). -/
def yRefuted (name : String) (p : Prop)
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] : IO Unit :=
  discard <| CountedTesting.refutedCore ycfg name p'

/-! ## Program generator -/

/-- One of four variables. -/
def vr (k : ℕ) : Identifier := s!"v{k % 4}"

/-- A literal. -/
def lit (n : ℕ) : Expr := .Lit (UInt256.ofNat n)

/-- A builtin call. -/
def call (op : PrimOp) (args : List Expr) : Expr := .Call (.inl op) args

/-- Statement number `n`; `straight := true` replaces `if`/`switch` by assignments. -/
def genStmt (straight : Bool) (n : ℕ) : Stmt :=
  let k := n / 9
  let a := vr k
  let b := vr (k / 4)
  let m := k % 13
  match n % 9 with
  | 0 => .Let [a] (some (call .ADD [.Var b, lit m]))
  | 1 => .Let [a] (some (call .MUL [.Var b, .Var a]))
  | 2 =>
    if straight then .Let [a] (some (call .SUB [.Var b, lit m])) else
    .If (call .LT [.Var b, lit m]) [.Let [a] (some (call .ADD [.Var a, lit 1]))]
  | 3 =>
    if straight then .Let [a] (some (call .EXP [.Var b, lit 2])) else
    .Switch (call .MOD [.Var b, lit 3])
      [(⟨0⟩, [.Let [a] (some (lit m))]),
       (⟨1⟩, [.Let [a] (some (call .EXP [.Var b, lit 2])), .Let [b] (some (call .NOT [.Var a]))])]
      [.Let [a] (some (call .NOT [.Var a]))]
  | 4 => .Let [a] (some (call .ISZERO [.Var b]))
  | 5 => .ExprStmtCall (call .POP [.Var b])
  | 6 => .ExprStmtCall (call .MSTORE [lit (32 * m), .Var b])
  | 7 => .Let [a] (some (call .MLOAD [lit (32 * (m % 4))]))
  | _ => if m = 0 then .Break else .Let [a] (some (call .AND [.Var a, .Var b]))

/-- The program: initialise `v0..v3` from `init`, then the statements `ns`. -/
def genProg (straight : Bool) (init ns : List ℕ) : Stmt :=
  .Block ((List.range 4).map (fun i => .Let [vr i] (some (lit (init.getD i i)))) ++
    ns.map (genStmt straight))

/-- The initial state used by the tests. -/
def s0 : State := .Ok default ∅

/-- What a test observes of a result: the outcome kind and the four variables. -/
def obs : Res → String
  | .ok (.Ok ss st) => s!"ok {(List.range 4).map (fun i => (lookupVar (.Ok ss st) (vr i)).toNat)}"
  | .ok (.Checkpoint _) => "jump"
  | .ok .OutOfFuel => "oof-state"
  | .error .OutOfFuel => "out of fuel"
  | .error _ => "error"

/-- The interpreter's observable result, `none` when it runs out of fuel. -/
def runExec (fuel : ℕ) (p : Stmt) : Option String :=
  match exec fuel p none s0 with
  | .error .OutOfFuel => none
  | r => some (obs r)

/-- The metered evaluator's observable result. -/
def runMetered (p : Stmt) : String := obs (execG cancun p s0).1

/-- Metered gas under the Cancun model. -/
def gasOf (p : Stmt) : ℕ := (execG cancun p s0).2

/-- Did the run end normally? -/
def endsOk (p : Stmt) : Bool :=
  match (execG cancun p s0).1 with
  | .ok (.Ok _ _) => true
  | _ => false

/-- Fuel that is always enough for `genProg _ _ ns` (see the non-vacuity property). -/
def enoughFuel (ns : List ℕ) : ℕ := 4 * ns.length + 50

/-! ## K10 for the generator, proved

`exec_ne_OOF_of_fuel` (`FuelAdequacy.lean`) holds for every safe fragment program. Here it is
instantiated for the generator: every generated statement is safe and needs at most 12 fuel, so a
generated program of `|ns|` statements needs at most `|ns| + 17 ≤ enoughFuel ns`. -/

theorem genStmt_safe_fuel (straight : Bool) (n : ℕ) :
    safeS (genStmt straight n) = true ∧ fuelS (genStmt straight n) ≤ 12 := by
  unfold genStmt
  dsimp only
  split <;> (try split) <;>
    simp [safeS, safeE, safeArgs, safeB, safeCases, fuelS, fuelE, maxFuelE, fuelB, fuelCases,
      oofFreePrims, call, lit]

theorem genProg_safe_fuel (straight : Bool) (init ns : List ℕ) :
    safeS (genProg straight init ns) = true ∧ fuelS (genProg straight init ns) ≤ ns.length + 17 := by
  have hmem : ∀ st ∈ (List.range 4).map (fun i => Stmt.Let [vr i] (some (lit (init.getD i i)))) ++
      ns.map (genStmt straight), safeS st = true ∧ fuelS st ≤ 12 := by
    intro st hst
    rcases List.mem_append.mp hst with h | h
    · obtain ⟨i, -, rfl⟩ := List.mem_map.mp h
      simp [safeS, safeE, fuelS, fuelE, lit]
    · obtain ⟨n, -, rfl⟩ := List.mem_map.mp h
      exact genStmt_safe_fuel straight n
  refine ⟨safeB_of_forall _ (fun st h => (hmem st h).1), ?_⟩
  have := fuelB_le_of_forall 12 _ (fun st h => (hmem st h).2)
  simp only [genProg, fuelS]
  simp only [List.length_append, List.length_map, List.length_range] at this
  omega

/-- **K10 (proved).** On every generated program, the interpreter with `enoughFuel ns` fuel never
runs out of fuel, from any start state and for any code override. -/
theorem genProg_fuel_adequate (straight : Bool) (init ns : List ℕ) (co : Option YulContract)
    (s : State) : exec (enoughFuel ns) (genProg straight init ns) co s ≠ OOF := by
  obtain ⟨hs, hf⟩ := genProg_safe_fuel straight init ns
  exact exec_ne_OOF_of_fuel hs (by unfold enoughFuel; omega)

/-! ## Mutants -/

mutual
/-- Mutant bound: forgets the body of an `if`. -/
def badGasS : Stmt → ℕ
  | .Block sts => badGasB sts
  | .If cond _ => gasE cancun cond + cancun.branch
  | st => gasS cancun st
/-- Blocks for `badGasS`. -/
def badGasB : List Stmt → ℕ
  | [] => 0
  | st :: sts => badGasS st + badGasB sts
end

mutual
/-- Mutant bound: the cheapest `switch` branch instead of the most expensive one. -/
def minGasS : Stmt → ℕ
  | .Block sts => minGasB sts
  | .Switch cond cases dflt =>
    gasE cancun cond + cancun.branch + min (gasB cancun dflt) (minCases cases)
  | st => gasS cancun st
/-- Blocks for `minGasS`. -/
def minGasB : List Stmt → ℕ
  | [] => 0
  | st :: sts => minGasS st + minGasB sts
/-- The cheapest case body. -/
def minCases : List (Literal × List Stmt) → ℕ
  | [] => 0
  | [(_, body)] => gasB cancun body
  | (_, body) :: rest => min (gasB cancun body) (minCases rest)
end

/-- Mutated program: every `ADD` becomes `SUB`. -/
def mutateAdd : Stmt → Stmt
  | .Block sts => .Block (sts.map fun
      | .Let vs (some (.Call (.inl .ADD) args)) => .Let vs (some (.Call (.inl .SUB) args))
      | st => st)
  | st => st

/-! ## Unit checks -/

/-- Every Yul builtin, once. -/
def allPrims : List PrimOp :=
  [.StopArith .STOP, .StopArith .ADD, .StopArith .MUL, .StopArith .SUB, .StopArith .DIV,
   .StopArith .SDIV, .StopArith .MOD, .StopArith .SMOD, .StopArith .ADDMOD, .StopArith .MULMOD,
   .StopArith .EXP, .StopArith .SIGNEXTEND, .CompBit .LT, .CompBit .GT, .CompBit .SLT,
   .CompBit .SGT, .CompBit .EQ, .CompBit .ISZERO, .CompBit .AND, .CompBit .OR, .CompBit .XOR,
   .CompBit .NOT, .CompBit .BYTE, .CompBit .SHL, .CompBit .SHR, .CompBit .SAR,
   .Keccak .KECCAK256, .Env .ADDRESS, .Env .BALANCE, .Env .ORIGIN, .Env .CALLER,
   .Env .CALLVALUE, .Env .CALLDATALOAD, .Env .CALLDATASIZE, .Env .CALLDATACOPY, .Env .GASPRICE,
   .Env .CODESIZE, .Env .CODECOPY, .Env .EXTCODESIZE, .Env .EXTCODECOPY, .Env .RETURNDATASIZE,
   .Env .RETURNDATACOPY, .Env .EXTCODEHASH, .Block .BLOCKHASH, .Block .COINBASE,
   .Block .TIMESTAMP, .Block .NUMBER, .Block .PREVRANDAO, .Block .GASLIMIT, .Block .CHAINID,
   .Block .SELFBALANCE, .Block .BASEFEE, .Block .BLOBHASH, .Block .BLOBBASEFEE,
   .StackMemFlow .POP, .StackMemFlow .MLOAD, .StackMemFlow .MSTORE, .StackMemFlow .SLOAD,
   .StackMemFlow .SSTORE, .StackMemFlow .MSTORE8, .StackMemFlow .MSIZE, .StackMemFlow .GAS,
   .StackMemFlow .TLOAD, .StackMemFlow .TSTORE, .StackMemFlow .MCOPY, .Log .LOG0, .Log .LOG1,
   .Log .LOG2, .Log .LOG3, .Log .LOG4, .System .CREATE, .System .CALL, .System .CALLCODE,
   .System .RETURN, .System .DELEGATECALL, .System .CREATE2, .System .STATICCALL, .System .REVERT,
   .System .INVALID, .System .SELFDESTRUCT]

/-- An EVM state with eight zero stack words, so that `C'` can read every operand it needs. -/
def evmS : EVM.State := { (default : EVM.State) with stack := List.replicate 8 ⟨0⟩ }

/-- `v0 := add(v0, 1)` three times after `let v0..v3`: three `ADD`s at `G_verylow = 3`. -/
def threeAdds : Stmt :=
  .Block ((List.range 4).map (fun i => .Let [vr i] (some (lit 0))) ++
    List.replicate 3 (.Let [vr 0] (some (call .ADD [.Var (vr 0), lit 1]))))

/-- `if lt(x, 5) { x := mul(x, x) }` after `let x := x0`. -/
def guarded (x0 : ℕ) : Stmt :=
  .Block [.Let ["x"] (some (lit x0)),
    .If (call .LT [.Var "x", lit 5]) [.Let ["x"] (some (call .MUL [.Var "x", .Var "x"]))]]

end EvmYul.Yul.GasTests
