module

public import EvmYul.Yul.Gas.MeteredTestHarness
public meta import EvmYul.Yul.Gas.MeteredTestHarness
public import EvmYul.Yul.Gas.Loops
public meta import EvmYul.Yul.Gas.Loops

@[expose] public meta section

/-!
# Test harness of `LoopsTests`

The definitions that `Gas/LoopsTests.lean` runs and that other test files reuse: generators, observers,
runners, mutants and the lemmas about them. They used to live in the test file itself, which made
other test files import a test file as a fixture library; `GUIDELINES.md` Rule 3 keeps shared
fixtures in a harness module instead (layout check L10). Every declaration keeps its name and
namespace.
-/

namespace EvmYul.Yul.GasTests.LoopsTests

open Plausible Ast Relational Gas
open EvmYul.Testing.EvmFixtures

/-- The loop counter. -/
def ctr : Identifier := "i"

/-- `let v0..v3` from `init`, then `let i := 0`. -/
def loopInit (init : List ℕ) : Stmt :=
  .Block (((List.range 4).map fun i => .Let [vr i] (some (lit (init.getD i i)))) ++
    [.Let [ctr] (some (lit 0))])

/-- The state after `loopInit`. -/
def startState (init : List ℕ) : State :=
  match (execG cancun (loopInit init) s0).1 with
  | .ok s => s
  | .error _ => s0

/-- `lt(i, k)`. -/
def lCond (k : ℕ) : Expr := call .LT [.Var ctr, lit k]

/-- `i := add(i, 1)`. -/
def lPost : List Stmt := [.Let [ctr] (some (call .ADD [.Var ctr, lit 1]))]

/-- The loop body: generated statements. -/
def lBody (straight : Bool) (ns : List ℕ) : List Stmt := ns.map (genStmt straight)

/-- Observable result: outcome kind, the four variables and the counter. -/
def obsL : Res → String
  | .ok (.Ok ss st) =>
    s!"ok {(List.range 4).map (fun i => (lookupVar (.Ok ss st) (vr i)).toNat)} \
      i={(lookupVar (.Ok ss st) ctr).toNat}"
  | r => obs r

/-- The metered loop with a budget of 1000 iterations. -/
def mLoop (k : ℕ) (straight : Bool) (init ns : List ℕ) : LoopOut :=
  loopG cancun 1000 (lCond k) lPost (lBody straight ns) (startState init)

/-- The interpreter on the loop, `none` when it runs out of fuel. -/
def eLoop (fuel k : ℕ) (straight : Bool) (init ns : List ℕ) : Option String :=
  match exec fuel (.For (lCond k) lPost (lBody straight ns)) none (startState init) with
  | .error .OutOfFuel => none
  | r => some (obsL r)

/-- Static gas of one iteration and of the exit test, for the test loops. -/
def iterG (k : ℕ) (straight : Bool) (ns : List ℕ) : ℕ :=
  loopIterGas cancun (lCond k) lPost (lBody straight ns)

/-- Static gas of the exit test. -/
def exitG (k : ℕ) : ℕ := loopExitGas cancun (lCond k)

/-- Fuel that is enough for the test loops (`k < 12` iterations). -/
def loopFuel (ns : List ℕ) : ℕ := 4 * ns.length + 150

/-- Statement numbers that `genStmt` never turns into `break`. -/
def noBreak (ns : List ℕ) : List ℕ := ns.map fun n => 9 * n + n % 8

/-- `for {} lt(i, 10) { i := add(i, 1) } { v0 := add(v0, 2) }`. -/
def tenLoop : Stmt × LoopOut :=
  let body := [.Let [vr 0] (some (call .ADD [.Var (vr 0), lit 2]))]
  (.For (lCond 10) lPost body, loopG cancun 1000 (lCond 10) lPost body (startState [0, 0, 0, 0]))

/-- A loop whose body breaks at once. -/
def breakLoop : LoopOut := loopG cancun 1000 (lCond 10) lPost [.Break] (startState [])

/-- A loop whose condition is the literal `0`. -/
def zeroLoop : LoopOut := loopG cancun 1000 (lit 0) lPost [.Break] (startState [])

end EvmYul.Yul.GasTests.LoopsTests
