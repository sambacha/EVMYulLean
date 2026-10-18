module

public import EvmYul.Yul.Gas.NestedLoopsTestHarness
public meta import EvmYul.Yul.Gas.NestedLoopsTestHarness
public import EvmYul.Yul.Gas.Functions.Complete
public meta import EvmYul.Yul.Gas.Functions.Complete
@[expose] public meta section

/-!
# Test harness of `CompleteTests`

The definitions that `Functions/CompleteTests.lean` runs and that other test files reuse: generators,
observers, runners, mutants and the lemmas about them. They used to live in the test file itself,
which made other test files import a test file as a fixture library; `GUIDELINES.md` Rule 3 keeps
shared fixtures in a harness module instead (layout check L10). Every declaration keeps its name and
namespace.
-/

namespace EvmYul.Yul.GasTests.CompleteTests

open Plausible Ast Relational Gas LoopsTests
open EvmYul.Testing.EvmFixtures

/-- A call of a user-defined function. -/
def ucall (f : YulFunctionName) (args : List Expr) : Expr := .Call (.inr f) args

/-- `inc(x) -> r { r := add(x, 1) }`. -/
def fInc : FunctionDefinition := .Def ["x"] ["r"] [.Let ["r"] (some (call .ADD [.Var "x", lit 1]))]

/-- `twice(x) -> r { r := inc(inc(x)) }`. -/
def fTwice : FunctionDefinition :=
  .Def ["x"] ["r"] [.Let ["r"] (some (ucall "inc" [ucall "inc" [.Var "x"]]))]

/-- `fact(n) -> r { r := 1  if gt(n, 0) { r := mul(n, fact(sub(n, 1))) } }`. -/
def fFact : FunctionDefinition :=
  .Def ["n"] ["r"] [.Let ["r"] (some (lit 1)),
    .If (call .GT [.Var "n", lit 0])
      [.Let ["r"] (some (call .MUL [.Var "n", ucall "fact" [call .SUB [.Var "n", lit 1]]]))]]

/-- `sumTo(n) -> r { r := 0  let i := 0  for {} lt(i, n) { i := add(i, 1) } { r := add(r, i) } }`. -/
def fSum : FunctionDefinition :=
  .Def ["n"] ["r"] [.Let ["r"] (some (lit 0)), .Let ["i"] (some (lit 0)),
    .For (call .LT [.Var "i", .Var "n"]) [.Let ["i"] (some (call .ADD [.Var "i", lit 1]))]
      [.Let ["r"] (some (call .ADD [.Var "r", .Var "i"]))]]

/-- `even(n) -> r { r := 1  if gt(n, 0) { r := odd(sub(n, 1)) } }`. -/
def fEven : FunctionDefinition :=
  .Def ["n"] ["r"] [.Let ["r"] (some (lit 1)),
    .If (call .GT [.Var "n", lit 0]) [.Let ["r"] (some (ucall "odd" [call .SUB [.Var "n", lit 1]]))]]

/-- `odd(n) -> r { r := 0  if gt(n, 0) { r := even(sub(n, 1)) } }`. -/
def fOdd : FunctionDefinition :=
  .Def ["n"] ["r"] [.Let ["r"] (some (lit 0)),
    .If (call .GT [.Var "n", lit 0]) [.Let ["r"] (some (ucall "even" [call .SUB [.Var "n", lit 1]]))]]

/-- The functions of the test contract, as a list (the oracle in `OracleTests` rewrites
each body). -/
def fnListT : List (Σ _ : YulFunctionName, FunctionDefinition) :=
  [⟨"inc", fInc⟩, ⟨"twice", fTwice⟩, ⟨"fact", fFact⟩, ⟨"sumTo", fSum⟩, ⟨"even", fEven⟩,
   ⟨"odd", fOdd⟩]

/-- The test contract. -/
def codeT : YulContract := ⟨.Block [], List.toFinmap fnListT⟩

/-- The test contract's function table. -/
def tblT : FnTable := fun f => codeT.functions.lookup f

/-- A start state whose code owner has an account (the interpreter looks it up on every call). -/
def sF : State :=
  .Ok { (default : SharedState .Yul) with
        accountMap := Std.TreeMap.insert ∅ (default : AccountAddress) default } ∅

/-- Initialise `v0..v3` to `0`, then run `body`. -/
def withInit (body : List Stmt) : Stmt :=
  .Block (((List.range 4).map fun i => .Let [vr i] (some (lit 0))) ++ body)

/-- The metered run with budgets `n`, `d`, observed. -/
def mObsF (n d : ℕ) (p : Stmt) : Option (String × ℕ) :=
  (runF cancunFn (some codeT) n d p sF).map fun (r, g) => (obs r, g)

/-- The interpreter's observable result, `none` when it runs out of fuel. -/
def eObsF (fuel : ℕ) (p : Stmt) : Option String :=
  match exec fuel p (some codeT) sF with
  | .error .OutOfFuel => none
  | r => some (obs r)

/-! ## Generators -/

/-- Statement number `n`: a statement of `Gas/MeteredTests.lean` or a call of a function of `codeT`. -/
def genFStmt (straight : Bool) (n : ℕ) : Stmt :=
  let k := n / 13
  let a := vr k
  let b := vr (k / 4)
  match n % 13 with
  | 9 => .Let [a] (some (ucall "twice" [.Var b]))
  | 10 => .Let [a] (some (ucall "fact" [call .MOD [.Var b, lit 6]]))
  | 11 => .Let [a] (some (ucall "sumTo" [call .MOD [.Var b, lit 8]]))
  | 12 =>
    if k % 5 = 0 then .ExprStmtCall (ucall "nosuch" [.Var b])
    else .Let [a] (some (ucall "inc" [.Var a]))
  | r => genStmt straight (r + 9 * k)

/-- Program: initialise `v0..v3` from `init`, then the statements `ns`. -/
def genFProg (straight : Bool) (init ns : List ℕ) : Stmt :=
  .Block ((List.range 4).map (fun i => .Let [vr i] (some (lit (init.getD i i)))) ++
    ns.map (genFStmt straight))

/-- Statement number `n` of a straight-line program calling only `inc` and `twice`. -/
def genSStmt (n : ℕ) : Stmt :=
  let k := n / 11
  match n % 11 with
  | 9 => .Let [vr k] (some (ucall "twice" [.Var (vr (k / 4))]))
  | 10 => .Let [vr k] (some (ucall "inc" [.Var (vr k)]))
  | r => genStmt true (r + 9 * k)

/-- Straight-line program calling only `inc` and `twice` (`ns` should be break-free). -/
def genSProg (init ns : List ℕ) : Stmt :=
  .Block ((List.range 4).map (fun i => .Let [vr i] (some (lit (init.getD i i)))) ++
    ns.map genSStmt)

/-- Fuel that is enough for the generated programs. -/
def fnFuel (ns : List ℕ) : ℕ := 60 * ns.length + 400

/-- Mutant bound: the call overhead is charged by the meter but left out of the bound. -/
def noCallModel : FnCostModel := { cancunFn with call := 0 }

/-- Mutant callee bound: every callee charged as if it made no calls (`gasFn` at depth 1). -/
def flatBound (n : ℕ) (p : Stmt) : ℕ := gasFS cancunFn (gasFn cancunFn tblT n 1) n p

/-! ## Unit tests -/

/-- `let v0 := fact(k)`. -/
def pFact (k : ℕ) : Stmt := withInit [.Let [vr 0] (some (ucall "fact" [lit k]))]

/-- `let v0 := twice(3)`. -/
def pTwice : Stmt := withInit [.Let [vr 0] (some (ucall "twice" [lit 3]))]

/-- `let v0 := sumTo(4)`. -/
def pSum : Stmt := withInit [.Let [vr 0] (some (ucall "sumTo" [lit 4]))]

/-- `let v0 := even(4)`. -/
def pEven : Stmt := withInit [.Let [vr 0] (some (ucall "even" [lit 4]))]

/-- `nosuch(4)`. -/
def pMissing : Stmt := withInit [.ExprStmtCall (ucall "nosuch" [lit 4])]

/-- `for { } lt(i, 3) { i := add(i, 1) } { v0 := sumTo(v0) }` with `v0 := 3`, `i := 0`. -/
def pLoopCall : Stmt :=
  .Block [.Let [vr 0] (some (lit 3)), .Let [vr 1] (some (lit 0)), .Let [vr 2] (some (lit 0)),
    .Let [vr 3] (some (lit 0)), .Let [ctr] (some (lit 0)),
    .For (call .LT [.Var ctr, lit 3]) [.Let [ctr] (some (call .ADD [.Var ctr, lit 1]))]
      [.Let [vr 0] (some (ucall "sumTo" [.Var (vr 0)]))]]

end EvmYul.Yul.GasTests.CompleteTests
