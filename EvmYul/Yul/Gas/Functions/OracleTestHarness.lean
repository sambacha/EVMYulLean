module

public import EvmYul.Yul.Gas.Functions.CompleteTestHarness
public meta import EvmYul.Yul.Gas.Functions.CompleteTestHarness
@[expose] public meta section

/-!
# Test harness of `OracleTests`

The definitions that `Functions/OracleTests.lean` runs and that other test files reuse: generators,
observers, runners, mutants and the lemmas about them. They used to live in the test file itself,
which made other test files import a test file as a fixture library; `GUIDELINES.md` Rule 3 keeps
shared fixtures in a harness module instead (layout check L10). Every declaration keeps its name and
namespace.
-/

namespace EvmYul.Yul.GasTests.OracleTests

open Plausible Ast Relational Gas CompleteTests
open EvmYul.Testing.EvmFixtures

/-! ## The rewrite -/

/-- `tstore(0, add(tload(0), k))`: add `k` to the counter. -/
def tick (k : ℕ) : Stmt := .ExprStmtCall (call .TSTORE [lit 0, call .ADD [call .TLOAD [lit 0], lit k]])

/-- Name of the wrapper of `prim` with `n` arguments; `void` for statement position (no result).
The `__` prefix keeps them apart from the contract's own functions (checked below). -/
def wrapName (void : Bool) (prim : PrimOp) (n : ℕ) : YulFunctionName :=
  s!"__{if void then "v" else "p"}{n}_{reprStr prim}"

/-- Name of the branch wrapper. -/
def brName : YulFunctionName := "__branch"

mutual

/-- Rewrite an expression: builtins go through their counting wrappers. -/
def instrE : Expr → Expr
  | .Lit v => .Lit v
  | .Var x => .Var x
  | .Call (.inl prim) args => .Call (.inr (wrapName false prim args.length)) (instrArgs args)
  | .Call (.inr f) args => .Call (.inr f) (instrArgs args)

/-- Rewrite an argument list. -/
def instrArgs : List Expr → List Expr
  | [] => []
  | a :: as => instrE a :: instrArgs as

end

mutual

/-- Rewrite a statement: builtins through wrappers, conditions through `__branch`. -/
def instrS : Stmt → Stmt
  | .Block sts => .Block (instrB sts)
  | .Let vars none => .Let vars none
  | .Let vars (some e) => .Let vars (some (instrE e))
  | .ExprStmtCall (.Call (.inl prim) args) =>
    .ExprStmtCall (.Call (.inr (wrapName true prim args.length)) (instrArgs args))
  | .ExprStmtCall e => .ExprStmtCall (instrE e)
  | .If cond body => .If (.Call (.inr brName) [instrE cond]) (instrB body)
  | .Switch cond cases dflt =>
    .Switch (.Call (.inr brName) [instrE cond]) (instrCases cases) (instrB dflt)
  | .For cond post body => .For (.Call (.inr brName) [instrE cond]) (instrB post) (instrB body)
  | .Continue => .Continue
  | .Break => .Break
  | .Leave => .Leave

/-- Rewrite a block. -/
def instrB : List Stmt → List Stmt
  | [] => []
  | st :: sts => instrS st :: instrB sts

/-- Rewrite the bodies of `switch` cases. -/
def instrCases : List (Ast.Literal × List Stmt) → List (Ast.Literal × List Stmt)
  | [] => []
  | (l, body) :: rest => (l, instrB body) :: instrCases rest

end

mutual

/-- The builtin calls of an expression, as `(void, prim, arity)`. -/
def primsE : Expr → List (Bool × PrimOp × ℕ)
  | .Lit _ => []
  | .Var _ => []
  | .Call (.inl prim) args => (false, prim, args.length) :: primsArgs args
  | .Call (.inr _) args => primsArgs args

/-- The builtin calls of an argument list. -/
def primsArgs : List Expr → List (Bool × PrimOp × ℕ)
  | [] => []
  | a :: as => primsE a ++ primsArgs as

end

mutual

/-- The builtin calls of a statement (statement-position calls are `void`). -/
def primsS : Stmt → List (Bool × PrimOp × ℕ)
  | .Block sts => primsB sts
  | .Let _ none => []
  | .Let _ (some e) => primsE e
  | .ExprStmtCall (.Call (.inl prim) args) => (true, prim, args.length) :: primsArgs args
  | .ExprStmtCall e => primsE e
  | .If cond body => primsE cond ++ primsB body
  | .Switch cond cases dflt => primsE cond ++ primsCases cases ++ primsB dflt
  | .For cond post body => primsE cond ++ primsB post ++ primsB body
  | .Continue | .Break | .Leave => []

/-- The builtin calls of a block. -/
def primsB : List Stmt → List (Bool × PrimOp × ℕ)
  | [] => []
  | st :: sts => primsS st ++ primsB sts

/-- The builtin calls of `switch` cases. -/
def primsCases : List (Ast.Literal × List Stmt) → List (Bool × PrimOp × ℕ)
  | [] => []
  | (_, body) :: rest => primsB body ++ primsCases rest

end

/-- Parameter names `a0, …, a(n-1)` of a wrapper. -/
def params (n : ℕ) : List Identifier := (List.range n).map fun i => s!"a{i}"

/-- The counting wrapper of `prim` with `n` arguments: tick `c.prim prim`, then perform `prim`. -/
def wrapper (c : FnCostModel) : Bool × PrimOp × ℕ → Σ _ : YulFunctionName, FunctionDefinition
  | (true, prim, n) =>
    ⟨wrapName true prim n, .Def (params n) []
      [tick (c.prim prim), .ExprStmtCall (call prim ((params n).map .Var))]⟩
  | (false, prim, n) =>
    ⟨wrapName false prim n, .Def (params n) ["r"]
      [tick (c.prim prim), .Let ["r"] (some (call prim ((params n).map .Var)))]⟩

/-- `__branch(x) -> y { tick(c.branch)  y := x }`. -/
def branchFn (c : FnCostModel) : Σ _ : YulFunctionName, FunctionDefinition :=
  ⟨brName, .Def ["x"] ["y"] [tick c.branch, .Let ["y"] (some (.Var "x"))]⟩

/-- A user function, rewritten; `callTick := false` is the oracle mutant that forgets the call
overhead. -/
def instrFn (c : FnCostModel) (callTick : Bool) :
    (Σ _ : YulFunctionName, FunctionDefinition) → Σ _ : YulFunctionName, FunctionDefinition
  | ⟨f, .Def ps rs body⟩ =>
    ⟨f, .Def ps rs ((if callTick then [tick c.call] else []) ++ instrB body)⟩

/-- The body of a function definition. -/
def fnBody : FunctionDefinition → List Stmt
  | .Def _ _ b => b

/-- The rewritten contract for program `p` and functions `fns`: the rewritten functions, one
wrapper per builtin use, and `__branch`. -/
def instrContract (c : FnCostModel) (callTick : Bool)
    (fns : List (Σ _ : YulFunctionName, FunctionDefinition)) (p : Stmt) : YulContract :=
  let uses := (primsS p ++ (fns.map fun fd => primsB (fnBody fd.2)).flatten).eraseDups
  ⟨.Block [], List.toFinmap (fns.map (instrFn c callTick) ++ uses.map (wrapper c) ++ [branchFn c])⟩

/-! ## Running the oracle -/

/-- The start state of `CompleteTests` with write permission, so that `tstore` is allowed (the
original programs use no permission-restricted builtin, so this changes nothing else). -/
def sW : State :=
  match sF with
  | .Ok ss vs => .Ok { ss with executionEnv := { ss.executionEnv with perm := true } } vs
  | s => s

/-- The counter of a final state. -/
def counter? : State → Option ℕ
  | .Ok ss _ => some (ss.toState.tload ⟨0⟩).2.toNat
  | .Checkpoint (.Break ss _) => some (ss.toState.tload ⟨0⟩).2.toNat
  | .Checkpoint (.Continue ss _) => some (ss.toState.tload ⟨0⟩).2.toNat
  | .Checkpoint (.Leave ss _) => some (ss.toState.tload ⟨0⟩).2.toNat
  | .OutOfFuel => none

/-- **The oracle**: run the self-counting program on the reference interpreter. `some (obs, gas)`
when the interpreter returns a state; `none` on an error or when it runs out of fuel. -/
def oracle (c : FnCostModel) (callTick : Bool) (fuel : ℕ) (p : Stmt) : Option (String × ℕ) :=
  match exec fuel (instrS p) (some (instrContract c callTick fnListT p)) sW with
  | .ok s => (counter? s).map fun g => (obs (.ok s), g)
  | .error _ => none

/-- Fuel for the rewritten programs (every builtin is now a call, so far more than `fnFuel`). -/
def oFuel (ns : List ℕ) : ℕ := 20 * fnFuel ns

/-- The meter's observation and gas, budgets `(8, 7)` (enough for the generator). -/
def meter (c : FnCostModel) (p : Stmt) : Option (String × ℕ) :=
  (runF c (some codeT) 8 7 p sF).map fun (r, g) => (obs r, g)

/-! ## Mutants -/

/-- Mutant meter: a callee's own calls are charged only the call price, not their bodies (the
gas of nested callees is dropped). -/
def callFlat (c : FnCostModel) (co : Option YulContract) (n : ℕ) : ℕ → Runner
  | 0 => fun _ _ _ => none
  | d + 1 => fun args f s =>
    match lookupFunction (some f) co s with
    | .error e => some (.error e, 0)
    | .ok fd =>
      let inner : Runner := fun a g s' => (callF c co n d a g s').map fun (r, _) => (r, 0)
      match blockF c inner n fd.body (State.mkOk (s.initcall fd.params args)) with
      | none => none
      | some (r, g) => some (callPost s fd r, g)

/-- The mutant meter's observation and gas. -/
def meterFlat (p : Stmt) : Option (String × ℕ) :=
  (execF cancunFn (callFlat cancunFn (some codeT) 8 7) 8 p sF).map fun (r, g) => (obs r, g)

/-- Mutant cost model: the call price one lower. -/
def cheapCall : FnCostModel := { cancunFn with call := cancunFn.call - 1 }

/-- Mutant cost model: the branch price one lower (branches inside callees included). -/
def cheapBranch : FnCostModel := { cancunFn with branch := cancunFn.branch - 1 }

/-! ## 3. Deterministic sweep -/

/-- A deterministic corpus of `count` programs with calls: a linear congruential stream of
statement numbers, lengths 1–24, initial values near 0 and near `2^256`. -/
def corpus (count : ℕ) : List (List ℕ × List ℕ) :=
  (List.range count).map fun i =>
    let x := (1103515245 * (i + 7) + 12345) % 2147483648
    let len := x % 24 + 1
    let ns := (List.range len).map fun j => (x / (j + 1) + 31 * j * i) % 600
    let init := [if i % 3 = 0 then UInt256.size - 1 - i % 5 else i % 7, x % 11, i, 0]
    (init, ns)

end EvmYul.Yul.GasTests.OracleTests
