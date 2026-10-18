module

public import EvmYul.Yul.Relational.PrimCallK

public section

/-!
# Relational (big-step, fuel-free) semantics of Yul

The executable Yul interpreter (`EvmYul/Yul/Interpreter.lean`) is a family of mutually recursive
functions that all take a `fuel` argument and return `.error .OutOfFuel` when it runs out. Every
user-facing theorem stated directly against it has to quantify over fuel (critique CE-1).

This file defines an inductive, fuel-free semantics with one relation per interpreter function:

| relation      | interpreter function            | meaning                                        |
|---------------|---------------------------------|------------------------------------------------|
| `ArgsR`       | `evalArgs` / `evalTail`         | evaluate a list of argument expressions        |
| `CallR`       | `call`                          | call a user-defined Yul function               |
| `DispatchR`   | `callDispatcher`                | run the dispatcher of a called contract        |
| `PrimR`       | `primCall`                      | run a builtin (including the CALL family)      |
| `EvalR`       | `eval`                          | evaluate an expression                         |
| `ExecR`       | `exec`                          | execute a statement                            |
| `LoopR`       | `loop`                          | execute a `for` loop                           |

Each constructor is one non-fuel branch of the interpreter, with every recursive call replaced by a
premise. `Eval` (= `ExecR`) is the user-facing name. `EvmYul/Yul/Relational/Soundness.lean` proves
that the interpreter is sound with respect to these relations: whenever `exec fuel stmt co s`
returns a result other than `.error .OutOfFuel`, `ExecR co stmt s` relates `s` to that result.

## Builtins and external calls

`primCall` is the only place where one contract calls another (CALL, STATICCALL, CALLCODE,
DELEGATECALL run the callee's dispatcher). `PrimR.mk` uses the fuel-free `primCallK` with a
dispatcher `k` that is *correct with respect to `DispatchR`* at every input, up to running out of
fuel (`DispatchOrOOF`); the result itself is required not to be `.error .OutOfFuel`. Because
`primCallK` passes an `OutOfFuel` error of `k` straight through, such a result can only come from
`k` calls that were themselves related by `DispatchR`.

## `switch`: a faithful quirk

The interpreter evaluates **every** case body and the default block before selecting one, and an
error raised by the *default block* aborts the whole `switch` even when a case matched. `ExecR`
follows the interpreter (`ExecR.switchDefaultErr`); see `switch_default_error_aborts` in
`EvmYul/Yul/Relational/Examples.lean` for a concrete program where this differs from the Yul
specification. Errors and fuel exhaustion inside non-selected case bodies are discarded by the
interpreter, so the relation does not mention those bodies at all.
-/

namespace EvmYul
namespace Yul
namespace Relational

open Ast

/-- Results of executing a statement. -/
@[expose] abbrev Res := Except Yul.Exception State
/-- Results of evaluating an expression. -/
@[expose] abbrev ResV := Except Yul.Exception (State × Literal)
/-- Results of evaluating a list of expressions, or of a call. -/
@[expose] abbrev ResL := Except Yul.Exception (State × List Literal)

/-- The first case body whose label is `c`, if any (what `switch` selects). -/
@[expose] def selectCase (c : Literal) : List (Literal × List Stmt) → Option (List Stmt)
  | [] => none
  | (v, body) :: cases => if v = c then some body else selectCase c cases

/-- Look up the function a user-level call refers to (the non-recursive part of `call`). -/
@[expose] def lookupFunction (fname : Option YulFunctionName) (co : Option YulContract) (s : State) :
    Except Yul.Exception FunctionDefinition :=
  match s.sharedState.accountMap.get? s.executionEnv.codeOwner with
  | .none => .error (.MissingContract (s!"{s.executionEnv.codeOwner}"))
  | .some yulContract =>
    let code : YulContract := co.getD yulContract.code
    let fOpt : Option FunctionDefinition :=
      match fname with
        | .none => .some (FunctionDefinition.Def [] [] [code.dispatcher])
        | .some yulFunctionName => code.functions.lookup yulFunctionName
    match fOpt with
    | .none => .error (.MissingContractFunction (fname.getD ".none"))
    | .some f => .ok f

/-- What `call` / `callDispatcher` do with the result of running the function body. -/
@[expose] def callPost (s : State) (f : FunctionDefinition) : Res → ResL
  | .error e => .error e
  | .ok s₂ => .ok (s₂.reviveJump.overwrite? s |>.setStore s, List.map s₂.lookup! f.rets)

/-- The function definition `callDispatcher` runs. -/
@[expose] def dispatcherFunction (s : State) : FunctionDefinition :=
  FunctionDefinition.Def [] [] [s.executionEnv.code.dispatcher]

/-- The selection `switch` makes among the evaluated branches (the `foldr` in `exec`). -/
@[expose] def selectBranch (cond : Literal) (dflt : Res) (branches : List (Literal × Res)) : Res :=
  List.foldr (λ (valᵢ, sᵢ) s ↦ if valᵢ = cond then sᵢ else s) dflt branches

/-- After running a loop body, the loop goes on (to `post` and the next iteration) exactly when the
body ended normally or with `continue`. -/
@[expose] def continuesLoop : State → Prop
  | .Ok _ _ => True
  | .Checkpoint (.Continue _ _) => True
  | _ => False

mutual

/-- `ArgsR co args s r`: evaluating the expressions `args` left to right from `s` gives `r`. -/
inductive ArgsR : Option YulContract → List Expr → State → ResL → Prop
  | nil {co : Option YulContract} (s : State) : ArgsR co [] s (.ok (s, []))
  | consErr {co : Option YulContract} {a : Expr} {as : List Expr} {s : State} {e : Yul.Exception} :
      EvalR co a s (.error e) → ArgsR co (a :: as) s (.error e)
  | cons {co : Option YulContract} {a : Expr} {as : List Expr} {s s₁ : State} {v : Literal} {r : ResL} :
      EvalR co a s (.ok (s₁, v)) → ArgsR co as s₁ r → ArgsR co (a :: as) s (cons' v r)

/-- `CallR co args fname s r`: calling the user function `fname` (the dispatcher if `none`) with
arguments `args` from `s` gives `r`. -/
inductive CallR :
    Option YulContract → List Literal → Option YulFunctionName → State → ResL → Prop
  | lookupErr {co : Option YulContract} {args : List Literal} {fname : Option YulFunctionName} {s : State}
      {e : Yul.Exception} :
      lookupFunction fname co s = .error e → CallR co args fname s (.error e)
  | body {co : Option YulContract} {args : List Literal} {fname : Option YulFunctionName} {s : State}
      {f : FunctionDefinition} {r : Res} :
      lookupFunction fname co s = .ok f →
      ExecR co (.Block f.body) (State.mkOk (s.initcall f.params args)) r →
      CallR co args fname s (callPost s f r)

/-- `DispatchR co s r`: running the dispatcher of the contract in `s.executionEnv.code` gives `r`. -/
inductive DispatchR : Option YulContract → State → ResL → Prop
  | mk {co : Option YulContract} {s : State} {r : Res} :
      ExecR co (.Block (dispatcherFunction s).body)
        (State.mkOk (s.initcall (dispatcherFunction s).params [])) r →
      DispatchR co s (callPost s (dispatcherFunction s) r)

/-- `DispatchR`, or running out of fuel. -/
inductive DispatchOrOOF : Option YulContract → State → ResL → Prop
  | ofDispatch {co : Option YulContract} {s : State} {r : ResL} :
      DispatchR co s r → DispatchOrOOF co s r
  | outOfFuel (co : Option YulContract) (s : State) : DispatchOrOOF co s (.error .OutOfFuel)

/-- `PrimR s prim args r`: the builtin `prim` applied to `args` in `s` gives `r`. -/
inductive PrimR : State → PrimOp → List Literal → ResL → Prop
  | mk {s : State} {prim : PrimOp} {args : List Literal}
      (k : Option YulContract → State → ResL) :
      (∀ co s', DispatchOrOOF co s' (k co s')) →
      primCallK k s prim args ≠ .error .OutOfFuel →
      PrimR s prim args (primCallK k s prim args)

/-- `EvalR co e s r`: evaluating expression `e` from `s` gives `r`. -/
inductive EvalR : Option YulContract → Expr → State → ResV → Prop
  | lit {co : Option YulContract} (v : Literal) (s : State) : EvalR co (.Lit v) s (.ok (s, v))
  | var {co : Option YulContract} (x : Identifier) (s : State) : EvalR co (.Var x) s (.ok (s, s[x]!))
  | primArgsErr {co : Option YulContract} {prim : PrimOp} {args : List Expr} {s : State} {e : Yul.Exception} :
      ArgsR co args.reverse s (.error e) → EvalR co (.Call (.inl prim) args) s (.error e)
  | prim {co : Option YulContract} {prim : PrimOp} {args : List Expr} {s s₁ : State} {vs : List Literal} {r : ResL} :
      ArgsR co args.reverse s (.ok (s₁, vs)) → PrimR s₁ prim vs.reverse r →
      EvalR co (.Call (.inl prim) args) s (head' r)
  | builtin {co : Option YulContract} {f : YulFunctionName} {args : List Expr} {s : State} {r : ResV} :
      evalObjectDataBuiltin? f args s = some r → EvalR co (.Call (.inr f) args) s r
  | callArgsErr {co : Option YulContract} {f : YulFunctionName} {args : List Expr} {s : State} {e : Yul.Exception} :
      evalObjectDataBuiltin? f args s = none →
      ArgsR co args.reverse s (.error e) → EvalR co (.Call (.inr f) args) s (.error e)
  | call {co : Option YulContract} {f : YulFunctionName} {args : List Expr} {s s₁ : State} {vs : List Literal} {r : ResL} :
      evalObjectDataBuiltin? f args s = none →
      ArgsR co args.reverse s (.ok (s₁, vs)) → CallR co vs.reverse (some f) s₁ r →
      EvalR co (.Call (.inr f) args) s (head' r)

/-- `ExecR co stmt s r`: executing statement `stmt` from `s` gives `r`. -/
inductive ExecR : Option YulContract → Stmt → State → Res → Prop
  | blockNil {co : Option YulContract} (s : State) : ExecR co (.Block []) s (.ok s)
  | blockErr {co : Option YulContract} {st : Stmt} {sts : List Stmt} {s : State} {e : Yul.Exception} :
      ExecR co st s (.error e) → ExecR co (.Block (st :: sts)) s (.error e)
  | blockCons {co : Option YulContract} {st : Stmt} {sts : List Stmt} {s : State} {ss : SharedState .Yul} {vs : VarStore}
      {r : Res} :
      ExecR co st s (.ok (.Ok ss vs)) → ExecR co (.Block sts) (.Ok ss vs) r →
      ExecR co (.Block (st :: sts)) s r
  | blockJump {co : Option YulContract} {st : Stmt} {sts : List Stmt} {s : State} {j : Jump} :
      ExecR co st s (.ok (.Checkpoint j)) → ExecR co (.Block (st :: sts)) s (.ok (.Checkpoint j))
  | blockOOF {co : Option YulContract} {st : Stmt} {sts : List Stmt} {s : State} :
      ExecR co st s (.ok .OutOfFuel) → ExecR co (.Block (st :: sts)) s (.ok .OutOfFuel)
  | letNone {co : Option YulContract} (vars : List Identifier) (s : State) :
      ExecR co (.Let vars none) s (.ok (List.foldr (λ var s ↦ s.insert var ⟨0⟩) s vars))
  | letVar {co : Option YulContract} (vars : List Identifier) (x : Identifier) (s : State) :
      ExecR co (.Let vars (some (.Var x))) s (.ok (s.insert vars.head! s[x]!))
  | letLit {co : Option YulContract} (vars : List Identifier) (v : Literal) (s : State) :
      ExecR co (.Let vars (some (.Lit v))) s (.ok (s.insert vars.head! v))
  | letPrimArgsErr {co : Option YulContract} {vars : List Identifier} {prim : PrimOp} {args : List Expr} {s : State}
      {e : Yul.Exception} :
      ArgsR co args.reverse s (.error e) →
      ExecR co (.Let vars (some (.Call (.inl prim) args))) s (.error e)
  | letPrim {co : Option YulContract} {vars : List Identifier} {prim : PrimOp} {args : List Expr} {s s₁ : State}
      {vs : List Literal} {r : ResL} :
      ArgsR co args.reverse s (.ok (s₁, vs)) → PrimR s₁ prim vs.reverse r →
      ExecR co (.Let vars (some (.Call (.inl prim) args))) s (multifill' vars r)
  | letCallArgsErr {co : Option YulContract} {vars : List Identifier} {f : YulFunctionName} {args : List Expr} {s : State}
      {e : Yul.Exception} :
      ArgsR co args.reverse s (.error e) →
      ExecR co (.Let vars (some (.Call (.inr f) args))) s (.error e)
  | letBuiltin {co : Option YulContract} {vars : List Identifier} {f : YulFunctionName} {args : List Expr} {s s₁ : State}
      {vs : List Literal} {r : Res} :
      ArgsR co args.reverse s (.ok (s₁, vs)) →
      execObjectDataBuiltin? f vars (.ok (s₁, vs.reverse)) = some r →
      ExecR co (.Let vars (some (.Call (.inr f) args))) s r
  | letCall {co : Option YulContract} {vars : List Identifier} {f : YulFunctionName} {args : List Expr} {s s₁ : State}
      {vs : List Literal} {r : ResL} :
      ArgsR co args.reverse s (.ok (s₁, vs)) →
      execObjectDataBuiltin? f vars (.ok (s₁, vs.reverse)) = none →
      CallR co vs.reverse (some f) s₁ r →
      ExecR co (.Let vars (some (.Call (.inr f) args))) s (multifill' vars r)
  | ifErr {co : Option YulContract} {cond : Expr} {body : List Stmt} {s : State} {e : Yul.Exception} :
      EvalR co cond s (.error e) → ExecR co (.If cond body) s (.error e)
  | ifTrue {co : Option YulContract} {cond : Expr} {body : List Stmt} {s s₁ : State} {c : Literal} {r : Res} :
      EvalR co cond s (.ok (s₁, c)) → c ≠ ⟨0⟩ → ExecR co (.Block body) s₁ r →
      ExecR co (.If cond body) s r
  | ifFalse {co : Option YulContract} {cond : Expr} {body : List Stmt} {s s₁ : State} {c : Literal} :
      EvalR co cond s (.ok (s₁, c)) → c = ⟨0⟩ → ExecR co (.If cond body) s (.ok s₁)
  | exprPrimArgsErr {co : Option YulContract} {prim : PrimOp} {args : List Expr} {s : State} {e : Yul.Exception} :
      ArgsR co args.reverse s (.error e) →
      ExecR co (.ExprStmtCall (.Call (.inl prim) args)) s (.error e)
  | exprPrim {co : Option YulContract} {prim : PrimOp} {args : List Expr} {s s₁ : State} {vs : List Literal} {r : ResL} :
      ArgsR co args.reverse s (.ok (s₁, vs)) → PrimR s₁ prim vs.reverse r →
      ExecR co (.ExprStmtCall (.Call (.inl prim) args)) s (multifill' [] r)
  | exprCallArgsErr {co : Option YulContract} {f : YulFunctionName} {args : List Expr} {s : State} {e : Yul.Exception} :
      ArgsR co args.reverse s (.error e) →
      ExecR co (.ExprStmtCall (.Call (.inr f) args)) s (.error e)
  | exprBuiltin {co : Option YulContract} {f : YulFunctionName} {args : List Expr} {s s₁ : State} {vs : List Literal}
      {r : Res} :
      ArgsR co args.reverse s (.ok (s₁, vs)) →
      execObjectDataBuiltin? f [] (.ok (s₁, vs.reverse)) = some r →
      ExecR co (.ExprStmtCall (.Call (.inr f) args)) s r
  | exprCall {co : Option YulContract} {f : YulFunctionName} {args : List Expr} {s s₁ : State} {vs : List Literal}
      {r : ResL} :
      ArgsR co args.reverse s (.ok (s₁, vs)) →
      execObjectDataBuiltin? f [] (.ok (s₁, vs.reverse)) = none →
      CallR co vs.reverse (some f) s₁ r →
      ExecR co (.ExprStmtCall (.Call (.inr f) args)) s (multifill' [] r)
  | exprVar {co : Option YulContract} (x : Identifier) (s : State) :
      ExecR co (.ExprStmtCall (.Var x)) s (.error .InvalidExpression)
  | exprLit {co : Option YulContract} (v : Literal) (s : State) :
      ExecR co (.ExprStmtCall (.Lit v)) s (.error .InvalidExpression)
  | switchCondErr {co : Option YulContract} {cond : Expr} {cases : List (Literal × List Stmt)} {dflt : List Stmt} {s : State}
      {e : Yul.Exception} :
      EvalR co cond s (.error e) → ExecR co (.Switch cond cases dflt) s (.error e)
  | switchDefaultErr {co : Option YulContract} {cond : Expr} {cases : List (Literal × List Stmt)} {dflt : List Stmt}
      {s s₁ : State} {c : Literal} {e : Yul.Exception} :
      EvalR co cond s (.ok (s₁, c)) → ExecR co (.Block dflt) s₁ (.error e) →
      ExecR co (.Switch cond cases dflt) s (.error e)
  | switchCase {co : Option YulContract} {cond : Expr} {cases : List (Literal × List Stmt)} {dflt : List Stmt}
      {s s₁ s₂ : State} {c : Literal} {body : List Stmt} {r : Res} :
      EvalR co cond s (.ok (s₁, c)) → ExecR co (.Block dflt) s₁ (.ok s₂) →
      selectCase c cases = some body → ExecR co (.Block body) s₁ r →
      ExecR co (.Switch cond cases dflt) s r
  | switchDefault {co : Option YulContract} {cond : Expr} {cases : List (Literal × List Stmt)} {dflt : List Stmt}
      {s s₁ s₂ : State} {c : Literal} :
      EvalR co cond s (.ok (s₁, c)) → ExecR co (.Block dflt) s₁ (.ok s₂) →
      selectCase c cases = none →
      ExecR co (.Switch cond cases dflt) s (.ok s₂)
  | for_ {co : Option YulContract} {cond : Expr} {post body : List Stmt} {s : State} {r : Res} :
      LoopR co cond post body s r → ExecR co (.For cond post body) s r
  | continue_ {co : Option YulContract} (s : State) : ExecR co .Continue s (.ok (State.setContinue s))
  | break_ {co : Option YulContract} (s : State) : ExecR co .Break s (.ok (State.setBreak s))
  | leave {co : Option YulContract} (s : State) : ExecR co .Leave s (.ok (State.setLeave s))

/-- `LoopR co cond post body s r`: running `for {} cond {post} {body}` from `s` gives `r`. -/
inductive LoopR :
    Option YulContract → Expr → List Stmt → List Stmt → State → Res → Prop
  | condErr {co : Option YulContract} {cond : Expr} {post body : List Stmt} {s : State} {e : Yul.Exception} :
      EvalR co cond (State.mkOk s) (.error e) → LoopR co cond post body s (.error e)
  | exit {co : Option YulContract} {cond : Expr} {post body : List Stmt} {s s₁ : State} {x : Literal} :
      EvalR co cond (State.mkOk s) (.ok (s₁, x)) → x = ⟨0⟩ →
      LoopR co cond post body s (.ok (s₁.overwrite? s))
  | bodyErr {co : Option YulContract} {cond : Expr} {post body : List Stmt} {s s₁ : State} {x : Literal} {e : Yul.Exception} :
      EvalR co cond (State.mkOk s) (.ok (s₁, x)) → x ≠ ⟨0⟩ →
      ExecR co (.Block body) s₁ (.error e) → LoopR co cond post body s (.error e)
  | bodyOOF {co : Option YulContract} {cond : Expr} {post body : List Stmt} {s s₁ : State} {x : Literal} :
      EvalR co cond (State.mkOk s) (.ok (s₁, x)) → x ≠ ⟨0⟩ →
      ExecR co (.Block body) s₁ (.ok .OutOfFuel) →
      LoopR co cond post body s (.ok (State.OutOfFuel.overwrite? s))
  | break_ {co : Option YulContract} {cond : Expr} {post body : List Stmt} {s s₁ : State} {x : Literal} {ss : SharedState .Yul} {vs : VarStore} :
      EvalR co cond (State.mkOk s) (.ok (s₁, x)) → x ≠ ⟨0⟩ →
      ExecR co (.Block body) s₁ (.ok (.Checkpoint (.Break ss vs))) →
      LoopR co cond post body s
        (.ok ((State.Checkpoint (.Break ss vs)).reviveJump.overwrite? s))
  | leave {co : Option YulContract} {cond : Expr} {post body : List Stmt} {s s₁ : State} {x : Literal} {ss : SharedState .Yul} {vs : VarStore} :
      EvalR co cond (State.mkOk s) (.ok (s₁, x)) → x ≠ ⟨0⟩ →
      ExecR co (.Block body) s₁ (.ok (.Checkpoint (.Leave ss vs))) →
      LoopR co cond post body s (.ok ((State.Checkpoint (.Leave ss vs)).overwrite? s))
  | postErr {co : Option YulContract} {cond : Expr} {post body : List Stmt} {s s₁ s₂ : State} {x : Literal} {e : Yul.Exception} :
      EvalR co cond (State.mkOk s) (.ok (s₁, x)) → x ≠ ⟨0⟩ →
      ExecR co (.Block body) s₁ (.ok s₂) → continuesLoop s₂ →
      ExecR co (.Block post) s₂.reviveJump (.error e) →
      LoopR co cond post body s (.error e)
  | next {co : Option YulContract} {cond : Expr} {post body : List Stmt} {s s₁ s₂ s₃ : State} {x : Literal} {r : Res} :
      EvalR co cond (State.mkOk s) (.ok (s₁, x)) → x ≠ ⟨0⟩ →
      ExecR co (.Block body) s₁ (.ok s₂) → continuesLoop s₂ →
      ExecR co (.Block post) s₂.reviveJump (.ok s₃) →
      ExecR co (.For cond post body) (s₃.overwrite? s) r →
      LoopR co cond post body s (r.map (·.overwrite? s))

end

/-- The user-facing name of the statement relation: `Eval co stmt s r`. -/
@[expose] abbrev Eval := ExecR

end Relational
end Yul
end EvmYul
