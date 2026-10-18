module

public import EvmYul.Yul.Gas.NestedLoops

public section

/-!
# Yul gas, part 7: user-defined functions (and nested loops)

`NestedLoops.lean` meters every call-free Yul program. This file adds **calls of user-defined Yul
functions**, including recursive ones, on top of arbitrarily nested loops (`fragFS`). Contract calls
(the CALL family) are still excluded: their cost is the callee contract's.

A recursive function's gas is not bounded statically, so, as for loops, the bound is stated in terms
of budgets:

* `n`, the iteration budget: the largest number of body executions of any single loop entry;
* `d`, the call-depth budget: the largest nesting depth of user-function calls (a call made at top
  level has depth 1).

Definitions:

* `FnCostModel`: a `CostModel` plus the price `call` of one user-function call (the call/return
  jumps); `cancunFn` instantiates it.
* `evalF`, `argsF`, `execF`, `blockF`, `casesF`, `loopF`: a metered evaluator parametrised by a
  *call runner* `rc : Runner` that meters a call of a user function. It returns `none` when a loop
  entry needs more than `n` iterations or `rc` gives up.
* `callF c co n d`: the call runner with depth budget `d`; it looks the function up exactly as the
  interpreter does (`lookupFunction`) and runs its body with depth budget `d - 1`.
* `runF c co n d st s := execF c (callF c co n d) n st s`.
* `gasFS c gc n st`: the static bound, given a bound `gc f` for each call of `f`; `gasFn c tbl n d f`
  computes these bounds from a function table `tbl`; `gasF c tbl n d st` is the static bound of a
  program.

Results in this file:

* `runF_gas_le`: whenever `runF c co n d st s = some (r, g)` and the function table `tbl` contains
  every function the interpreter can look up (`TableCovers`; `tableCovers_some` shows it holds for
  `co = some code` and `tbl = code.functions.lookup`), **`g ≤ gasF c tbl n d st`**.
* `runF_mono`: a run that fits in budgets `n`, `d` gives the same result and gas with all larger
  budgets.

The link with the interpreter is in `Functions/Complete.lean`.
-/

namespace EvmYul
namespace Yul
namespace Gas

open Ast Relational EVM GasConstants

/-! ## Cost model and fragment -/

/-- A Yul cost model with a price for calls of user-defined functions. -/
structure FnCostModel extends CostModel where
  /-- Price of one call of a user-defined function (the call and return jumps). -/
  call : ℕ

/-- The Cancun cost model, plus a user-function call priced as `PUSH` of the return label
(`G_verylow`), two `JUMP`s (`G_mid` each) and two `JUMPDEST`s (`G_jumpdest` each). Like
`cancun.branch`, this price is an assumption about the code a compiler emits, not something read
off compiled code. -/
@[expose] def cancunFn : FnCostModel := { cancun with call := Gverylow + 2 * (Gmid + Gjumpdest) }

mutual

/-- Expressions of the fragment with user calls: no contract calls. -/
@[expose] def fragFE : Expr → Bool
  | .Lit _ => true
  | .Var _ => true
  | .Call (.inl prim) args => decide (prim ∉ callFamily) && fragFArgs args
  | .Call (.inr _) args => fragFArgs args

/-- Argument lists of `fragFE` expressions. -/
@[expose] def fragFArgs : List Expr → Bool
  | [] => true
  | a :: as => fragFE a && fragFArgs as

end

mutual

/-- Statements of the fragment with user calls and (nested) loops. -/
@[expose] def fragFS : Stmt → Bool
  | .Block sts => fragFB sts
  | .Let _ none => true
  | .Let _ (some e) => fragFE e
  | .ExprStmtCall e => fragFE e
  | .If cond body => fragFE cond && fragFB body
  | .Switch cond cases dflt => fragFE cond && fragFCases cases && fragFB dflt
  | .For cond post body => fragFE cond && fragFB post && fragFB body
  | .Continue => true
  | .Break => true
  | .Leave => true

/-- Blocks of `fragFS` statements. -/
@[expose] def fragFB : List Stmt → Bool
  | [] => true
  | st :: sts => fragFS st && fragFB sts

/-- `switch` cases whose bodies are `fragFB`. -/
@[expose] def fragFCases : List (Literal × List Stmt) → Bool
  | [] => true
  | (_, body) :: rest => fragFB body && fragFCases rest

end

/-- The fragment of Yul with user-defined function calls and nested loops (no contract calls). -/
@[expose] abbrev InFnFragment (st : Stmt) : Prop := fragFS st = true

/-- Every function the interpreter can look up (with code override `co`) has a body in the
fragment. -/
@[expose] def FunctionsInFragment (co : Option YulContract) : Prop :=
  ∀ s f fd, lookupFunction (some f) co s = .ok fd → fragFB fd.body = true

/-- A function table. -/
@[expose] abbrev FnTable := YulFunctionName → Option FunctionDefinition

/-- The table `tbl` contains every function the interpreter can look up with code override `co`. -/
@[expose] def TableCovers (co : Option YulContract) (tbl : FnTable) : Prop :=
  ∀ s f fd, lookupFunction (some f) co s = .ok fd → tbl f = some fd

/-- With a code override `some code`, the interpreter looks functions up in `code.functions`. -/
theorem tableCovers_some (code : YulContract) :
    TableCovers (some code) (fun f => code.functions.lookup f) := by
  intro s f fd h
  simp only [lookupFunction] at h
  split at h
  · cases h
  · simp only [Option.getD_some] at h
    split at h
    · cases h
    · rename_i fd' hfd; cases h; exact hfd

/-! ## The metered evaluator -/

/-- A metered runner for calls of user functions: arguments, function name, state; result and gas,
or `none` if it gives up. -/
@[expose] abbrev Runner := List Literal → YulFunctionName → State → Option (ResL × ℕ)

variable (c : FnCostModel)

mutual

/-- Metered evaluation of an expression, calls metered by `rc`. -/
@[expose] def evalF (rc : Runner) : Expr → State → Option (ResV × ℕ)
  | .Lit v, s => some (.ok (s, v), 0)
  | .Var x, s => some (.ok (s, s[x]!), 0)
  | .Call (.inl prim) args, s =>
    match argsF rc args s with
    | none => none
    | some (.error e, g) => some (.error e, g)
    | some (.ok (s₁, vs), g) => some (head' (primResult s₁ prim vs.reverse), g + c.prim prim)
  | .Call (.inr f) args, s =>
    match evalObjectDataBuiltin? f args s with
    | some r => some (r, 0)
    | none =>
      match argsF rc args s with
      | none => none
      | some (.error e, g) => some (.error e, g)
      | some (.ok (s₁, vs), g) =>
        match rc vs.reverse f s₁ with
        | none => none
        | some (r, g') => some (head' r, g + c.call + g')

/-- Metered evaluation of call arguments, **right to left** like the interpreter (which evaluates
`args.reverse`); the values come back in evaluation order. -/
@[expose] def argsF (rc : Runner) : List Expr → State → Option (ResL × ℕ)
  | [], s => some (.ok (s, []), 0)
  | a :: as, s =>
    match argsF rc as s with
    | none => none
    | some (.error e, g) => some (.error e, g)
    | some (.ok (s₁, vs), g) =>
      match evalF rc a s₁ with
      | none => none
      | some (.error e, g') => some (.error e, g + g')
      | some (.ok (s₂, v), g') => some (.ok (s₂, vs ++ [v]), g + g')

end

/-- The loop driver for `for {} cond {post} {body}` with metered runners for the condition, the
body and the post block, and `k` body executions allowed. Mirrors the interpreter's `loop`. -/
@[expose] def loopF (runCond : State → Option (ResV × ℕ)) (runBody runPost : State → Option (Res × ℕ)) :
    ℕ → State → Option (Res × ℕ)
  | k, s =>
    match runCond (State.mkOk s) with
    | none => none
    | some (.error e, g) => some (.error e, g)
    | some (.ok (s₁, x), g) =>
      if x = ⟨0⟩ then some (.ok (s₁.overwrite? s), g + c.branch)
      else
        match k with
        | 0 => none
        | k + 1 =>
          match runBody s₁ with
          | none => none
          | some (.error e, gb) => some (.error e, g + c.branch + gb)
          | some (.ok .OutOfFuel, gb) => some (.ok (State.OutOfFuel.overwrite? s), g + c.branch + gb)
          | some (.ok (.Checkpoint (.Break ss vs)), gb) =>
            some (.ok ((State.Checkpoint (.Break ss vs)).reviveJump.overwrite? s), g + c.branch + gb)
          | some (.ok (.Checkpoint (.Leave ss vs)), gb) =>
            some (.ok ((State.Checkpoint (.Leave ss vs)).overwrite? s), g + c.branch + gb)
          | some (.ok (.Checkpoint (.Continue ss vs)), gb) =>
            match runPost (State.Checkpoint (.Continue ss vs)).reviveJump with
            | none => none
            | some (.error e, gp) => some (.error e, g + c.branch + gb + gp)
            | some (.ok s₃, gp) =>
              match loopF runCond runBody runPost k (s₃.overwrite? s) with
              | none => none
              | some (r, g') => some (r.map (·.overwrite? s), g + c.branch + gb + gp + g')
          | some (.ok (.Ok ss vs), gb) =>
            match runPost (State.Ok ss vs).reviveJump with
            | none => none
            | some (.error e, gp) => some (.error e, g + c.branch + gb + gp)
            | some (.ok s₃, gp) =>
              match loopF runCond runBody runPost k (s₃.overwrite? s) with
              | none => none
              | some (r, g') => some (r.map (·.overwrite? s), g + c.branch + gb + gp + g')

/-- A builtin call in statement position (`let vars := prim(args)` or `prim(args)`). -/
@[expose] def stmtPrimF (rc : Runner) (vars : List Identifier) (prim : PrimOp) (args : List Expr)
    (s : State) : Option (Res × ℕ) :=
  match argsF c rc args s with
  | none => none
  | some (.error e, g) => some (.error e, g)
  | some (.ok (s₁, vs), g) => some (multifill' vars (primResult s₁ prim vs.reverse), g + c.prim prim)

/-- A user call in statement position (`let vars := f(args)` or `f(args)`), including the
object-data builtins (`datacopy`) the interpreter handles there. -/
@[expose] def stmtCallF (rc : Runner) (vars : List Identifier) (f : YulFunctionName) (args : List Expr)
    (s : State) : Option (Res × ℕ) :=
  match argsF c rc args s with
  | none => none
  | some (.error e, g) => some (.error e, g)
  | some (.ok (s₁, vs), g) =>
    match execObjectDataBuiltin? f vars (.ok (s₁, vs.reverse)) with
    | some r => some (r, g)
    | none =>
      match rc vs.reverse f s₁ with
      | none => none
      | some (r, g') => some (multifill' vars r, g + c.call + g')

mutual

/-- Metered execution with call runner `rc` and per-loop-entry iteration budget `n`. -/
@[expose] def execF (rc : Runner) (n : ℕ) : Stmt → State → Option (Res × ℕ)
  | .Block sts, s => blockF rc n sts s
  | .Let vars none, s => some (.ok (List.foldr (λ var s ↦ s.insert var ⟨0⟩) s vars), 0)
  | .Let vars (some (.Var x)), s => some (.ok (s.insert vars.head! s[x]!), 0)
  | .Let vars (some (.Lit v)), s => some (.ok (s.insert vars.head! v), 0)
  | .Let vars (some (.Call (.inl prim) args)), s => stmtPrimF c rc vars prim args s
  | .Let vars (some (.Call (.inr f) args)), s => stmtCallF c rc vars f args s
  | .ExprStmtCall (.Call (.inl prim) args), s => stmtPrimF c rc [] prim args s
  | .ExprStmtCall (.Call (.inr f) args), s => stmtCallF c rc [] f args s
  | .ExprStmtCall (.Var _), _ => some (.error .InvalidExpression, 0)
  | .ExprStmtCall (.Lit _), _ => some (.error .InvalidExpression, 0)
  | .If cond body, s =>
    match evalF c rc cond s with
    | none => none
    | some (.error e, g) => some (.error e, g)
    | some (.ok (s₁, v), g) =>
      if v ≠ ⟨0⟩ then addGas (g + c.branch) (blockF rc n body s₁)
      else some (.ok s₁, g + c.branch)
  | .Switch cond cases dflt, s =>
    match evalF c rc cond s with
    | none => none
    | some (.error e, g) => some (.error e, g)
    | some (.ok (s₁, v), g) =>
      match blockF rc n dflt s₁ with
      | none => none
      | some (.error e, gd) => some (.error e, g + c.branch + gd)
      | some (.ok s₂, gd) =>
        match casesF rc n cases v s₁ with
        | none => none
        | some none => some (.ok s₂, g + c.branch + gd)
        | some (some (r, gb)) => some (r, g + c.branch + gb)
  | .For cond post body, s =>
    loopF c (evalF c rc cond) (blockF rc n body) (blockF rc n post) n s
  | .Continue, s => some (.ok (State.setContinue s), 0)
  | .Break, s => some (.ok (State.setBreak s), 0)
  | .Leave, s => some (.ok (State.setLeave s), 0)

/-- Metered execution of a block. -/
@[expose] def blockF (rc : Runner) (n : ℕ) : List Stmt → State → Option (Res × ℕ)
  | [], s => some (.ok s, 0)
  | st :: sts, s =>
    match execF rc n st s with
    | none => none
    | some (.ok (.Ok ss vs), g) => addGas g (blockF rc n sts (.Ok ss vs))
    | some (r, g) => some (r, g)

/-- The selected `switch` case: `some none` when no case matches. -/
@[expose] def casesF (rc : Runner) (n : ℕ) :
    List (Literal × List Stmt) → Literal → State → Option (Option (Res × ℕ))
  | [], _, _ => some none
  | (l, body) :: rest, v, s =>
    if l = v then (blockF rc n body s).map some else casesF rc n rest v s

end

/-- The call runner with call-depth budget `d`: it looks the function up as the interpreter does
and runs its body with depth budget `d - 1`. At depth budget `0` it gives up. -/
@[expose] def callF (co : Option YulContract) (n : ℕ) : ℕ → Runner
  | 0 => fun _ _ _ => none
  | d + 1 => fun args f s =>
    match lookupFunction (some f) co s with
    | .error e => some (.error e, 0)
    | .ok fd =>
      match blockF c (callF co n d) n fd.body (State.mkOk (s.initcall fd.params args)) with
      | none => none
      | some (r, g) => some (callPost s fd r, g)

/-- **The metered semantics of Yul with user functions**: iteration budget `n`, call-depth budget
`d`, code override `co`. -/
@[expose] def runF (co : Option YulContract) (n d : ℕ) (st : Stmt) (s : State) : Option (Res × ℕ) :=
  execF c (callF c co n d) n st s

/-! ## The static bound -/

mutual

/-- Static gas of an expression, given a bound `gc f` for each call of the user function `f`. -/
@[expose] def gasFE (gc : YulFunctionName → ℕ) : Expr → ℕ
  | .Lit _ => 0
  | .Var _ => 0
  | .Call (.inl prim) args => gasFArgs gc args + c.prim prim
  | .Call (.inr f) args => gasFArgs gc args + c.call + gc f

/-- Static gas of an argument list. -/
@[expose] def gasFArgs (gc : YulFunctionName → ℕ) : List Expr → ℕ
  | [] => 0
  | a :: as => gasFE gc a + gasFArgs gc as

end

mutual

/-- Static gas of a statement, for iteration budget `n`. -/
@[expose] def gasFS (gc : YulFunctionName → ℕ) (n : ℕ) : Stmt → ℕ
  | .Block sts => gasFB gc n sts
  | .Let _ none => 0
  | .Let _ (some e) => gasFE c gc e
  | .ExprStmtCall e => gasFE c gc e
  | .If cond body => gasFE c gc cond + c.branch + gasFB gc n body
  | .Switch cond cases dflt => gasFE c gc cond + c.branch + max (gasFB gc n dflt) (gasFCases gc n cases)
  | .For cond post body =>
    n * (gasFE c gc cond + c.branch + gasFB gc n body + gasFB gc n post) + (gasFE c gc cond + c.branch)
  | .Continue => 0
  | .Break => 0
  | .Leave => 0

/-- Static gas of a block. -/
@[expose] def gasFB (gc : YulFunctionName → ℕ) (n : ℕ) : List Stmt → ℕ
  | [] => 0
  | st :: sts => gasFS gc n st + gasFB gc n sts

/-- The largest static gas among `switch` case bodies. -/
@[expose] def gasFCases (gc : YulFunctionName → ℕ) (n : ℕ) : List (Literal × List Stmt) → ℕ
  | [] => 0
  | (_, body) :: rest => max (gasFB gc n body) (gasFCases gc n rest)

end

/-- Static gas of the body of each function in `tbl`, at call-depth budget `d` (calls made inside the
body get depth budget `d - 1`). A function missing from the table costs nothing (the call fails). -/
@[expose] def gasFn (tbl : FnTable) (n : ℕ) : ℕ → YulFunctionName → ℕ
  | 0 => fun _ => 0
  | d + 1 => fun f =>
    match tbl f with
    | none => 0
    | some fd => gasFB c (gasFn tbl n d) n fd.body

/-- **The static gas bound** of a program, for iteration budget `n` and call-depth budget `d`. -/
@[expose] def gasF (tbl : FnTable) (n d : ℕ) (st : Stmt) : ℕ := gasFS c (gasFn c tbl n d) n st


/-! ## The static bound is sound -/

/-- The runner `rc` charges at most `gc f` for each call of `f`. -/
@[expose] def RunnerLe (rc : Runner) (gc : YulFunctionName → ℕ) : Prop :=
  ∀ args f s r g, rc args f s = some (r, g) → g ≤ gc f

mutual

/-- Gas bound for expressions. -/
theorem evalF_gas_le {rc : Runner} {gc : YulFunctionName → ℕ} (hrc : RunnerLe rc gc) :
    (e : Expr) → (s : State) → {r : ResV} → {g : ℕ} → evalF c rc e s = some (r, g) →
      g ≤ gasFE c gc e
  | .Lit _, _, _, _, h => by
    simp only [evalF, Option.some.injEq, Prod.mk.injEq] at h; simp [gasFE, ← h.2]
  | .Var _, _, _, _, h => by
    simp only [evalF, Option.some.injEq, Prod.mk.injEq] at h; simp [gasFE, ← h.2]
  | .Call (.inl prim) args, s, r, g, h => by
    rcases ha : argsF c rc args s with _ | ⟨_ | ⟨s₁, vs⟩, g₀⟩
    · simp [evalF, ha] at h
    · have := argsF_gas_le hrc args s ha
      simp only [evalF, ha, Option.some.injEq, Prod.mk.injEq] at h
      simp only [gasFE]; omega
    · have := argsF_gas_le hrc args s ha
      simp only [evalF, ha, Option.some.injEq, Prod.mk.injEq] at h
      simp only [gasFE]; omega
  | .Call (.inr f) args, s, r, g, h => by
    rcases hb : evalObjectDataBuiltin? f args s with _ | r₀
    · rcases ha : argsF c rc args s with _ | ⟨_ | ⟨s₁, vs⟩, g₀⟩
      · simp [evalF, hb, ha] at h
      · have := argsF_gas_le hrc args s ha
        simp only [evalF, hb, ha, Option.some.injEq, Prod.mk.injEq] at h
        simp only [gasFE]; omega
      · have := argsF_gas_le hrc args s ha
        rcases hc : rc vs.reverse f s₁ with _ | ⟨r₁, g₁⟩
        · simp [evalF, hb, ha, hc] at h
        · have := hrc _ _ _ _ _ hc
          simp only [evalF, hb, ha, hc, Option.some.injEq, Prod.mk.injEq] at h
          simp only [gasFE]; omega
    · simp only [evalF, hb, Option.some.injEq, Prod.mk.injEq] at h
      omega

/-- Gas bound for argument lists. -/
theorem argsF_gas_le {rc : Runner} {gc : YulFunctionName → ℕ} (hrc : RunnerLe rc gc) :
    (as : List Expr) → (s : State) → {r : ResL} → {g : ℕ} → argsF c rc as s = some (r, g) →
      g ≤ gasFArgs c gc as
  | [], _, _, _, h => by
    simp only [argsF, Option.some.injEq, Prod.mk.injEq] at h; simp [gasFArgs, ← h.2]
  | a :: as, s, r, g, h => by
    rcases ha : argsF c rc as s with _ | ⟨_ | ⟨s₁, vs⟩, g₀⟩
    · simp [argsF, ha] at h
    · have := argsF_gas_le hrc as s ha
      simp only [argsF, ha, Option.some.injEq, Prod.mk.injEq] at h
      simp only [gasFArgs]; omega
    · have h₀ := argsF_gas_le hrc as s ha
      rcases he : evalF c rc a s₁ with _ | ⟨_ | ⟨s₂, v⟩, g₁⟩
      · simp [argsF, ha, he] at h
      · have := evalF_gas_le hrc a s₁ he
        simp only [argsF, ha, he, Option.some.injEq, Prod.mk.injEq] at h
        simp only [gasFArgs]; omega
      · have := evalF_gas_le hrc a s₁ he
        simp only [argsF, ha, he, Option.some.injEq, Prod.mk.injEq] at h
        simp only [gasFArgs]; omega

end

/-- Gas bound for the loop driver, given bounds for its three runners. -/
theorem loopF_gas_le (runCond : State → Option (ResV × ℕ)) (runBody runPost : State → Option (Res × ℕ))
    (Bc Bb Bp : ℕ) (hc : ∀ s r g, runCond s = some (r, g) → g ≤ Bc)
    (hb : ∀ s r g, runBody s = some (r, g) → g ≤ Bb)
    (hp : ∀ s r g, runPost s = some (r, g) → g ≤ Bp) :
    ∀ k s r g, loopF c runCond runBody runPost k s = some (r, g) →
      g ≤ k * (Bc + c.branch + Bb + Bp) + (Bc + c.branch) := by
  intro k
  induction k with
  | zero =>
    intro s r g h
    unfold loopF at h
    rcases hrc : runCond (State.mkOk s) with _ | ⟨_ | ⟨s₁, x⟩, g₀⟩
    · simp [hrc] at h
    · have := hc _ _ _ hrc
      simp only [hrc, Option.some.injEq, Prod.mk.injEq] at h; omega
    · have := hc _ _ _ hrc
      simp only [hrc] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
      · simp at h
  | succ k ih =>
    intro s r g h
    unfold loopF at h
    rcases hrc : runCond (State.mkOk s) with _ | ⟨_ | ⟨s₁, x⟩, g₀⟩
    · simp [hrc] at h
    · have := hc _ _ _ hrc
      simp only [hrc, Option.some.injEq, Prod.mk.injEq] at h; omega
    · have hc₀ := hc _ _ _ hrc
      simp only [hrc] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
      · split at h
        · simp at h
        all_goals rename_i hrb; have hgb := hb _ _ _ hrb; rw [Nat.succ_mul]
        all_goals first
          | (simp only [Option.some.injEq, Prod.mk.injEq] at h; omega)
          | (split at h
             · simp at h
             · rename_i hrp; have hgp := hp _ _ _ hrp
               simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
             · rename_i hrp; have hgp := hp _ _ _ hrp
               split at h
               · simp at h
               · rename_i hrec; have hg' := ih _ _ _ hrec
                 simp only [Option.some.injEq, Prod.mk.injEq] at h; omega)

theorem stmtPrimF_gas_le {rc : Runner} {gc : YulFunctionName → ℕ} (hrc : RunnerLe rc gc)
    (vars : List Identifier) (prim : PrimOp) (args : List Expr) (s : State) {r : Res} {g : ℕ}
    (h : stmtPrimF c rc vars prim args s = some (r, g)) :
    g ≤ gasFE c gc (.Call (.inl prim) args) := by
  rcases ha : argsF c rc args s with _ | ⟨_ | ⟨s₁, vs⟩, g₀⟩
  · simp [stmtPrimF, ha] at h
  · have := argsF_gas_le c hrc args s ha
    simp only [stmtPrimF, ha, Option.some.injEq, Prod.mk.injEq] at h
    simp only [gasFE]; omega
  · have := argsF_gas_le c hrc args s ha
    simp only [stmtPrimF, ha, Option.some.injEq, Prod.mk.injEq] at h
    simp only [gasFE]; omega

theorem stmtCallF_gas_le {rc : Runner} {gc : YulFunctionName → ℕ} (hrc : RunnerLe rc gc)
    (vars : List Identifier) (f : YulFunctionName) (args : List Expr) (s : State) {r : Res} {g : ℕ}
    (h : stmtCallF c rc vars f args s = some (r, g)) :
    g ≤ gasFE c gc (.Call (.inr f) args) := by
  rcases ha : argsF c rc args s with _ | ⟨_ | ⟨s₁, vs⟩, g₀⟩
  · simp [stmtCallF, ha] at h
  · have := argsF_gas_le c hrc args s ha
    simp only [stmtCallF, ha, Option.some.injEq, Prod.mk.injEq] at h
    simp only [gasFE]; omega
  · have := argsF_gas_le c hrc args s ha
    rcases hb : execObjectDataBuiltin? f vars (.ok (s₁, vs.reverse)) with _ | r₀
    · rcases hc : rc vs.reverse f s₁ with _ | ⟨r₁, g₁⟩
      · simp [stmtCallF, ha, hb, hc] at h
      · have := hrc _ _ _ _ _ hc
        simp only [stmtCallF, ha, hb, hc, Option.some.injEq, Prod.mk.injEq] at h
        simp only [gasFE]; omega
    · simp only [stmtCallF, ha, hb, Option.some.injEq, Prod.mk.injEq] at h
      simp only [gasFE]; omega

mutual

/-- **Gas bound for statements.** A metered run with a call runner bounded by `gc` is charged at
most `gasFS c gc n st`. -/
theorem execF_gas_le {rc : Runner} {gc : YulFunctionName → ℕ} (hrc : RunnerLe rc gc) (n : ℕ) :
    (st : Stmt) → (s : State) → {r : Res} → {g : ℕ} → execF c rc n st s = some (r, g) →
      g ≤ gasFS c gc n st
  | .Block sts, s, _, _, h => by
    simp only [execF] at h; simpa only [gasFS] using blockF_gas_le hrc n sts s h
  | .Let _ none, _, _, _, h => by
    simp only [execF, Option.some.injEq, Prod.mk.injEq] at h; simp [gasFS, ← h.2]
  | .Let _ (some (.Var _)), _, _, _, h => by
    simp only [execF, Option.some.injEq, Prod.mk.injEq] at h; simp [gasFS, ← h.2]
  | .Let _ (some (.Lit _)), _, _, _, h => by
    simp only [execF, Option.some.injEq, Prod.mk.injEq] at h; simp [gasFS, ← h.2]
  | .Let vars (some (.Call (.inl prim) args)), s, _, _, h => by
    simp only [execF] at h; simpa only [gasFS] using stmtPrimF_gas_le c hrc vars prim args s h
  | .Let vars (some (.Call (.inr f) args)), s, _, _, h => by
    simp only [execF] at h; simpa only [gasFS] using stmtCallF_gas_le c hrc vars f args s h
  | .ExprStmtCall (.Call (.inl prim) args), s, _, _, h => by
    simp only [execF] at h; simpa only [gasFS] using stmtPrimF_gas_le c hrc [] prim args s h
  | .ExprStmtCall (.Call (.inr f) args), s, _, _, h => by
    simp only [execF] at h; simpa only [gasFS] using stmtCallF_gas_le c hrc [] f args s h
  | .ExprStmtCall (.Var _), _, _, _, h => by
    simp only [execF, Option.some.injEq, Prod.mk.injEq] at h; simp [gasFS, ← h.2]
  | .ExprStmtCall (.Lit _), _, _, _, h => by
    simp only [execF, Option.some.injEq, Prod.mk.injEq] at h; simp [gasFS, ← h.2]
  | .If cond body, s, r, g, h => by
    rcases hev : evalF c rc cond s with _ | ⟨_ | ⟨s₁, v⟩, g₀⟩
    · simp [execF, hev] at h
    · have := evalF_gas_le c hrc cond s hev
      simp only [execF, hev, Option.some.injEq, Prod.mk.injEq] at h; simp only [gasFS]; omega
    · have hc := evalF_gas_le c hrc cond s hev
      by_cases hv : v = ⟨0⟩
      · simp only [execF, hev, hv, ne_eq, not_true_eq_false, if_false, Option.some.injEq,
          Prod.mk.injEq] at h
        simp only [gasFS]; omega
      · simp only [execF, hev, hv, ne_eq, not_false_eq_true, if_true] at h
        obtain ⟨g₁, h1, rfl⟩ := addGas_eq_some h
        have := blockF_gas_le hrc n body s₁ h1
        simp only [gasFS]; omega
  | .Switch cond cases dflt, s, r, g, h => by
    rcases hev : evalF c rc cond s with _ | ⟨_ | ⟨s₁, v⟩, g₀⟩
    · simp [execF, hev] at h
    · have := evalF_gas_le c hrc cond s hev
      simp only [execF, hev, Option.some.injEq, Prod.mk.injEq] at h; simp only [gasFS]; omega
    · have hc := evalF_gas_le c hrc cond s hev
      rcases hd : blockF c rc n dflt s₁ with _ | ⟨_ | s₂, gd⟩
      · simp [execF, hev, hd] at h
      · have := blockF_gas_le hrc n dflt s₁ hd
        simp only [execF, hev, hd, Option.some.injEq, Prod.mk.injEq] at h
        simp only [gasFS]; omega
      · have hdl := blockF_gas_le hrc n dflt s₁ hd
        rcases hcs : casesF c rc n cases v s₁ with _ | _ | ⟨r₁, gb⟩
        · simp [execF, hev, hd, hcs] at h
        · simp only [execF, hev, hd, hcs, Option.some.injEq, Prod.mk.injEq] at h
          simp only [gasFS]; omega
        · have := casesF_gas_le hrc n cases v s₁ hcs
          simp only [execF, hev, hd, hcs, Option.some.injEq, Prod.mk.injEq] at h
          simp only [gasFS]; omega
  | .For cond post body, s, r, g, h => by
    simp only [execF] at h
    simp only [gasFS]
    exact loopF_gas_le c _ _ _ (gasFE c gc cond) (gasFB c gc n body) (gasFB c gc n post)
      (fun s _ _ h => evalF_gas_le c hrc cond s h)
      (fun s _ _ h => blockF_gas_le hrc n body s h) (fun s _ _ h => blockF_gas_le hrc n post s h)
      n s r g h
  | .Continue, _, _, _, h => by
    simp only [execF, Option.some.injEq, Prod.mk.injEq] at h; simp [gasFS, h.2.symm]
  | .Break, _, _, _, h => by
    simp only [execF, Option.some.injEq, Prod.mk.injEq] at h; simp [gasFS, h.2.symm]
  | .Leave, _, _, _, h => by
    simp only [execF, Option.some.injEq, Prod.mk.injEq] at h; simp [gasFS, h.2.symm]

/-- Gas bound for blocks. -/
theorem blockF_gas_le {rc : Runner} {gc : YulFunctionName → ℕ} (hrc : RunnerLe rc gc) (n : ℕ) :
    (sts : List Stmt) → (s : State) → {r : Res} → {g : ℕ} → blockF c rc n sts s = some (r, g) →
      g ≤ gasFB c gc n sts
  | [], _, _, _, h => by
    simp only [blockF, Option.some.injEq, Prod.mk.injEq] at h; simp [gasFB, h.2.symm]
  | st :: sts, s, r, g, h => by
    rcases hx : execF c rc n st s with _ | ⟨r₀, g₀⟩
    · simp [blockF, hx] at h
    · have h₀ := execF_gas_le hrc n st s hx
      rcases r₀ with e | (⟨ss, vs⟩ | _ | j)
      · simp only [blockF, hx, Option.some.injEq, Prod.mk.injEq] at h; simp only [gasFB]; omega
      · simp only [blockF, hx] at h
        obtain ⟨g₁, h1, rfl⟩ := addGas_eq_some h
        have := blockF_gas_le hrc n sts _ h1
        simp only [gasFB]; omega
      · simp only [blockF, hx, Option.some.injEq, Prod.mk.injEq] at h; simp only [gasFB]; omega
      · simp only [blockF, hx, Option.some.injEq, Prod.mk.injEq] at h; simp only [gasFB]; omega

/-- Gas bound for the selected `switch` case. -/
theorem casesF_gas_le {rc : Runner} {gc : YulFunctionName → ℕ} (hrc : RunnerLe rc gc) (n : ℕ) :
    (cases : List (Literal × List Stmt)) → (v : Literal) → (s : State) → {r : Res} → {g : ℕ} →
    casesF c rc n cases v s = some (some (r, g)) → g ≤ gasFCases c gc n cases
  | [], _, _, _, _, h => by simp [casesF] at h
  | (l, body) :: rest, v, s, r, g, h => by
    by_cases hl : l = v
    · simp only [casesF, hl, if_true] at h
      rcases hb : blockF c rc n body s with _ | ⟨r₁, g₁⟩
      · simp [hb] at h
      · simp only [hb, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        have := blockF_gas_le hrc n body s hb
        simp only [gasFCases]; omega
    · simp only [casesF, hl, if_false] at h
      have := casesF_gas_le hrc n rest v s h
      simp only [gasFCases]; omega

end

/-- The call runner at depth budget `d` is bounded by `gasFn c tbl n d`, for every table covering
the functions the interpreter can look up. -/
theorem callF_le {co : Option YulContract} {tbl : FnTable} (htbl : TableCovers co tbl) (n : ℕ) :
    ∀ d, RunnerLe (callF c co n d) (gasFn c tbl n d) := by
  intro d
  induction d with
  | zero => intro args f s r g h; simp [callF] at h
  | succ d ih =>
    intro args f s r g h
    simp only [callF] at h
    rcases hl : lookupFunction (some f) co s with e | fd
    · simp only [hl, Option.some.injEq, Prod.mk.injEq] at h; omega
    · simp only [hl] at h
      rcases hb : blockF c (callF c co n d) n fd.body (State.mkOk (s.initcall fd.params args))
        with _ | ⟨r₁, g₁⟩
      · simp [hb] at h
      · simp only [hb, Option.some.injEq, Prod.mk.injEq] at h
        have := blockF_gas_le c ih n fd.body _ hb
        simp only [gasFn, htbl s f fd hl]; omega

/-- **Yul gas bound with user functions.** A metered run within iteration budget `n` and call-depth
budget `d` is charged at most `gasF c tbl n d st`, for every function table `tbl` that covers the
functions the interpreter can look up. -/
theorem runF_gas_le {co : Option YulContract} {tbl : FnTable} (htbl : TableCovers co tbl)
    (n d : ℕ) (st : Stmt) (s : State) {r : Res} {g : ℕ} (h : runF c co n d st s = some (r, g)) :
    g ≤ gasF c tbl n d st :=
  execF_gas_le c (callF_le c htbl n d) n st s h

/-! ## Monotonicity in the budgets -/

/-- The runner `rc'` extends `rc`: wherever `rc` succeeds, `rc'` gives the same answer. -/
@[expose] def RunnerExt (rc rc' : Runner) : Prop :=
  ∀ args f s o, rc args f s = some o → rc' args f s = some o

mutual

theorem evalF_mono {rc rc' : Runner} (hrc : RunnerExt rc rc') : (e : Expr) → (s : State) →
    {o : ResV × ℕ} → evalF c rc e s = some o → evalF c rc' e s = some o
  | .Lit _, _, _, h => by simpa only [evalF] using h
  | .Var _, _, _, h => by simpa only [evalF] using h
  | .Call (.inl prim) args, s, _, h => by
    rcases ha : argsF c rc args s with _ | ⟨r, g⟩
    · simp [evalF, ha] at h
    · simp only [evalF, ha] at h; simp only [evalF, argsF_mono hrc args s ha]; exact h
  | .Call (.inr f) args, s, _, h => by
    rcases hb : evalObjectDataBuiltin? f args s with _ | r₀
    · rcases ha : argsF c rc args s with _ | ⟨_ | ⟨s₁, vs⟩, g⟩
      · simp [evalF, hb, ha] at h
      · simp only [evalF, hb, ha] at h; simp only [evalF, hb, argsF_mono hrc args s ha]; exact h
      · rcases hc : rc vs.reverse f s₁ with _ | ⟨r₁, g₁⟩
        · simp [evalF, hb, ha, hc] at h
        · simp only [evalF, hb, ha, hc] at h
          simp only [evalF, hb, argsF_mono hrc args s ha, hrc _ _ _ _ hc]; exact h
    · simp only [evalF, hb] at h ⊢; exact h

theorem argsF_mono {rc rc' : Runner} (hrc : RunnerExt rc rc') : (as : List Expr) → (s : State) →
    {o : ResL × ℕ} → argsF c rc as s = some o → argsF c rc' as s = some o
  | [], _, _, h => by simpa only [argsF] using h
  | a :: as, s, _, h => by
    rcases ha : argsF c rc as s with _ | ⟨_ | ⟨s₁, vs⟩, g⟩
    · simp [argsF, ha] at h
    · simp only [argsF, ha] at h; simp only [argsF, argsF_mono hrc as s ha]; exact h
    · rcases he : evalF c rc a s₁ with _ | ⟨r₁, g₁⟩
      · simp [argsF, ha, he] at h
      · simp only [argsF, ha, he] at h
        simp only [argsF, argsF_mono hrc as s ha, evalF_mono hrc a s₁ he]; exact h

end

/-- The loop driver is monotone in its runners and in the number of iterations allowed. -/
theorem loopF_mono {rcd rcd' : State → Option (ResV × ℕ)} {rb rp rb' rp' : State → Option (Res × ℕ)}
    (hcd : ∀ s o, rcd s = some o → rcd' s = some o)
    (hb : ∀ s o, rb s = some o → rb' s = some o) (hp : ∀ s o, rp s = some o → rp' s = some o) :
    ∀ k k' s o, k ≤ k' → loopF c rcd rb rp k s = some o → loopF c rcd' rb' rp' k' s = some o := by
  intro k
  induction k with
  | zero =>
    intro k' s o _ h
    unfold loopF at h ⊢
    rcases hev : rcd (State.mkOk s) with _ | ⟨_ | ⟨s₁, x⟩, g⟩
    · simp [hev] at h
    · rw [hev] at h; rw [hcd _ _ hev]; exact h
    · rw [hev] at h; rw [hcd _ _ hev]
      by_cases hx : x = ⟨0⟩
      · simp only [hx, if_true] at h ⊢; exact h
      · simp [hx] at h
  | succ k ih =>
    intro k' s o hk h
    obtain ⟨k', rfl⟩ : ∃ j, k' = j + 1 := ⟨k' - 1, by omega⟩
    unfold loopF at h ⊢
    rcases hev : rcd (State.mkOk s) with _ | ⟨_ | ⟨s₁, x⟩, g⟩
    · simp [hev] at h
    · rw [hev] at h; rw [hcd _ _ hev]; exact h
    · rw [hev] at h; rw [hcd _ _ hev]
      by_cases hx : x = ⟨0⟩
      · simp only [hx, if_true] at h ⊢; exact h
      · simp only [hx, if_false] at h ⊢
        rcases hr : rb s₁ with _ | ⟨r, gb⟩
        · simp [hr] at h
        · rw [hb _ _ hr]; rw [hr] at h
          rcases r with e | (⟨ss, vs⟩ | _ | (⟨ss, vs⟩ | ⟨ss, vs⟩ | ⟨ss, vs⟩))
          · exact h
          · simp only at h ⊢
            rcases hq : rp (State.Ok ss vs).reviveJump with _ | ⟨q, gp⟩
            · simp [hq] at h
            · rw [hp _ _ hq]; rw [hq] at h
              rcases q with e | s₃
              · exact h
              · simp only at h ⊢
                rcases hl : loopF c rcd rb rp k (s₃.overwrite? s) with _ | ⟨r', g'⟩
                · simp [hl] at h
                · rw [ih k' _ _ (by omega) hl]; rw [hl] at h; exact h
          · exact h
          · simp only at h ⊢
            rcases hq : rp (State.Checkpoint (.Continue ss vs)).reviveJump with _ | ⟨q, gp⟩
            · simp [hq] at h
            · rw [hp _ _ hq]; rw [hq] at h
              rcases q with e | s₃
              · exact h
              · simp only at h ⊢
                rcases hl : loopF c rcd rb rp k (s₃.overwrite? s) with _ | ⟨r', g'⟩
                · simp [hl] at h
                · rw [ih k' _ _ (by omega) hl]; rw [hl] at h; exact h
          · exact h
          · exact h

theorem stmtPrimF_mono {rc rc' : Runner} (hrc : RunnerExt rc rc') (vars : List Identifier)
    (prim : PrimOp) (args : List Expr) (s : State) {o : Res × ℕ}
    (h : stmtPrimF c rc vars prim args s = some o) : stmtPrimF c rc' vars prim args s = some o := by
  rcases ha : argsF c rc args s with _ | ⟨r, g⟩
  · simp [stmtPrimF, ha] at h
  · simp only [stmtPrimF, ha] at h; simp only [stmtPrimF, argsF_mono c hrc args s ha]; exact h

theorem stmtCallF_mono {rc rc' : Runner} (hrc : RunnerExt rc rc') (vars : List Identifier)
    (f : YulFunctionName) (args : List Expr) (s : State) {o : Res × ℕ}
    (h : stmtCallF c rc vars f args s = some o) : stmtCallF c rc' vars f args s = some o := by
  rcases ha : argsF c rc args s with _ | ⟨_ | ⟨s₁, vs⟩, g⟩
  · simp [stmtCallF, ha] at h
  · simp only [stmtCallF, ha] at h; simp only [stmtCallF, argsF_mono c hrc args s ha]; exact h
  · rcases hb : execObjectDataBuiltin? f vars (.ok (s₁, vs.reverse)) with _ | r₀
    · rcases hc : rc vs.reverse f s₁ with _ | ⟨r₁, g₁⟩
      · simp [stmtCallF, ha, hb, hc] at h
      · simp only [stmtCallF, ha, hb, hc] at h
        simp only [stmtCallF, argsF_mono c hrc args s ha, hb, hrc _ _ _ _ hc]; exact h
    · simp only [stmtCallF, ha, hb] at h
      simp only [stmtCallF, argsF_mono c hrc args s ha, hb]; exact h

mutual

/-- **Monotonicity.** A run that succeeds with runner `rc` and budget `n` gives the same result and
gas with any runner extending `rc` and any larger budget. -/
theorem execF_mono {rc rc' : Runner} (hrc : RunnerExt rc rc') {n n' : ℕ} (hn : n ≤ n') :
    (st : Stmt) → (s : State) → {o : Res × ℕ} → execF c rc n st s = some o →
      execF c rc' n' st s = some o
  | .Block sts, s, _, h => by
    simp only [execF] at h ⊢; exact blockF_mono hrc hn sts s h
  | .Let _ none, _, _, h => by simpa only [execF] using h
  | .Let _ (some (.Var _)), _, _, h => by simpa only [execF] using h
  | .Let _ (some (.Lit _)), _, _, h => by simpa only [execF] using h
  | .Let vars (some (.Call (.inl prim) args)), s, _, h => by
    simp only [execF] at h ⊢; exact stmtPrimF_mono c hrc vars prim args s h
  | .Let vars (some (.Call (.inr f) args)), s, _, h => by
    simp only [execF] at h ⊢; exact stmtCallF_mono c hrc vars f args s h
  | .ExprStmtCall (.Call (.inl prim) args), s, _, h => by
    simp only [execF] at h ⊢; exact stmtPrimF_mono c hrc [] prim args s h
  | .ExprStmtCall (.Call (.inr f) args), s, _, h => by
    simp only [execF] at h ⊢; exact stmtCallF_mono c hrc [] f args s h
  | .ExprStmtCall (.Var _), _, _, h => by simpa only [execF] using h
  | .ExprStmtCall (.Lit _), _, _, h => by simpa only [execF] using h
  | .If cond body, s, _, h => by
    rcases hev : evalF c rc cond s with _ | ⟨_ | ⟨s₁, v⟩, g₀⟩
    · simp [execF, hev] at h
    · simp only [execF, hev] at h; simp only [execF, evalF_mono c hrc cond s hev]; exact h
    · simp only [execF, hev] at h; simp only [execF, evalF_mono c hrc cond s hev]
      by_cases hv : v = ⟨0⟩
      · simp only [hv, ne_eq, not_true_eq_false, if_false] at h ⊢; exact h
      · simp only [hv, ne_eq, not_false_eq_true, if_true] at h ⊢
        rcases hb : blockF c rc n body s₁ with _ | ⟨r, g⟩
        · simp [hb, addGas] at h
        · rw [blockF_mono hrc hn body s₁ hb]; rw [hb] at h; exact h
  | .Switch cond cases dflt, s, _, h => by
    rcases hev : evalF c rc cond s with _ | ⟨_ | ⟨s₁, v⟩, g₀⟩
    · simp [execF, hev] at h
    · simp only [execF, hev] at h; simp only [execF, evalF_mono c hrc cond s hev]; exact h
    · simp only [execF, hev] at h; simp only [execF, evalF_mono c hrc cond s hev]
      rcases hd : blockF c rc n dflt s₁ with _ | ⟨r, gd⟩
      · simp [hd] at h
      · rw [blockF_mono hrc hn dflt s₁ hd]; rw [hd] at h
        rcases r with e | s₂
        · exact h
        · simp only at h ⊢
          rcases hcs : casesF c rc n cases v s₁ with _ | oo
          · simp [hcs] at h
          · rw [casesF_mono hrc hn cases v s₁ hcs]; rw [hcs] at h; exact h
  | .For cond post body, s, o, h => by
    simp only [execF] at h ⊢
    exact loopF_mono c (fun s _ h => evalF_mono c hrc cond s h)
      (fun s _ h => blockF_mono hrc hn body s h) (fun s _ h => blockF_mono hrc hn post s h)
      n n' s o hn h
  | .Continue, _, _, h => by simpa only [execF] using h
  | .Break, _, _, h => by simpa only [execF] using h
  | .Leave, _, _, h => by simpa only [execF] using h

theorem blockF_mono {rc rc' : Runner} (hrc : RunnerExt rc rc') {n n' : ℕ} (hn : n ≤ n') :
    (sts : List Stmt) → (s : State) → {o : Res × ℕ} → blockF c rc n sts s = some o →
      blockF c rc' n' sts s = some o
  | [], _, _, h => by simpa only [blockF] using h
  | st :: sts, s, _, h => by
    rcases hx : execF c rc n st s with _ | ⟨r₀, g₀⟩
    · simp [blockF, hx] at h
    · have h' := execF_mono hrc hn st s hx
      rcases r₀ with e | (⟨ss, vs⟩ | _ | j)
      · simp only [blockF, hx, h'] at h ⊢; exact h
      · simp only [blockF, hx, h'] at h ⊢
        rcases hb : blockF c rc n sts (.Ok ss vs) with _ | ⟨r, g⟩
        · simp [hb, addGas] at h
        · rw [blockF_mono hrc hn sts _ hb]; rw [hb] at h; exact h
      · simp only [blockF, hx, h'] at h ⊢; exact h
      · simp only [blockF, hx, h'] at h ⊢; exact h

theorem casesF_mono {rc rc' : Runner} (hrc : RunnerExt rc rc') {n n' : ℕ} (hn : n ≤ n') :
    (cases : List (Literal × List Stmt)) → (v : Literal) → (s : State) →
    {oo : Option (Res × ℕ)} → casesF c rc n cases v s = some oo → casesF c rc' n' cases v s = some oo
  | [], _, _, _, h => by simpa only [casesF] using h
  | (l, body) :: rest, v, s, _, h => by
    by_cases hl : l = v
    · simp only [casesF, hl, if_true] at h ⊢
      rcases hb : blockF c rc n body s with _ | ⟨r, g⟩
      · simp [hb] at h
      · rw [blockF_mono hrc hn body s hb]; rw [hb] at h; exact h
    · simp only [casesF, hl, if_false] at h ⊢; exact casesF_mono hrc hn rest v s h

end

/-- The call runner is monotone in both budgets. -/
theorem callF_mono (co : Option YulContract) {n n' : ℕ} (hn : n ≤ n') :
    ∀ {d d' : ℕ}, d ≤ d' → RunnerExt (callF c co n d) (callF c co n' d')
  | 0, _, _ => by intro args f s o h; simp [callF] at h
  | d + 1, d', hd => by
    obtain ⟨d', rfl⟩ : ∃ j, d' = j + 1 := ⟨d' - 1, by omega⟩
    intro args f s o h
    simp only [callF] at h ⊢
    rcases hl : lookupFunction (some f) co s with e | fd
    · simp only [hl] at h ⊢; exact h
    · simp only [hl] at h ⊢
      rcases hb : blockF c (callF c co n d) n fd.body (State.mkOk (s.initcall fd.params args))
        with _ | ⟨r, g⟩
      · simp [hb] at h
      · rw [blockF_mono c (callF_mono co hn (d := d) (d' := d') (by omega)) hn _ _ hb]
        rw [hb] at h; exact h

/-- **Budget monotonicity.** A run that fits in budgets `n`, `d` gives the same result and gas with
all larger budgets. -/
theorem runF_mono {co : Option YulContract} {n n' d d' : ℕ} (hn : n ≤ n') (hd : d ≤ d')
    {st : Stmt} {s : State} {o : Res × ℕ} (h : runF c co n d st s = some o) :
    runF c co n' d' st s = some o :=
  execF_mono c (callF_mono c co hn hd) hn st s h

/-- Successful runs with different budgets agree (result and gas). -/
theorem runF_budget_indep {co : Option YulContract} {n n' d d' : ℕ} {st : Stmt} {s : State}
    {o o' : Res × ℕ} (h : runF c co n d st s = some o) (h' : runF c co n' d' st s = some o') :
    o = o' := by
  have a := runF_mono c (le_max_left n n') (le_max_left d d') h
  have b := runF_mono c (le_max_right n n') (le_max_right d d') h'
  rw [a] at b; exact Option.some.inj b

end Gas
end Yul
end EvmYul
