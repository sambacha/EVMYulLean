module

public import EvmYul.Yul.Ast

public section

/-!
# Well-scoped Yul programs

The interpreter reads a variable with `s[x]!`, which silently returns `0` for a variable that was
never declared, and it accepts `break`/`continue` outside a loop and `leave` outside a function
(the result is then a stray checkpoint state). The Yul specification rejects all of these
statically. This file adds that static check **without changing the AST**:

* `checkStmt`/`checkBlock` — a scope checker. It returns the scope after the statement (`let`
  extends it, blocks discard their local declarations), or `none` if the statement uses an
  undeclared variable, or `break`/`continue`/`leave` in the wrong place.
* `WellScoped p` — `p` passes the checker from the empty scope, at top level. It is decidable.
* `ScopedStmt := {p : Stmt // WellScoped p}` — the subtype of well-scoped programs, with the
  smart constructor `ScopedStmt.ofStmt?`.
* `FunctionDefinition.WellScoped`, `YulContract.WellScoped` — function bodies are checked with
  their parameters and return variables in scope, with `leave` allowed.

The interpreter's AST has no assignment statement: `x := e` is encoded as `Let [x] (some e)` on an
existing variable. Re-declaration is therefore accepted (it is assignment). Calls to user functions
(`Sum.inr f`) are not resolved here: the function table lives in the contract, not in the
statement.

Proved facts: the checker only grows scopes (`checkStmt_extends`), it is monotone in the scope
(`checkStmt_mono`: well-scoped code stays well-scoped under more declarations), and the
specification-style rules hold as lemmas (`wellScoped_*`). `ill_scoped_read_defaults_to_zero`
and `stray_break_escapes` in `EvmYul/Yul/Relational/Examples.lean` show the interpreter behaviour
the check excludes.
-/

namespace EvmYul
namespace Yul

open Ast

/-- Variables in scope. -/
abbrev Scope := List Identifier

@[expose] section

/-- Where a statement occurs: inside a loop body, inside a function body. -/
structure ScopeCtx where
  inLoop : Bool := false
  inFun : Bool := false
  deriving DecidableEq, Repr

end

mutual
  /-- Every variable read by the expression is in scope. -/
  @[expose] def exprScoped (sc : Scope) : Expr → Bool
    | .Var x => decide (x ∈ sc)
    | .Lit _ => true
    | .Call _ args => argsScoped sc args

  /-- Every variable read by the arguments is in scope. -/
  @[expose] def argsScoped (sc : Scope) : List Expr → Bool
    | [] => true
    | a :: as => exprScoped sc a && argsScoped sc as
end

mutual
  /-- Scope check of a statement; `some sc'` is the scope after it. -/
  @[expose] def checkStmt (sc : Scope) (ctx : ScopeCtx) : Stmt → Option Scope
    | .Block sts => (checkBlock sc ctx sts).map fun _ => sc
    | .Let vars none => some (vars ++ sc)
    | .Let vars (some e) => if exprScoped sc e then some (vars ++ sc) else none
    | .ExprStmtCall e => if exprScoped sc e then some sc else none
    | .Switch c cases dflt =>
      if exprScoped sc c && checkCases sc ctx cases && (checkBlock sc ctx dflt).isSome
      then some sc else none
    | .For c post body =>
      if exprScoped sc c && (checkBlock sc { ctx with inLoop := false } post).isSome &&
          (checkBlock sc { ctx with inLoop := true } body).isSome
      then some sc else none
    | .If c body =>
      if exprScoped sc c && (checkBlock sc ctx body).isSome then some sc else none
    | .Continue => if ctx.inLoop then some sc else none
    | .Break => if ctx.inLoop then some sc else none
    | .Leave => if ctx.inFun then some sc else none

  /-- Scope check of a statement list, threading the scope. -/
  @[expose] def checkBlock (sc : Scope) (ctx : ScopeCtx) : List Stmt → Option Scope
    | [] => some sc
    | st :: sts =>
      match checkStmt sc ctx st with
      | some sc' => checkBlock sc' ctx sts
      | none => none

  /-- Every case body of a `switch` is well scoped. -/
  def checkCases (sc : Scope) (ctx : ScopeCtx) : List (Literal × List Stmt) → Bool
    | [] => true
    | (_, body) :: cases => (checkBlock sc ctx body).isSome && checkCases sc ctx cases
end

/-- A top-level program is well scoped. -/
@[expose] def WellScoped (p : Stmt) : Prop := (checkStmt [] {} p).isSome

@[expose] instance (p : Stmt) : Decidable (WellScoped p) := inferInstanceAs (Decidable (_ = _))

/-- Well-scoped programs. -/
abbrev ScopedStmt := {p : Stmt // WellScoped p}

/-- Accept a program if (and only if) it is well scoped. -/
def ScopedStmt.ofStmt? (p : Stmt) : Option ScopedStmt :=
  if h : WellScoped p then some ⟨p, h⟩ else none

theorem ScopedStmt.ofStmt?_isSome_iff (p : Stmt) : (ScopedStmt.ofStmt? p).isSome ↔ WellScoped p := by
  unfold ScopedStmt.ofStmt?; split <;> simp_all

theorem ScopedStmt.ofStmt?_val {p : Stmt} {q : ScopedStmt} (h : ScopedStmt.ofStmt? p = some q) :
    q.val = p := by
  unfold ScopedStmt.ofStmt? at h; split at h <;> simp_all; rw [← h]

/-- A function body is well scoped with its parameters and return variables in scope. -/
@[expose] def Ast.FunctionDefinition.WellScoped : FunctionDefinition → Prop
  | .Def params rets body => (checkBlock (params ++ rets) { inFun := true } body).isSome

@[expose] instance (f : FunctionDefinition) : Decidable f.WellScoped := by
  cases f; unfold Ast.FunctionDefinition.WellScoped; infer_instance

/-- A contract is well scoped: its dispatcher and all its functions. -/
@[expose] def Ast.YulContract.WellScoped (c : YulContract) : Prop :=
  Yul.WellScoped c.dispatcher ∧ ∀ f ∈ c.functions, ∀ d ∈ c.functions.lookup f, d.WellScoped

/-! ## The checker only grows scopes, and is monotone -/

private theorem append_subset_of_subset {vars sc sc₂ : Scope} (hsub : sc ⊆ sc₂) :
    vars ++ sc ⊆ vars ++ sc₂ := by
  intro a ha
  simp only [List.mem_append] at ha ⊢
  exact ha.imp id (fun h => hsub h)

mutual
  theorem checkStmt_extends {sc sc' : Scope} {ctx : ScopeCtx} :
      ∀ {st : Stmt}, checkStmt sc ctx st = some sc' → sc ⊆ sc'
    | .Block sts, h => by
      simp only [checkStmt, Option.map_eq_some_iff] at h
      obtain ⟨_, _, rfl⟩ := h; exact List.Subset.refl _
    | .Let vars none, h => by
      simp only [checkStmt, Option.some.injEq] at h; subst h; exact List.subset_append_right _ _
    | .Let vars (some e), h => by
      simp only [checkStmt] at h; split at h <;> simp_all
      subst h; exact List.subset_append_right _ _
    | .ExprStmtCall e, h => by simp only [checkStmt] at h; split at h <;> simp_all
    | .Switch c cases dflt, h => by simp only [checkStmt] at h; split at h <;> simp_all
    | .For c post body, h => by simp only [checkStmt] at h; split at h <;> simp_all
    | .If c body, h => by simp only [checkStmt] at h; split at h <;> simp_all
    | .Continue, h => by simp only [checkStmt] at h; split at h <;> simp_all
    | .Break, h => by simp only [checkStmt] at h; split at h <;> simp_all
    | .Leave, h => by simp only [checkStmt] at h; split at h <;> simp_all

  theorem checkBlock_extends {sc sc' : Scope} {ctx : ScopeCtx} :
      ∀ {sts : List Stmt}, checkBlock sc ctx sts = some sc' → sc ⊆ sc'
    | [], h => by simp only [checkBlock, Option.some.injEq] at h; subst h; exact List.Subset.refl _
    | st :: sts, h => by
      simp only [checkBlock] at h
      split at h
      · rename_i sc₁ h₁
        exact List.Subset.trans (checkStmt_extends h₁) (checkBlock_extends h)
      · simp at h
end

mutual
  theorem exprScoped_mono {sc sc₂ : Scope} (hsub : sc ⊆ sc₂) :
      ∀ {e : Expr}, exprScoped sc e = true → exprScoped sc₂ e = true
    | .Var x, h => by simp only [exprScoped, decide_eq_true_eq] at h ⊢; exact hsub h
    | .Lit _, _ => rfl
    | .Call _ args, h => by simp only [exprScoped] at h ⊢; exact argsScoped_mono hsub h

  theorem argsScoped_mono {sc sc₂ : Scope} (hsub : sc ⊆ sc₂) :
      ∀ {as : List Expr}, argsScoped sc as = true → argsScoped sc₂ as = true
    | [], _ => rfl
    | a :: as, h => by
      simp only [argsScoped, Bool.and_eq_true] at h ⊢
      exact ⟨exprScoped_mono hsub h.1, argsScoped_mono hsub h.2⟩
end

mutual
  /-- **Weakening.** Code that is well scoped stays well scoped when more variables are in
  scope, and the resulting scope grows accordingly. -/
  theorem checkStmt_mono {sc sc₂ sc' : Scope} {ctx : ScopeCtx} (hsub : sc ⊆ sc₂) :
      ∀ {st : Stmt}, checkStmt sc ctx st = some sc' →
        ∃ sc₂', checkStmt sc₂ ctx st = some sc₂' ∧ sc' ⊆ sc₂'
    | .Block sts, h => by
      simp only [checkStmt, Option.map_eq_some_iff] at h ⊢
      obtain ⟨sc₁, h₁, rfl⟩ := h
      obtain ⟨sc₃, h₃, _⟩ := checkBlock_mono hsub h₁
      exact ⟨sc₂, ⟨sc₃, h₃, rfl⟩, hsub⟩
    | .Let vars none, h => by
      simp only [checkStmt, Option.some.injEq] at h ⊢; subst h
      exact ⟨_, rfl, append_subset_of_subset hsub⟩
    | .Let vars (some e), h => by
      simp only [checkStmt] at h ⊢
      split at h
      · rename_i he
        simp only [Option.some.injEq] at h; subst h
        rw [if_pos (exprScoped_mono hsub he)]
        exact ⟨_, rfl, append_subset_of_subset hsub⟩
      · simp at h
    | .ExprStmtCall e, h => by
      simp only [checkStmt] at h ⊢
      split at h
      · rename_i he
        simp only [Option.some.injEq] at h; subst h
        rw [if_pos (exprScoped_mono hsub he)]
        exact ⟨_, rfl, hsub⟩
      · simp at h
    | .Switch c cases dflt, h => by
      simp only [checkStmt] at h ⊢
      split at h
      · rename_i hc
        simp only [Option.some.injEq] at h; subst h
        simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hc
        obtain ⟨⟨hc1, hc2⟩, ⟨d, hd⟩⟩ := hc
        obtain ⟨d', hd', _⟩ := checkBlock_mono hsub hd
        rw [if_pos (by simp [exprScoped_mono hsub hc1, checkCases_mono hsub hc2, hd'])]
        exact ⟨_, rfl, hsub⟩
      · simp at h
    | .For c post body, h => by
      simp only [checkStmt] at h ⊢
      split at h
      · rename_i hc
        simp only [Option.some.injEq] at h; subst h
        simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hc
        obtain ⟨⟨hc1, ⟨p, hp⟩⟩, ⟨b, hb⟩⟩ := hc
        obtain ⟨p', hp', _⟩ := checkBlock_mono hsub hp
        obtain ⟨b', hb', _⟩ := checkBlock_mono hsub hb
        rw [if_pos (by simp [exprScoped_mono hsub hc1, hp', hb'])]
        exact ⟨_, rfl, hsub⟩
      · simp at h
    | .If c body, h => by
      simp only [checkStmt] at h ⊢
      split at h
      · rename_i hc
        simp only [Option.some.injEq] at h; subst h
        simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hc
        obtain ⟨hc1, ⟨b, hb⟩⟩ := hc
        obtain ⟨b', hb', _⟩ := checkBlock_mono hsub hb
        rw [if_pos (by simp [exprScoped_mono hsub hc1, hb'])]
        exact ⟨_, rfl, hsub⟩
      · simp at h
    | .Continue, h => by
      simp only [checkStmt] at h ⊢; split at h <;> simp_all
    | .Break, h => by
      simp only [checkStmt] at h ⊢; split at h <;> simp_all
    | .Leave, h => by
      simp only [checkStmt] at h ⊢; split at h <;> simp_all

  theorem checkBlock_mono {sc sc₂ sc' : Scope} {ctx : ScopeCtx} (hsub : sc ⊆ sc₂) :
      ∀ {sts : List Stmt}, checkBlock sc ctx sts = some sc' →
        ∃ sc₂', checkBlock sc₂ ctx sts = some sc₂' ∧ sc' ⊆ sc₂'
    | [], h => by
      simp only [checkBlock, Option.some.injEq] at h ⊢; subst h; exact ⟨_, rfl, hsub⟩
    | st :: sts, h => by
      simp only [checkBlock] at h ⊢
      split at h
      · rename_i sc₁ h₁
        obtain ⟨sc₃, h₃, hsub₃⟩ := checkStmt_mono hsub h₁
        rw [h₃]
        exact checkBlock_mono hsub₃ h
      · simp at h

  theorem checkCases_mono {sc sc₂ : Scope} {ctx : ScopeCtx} (hsub : sc ⊆ sc₂) :
      ∀ {cases : List (Literal × List Stmt)}, checkCases sc ctx cases = true →
        checkCases sc₂ ctx cases = true
    | [], _ => rfl
    | (_, body) :: cases, h => by
      simp only [checkCases, Bool.and_eq_true, Option.isSome_iff_exists] at h ⊢
      obtain ⟨⟨b, hb⟩, hc⟩ := h
      obtain ⟨b', hb', _⟩ := checkBlock_mono hsub hb
      exact ⟨⟨b', hb'⟩, checkCases_mono hsub hc⟩
end

/-! ## Specification-style rules -/

theorem wellScoped_block_iff (sts : List Stmt) :
    WellScoped (.Block sts) ↔ (checkBlock [] {} sts).isSome := by
  simp [WellScoped, checkStmt]

/-- `break` is never well scoped at top level (it must be inside a loop body). -/
theorem not_wellScoped_break : ¬ WellScoped .Break := by
  simp [WellScoped, checkStmt]

/-- `leave` is never well scoped at top level (it must be inside a function body). -/
theorem not_wellScoped_leave : ¬ WellScoped .Leave := by
  simp [WellScoped, checkStmt]

/-- A variable read is well scoped only if the variable was declared earlier in the block. -/
theorem checkBlock_let_var {sc : Scope} {ctx : ScopeCtx} {x y : Identifier} {sts : List Stmt} :
    checkBlock sc ctx (.Let [x] (some (.Var y)) :: sts) =
      if y ∈ sc then checkBlock (x :: sc) ctx sts else none := by
  by_cases hy : y ∈ sc <;> simp [checkBlock, checkStmt, exprScoped, hy]

/-- Declarations made inside a nested block are not visible after it. -/
theorem checkStmt_block_scope {sc : Scope} {ctx : ScopeCtx} {sts : List Stmt} {sc' : Scope}
    (h : checkStmt sc ctx (.Block sts) = some sc') : sc' = sc := by
  simp only [checkStmt, Option.map_eq_some_iff] at h
  obtain ⟨_, _, rfl⟩ := h; rfl

/-- `break`/`continue` in a loop body are well scoped; in the post block they are not. -/
theorem checkStmt_for_break_body {sc : Scope} {ctx : ScopeCtx} {c : Expr} (hc : exprScoped sc c) :
    checkStmt sc ctx (.For c [] [.Break]) = some sc ∧
      checkStmt sc ctx (.For c [.Break] []) = none := by
  simp [checkStmt, checkBlock, hc]

end Yul
end EvmYul
