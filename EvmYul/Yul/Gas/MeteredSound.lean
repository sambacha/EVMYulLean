module

public import EvmYul.Yul.Gas.Metered
public import EvmYul.ProofTags

public section

/-!
# Yul gas, part 3: the metered evaluator is the relational semantics

* `execG_sound`: every result of `execG` other than running out of fuel is an `ExecR` run. This
  holds for **every** program (outside the fragment `execG` answers `OutOfFuel`).
* `execG_complete`: on the fragment, every `ExecR` run has exactly the result of `execG`.
* `exec_eq_execG`: so every run of the interpreter `exec` that does not run out of fuel returns the
  metered result, and (`exec_gas_bound`) its gas under any cost model is at most `gasS`.
-/

namespace EvmYul
namespace Yul
namespace Gas

open Ast Relational

/-! ## Evaluating one more argument -/

theorem ArgsR.snoc_err {co : Option YulContract} {a : Expr} :
    ∀ {l : List Expr} {s : State} {e : Yul.Exception},
    ArgsR co l s (.error e) → ArgsR co (l ++ [a]) s (.error e)
  | [], _, _, h => by cases h
  | b :: l, s, e, h => by
    generalize hr : (Except.error e : ResL) = r at h
    cases h with
    | consErr hb => cases hr; exact .consErr hb
    | @cons _ _ _ _ s₁ v r' hb hl =>
      rcases r' with e' | ⟨s', vs'⟩
      · simp only [cons', Except.error.injEq] at hr
        subst hr
        exact .cons hb (ArgsR.snoc_err hl)
      · simp [cons'] at hr

theorem ArgsR.snoc_evalErr {co : Option YulContract} {a : Expr} :
    ∀ {l : List Expr} {s s₁ : State} {vs : List Literal} {e : Yul.Exception},
    ArgsR co l s (.ok (s₁, vs)) → EvalR co a s₁ (.error e) → ArgsR co (l ++ [a]) s (.error e)
  | [], s, s₁, vs, e, h, ha => by
    generalize hr : (Except.ok (s₁, vs) : ResL) = r at h
    cases h with
    | nil => cases hr; exact .consErr ha
  | b :: l, s, s₁, vs, e, h, ha => by
    generalize hr : (Except.ok (s₁, vs) : ResL) = r at h
    cases h with
    | consErr hb => cases hr
    | @cons _ _ _ _ s' v r' hb hl =>
      rcases r' with e' | ⟨s'', vs'⟩
      · simp [cons'] at hr
      · simp only [cons', Except.ok.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        exact .cons hb (ArgsR.snoc_evalErr hl ha)

theorem ArgsR.snoc_ok {co : Option YulContract} {a : Expr} :
    ∀ {l : List Expr} {s s₁ s₂ : State} {vs : List Literal} {v : Literal},
    ArgsR co l s (.ok (s₁, vs)) → EvalR co a s₁ (.ok (s₂, v)) →
      ArgsR co (l ++ [a]) s (.ok (s₂, vs ++ [v]))
  | [], s, s₁, s₂, vs, v, h, ha => by
    generalize hr : (Except.ok (s₁, vs) : ResL) = r at h
    cases h with
    | nil => cases hr; exact .cons ha (.nil s₂)
  | b :: l, s, s₁, s₂, vs, v, h, ha => by
    generalize hr : (Except.ok (s₁, vs) : ResL) = r at h
    cases h with
    | consErr hb => cases hr
    | @cons _ _ _ _ s' v' r' hb hl =>
      rcases r' with e' | ⟨s'', vs'⟩
      · simp [cons'] at hr
      · simp only [cons', Except.ok.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        exact .cons hb (ArgsR.snoc_ok hl ha)

/-- Inversion: how `l ++ [a]` can be evaluated. -/
theorem ArgsR.snoc_inv {co : Option YulContract} {a : Expr} :
    ∀ {l : List Expr} {s : State} {r : ResL}, ArgsR co (l ++ [a]) s r →
      (∃ e, ArgsR co l s (.error e) ∧ r = .error e) ∨
      (∃ s₁ vs, ArgsR co l s (.ok (s₁, vs)) ∧
        ((∃ e, EvalR co a s₁ (.error e) ∧ r = .error e) ∨
         (∃ s₂ v, EvalR co a s₁ (.ok (s₂, v)) ∧ r = .ok (s₂, vs ++ [v]))))
  | [], s, r, h => by
    cases h with
    | consErr ha => exact .inr ⟨s, [], .nil s, .inl ⟨_, ha, rfl⟩⟩
    | @cons _ _ _ _ s₁ v r' ha hl =>
      cases hl with
      | nil => exact .inr ⟨s, [], .nil s, .inr ⟨s₁, v, ha, rfl⟩⟩
  | b :: l, s, r, h => by
    cases h with
    | consErr hb => exact .inl ⟨_, .consErr hb, rfl⟩
    | @cons _ _ _ _ s₁ v r' hb hl =>
      rcases ArgsR.snoc_inv hl with ⟨e, hl', rfl⟩ | ⟨s₂, vs, hl', (⟨e, ha, rfl⟩ | ⟨s₃, w, ha, rfl⟩)⟩
      · exact .inl ⟨e, .cons hb hl', rfl⟩
      · exact .inr ⟨s₂, v :: vs, .cons hb hl', .inl ⟨e, ha, rfl⟩⟩
      · exact .inr ⟨s₂, v :: vs, .cons hb hl', .inr ⟨s₃, w, ha, rfl⟩⟩

/-- A builtin whose result is not "out of fuel" is a `PrimR` step (with the dispatcher that always
runs out of fuel, which is trivially `DispatchR`-correct up to fuel). -/
theorem primR_primResult {s : State} {prim : PrimOp} {args : List Literal}
    (h : primResult s prim args ≠ OOF) : PrimR s prim args (primResult s prim args) :=
  PrimR.mk _ (fun co s' => DispatchOrOOF.outOfFuel co s') h

variable (c : CostModel)

theorem casesG_eq_none : ∀ {cases : List (Literal × List Stmt)} {v : Literal} {s : State},
    casesG c cases v s = none → selectCase v cases = none
  | [], _, _, _ => rfl
  | (l, body) :: rest, v, s, h => by
    by_cases hl : l = v
    · simp [casesG, hl] at h
    · simp only [casesG, hl, if_false] at h
      simp only [selectCase, hl, if_false]
      exact casesG_eq_none h

theorem casesG_of_selectCase_none : ∀ {cases : List (Literal × List Stmt)} {v : Literal} {s : State},
    selectCase v cases = none → casesG c cases v s = none
  | [], _, _, _ => rfl
  | (l, body) :: rest, v, s, h => by
    by_cases hl : l = v
    · simp [selectCase, hl] at h
    · simp only [selectCase, hl, if_false] at h
      simp only [casesG, hl, if_false]
      exact casesG_of_selectCase_none h

/-! ## Soundness: `execG` runs are `ExecR` runs -/

mutual

theorem evalG_sound (co : Option YulContract) : (e : Expr) → (s : State) →
    (evalG c e s).1 ≠ OOF → EvalR co e s (evalG c e s).1
  | .Lit v, s, _ => by simp only [evalG]; exact .lit v s
  | .Var x, s, _ => by simp only [evalG]; exact .var x s
  | .Call (.inl prim) args, s, h => by
    rcases ha : argsG c args s with ⟨_ | ⟨s₁, vs⟩, g⟩
    · simp only [evalG, ha] at h ⊢
      have ih := argsG_sound co args s (by rw [ha]; dsimp only; exact err_ne_oof h)
      rw [ha] at ih
      exact .primArgsErr ih
    · simp only [evalG, ha] at h ⊢
      have ih := argsG_sound co args s (by rw [ha]; simp [OOF])
      rw [ha] at ih
      exact .prim ih (primR_primResult (head'_ne_oof h))
  | .Call (.inr _) _, _, h => by simp [evalG, OOF] at h

theorem argsG_sound (co : Option YulContract) : (as : List Expr) → (s : State) →
    (argsG c as s).1 ≠ OOF → ArgsR co as.reverse s (argsG c as s).1
  | [], s, _ => by simp only [argsG, List.reverse_nil]; exact .nil s
  | a :: as, s, h => by
    rw [List.reverse_cons]
    rcases ha : argsG c as s with ⟨_ | ⟨s₁, vs⟩, g⟩
    · simp only [argsG, ha] at h ⊢
      have ih := argsG_sound co as s (by rw [ha]; dsimp only; exact err_ne_oof h)
      rw [ha] at ih
      exact ArgsR.snoc_err ih
    · have ih := argsG_sound co as s (by rw [ha]; simp [OOF])
      rw [ha] at ih
      rcases he : evalG c a s₁ with ⟨_ | ⟨s₂, v⟩, g'⟩
      · simp only [argsG, ha, he] at h ⊢
        have iha := evalG_sound co a s₁ (by rw [he]; dsimp only; exact err_ne_oof h)
        rw [he] at iha
        exact ArgsR.snoc_evalErr ih iha
      · simp only [argsG, ha, he]
        have iha := evalG_sound co a s₁ (by rw [he]; simp [OOF])
        rw [he] at iha
        exact ArgsR.snoc_ok ih iha

end

mutual

theorem execG_sound (co : Option YulContract) : (st : Stmt) → (s : State) →
    (execG c st s).1 ≠ OOF → ExecR co st s (execG c st s).1
  | .Block sts, s, h => by
    simp only [execG] at h ⊢
    exact blockG_sound co sts s h
  | .Let vars none, s, _ => by simp only [execG]; exact .letNone vars s
  | .Let vars (some (.Var x)), s, _ => by simp only [execG]; exact .letVar vars x s
  | .Let vars (some (.Lit v)), s, _ => by simp only [execG]; exact .letLit vars v s
  | .Let vars (some (.Call (.inl prim) args)), s, h => by
    rcases ha : argsG c args s with ⟨_ | ⟨s₁, vs⟩, g⟩
    · simp only [execG, ha] at h ⊢
      have ih := argsG_sound c co args s (by rw [ha]; dsimp only; exact err_ne_oof h)
      rw [ha] at ih
      exact .letPrimArgsErr ih
    · simp only [execG, ha] at h ⊢
      have ih := argsG_sound c co args s (by rw [ha]; simp [OOF])
      rw [ha] at ih
      exact .letPrim ih (primR_primResult (multifill'_ne_oof h))
  | .Let _ (some (.Call (.inr _) _)), _, h => by simp [execG, OOF] at h
  | .ExprStmtCall (.Call (.inl prim) args), s, h => by
    rcases ha : argsG c args s with ⟨_ | ⟨s₁, vs⟩, g⟩
    · simp only [execG, ha] at h ⊢
      have ih := argsG_sound c co args s (by rw [ha]; dsimp only; exact err_ne_oof h)
      rw [ha] at ih
      exact .exprPrimArgsErr ih
    · simp only [execG, ha] at h ⊢
      have ih := argsG_sound c co args s (by rw [ha]; simp [OOF])
      rw [ha] at ih
      exact .exprPrim ih (primR_primResult (multifill'_ne_oof h))
  | .ExprStmtCall (.Call (.inr _) _), _, h => by simp [execG, OOF] at h
  | .ExprStmtCall (.Var x), s, _ => by simp only [execG]; exact .exprVar x s
  | .ExprStmtCall (.Lit v), s, _ => by simp only [execG]; exact .exprLit v s
  | .If cond body, s, h => by
    rcases hc : evalG c cond s with ⟨_ | ⟨s₁, v⟩, g⟩
    · simp only [execG, hc] at h ⊢
      have ih := evalG_sound c co cond s (by rw [hc]; dsimp only; exact err_ne_oof h)
      rw [hc] at ih
      exact .ifErr ih
    · have ih := evalG_sound c co cond s (by rw [hc]; simp [OOF])
      rw [hc] at ih
      by_cases hv : v = ⟨0⟩
      · simp only [execG, hc, hv, ne_eq, not_true_eq_false, if_false]
        exact .ifFalse ih hv
      · rcases hb : blockG c body s₁ with ⟨r, g'⟩
        simp only [execG, hc, hv, hb, ne_eq, not_false_eq_true, if_true] at h ⊢
        have ihb := blockG_sound co body s₁ (by rw [hb]; dsimp only; exact h)
        rw [hb] at ihb
        exact .ifTrue ih hv ihb
  | .Switch cond cases dflt, s, h => by
    rcases hc : evalG c cond s with ⟨_ | ⟨s₁, v⟩, g⟩
    · simp only [execG, hc] at h ⊢
      have ih := evalG_sound c co cond s (by rw [hc]; dsimp only; exact err_ne_oof h)
      rw [hc] at ih
      exact .switchCondErr ih
    · have ih := evalG_sound c co cond s (by rw [hc]; simp [OOF])
      rw [hc] at ih
      rcases hd : blockG c dflt s₁ with ⟨_ | s₂, gd⟩
      · simp only [execG, hc, hd] at h ⊢
        have ihd := blockG_sound co dflt s₁ (by rw [hd]; dsimp only; exact err_ne_oof h)
        rw [hd] at ihd
        exact .switchDefaultErr ih ihd
      · have ihd := blockG_sound co dflt s₁ (by rw [hd]; simp [OOF])
        rw [hd] at ihd
        rcases hcs : casesG c cases v s₁ with _ | ⟨r, gb⟩
        · simp only [execG, hc, hd, hcs]
          exact .switchDefault ih ihd (casesG_eq_none c hcs)
        · simp only [execG, hc, hd, hcs] at h ⊢
          obtain ⟨body, hsel, hbody⟩ := casesG_sound co cases v s₁ hcs h
          exact .switchCase ih ihd hsel hbody
  | .For _ _ _, _, h => by simp [execG, OOF] at h
  | .Continue, s, _ => by simp only [execG]; exact .continue_ s
  | .Break, s, _ => by simp only [execG]; exact .break_ s
  | .Leave, s, _ => by simp only [execG]; exact .leave s

theorem blockG_sound (co : Option YulContract) : (sts : List Stmt) → (s : State) →
    (blockG c sts s).1 ≠ OOF → ExecR co (.Block sts) s (blockG c sts s).1
  | [], s, _ => by simp only [blockG]; exact .blockNil s
  | st :: sts, s, h => by
    rcases he : execG c st s with ⟨r, g⟩
    rcases r with e | (⟨ss, vs⟩ | _ | j)
    · simp only [blockG, he] at h ⊢
      have ih := execG_sound co st s (by rw [he]; dsimp only; exact err_ne_oof h)
      rw [he] at ih
      exact .blockErr ih
    · have ih := execG_sound co st s (by rw [he]; simp [OOF])
      rw [he] at ih
      rcases hb : blockG c sts (.Ok ss vs) with ⟨r', g'⟩
      simp only [blockG, he, hb] at h ⊢
      have ihb := blockG_sound co sts (.Ok ss vs) (by rw [hb]; dsimp only; exact h)
      rw [hb] at ihb
      exact .blockCons ih ihb
    · have ih := execG_sound co st s (by rw [he]; simp [OOF])
      rw [he] at ih
      simp only [blockG, he]
      exact .blockOOF ih
    · have ih := execG_sound co st s (by rw [he]; simp [OOF])
      rw [he] at ih
      simp only [blockG, he]
      exact .blockJump ih

theorem casesG_sound (co : Option YulContract) : (cases : List (Literal × List Stmt)) →
    (v : Literal) → (s : State) → {r : Res} → {g : ℕ} → casesG c cases v s = some (r, g) →
    r ≠ OOF → ∃ body, selectCase v cases = some body ∧ ExecR co (.Block body) s r
  | [], _, _, _, _, h, _ => by simp [casesG] at h
  | (l, body) :: rest, v, s, r, g, h, hr => by
    by_cases hl : l = v
    · simp only [casesG, hl, if_true, Option.some.injEq] at h
      refine ⟨body, by simp [selectCase, hl], ?_⟩
      have := blockG_sound co body s (by rw [h]; dsimp only; exact hr)
      rwa [h] at this
    · simp only [casesG, hl, if_false] at h
      obtain ⟨b, hsel, hb⟩ := casesG_sound co rest v s h hr
      exact ⟨b, by simp [selectCase, hl, hsel], hb⟩

end

/-! ## Completeness: on the fragment, every `ExecR` run is the `execG` run -/

@[reviewed_generic "pair projection helper"]
theorem fst_eq_elim {α β : Type} {p : α × β} {a : α} (h : a = p.1) : ∃ g, p = (a, g) :=
  ⟨p.2, by cases p; simp_all⟩

mutual

theorem evalG_complete (co : Option YulContract) : (e : Expr) → (s : State) → fragE e = true →
    {r : ResV} → EvalR co e s r → r = (evalG c e s).1
  | .Lit _, _, _, _, h => by cases h; rfl
  | .Var _, _, _, _, h => by cases h; rfl
  | .Call (.inl prim) args, s, hf, _, h => by
    simp only [fragE, Bool.and_eq_true, decide_eq_true_eq] at hf
    cases h with
    | primArgsErr ha =>
      obtain ⟨g, hag⟩ := fst_eq_elim (argsG_complete co args s hf.2 ha)
      simp only [evalG, hag]
    | prim ha hP =>
      obtain ⟨g, hag⟩ := fst_eq_elim (argsG_complete co args s hf.2 ha)
      simp only [evalG, hag, PrimR.eq_primResult hf.1 hP]
  | .Call (.inr _) _, _, hf, _, _ => by simp [fragE] at hf

theorem argsG_complete (co : Option YulContract) : (as : List Expr) → (s : State) →
    fragArgs as = true → {r : ResL} → ArgsR co as.reverse s r → r = (argsG c as s).1
  | [], _, _, _, h => by simp only [List.reverse_nil] at h; cases h; rfl
  | a :: as, s, hf, _, h => by
    simp only [fragArgs, Bool.and_eq_true] at hf
    rw [List.reverse_cons] at h
    rcases ArgsR.snoc_inv h with
      ⟨e, hl, rfl⟩ | ⟨s₁, vs, hl, (⟨e, ha, rfl⟩ | ⟨s₂, v, ha, rfl⟩)⟩
    · obtain ⟨g, hag⟩ := fst_eq_elim (argsG_complete co as s hf.2 hl)
      simp only [argsG, hag]
    · obtain ⟨g, hag⟩ := fst_eq_elim (argsG_complete co as s hf.2 hl)
      obtain ⟨g', he⟩ := fst_eq_elim (evalG_complete co a s₁ hf.1 ha)
      simp only [argsG, hag, he]
    · obtain ⟨g, hag⟩ := fst_eq_elim (argsG_complete co as s hf.2 hl)
      obtain ⟨g', he⟩ := fst_eq_elim (evalG_complete co a s₁ hf.1 ha)
      simp only [argsG, hag, he]

end

mutual

theorem execG_complete (co : Option YulContract) : (st : Stmt) → (s : State) →
    fragS st = true → {r : Res} → ExecR co st s r → r = (execG c st s).1
  | .Block sts, s, hf, _, h => by
    simp only [fragS] at hf
    simp only [execG]
    exact blockG_complete co sts s hf h
  | .Let _ none, _, _, _, h => by cases h; rfl
  | .Let _ (some (.Var _)), _, _, _, h => by cases h; rfl
  | .Let _ (some (.Lit _)), _, _, _, h => by cases h; rfl
  | .Let vars (some (.Call (.inl prim) args)), s, hf, _, h => by
    simp only [fragS, fragE, Bool.and_eq_true, decide_eq_true_eq] at hf
    cases h with
    | letPrimArgsErr ha =>
      obtain ⟨g, hag⟩ := fst_eq_elim (argsG_complete c co args s hf.2 ha)
      simp only [execG, hag]
    | letPrim ha hP =>
      obtain ⟨g, hag⟩ := fst_eq_elim (argsG_complete c co args s hf.2 ha)
      simp only [execG, hag, PrimR.eq_primResult hf.1 hP]
  | .Let _ (some (.Call (.inr _) _)), _, hf, _, _ => by simp [fragS, fragE] at hf
  | .ExprStmtCall (.Call (.inl prim) args), s, hf, _, h => by
    simp only [fragS, fragE, Bool.and_eq_true, decide_eq_true_eq] at hf
    cases h with
    | exprPrimArgsErr ha =>
      obtain ⟨g, hag⟩ := fst_eq_elim (argsG_complete c co args s hf.2 ha)
      simp only [execG, hag]
    | exprPrim ha hP =>
      obtain ⟨g, hag⟩ := fst_eq_elim (argsG_complete c co args s hf.2 ha)
      simp only [execG, hag, PrimR.eq_primResult hf.1 hP]
  | .ExprStmtCall (.Call (.inr _) _), _, hf, _, _ => by simp [fragS, fragE] at hf
  | .ExprStmtCall (.Var _), _, _, _, h => by cases h; rfl
  | .ExprStmtCall (.Lit _), _, _, _, h => by cases h; rfl
  | .If cond body, s, hf, _, h => by
    simp only [fragS, Bool.and_eq_true] at hf
    cases h with
    | ifErr hc =>
      obtain ⟨g, hce⟩ := fst_eq_elim (evalG_complete c co cond s hf.1 hc)
      simp only [execG, hce]
    | ifTrue hc hv hb =>
      obtain ⟨g, hce⟩ := fst_eq_elim (evalG_complete c co cond s hf.1 hc)
      obtain ⟨g', hbe⟩ := fst_eq_elim (blockG_complete co body _ hf.2 hb)
      simp only [execG, hce, hbe, hv, ne_eq, not_false_eq_true, if_true]
    | ifFalse hc hv =>
      obtain ⟨g, hce⟩ := fst_eq_elim (evalG_complete c co cond s hf.1 hc)
      simp only [execG, hce, hv, ne_eq, not_true_eq_false, if_false]
  | .Switch cond cases dflt, s, hf, _, h => by
    simp only [fragS, Bool.and_eq_true] at hf
    obtain ⟨⟨hfc, hfcs⟩, hfd⟩ := hf
    cases h with
    | switchCondErr hc =>
      obtain ⟨g, hce⟩ := fst_eq_elim (evalG_complete c co cond s hfc hc)
      simp only [execG, hce]
    | switchDefaultErr hc hd =>
      obtain ⟨g, hce⟩ := fst_eq_elim (evalG_complete c co cond s hfc hc)
      obtain ⟨gd, hde⟩ := fst_eq_elim (blockG_complete co dflt _ hfd hd)
      simp only [execG, hce, hde]
    | switchCase hc hd hsel hb =>
      obtain ⟨g, hce⟩ := fst_eq_elim (evalG_complete c co cond s hfc hc)
      obtain ⟨gd, hde⟩ := fst_eq_elim (blockG_complete co dflt _ hfd hd)
      obtain ⟨gb, hcs⟩ := casesG_complete co cases _ _ hfcs hsel hb
      simp only [execG, hce, hde, hcs]
    | switchDefault hc hd hsel =>
      obtain ⟨g, hce⟩ := fst_eq_elim (evalG_complete c co cond s hfc hc)
      obtain ⟨gd, hde⟩ := fst_eq_elim (blockG_complete co dflt _ hfd hd)
      simp only [execG, hce, hde, casesG_of_selectCase_none c hsel]
  | .For _ _ _, _, hf, _, _ => by simp [fragS] at hf
  | .Continue, _, _, _, h => by cases h; rfl
  | .Break, _, _, _, h => by cases h; rfl
  | .Leave, _, _, _, h => by cases h; rfl

theorem blockG_complete (co : Option YulContract) : (sts : List Stmt) → (s : State) →
    fragB sts = true → {r : Res} → ExecR co (.Block sts) s r → r = (blockG c sts s).1
  | [], _, _, _, h => by cases h; rfl
  | st :: sts, s, hf, _, h => by
    simp only [fragB, Bool.and_eq_true] at hf
    cases h with
    | blockErr h₁ =>
      obtain ⟨g, he⟩ := fst_eq_elim (execG_complete co st s hf.1 h₁)
      simp only [blockG, he]
    | blockCons h₁ h₂ =>
      obtain ⟨g, he⟩ := fst_eq_elim (execG_complete co st s hf.1 h₁)
      obtain ⟨g', hb⟩ := fst_eq_elim (blockG_complete co sts _ hf.2 h₂)
      simp only [blockG, he, hb]
    | blockJump h₁ =>
      obtain ⟨g, he⟩ := fst_eq_elim (execG_complete co st s hf.1 h₁)
      simp only [blockG, he]
    | blockOOF h₁ =>
      obtain ⟨g, he⟩ := fst_eq_elim (execG_complete co st s hf.1 h₁)
      simp only [blockG, he]

theorem casesG_complete (co : Option YulContract) : (cases : List (Literal × List Stmt)) →
    (v : Literal) → (s : State) → fragCases cases = true → {body : List Stmt} → {r : Res} →
    selectCase v cases = some body → ExecR co (.Block body) s r →
    ∃ g, casesG c cases v s = some (r, g)
  | [], _, _, _, _, _, hsel, _ => by simp [selectCase] at hsel
  | (l, b) :: rest, v, s, hf, _, _, hsel, h => by
    simp only [fragCases, Bool.and_eq_true] at hf
    by_cases hl : l = v
    · simp only [selectCase, hl, if_true, Option.some.injEq] at hsel
      subst hsel
      obtain ⟨g, hb⟩ := fst_eq_elim (blockG_complete co b s hf.1 h)
      exact ⟨g, by simp [casesG, hl, hb]⟩
    · simp only [selectCase, hl, if_false] at hsel
      obtain ⟨g, hg⟩ := casesG_complete co rest v s hf.2 hsel h
      exact ⟨g, by simp [casesG, hl, hg]⟩

end

/-! ## Consequences for the interpreter -/

/-- On the fragment, `ExecR` is deterministic. -/
theorem execR_deterministic {co : Option YulContract} {st : Stmt} {s : State} {r₁ r₂ : Res}
    (hf : InFragment st) (h₁ : ExecR co st s r₁) (h₂ : ExecR co st s r₂) : r₁ = r₂ := by
  rw [execG_complete defaultModel co st s hf h₁, execG_complete defaultModel co st s hf h₂]
where
  /-- Any cost model will do; the result component of `execG` does not depend on it. -/
  defaultModel : CostModel := ⟨fun _ => 0, 0⟩

/-- **The interpreter computes the metered result.** On the fragment, every run of `exec` (with
any fuel) that does not run out of fuel returns exactly the result of `execG`. -/
theorem exec_eq_execG {fuel : ℕ} {st : Stmt} {co : Option YulContract} {s : State}
    (hf : InFragment st) (h : exec fuel st co s ≠ OOF) : exec fuel st co s = (execG c st s).1 :=
  execG_complete c co st s hf (exec_sound rfl h)

/-- **Yul gas bound (analysis §5, Approach B).** For a loop-free, call-free Yul program, every run
of the interpreter that does not run out of fuel is metered by `execG`, and the gas it is charged
under the cost model `c` is at most the static bound `gasS c st`, whatever the start state. -/
theorem exec_gas_bound {fuel : ℕ} {st : Stmt} {co : Option YulContract} {s : State} {r : Res}
    (hf : InFragment st) (h : exec fuel st co s = r) (hr : r ≠ OOF) :
    ∃ g, execG c st s = (r, g) ∧ g ≤ gasS c st := by
  refine ⟨(execG c st s).2, ?_, execG_gas_le c st s⟩
  have := exec_eq_execG c (fuel := fuel) (co := co) (s := s) hf (h ▸ hr)
  rw [← h, this]

/-- **The bound is attained.** For a straight-line fragment program (no `if`, no `switch`), every
interpreter run that ends normally is charged exactly `gasS c st`. -/
theorem exec_gas_exact {fuel : ℕ} {st : Stmt} {co : Option YulContract} {s : State}
    {ss : SharedState .Yul} {vs : VarStore} (hf : InFragment st) (hst : Straight st)
    (h : exec fuel st co s = .ok (.Ok ss vs)) : execG c st s = (.ok (.Ok ss vs), gasS c st) := by
  have hr : (execG c st s).1 = .ok (.Ok ss vs) := by
    rw [← h, exec_eq_execG c hf (by rw [h]; simp [OOF])]
  have hg := execG_gas_eq_of_ok c st s hst hr
  rw [← hr, ← hg]

end Gas
end Yul
end EvmYul
