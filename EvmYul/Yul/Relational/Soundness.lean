module

public import EvmYul.Yul.Relational.Semantics

public section

/-!
# The Yul interpreter is sound with respect to the relational semantics

Main results (`exec_sound`, `eval_sound`): if the fuelled interpreter returns anything other than
`.error .OutOfFuel`, the fuel-free relation relates the input to that result. Fuel therefore never
has to appear in a theorem about a terminating run: prove it about `ExecR` (e.g. with the WP
calculus in `EvmYul/Yul/Relational/WP.lean`) and transfer it with `exec_sound`.

The proof is one strong induction on fuel over all interpreter functions at once (`SoundAt`).
-/

namespace EvmYul
namespace Yul
namespace Relational

open Ast

/-- Shorthand for the interpreter's fuel-exhaustion error. -/
@[expose] abbrev OOF {α : Type} : Except Yul.Exception α := .error .OutOfFuel

/-- The relation for `execSwitchCases`: the evaluated branches carry the case labels in order, and
every branch result that is not fuel exhaustion is related to its case body. -/
def SwitchBranchesR (co : Option YulContract) (s : State) :
    List (Literal × List Stmt) → List (Literal × Res) → Prop :=
  List.Forall₂ fun vb vr => vb.1 = vr.1 ∧ (vr.2 ≠ OOF → ExecR co (.Block vb.2) s vr.2)

/-- Soundness of every interpreter function at fuel `n`. -/
structure SoundAt (n : ℕ) : Prop where
  args : ∀ co args s, evalArgs n args co s ≠ OOF → ArgsR co args s (evalArgs n args co s)
  call : ∀ co args fname s, call n args fname co s ≠ OOF →
    CallR co args fname s (call n args fname co s)
  dispatch : ∀ co s, callDispatcher n co s ≠ OOF → DispatchR co s (callDispatcher n co s)
  prim : ∀ s prim args, primCall n s prim args ≠ OOF → PrimR s prim args (primCall n s prim args)
  eval : ∀ co e s, eval n e co s ≠ OOF → EvalR co e s (eval n e co s)
  exec : ∀ co st s, exec n st co s ≠ OOF → ExecR co st s (exec n st co s)
  loop : ∀ co cond post body s, loop n cond post body co s ≠ OOF →
    LoopR co cond post body s (loop n cond post body co s)
  switch : ∀ co s cases branches, execSwitchCases n co s cases = .ok branches →
    SwitchBranchesR co s cases branches

/-! ## Small facts about the result plumbing -/

theorem head'_ne_oof {r : ResL} (h : head' r ≠ OOF) : r ≠ OOF := by
  rintro rfl; exact h rfl

theorem cons'_ne_oof {v : Literal} {r : ResL} (h : cons' v r ≠ OOF) : r ≠ OOF := by
  rintro rfl; exact h rfl

theorem multifill'_ne_oof {vars : List Identifier} {r : ResL} (h : multifill' vars r ≠ OOF) :
    r ≠ OOF := by
  rintro rfl; exact h rfl

theorem callPost_ne_oof {s : State} {f : FunctionDefinition} {r : Res}
    (h : callPost s f r ≠ OOF) : r ≠ OOF := by
  rintro rfl; exact h rfl

theorem err_ne_oof {α β : Type} {e : Yul.Exception}
    (h : (Except.error e : Except Yul.Exception α) ≠ OOF) :
    (Except.error e : Except Yul.Exception β) ≠ OOF := by
  intro h'; cases h'; exact h rfl

theorem call_succ_eq (m : ℕ) (args : List Literal) (fname : Option YulFunctionName)
    (co : Option YulContract) (s : State) :
    call (m + 1) args fname co s =
      match lookupFunction fname co s with
      | .error e => .error e
      | .ok f => callPost s f (exec m (.Block f.body) co (State.mkOk (s.initcall f.params args))) := by
  rw [call]
  simp only [lookupFunction]
  cases s.sharedState.accountMap.get? s.executionEnv.codeOwner with
  | none => rfl
  | some c =>
    cases fname with
    | none =>
      (try dsimp only)
      cases exec m (.Block [(co.getD c.code).dispatcher]) co (State.mkOk (s.initcall [] args)) <;>
        rfl
    | some name =>
      (try dsimp only)
      cases Finmap.lookup name (co.getD c.code).functions with
      | none => rfl
      | some f =>
        (try dsimp only)
        cases exec m (.Block f.body) co (State.mkOk (s.initcall f.params args)) <;> rfl

theorem callDispatcher_succ_eq (m : ℕ) (co : Option YulContract) (s : State) :
    callDispatcher (m + 1) co s =
      callPost s (dispatcherFunction s) (exec m (.Block (dispatcherFunction s).body) co
        (State.mkOk (s.initcall (dispatcherFunction s).params []))) := by
  rw [callDispatcher]
  simp only [callPost, dispatcherFunction]
  cases exec m (.Block [s.executionEnv.code.dispatcher]) co
    (State.mkOk (s.initcall [] [])) <;> rfl

theorem map_ne_oof {f : State → State} {r : Res} (h : r.map f ≠ OOF) : r ≠ OOF := by
  rintro rfl; exact h rfl

/-! ## `switch` plumbing -/

/-- `execSwitchCases` can only fail by running out of fuel: errors of the case bodies are stored in
the branch list, not propagated. -/
theorem execSwitchCases_error {n : ℕ} {co : Option YulContract} {s : State}
    {cases : List (Literal × List Stmt)} {e : Yul.Exception}
    (h : execSwitchCases n co s cases = .error e) : e = .OutOfFuel := by
  induction cases generalizing n with
  | nil => simp [execSwitchCases] at h
  | cons c cs ihc =>
    obtain ⟨val, stmts⟩ := c
    match n with
    | 0 => simp [execSwitchCases] at h; exact h.symm
    | m + 1 =>
      simp only [execSwitchCases] at h
      split at h <;> (split at h <;> first | (cases h; done) | (cases h; exact ihc (by assumption)))

theorem execSwitchCases_cons_ok {m : ℕ} {co : Option YulContract} {s : State} {val : Literal}
    {stmts : List Stmt} {cs : List (Literal × List Stmt)} {branches : List (Literal × Res)}
    (h : execSwitchCases (m + 1) co s ((val, stmts) :: cs) = .ok branches) :
    ∃ rest, execSwitchCases m co s cs = .ok rest ∧
      branches = (val, exec m (.Block stmts) co s) :: rest := by
  simp only [execSwitchCases] at h
  split at h <;> (split at h <;> first | (cases h; done) | skip)
  all_goals
    rename_i heq _ rest hrest
    cases h
    exact ⟨rest, hrest, by rw [heq]⟩

theorem selectCase_of_branches {co : Option YulContract} {s s₂ : State} {c : Literal}
    {cases : List (Literal × List Stmt)} {branches : List (Literal × Res)}
    (hb : SwitchBranchesR co s cases branches) (hne : selectBranch c (.ok s₂) branches ≠ OOF) :
    (∃ body, selectCase c cases = some body ∧
        ExecR co (.Block body) s (selectBranch c (.ok s₂) branches)) ∨
      (selectCase c cases = none ∧ selectBranch c (.ok s₂) branches = .ok s₂) := by
  induction hb with
  | nil => exact Or.inr ⟨rfl, rfl⟩
  | @cons vb vr cases branches hvr _ ihb =>
    obtain ⟨v, body⟩ := vb
    obtain ⟨v', r⟩ := vr
    obtain ⟨hv, hr⟩ := hvr
    simp only at hv hr
    subst hv
    by_cases hc : v = c
    · have hsel : selectBranch c (.ok s₂) ((v, r) :: branches) = r := by
        simp only [selectBranch, List.foldr, hc, if_true]
      rw [hsel] at hne ⊢
      exact Or.inl ⟨body, by simp only [selectCase, hc, if_true], hr hne⟩
    · have hsel : selectBranch c (.ok s₂) ((v, r) :: branches) =
          selectBranch c (.ok s₂) branches := by
        simp only [selectBranch, List.foldr, hc, if_false]
      have hcase : selectCase c ((v, body) :: cases) = selectCase c cases := by
        simp only [selectCase, hc, if_false]
      rw [hsel] at hne ⊢
      rw [hcase]
      exact ihb hne

/-- The shared shape of `let`-with-builtin and expression-statement-with-builtin. -/
theorem primStmt_case {m : ℕ} (hm : SoundAt m) {co : Option YulContract} {prim : PrimOp}
    {args : List Expr} {s : State} {vars : List Identifier} {target : Stmt}
    (hErr : ∀ e, ArgsR co args.reverse s (.error e) → ExecR co target s (.error e))
    (hOk : ∀ s₁ vs r, ArgsR co args.reverse s (.ok (s₁, vs)) → PrimR s₁ prim vs.reverse r →
      ExecR co target s (multifill' vars r))
    (h : execPrimCall m prim vars (reverse' (evalArgs m args.reverse co s)) ≠ OOF) :
    ExecR co target s (execPrimCall m prim vars (reverse' (evalArgs m args.reverse co s))) := by
  cases ha : evalArgs m args.reverse co s with
  | error e =>
    rw [ha] at h
    simp only [reverse', execPrimCall] at h ⊢
    exact hErr e (ha ▸ hm.args co _ s (by rw [ha]; exact err_ne_oof h))
  | ok p =>
    obtain ⟨s₁, vs⟩ := p
    rw [ha] at h
    simp only [reverse', execPrimCall] at h ⊢
    exact hOk s₁ vs _ (ha ▸ hm.args co _ s (by rw [ha]; simp))
      (hm.prim s₁ prim vs.reverse (multifill'_ne_oof h))

/-- The shared shape of `let`-with-user-call and expression-statement-with-user-call. -/
theorem callStmt_case {m : ℕ} (hm : SoundAt m) (ih : ∀ m' < m, SoundAt m')
    {co : Option YulContract} {f : YulFunctionName}
    {args : List Expr} {s : State} {vars : List Identifier} {target : Stmt}
    (hErr : ∀ e, ArgsR co args.reverse s (.error e) → ExecR co target s (.error e))
    (hBuiltin : ∀ s₁ vs r, ArgsR co args.reverse s (.ok (s₁, vs)) →
      execObjectDataBuiltin? f vars (.ok (s₁, vs.reverse)) = some r → ExecR co target s r)
    (hCall : ∀ s₁ vs r, ArgsR co args.reverse s (.ok (s₁, vs)) →
      execObjectDataBuiltin? f vars (.ok (s₁, vs.reverse)) = none →
      CallR co vs.reverse (some f) s₁ r → ExecR co target s (multifill' vars r))
    (h : (match execObjectDataBuiltin? f vars (reverse' (evalArgs m args.reverse co s)) with
      | some result => result
      | none => execCall m f vars co (reverse' (evalArgs m args.reverse co s))) ≠ OOF) :
    ExecR co target s (match execObjectDataBuiltin? f vars (reverse' (evalArgs m args.reverse co s)) with
      | some result => result
      | none => execCall m f vars co (reverse' (evalArgs m args.reverse co s))) := by
  cases ha : evalArgs m args.reverse co s with
  | error e =>
    rw [ha] at h
    simp only [reverse', execObjectDataBuiltin?] at h ⊢
    exact hErr e (ha ▸ hm.args co _ s (by rw [ha]; exact err_ne_oof h))
  | ok p =>
    obtain ⟨s₁, vs⟩ := p
    rw [ha] at h
    have hA : ArgsR co args.reverse s (.ok (s₁, vs)) := ha ▸ hm.args co _ s (by rw [ha]; simp)
    simp only [reverse'] at h ⊢
    cases hb : execObjectDataBuiltin? f vars (.ok (s₁, vs.reverse)) with
    | some r => exact hBuiltin s₁ vs r hA hb
    | none =>
      rw [hb] at h
      simp only at h ⊢
      match m, ih, h with
      | 0, _, h => exact absurd (by simp [execCall]) h
      | m' + 1, ih, h =>
        simp only [execCall] at h ⊢
        exact hCall s₁ vs _ hA hb ((ih m' (by omega)).call co _ _ s₁ (multifill'_ne_oof h))

/-! ## One induction step per interpreter function -/

section Steps

variable {n : ℕ} (ih : ∀ m < n, SoundAt m)
include ih

theorem args_step : ∀ co args s, evalArgs n args co s ≠ OOF →
    ArgsR co args s (evalArgs n args co s) := by
  intro co args s h
  match n, args with
  | 0, _ => exact absurd (by simp [evalArgs]) h
  | m + 1, [] => simp only [evalArgs]; exact ArgsR.nil s
  | m + 1, a :: as =>
    simp only [evalArgs] at h ⊢
    have hm := ih m (by omega)
    cases he : eval m a co s with
    | error e =>
      rw [he] at h
      simp only [evalTail] at h ⊢
      exact ArgsR.consErr (he ▸ hm.eval co a s (by rw [he]; exact err_ne_oof h))
    | ok p =>
      obtain ⟨s₁, v⟩ := p
      rw [he] at h
      have hEv : EvalR co a s (.ok (s₁, v)) := he ▸ hm.eval co a s (by rw [he]; simp)
      match m, hm, hEv, h with
      | 0, _, _, h => exact absurd (by simp [evalTail]) h
      | m' + 1, _, hEv, h =>
        simp only [evalTail] at h ⊢
        have hm' := ih m' (by omega)
        exact ArgsR.cons hEv (hm'.args co as s₁ (cons'_ne_oof h))

theorem call_step : ∀ co args fname s, call n args fname co s ≠ OOF →
    CallR co args fname s (call n args fname co s) := by
  intro co args fname s h
  match n with
  | 0 => exact absurd (by simp [call]) h
  | m + 1 =>
    rw [call_succ_eq] at h ⊢
    cases hf : lookupFunction fname co s with
    | error e => exact CallR.lookupErr hf
    | ok f =>
      rw [hf] at h
      exact CallR.body hf ((ih m (by omega)).exec co _ _ (callPost_ne_oof h))

theorem dispatch_step : ∀ co s, callDispatcher n co s ≠ OOF →
    DispatchR co s (callDispatcher n co s) := by
  intro co s h
  match n with
  | 0 => exact absurd (by simp [callDispatcher]) h
  | m + 1 =>
    rw [callDispatcher_succ_eq] at h ⊢
    exact DispatchR.mk ((ih m (by omega)).exec co _ _ (callPost_ne_oof h))

theorem prim_step : ∀ s prim args, primCall n s prim args ≠ OOF →
    PrimR s prim args (primCall n s prim args) := by
  intro s prim args h
  match n with
  | 0 => exact absurd (primCall_zero s prim args) h
  | m + 1 =>
    rw [primCall_succ_eq_primCallK] at h ⊢
    refine PrimR.mk _ (fun co s' => ?_) h
    by_cases hd : callDispatcher m co s' = OOF
    · rw [hd]; exact DispatchOrOOF.outOfFuel co s'
    · exact DispatchOrOOF.ofDispatch ((ih m (by omega)).dispatch co s' hd)

theorem eval_step : ∀ co e s, eval n e co s ≠ OOF → EvalR co e s (eval n e co s) := by
  intro co e s h
  match n with
  | 0 => exact absurd (by simp [eval]) h
  | m + 1 =>
    have hm := ih m (by omega)
    match e with
    | .Lit v => simp only [eval]; exact EvalR.lit v s
    | .Var x => simp only [eval]; exact EvalR.var x s
    | .Call (.inl prim) args =>
      simp only [eval] at h ⊢
      cases ha : evalArgs m args.reverse co s with
      | error e =>
        rw [ha] at h
        simp only [reverse', evalPrimCall] at h ⊢
        have hA : ArgsR co args.reverse s (.error e) :=
          ha ▸ hm.args co _ s (by rw [ha]; exact err_ne_oof h)
        exact EvalR.primArgsErr hA
      | ok p =>
        obtain ⟨s₁, vs⟩ := p
        rw [ha] at h
        have hA : ArgsR co args.reverse s (.ok (s₁, vs)) :=
          ha ▸ hm.args co _ s (by rw [ha]; simp)
        simp only [reverse', evalPrimCall] at h ⊢
        exact EvalR.prim hA (hm.prim s₁ prim vs.reverse (head'_ne_oof h))
    | .Call (.inr f) args =>
      simp only [eval] at h ⊢
      cases hb : evalObjectDataBuiltin? f args s with
      | some r => exact EvalR.builtin hb
      | none =>
        rw [hb] at h
        simp only at h ⊢
        cases ha : evalArgs m args.reverse co s with
        | error e =>
          rw [ha] at h
          simp only [reverse', evalCall] at h ⊢
          have hA : ArgsR co args.reverse s (.error e) :=
            ha ▸ hm.args co _ s (by rw [ha]; exact err_ne_oof h)
          exact EvalR.callArgsErr hb hA
        | ok p =>
          obtain ⟨s₁, vs⟩ := p
          rw [ha] at h
          have hA : ArgsR co args.reverse s (.ok (s₁, vs)) :=
            ha ▸ hm.args co _ s (by rw [ha]; simp)
          simp only [reverse'] at h ⊢
          match m, hm, hA, h with
          | 0, _, _, h => exact absurd (by simp [evalCall]) h
          | m' + 1, _, hA, h =>
            simp only [evalCall] at h ⊢
            exact EvalR.call hb hA ((ih m' (by omega)).call co _ _ s₁ (head'_ne_oof h))

theorem switch_step : ∀ co s cases branches, execSwitchCases n co s cases = .ok branches →
    SwitchBranchesR co s cases branches := by
  intro co s cases branches h
  match n, cases with
  | _, [] =>
    simp only [execSwitchCases, Except.ok.injEq] at h
    subst h; exact List.Forall₂.nil
  | 0, (_, _) :: _ => simp [execSwitchCases] at h
  | m + 1, (val, stmts) :: cs =>
    obtain ⟨rest, hrest, rfl⟩ := execSwitchCases_cons_ok h
    have hm := ih m (by omega)
    exact List.Forall₂.cons ⟨rfl, fun hne => hm.exec co _ s hne⟩ (hm.switch co s cs rest hrest)

theorem loop_step : ∀ co cond post body s, loop n cond post body co s ≠ OOF →
    LoopR co cond post body s (loop n cond post body co s) := by
  intro co cond post body s h
  match n with
  | 0 => exact absurd (by simp [loop]) h
  | 1 => exact absurd (by simp [loop]) h
  | m + 2 =>
    have hm := ih m (by omega)
    simp only [loop] at h ⊢
    cases hc : eval m cond co (State.mkOk s) with
    | error e =>
      rw [hc] at h
      exact LoopR.condErr (hc ▸ hm.eval co cond _ (by rw [hc]; exact err_ne_oof h))
    | ok p =>
      obtain ⟨s₁, x⟩ := p
      have hE : EvalR co cond (State.mkOk s) (.ok (s₁, x)) :=
        hc ▸ hm.eval co cond _ (by rw [hc]; simp)
      rw [hc] at h
      simp only at h ⊢
      by_cases hx : x = ⟨0⟩
      · simp only [hx, if_true] at h ⊢
        exact LoopR.exit (hx ▸ hE) rfl
      · simp only [hx, if_false] at h ⊢
        cases hb : exec m (.Block body) co s₁ with
        | error e =>
          rw [hb] at h
          exact LoopR.bodyErr hE hx (hb ▸ hm.exec co _ s₁ (by rw [hb]; exact err_ne_oof h))
        | ok s₂ =>
          have hB : ExecR co (.Block body) s₁ (.ok s₂) :=
            hb ▸ hm.exec co _ s₁ (by rw [hb]; simp)
          rw [hb] at h
          simp only at h ⊢
          have post_case : continuesLoop s₂ →
              (match exec m (.Block post) co s₂.reviveJump with
                | .error e => .error e
                | .ok s₃ =>
                  match exec m (.For cond post body) co (s₃.overwrite? s) with
                  | .error e => .error e
                  | .ok s₅ => .ok (s₅.overwrite? s)) ≠ OOF →
              LoopR co cond post body s
                (match exec m (.Block post) co s₂.reviveJump with
                | .error e => .error e
                | .ok s₃ =>
                  match exec m (.For cond post body) co (s₃.overwrite? s) with
                  | .error e => .error e
                  | .ok s₅ => .ok (s₅.overwrite? s)) := by
            intro hcont h
            cases hp : exec m (.Block post) co s₂.reviveJump with
            | error e =>
              rw [hp] at h
              exact LoopR.postErr hE hx hB hcont
                (hp ▸ hm.exec co _ _ (by rw [hp]; exact err_ne_oof h))
            | ok s₃ =>
              have hP : ExecR co (.Block post) s₂.reviveJump (.ok s₃) :=
                hp ▸ hm.exec co _ _ (by rw [hp]; simp)
              rw [hp] at h
              simp only at h ⊢
              cases hr : exec m (.For cond post body) co (s₃.overwrite? s) with
              | error e =>
                rw [hr] at h
                exact LoopR.next (r := .error e) hE hx hB hcont hP
                  (hr ▸ hm.exec co _ _ (by rw [hr]; exact err_ne_oof h))
              | ok s₅ =>
                exact LoopR.next (r := .ok s₅) hE hx hB hcont hP
                  (hr ▸ hm.exec co _ _ (by rw [hr]; simp))
          match s₂, hB, h, post_case with
          | .OutOfFuel, hB, _, _ => exact LoopR.bodyOOF hE hx hB
          | .Checkpoint (.Break ss vs), hB, _, _ => exact LoopR.break_ hE hx hB
          | .Checkpoint (.Leave ss vs), hB, _, _ => exact LoopR.leave hE hx hB
          | .Checkpoint (.Continue ss vs), _, h, post_case => exact post_case trivial h
          | .Ok ss vs, _, h, post_case => exact post_case trivial h

theorem exec_step : ∀ co st s, exec n st co s ≠ OOF → ExecR co st s (exec n st co s) := by
  intro co st s h
  match n with
  | 0 => exact absurd (by simp [exec]) h
  | m + 1 =>
    have hm := ih m (by omega)
    have ihm : ∀ m' < m, SoundAt m' := fun m' hm' => ih m' (by omega)
    match st with
    | .Block [] => simp only [exec]; exact ExecR.blockNil s
    | .Block (st :: sts) =>
      simp only [exec] at h ⊢
      cases h1 : exec m st co s with
      | error e =>
        rw [h1] at h
        exact ExecR.blockErr (h1 ▸ hm.exec co st s (by rw [h1]; exact err_ne_oof h))
      | ok s₁ =>
        have hS : ExecR co st s (.ok s₁) := h1 ▸ hm.exec co st s (by rw [h1]; simp)
        rw [h1] at h
        simp only at h ⊢
        match s₁, hS, h with
        | .Ok ss vs, hS, h => exact ExecR.blockCons hS (hm.exec co _ _ h)
        | .OutOfFuel, hS, _ => exact ExecR.blockOOF hS
        | .Checkpoint j, hS, _ => exact ExecR.blockJump hS
    | .Let vars none => simp only [exec]; exact ExecR.letNone vars s
    | .Let vars (some (.Var x)) => simp only [exec]; exact ExecR.letVar vars x s
    | .Let vars (some (.Lit v)) => simp only [exec]; exact ExecR.letLit vars v s
    | .Let vars (some (.Call (.inl prim) args)) =>
      simp only [exec] at h ⊢
      exact primStmt_case hm (fun e hA => ExecR.letPrimArgsErr hA)
        (fun _ _ _ hA hP => ExecR.letPrim hA hP) h
    | .Let vars (some (.Call (.inr f) args)) =>
      simp only [exec] at h ⊢
      exact callStmt_case hm ihm (fun e hA => ExecR.letCallArgsErr hA)
        (fun _ _ _ hA hB => ExecR.letBuiltin hA hB) (fun _ _ _ hA hB hC => ExecR.letCall hA hB hC) h
    | .ExprStmtCall (.Call (.inl prim) args) =>
      simp only [exec] at h ⊢
      exact primStmt_case hm (fun e hA => ExecR.exprPrimArgsErr hA)
        (fun _ _ _ hA hP => ExecR.exprPrim hA hP) h
    | .ExprStmtCall (.Call (.inr f) args) =>
      simp only [exec] at h ⊢
      exact callStmt_case hm ihm (fun e hA => ExecR.exprCallArgsErr hA)
        (fun _ _ _ hA hB => ExecR.exprBuiltin hA hB) (fun _ _ _ hA hB hC => ExecR.exprCall hA hB hC) h
    | .ExprStmtCall (.Var x) => simp only [exec]; exact ExecR.exprVar x s
    | .ExprStmtCall (.Lit v) => simp only [exec]; exact ExecR.exprLit v s
    | .If cond body =>
      simp only [exec] at h ⊢
      cases hc : eval m cond co s with
      | error e =>
        rw [hc] at h
        exact ExecR.ifErr (hc ▸ hm.eval co cond s (by rw [hc]; exact err_ne_oof h))
      | ok p =>
        obtain ⟨s₁, c⟩ := p
        have hE : EvalR co cond s (.ok (s₁, c)) := hc ▸ hm.eval co cond s (by rw [hc]; simp)
        rw [hc] at h
        simp only at h ⊢
        by_cases hz : c = ⟨0⟩
        · simp only [hz, ne_eq, not_true_eq_false, if_false] at h ⊢
          exact ExecR.ifFalse (hz ▸ hE) rfl
        · simp only [ne_eq, hz, not_false_eq_true, if_true] at h ⊢
          exact ExecR.ifTrue hE hz (hm.exec co _ s₁ h)
    | .Switch cond cases dflt =>
      simp only [exec] at h ⊢
      cases hc : eval m cond co s with
      | error e =>
        rw [hc] at h
        exact ExecR.switchCondErr (hc ▸ hm.eval co cond s (by rw [hc]; exact err_ne_oof h))
      | ok p =>
        obtain ⟨s₁, c⟩ := p
        have hE : EvalR co cond s (.ok (s₁, c)) := hc ▸ hm.eval co cond s (by rw [hc]; simp)
        rw [hc] at h
        simp only at h ⊢
        cases hsw : execSwitchCases m co s₁ cases with
        | error e =>
          rw [hsw] at h
          exact absurd (by rw [execSwitchCases_error hsw]) h
        | ok branches =>
          have hBr := hm.switch co s₁ cases branches hsw
          rw [hsw] at h
          simp only at h ⊢
          cases hd : exec m (.Block dflt) co s₁ with
          | error e =>
            rw [hd] at h
            exact ExecR.switchDefaultErr hE (hd ▸ hm.exec co _ s₁ (by rw [hd]; exact err_ne_oof h))
          | ok s₂ =>
            have hD : ExecR co (.Block dflt) s₁ (.ok s₂) := hd ▸ hm.exec co _ s₁ (by rw [hd]; simp)
            rw [hd] at h
            simp only at h ⊢
            change selectBranch c (.ok s₂) branches ≠ OOF at h
            change ExecR co _ s (selectBranch c (.ok s₂) branches)
            rcases selectCase_of_branches hBr h with ⟨body, hsel, hX⟩ | ⟨hsel, hres⟩
            · exact ExecR.switchCase hE hD hsel hX
            · rw [hres]; exact ExecR.switchDefault hE hD hsel
    | .For cond post body =>
      simp only [exec] at h ⊢
      exact ExecR.for_ (hm.loop co cond post body s h)
    | .Continue => simp only [exec]; exact ExecR.continue_ s
    | .Break => simp only [exec]; exact ExecR.break_ s
    | .Leave => simp only [exec]; exact ExecR.leave s

end Steps

/-- Every interpreter function is sound at every fuel. -/
theorem soundAt : ∀ n, SoundAt n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    exact ⟨args_step ih, call_step ih, dispatch_step ih, prim_step ih, eval_step ih,
      exec_step ih, loop_step ih, switch_step ih⟩

/-- **Soundness of the Yul interpreter.** If `exec` terminates with any result other than running
out of fuel, the relational semantics relates the initial state to that result. -/
theorem exec_sound {fuel : ℕ} {stmt : Stmt} {co : Option YulContract} {s : State} {r : Res}
    (h : exec fuel stmt co s = r) (hr : r ≠ .error .OutOfFuel) : Eval co stmt s r :=
  h ▸ (soundAt fuel).exec co stmt s (h ▸ hr)

/-- **Soundness of expression evaluation.** -/
theorem eval_sound {fuel : ℕ} {e : Expr} {co : Option YulContract} {s : State} {r : ResV}
    (h : eval fuel e co s = r) (hr : r ≠ .error .OutOfFuel) : EvalR co e s r :=
  h ▸ (soundAt fuel).eval co e s (h ▸ hr)

/-- Soundness for the top-level runner used by the tests: a successful `exec` is a derivation. -/
theorem exec_ok_sound {fuel : ℕ} {stmt : Stmt} {co : Option YulContract} {s s' : State}
    (h : exec fuel stmt co s = .ok s') : Eval co stmt s (.ok s') :=
  exec_sound h (by simp)

end Relational
end Yul
end EvmYul
