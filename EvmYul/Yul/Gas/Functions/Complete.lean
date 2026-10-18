module

public import EvmYul.Yul.Gas.Functions.Basic
public import EvmYul.Yul.Gas.FuelAdequacy

public section

/-!
# Yul gas, part 8: the interpreter is metered by `runF` (user functions)

On the fragment with user-defined functions and nested loops (`fragFS`), and provided every function
the interpreter can look up has its body in the fragment (`FunctionsInFragment co`):

* `exec_complete_runF`: every interpreter run that does not run out of fuel is a `runF` run for some
  iteration budget `n` and call-depth budget `d`;
* `exec_fn_gas_bound`: the headline statement combining this with `runF_gas_le` and `runF_mono`.

The proof is one strong induction on fuel over `eval`, `exec` and `call` at once.
-/

namespace EvmYul
namespace Yul
namespace Gas

open Ast Relational

variable (c : FnCostModel)

/-! ## Arguments, left to right -/

/-- Metered evaluation of a list of expressions **left to right**, as the interpreter's `evalArgs`
does. `argsF` is this on the reversed list (`argsF_eq_argsLF`). -/
def argsLF (rc : Runner) : List Expr → State → Option (ResL × ℕ)
  | [], s => some (.ok (s, []), 0)
  | a :: as, s =>
    match evalF c rc a s with
    | none => none
    | some (.error e, g) => some (.error e, g)
    | some (.ok (s₁, v), g) =>
      match argsLF rc as s₁ with
      | none => none
      | some (r, g') => some (cons' v r, g + g')

theorem argsLF_snoc (rc : Runner) : ∀ (l : List Expr) (a : Expr) (s : State),
    argsLF c rc (l ++ [a]) s =
      match argsLF c rc l s with
      | none => none
      | some (.error e, g) => some (.error e, g)
      | some (.ok (s₁, vs), g) =>
        match evalF c rc a s₁ with
        | none => none
        | some (.error e, g') => some (.error e, g + g')
        | some (.ok (s₂, v), g') => some (.ok (s₂, vs ++ [v]), g + g') := by
  intro l a s
  induction l generalizing s with
  | nil =>
    simp only [List.nil_append, argsLF]
    rcases h : evalF c rc a s with _ | ⟨_ | ⟨s₂, v⟩, g⟩ <;> simp [cons']
  | cons b l ih =>
    simp only [List.cons_append, argsLF]
    rcases hb : evalF c rc b s with _ | ⟨_ | ⟨s₁, v⟩, g⟩
    · rfl
    · rfl
    · simp only [ih]
      rcases hl : argsLF c rc l s₁ with _ | ⟨_ | ⟨s₂, vs⟩, g₁⟩
      · rfl
      · simp [cons']
      · simp only
        rcases ha : evalF c rc a s₂ with _ | ⟨_ | ⟨s₃, w⟩, g₂⟩
        · simp [ha, cons']
        · simp [ha, cons', Nat.add_assoc]
        · simp [ha, cons', Nat.add_assoc]

theorem argsF_eq_argsLF (rc : Runner) : ∀ (l : List Expr) (s : State),
    argsF c rc l s = argsLF c rc l.reverse s := by
  intro l s
  induction l generalizing s with
  | nil => rfl
  | cons a as ih =>
    rw [List.reverse_cons, argsLF_snoc, ← ih]
    simp only [argsF]
    rcases argsF c rc as s with _ | ⟨_ | ⟨s₁, vs⟩, g⟩
    · rfl
    · rfl
    · simp only
      rcases evalF c rc a s₁ with _ | ⟨_ | ⟨s₂, v⟩, g'⟩ <;> rfl

/-! ## What is proved at each fuel -/

/-- Completeness of `evalF` for interpreter evaluations with fuel `fuel`. -/
@[expose] def EvalC (co : Option YulContract) (fuel : ℕ) : Prop :=
  ∀ e s, fragFE e = true → eval fuel e co s ≠ OOF →
    ∃ n d g, evalF c (callF c co n d) e s = some (eval fuel e co s, g)

/-- Completeness of `runF` for interpreter runs with fuel `fuel`. -/
@[expose] def ExecC (co : Option YulContract) (fuel : ℕ) : Prop :=
  ∀ st s, fragFS st = true → exec fuel st co s ≠ OOF →
    ∃ n d g, runF c co n d st s = some (exec fuel st co s, g)

/-- Completeness of `callF` for interpreter calls with fuel `fuel`. -/
@[expose] def CallC (co : Option YulContract) (fuel : ℕ) : Prop :=
  ∀ args f s, call fuel args (some f) co s ≠ OOF →
    ∃ n d g, callF c co n d args f s = some (call fuel args (some f) co s, g)

/-- All three, at every fuel below `fuel`. -/
@[expose] def AllBelow (co : Option YulContract) (fuel : ℕ) : Prop :=
  ∀ m < fuel, EvalC c co m ∧ ExecC c co m ∧ CallC c co m

/-! ## Lifting runs to larger budgets -/

theorem liftE {co : Option YulContract} {n d N D : ℕ} (hn : n ≤ N) (hd : d ≤ D) {e : Expr}
    {s : State} {o : ResV × ℕ} (h : evalF c (callF c co n d) e s = some o) :
    evalF c (callF c co N D) e s = some o :=
  evalF_mono c (callF_mono c co hn hd) e s h

theorem liftA {co : Option YulContract} {n d N D : ℕ} (hn : n ≤ N) (hd : d ≤ D) {as : List Expr}
    {s : State} {o : ResL × ℕ} (h : argsF c (callF c co n d) as s = some o) :
    argsF c (callF c co N D) as s = some o :=
  argsF_mono c (callF_mono c co hn hd) as s h

theorem liftB {co : Option YulContract} {n d N D : ℕ} (hn : n ≤ N) (hd : d ≤ D) {sts : List Stmt}
    {s : State} {o : Res × ℕ} (h : blockF c (callF c co n d) n sts s = some o) :
    blockF c (callF c co N D) N sts s = some o :=
  blockF_mono c (callF_mono c co hn hd) hn sts s h

theorem liftC {co : Option YulContract} {n d N D : ℕ} (hn : n ≤ N) (hd : d ≤ D)
    {args : List Literal} {f : YulFunctionName} {s : State} {o : ResL × ℕ}
    (h : callF c co n d args f s = some o) : callF c co N D args f s = some o :=
  callF_mono c co hn hd _ _ _ _ h

/-! ## Arguments -/

/-- Raising the call budget never changes a successful metered argument evaluation. -/
theorem argsLF_mono {co : Option YulContract} {n d N D : ℕ} (hn : n ≤ N) (hd : d ≤ D) :
    ∀ {L : List Expr} {s : State} {o : ResL × ℕ},
    argsLF c (callF c co n d) L s = some o → argsLF c (callF c co N D) L s = some o := by
  intro L
  induction L with
  | nil => intro s o h; simpa [argsLF] using h
  | cons a as ih =>
    intro s o h
    rcases he : evalF c (callF c co n d) a s with _ | ⟨_ | ⟨s₁, v⟩, g⟩
    · simp [argsLF, he] at h
    · simp only [argsLF, he] at h; simp only [argsLF, liftE c hn hd he]; exact h
    · rcases hl : argsLF c (callF c co n d) as s₁ with _ | ⟨r, g'⟩
      · simp [argsLF, he, hl] at h
      · simp only [argsLF, he, hl] at h; simp only [argsLF, liftE c hn hd he, ih hl]; exact h

/-- The interpreter's `evalArgs` is metered by `argsLF`, given completeness of `eval` below. -/
theorem evalArgs_complete {co : Option YulContract} : ∀ (L : List Expr) (F : ℕ) (s : State),
    (∀ m < F, EvalC c co m) → (∀ a ∈ L, fragFE a = true) → evalArgs F L co s ≠ OOF →
      ∃ n d g, argsLF c (callF c co n d) L s = some (evalArgs F L co s, g)
  | _, 0, s, _, _, hne => absurd (by simp [evalArgs]) hne
  | [], F + 1, s, _, _, _ => ⟨0, 0, 0, by simp [evalArgs, argsLF]⟩
  | a :: as, m + 1, s, hE, hf, hne => by
    simp only [evalArgs] at hne ⊢
    cases he : eval m a co s with
    | error e =>
      rw [he] at hne; simp only [evalTail] at hne ⊢
      obtain ⟨n, d, g, h⟩ := hE m (by omega) a s (hf a List.mem_cons_self)
        (by rw [he]; exact err_ne_oof hne)
      rw [he] at h
      exact ⟨n, d, g, by simp [argsLF, h]⟩
    | ok p =>
      obtain ⟨s₁, v⟩ := p
      obtain ⟨n, d, g, h⟩ := hE m (by omega) a s (hf a List.mem_cons_self) (by rw [he]; simp [OOF])
      rw [he] at h hne
      match m, hE, hne, h with
      | 0, _, hne, _ => exact absurd (by simp [evalTail]) hne
      | m' + 1, hE, hne, h =>
        simp only [evalTail] at hne ⊢
        obtain ⟨n₂, d₂, g₂, h₂⟩ := evalArgs_complete as m' s₁ (fun k hk => hE k (by omega))
          (fun b hb => hf b (List.mem_cons_of_mem _ hb)) (cons'_ne_oof hne)
        refine ⟨max n n₂, max d d₂, g + g₂, ?_⟩
        have a1 := liftE c (le_max_left n n₂) (le_max_left d d₂) h
        have a2 := argsLF_mono c (le_max_right n n₂) (le_max_right d d₂) h₂
        simp [argsLF, a1, a2]

/-- Every argument of an argument list in the fragment is in the fragment. -/
theorem fragFE_of_mem_fragFArgs (a : Expr) :
    ∀ (l : List Expr), fragFArgs l = true → a ∈ l → fragFE a = true
  | [], _, h => by simp at h
  | b :: bs, hf, h => by
    simp only [fragFArgs, Bool.and_eq_true] at hf
    rcases List.mem_cons.mp h with rfl | h'
    · exact hf.1
    · exact fragFE_of_mem_fragFArgs a bs hf.2 h'

/-- Arguments of a call, as the interpreter evaluates them (`args.reverse`). -/
theorem evalArgs_reverse_complete {co : Option YulContract} {args : List Expr} {F : ℕ} {s : State}
    (hE : ∀ m < F, EvalC c co m) (hf : fragFArgs args = true)
    (hne : evalArgs F args.reverse co s ≠ OOF) :
    ∃ n d g, argsF c (callF c co n d) args s = some (evalArgs F args.reverse co s, g) := by
  have hf' : ∀ a ∈ args.reverse, fragFE a = true := by
    intro a ha
    exact fragFE_of_mem_fragFArgs a args hf (List.mem_reverse.mp ha)
  obtain ⟨n, d, g, h⟩ := evalArgs_complete c args.reverse F s hE hf' hne
  exact ⟨n, d, g, by rw [argsF_eq_argsLF]; exact h⟩

/-! ## Expressions and calls -/

theorem evalC_step {co : Option YulContract} {fuel : ℕ} (hAll : AllBelow c co fuel) :
    EvalC c co fuel := by
  intro e s hf hne
  match fuel, hAll, hne with
  | 0, _, hne => exact absurd (by simp [eval]) hne
  | m + 1, hAll, hne =>
  have hE : ∀ k < m, EvalC c co k := fun k hk => (hAll k (by omega)).1
  match e with
  | .Lit v => exact ⟨0, 0, 0, by simp [eval, evalF]⟩
  | .Var x => exact ⟨0, 0, 0, by simp [eval, evalF]⟩
  | .Call (.inl prim) args =>
    simp only [fragFE, Bool.and_eq_true, decide_eq_true_eq] at hf
    simp only [eval] at hne ⊢
    cases ha : evalArgs m args.reverse co s with
    | error e =>
      rw [ha] at hne; simp only [reverse', evalPrimCall] at hne ⊢
      obtain ⟨n, d, g, h⟩ := evalArgs_reverse_complete c hE hf.2 (by rw [ha]; exact err_ne_oof hne)
      rw [ha] at h
      exact ⟨n, d, g, by simp [evalF, h]⟩
    | ok p =>
      obtain ⟨s₁, vs⟩ := p
      rw [ha] at hne; simp only [reverse', evalPrimCall] at hne ⊢
      obtain ⟨n, d, g, h⟩ := evalArgs_reverse_complete c hE hf.2 (by rw [ha]; simp [OOF])
      rw [ha] at h
      have hm : 1 ≤ m := by
        rcases m with _ | m
        · exact absurd (by simp [primCall, head']) hne
        · omega
      rw [primCall_eq_primResult hf.1 hm]
      exact ⟨n, d, g + c.prim prim, by simp [evalF, h]⟩
  | .Call (.inr f) args =>
    simp only [fragFE] at hf
    simp only [eval] at hne ⊢
    rcases hb : evalObjectDataBuiltin? f args s with _ | r
    · simp only [hb] at hne ⊢
      cases ha : evalArgs m args.reverse co s with
      | error e =>
        rw [ha] at hne; simp only [reverse', evalCall] at hne ⊢
        obtain ⟨n, d, g, h⟩ := evalArgs_reverse_complete c hE hf (by rw [ha]; exact err_ne_oof hne)
        rw [ha] at h
        exact ⟨n, d, g, by simp [evalF, hb, h]⟩
      | ok p =>
        obtain ⟨s₁, vs⟩ := p
        rw [ha] at hne; simp only [reverse'] at hne ⊢
        obtain ⟨n, d, g, h⟩ := evalArgs_reverse_complete c hE hf (by rw [ha]; simp [OOF])
        rw [ha] at h
        cases m with
        | zero => simp [evalCall] at hne
        | succ m' =>
          simp only [evalCall] at hne ⊢
          obtain ⟨n₂, d₂, g₂, h₂⟩ := (hAll m' (by omega)).2.2 vs.reverse f s₁ (head'_ne_oof hne)
          refine ⟨max n n₂, max d d₂, g + c.call + g₂, ?_⟩
          have a1 := liftA c (le_max_left n n₂) (le_max_left d d₂) h
          have a2 := liftC c (le_max_right n n₂) (le_max_right d d₂) h₂
          simp [evalF, hb, a1, a2]
    · simp only [hb] at hne ⊢; exact ⟨0, 0, 0, by simp [evalF, hb]⟩

theorem callC_step {co : Option YulContract} (hfun : FunctionsInFragment co) {fuel : ℕ}
    (hAll : AllBelow c co fuel) : CallC c co fuel := by
  intro args f s hne
  match fuel, hAll, hne with
  | 0, _, hne => exact absurd (by simp [call]) hne
  | m + 1, hAll, hne =>
    rw [call_succ_eq] at hne ⊢
    rcases hl : lookupFunction (some f) co s with e | fd
    · exact ⟨0, 1, 0, by simp [callF, hl]⟩
    · simp only [hl] at hne ⊢
      obtain ⟨n, d, g, h⟩ := (hAll m (by omega)).2.1 (.Block fd.body) _
        (by simpa [fragFS] using hfun s f fd hl) (callPost_ne_oof hne)
      simp only [runF, execF] at h
      exact ⟨n, d + 1, g, by simp [callF, hl, h]⟩

theorem casesF_of_selectCase_some {rc : Runner} {n : ℕ} {v : Literal} {s : State} {body : List Stmt} :
    ∀ {cases : List (Literal × List Stmt)}, selectCase v cases = some body →
      casesF c rc n cases v s = (blockF c rc n body s).map some
  | [], h => by simp [selectCase] at h
  | (l, b) :: rest, h => by
    by_cases hl : l = v
    · simp only [selectCase, hl, if_true, Option.some.injEq] at h
      subst h; simp [casesF, hl]
    · simp only [selectCase, hl, if_false] at h
      simp only [casesF, hl, if_false]; exact casesF_of_selectCase_some h

theorem casesF_of_selectCase_none {rc : Runner} {n : ℕ} {v : Literal} {s : State} :
    ∀ {cases : List (Literal × List Stmt)}, selectCase v cases = none →
      casesF c rc n cases v s = some none
  | [], _ => by simp [casesF]
  | (l, b) :: rest, h => by
    by_cases hl : l = v
    · simp [selectCase, hl] at h
    · simp only [selectCase, hl, if_false] at h
      simp only [casesF, hl, if_false]; exact casesF_of_selectCase_none h

theorem fragFB_of_selectCaseF {v : Literal} {body : List Stmt} :
    ∀ {cases : List (Literal × List Stmt)}, fragFCases cases = true →
      selectCase v cases = some body → fragFB body = true
  | [], _, h => by simp [selectCase] at h
  | (l, b) :: rest, hf, h => by
    simp only [fragFCases, Bool.and_eq_true] at hf
    by_cases hl : l = v
    · simp only [selectCase, hl, if_true, Option.some.injEq] at h
      subst h; exact hf.1
    · simp only [selectCase, hl, if_false] at h
      exact fragFB_of_selectCaseF hf.2 h

/-! ## Calls in statement position -/

theorem stmtPrim_complete {co : Option YulContract} {m : ℕ} (hE : ∀ k < m, EvalC c co k)
    {vars : List Identifier} {prim : PrimOp} {args : List Expr} {s : State}
    (hp : prim ∉ callFamily) (hf : fragFArgs args = true)
    (hne : execPrimCall m prim vars (reverse' (evalArgs m args.reverse co s)) ≠ OOF) :
    ∃ n d g, stmtPrimF c (callF c co n d) vars prim args s =
      some (execPrimCall m prim vars (reverse' (evalArgs m args.reverse co s)), g) := by
  cases ha : evalArgs m args.reverse co s with
  | error e =>
    rw [ha] at hne; simp only [reverse', execPrimCall] at hne ⊢
    obtain ⟨n, d, g, h⟩ := evalArgs_reverse_complete c hE hf (by rw [ha]; exact err_ne_oof hne)
    rw [ha] at h
    exact ⟨n, d, g, by simp [stmtPrimF, h]⟩
  | ok p =>
    obtain ⟨s₁, vs⟩ := p
    rw [ha] at hne; simp only [reverse', execPrimCall] at hne ⊢
    obtain ⟨n, d, g, h⟩ := evalArgs_reverse_complete c hE hf (by rw [ha]; simp [OOF])
    rw [ha] at h
    have hm : 1 ≤ m := by
      rcases m with _ | m
      · exact absurd (by simp [primCall, multifill']) hne
      · omega
    rw [primCall_eq_primResult hp hm]
    exact ⟨n, d, g + c.prim prim, by simp [stmtPrimF, h]⟩

theorem stmtCall_complete {co : Option YulContract} {m : ℕ} (hAll : AllBelow c co (m + 1))
    {vars : List Identifier} {f : YulFunctionName} {args : List Expr} {s : State}
    (hf : fragFArgs args = true)
    (hne : (match execObjectDataBuiltin? f vars (reverse' (evalArgs m args.reverse co s)) with
      | some r => r
      | none => execCall m f vars co (reverse' (evalArgs m args.reverse co s))) ≠ OOF) :
    ∃ n d g, stmtCallF c (callF c co n d) vars f args s =
      some ((match execObjectDataBuiltin? f vars (reverse' (evalArgs m args.reverse co s)) with
      | some r => r
      | none => execCall m f vars co (reverse' (evalArgs m args.reverse co s))), g) := by
  have hE : ∀ k < m, EvalC c co k := fun k hk => (hAll k (by omega)).1
  cases ha : evalArgs m args.reverse co s with
  | error e =>
    rw [ha] at hne; simp only [reverse', execObjectDataBuiltin?] at hne ⊢
    obtain ⟨n, d, g, h⟩ := evalArgs_reverse_complete c hE hf (by rw [ha]; exact err_ne_oof hne)
    rw [ha] at h
    exact ⟨n, d, g, by simp [stmtCallF, h]⟩
  | ok p =>
    obtain ⟨s₁, vs⟩ := p
    rw [ha] at hne; simp only [reverse'] at hne ⊢
    obtain ⟨n, d, g, h⟩ := evalArgs_reverse_complete c hE hf (by rw [ha]; simp [OOF])
    rw [ha] at h
    rcases hb : execObjectDataBuiltin? f vars (.ok (s₁, vs.reverse)) with _ | r
    · rw [hb] at hne; simp only at hne ⊢
      cases m with
      | zero => simp [execCall] at hne
      | succ m' =>
        simp only [execCall] at hne ⊢
        obtain ⟨n₂, d₂, g₂, h₂⟩ := (hAll m' (by omega)).2.2 vs.reverse f s₁ (multifill'_ne_oof hne)
        refine ⟨max n n₂, max d d₂, g + c.call + g₂, ?_⟩
        have a1 := liftA c (le_max_left n n₂) (le_max_left d d₂) h
        have a2 := liftC c (le_max_right n n₂) (le_max_right d d₂) h₂
        simp [stmtCallF, hb, a1, a2]
    · exact ⟨n, d, g, by simp [stmtCallF, h, hb]⟩

/-! ## Statements -/

theorem liftX {co : Option YulContract} {n d N D : ℕ} (hn : n ≤ N) (hd : d ≤ D) {st : Stmt}
    {s : State} {o : Res × ℕ} (h : execF c (callF c co n d) n st s = some o) :
    execF c (callF c co N D) N st s = some o :=
  execF_mono c (callF_mono c co hn hd) hn st s h

theorem liftFor {co : Option YulContract} {n d N D k : ℕ} (hn : n ≤ N) (hd : d ≤ D) (hk : n ≤ k)
    {cond : Expr} {post body : List Stmt} {s : State} {o : Res × ℕ}
    (h : runF c co n d (.For cond post body) s = some o) :
    loopF c (evalF c (callF c co N D) cond) (blockF c (callF c co N D) N body)
      (blockF c (callF c co N D) N post) k s = some o := by
  simp only [runF, execF] at h
  exact loopF_mono c (fun s _ h => liftE c hn hd h) (fun s _ h => liftB c hn hd h)
    (fun s _ h => liftB c hn hd h) n k s o hk h

theorem execC_step {co : Option YulContract} {fuel : ℕ} (hAll : AllBelow c co fuel) :
    ExecC c co fuel := by
  intro st s hf hne
  match fuel, hAll, hne with
  | 0, _, hne => exact absurd (by simp [exec]) hne
  | m + 1, hAll, hne =>
  have hE : ∀ k < m, EvalC c co k := fun k hk => (hAll k (by omega)).1
  have hEm : EvalC c co m := (hAll m (by omega)).1
  have hXm : ExecC c co m := (hAll m (by omega)).2.1
  simp only [runF]
  match st with
  | .Block [] => exact ⟨0, 0, 0, by simp [exec, execF, blockF]⟩
  | .Block (st :: sts) =>
    simp only [fragFS, fragFB, Bool.and_eq_true] at hf
    simp only [exec] at hne ⊢
    cases h1 : exec m st co s with
    | error e =>
      rw [h1] at hne; simp only at hne
      obtain ⟨n, d, g, hn⟩ := hXm st s hf.1 (by rw [h1]; exact hne)
      rw [h1] at hn; simp only [runF] at hn
      exact ⟨n, d, g, by simp [execF, blockF, hn]⟩
    | ok s₁ =>
      obtain ⟨n, d, g, hn⟩ := hXm st s hf.1 (by rw [h1]; simp [OOF])
      rw [h1] at hn hne; simp only [runF] at hn
      simp only at hne ⊢
      match s₁, hn, hne with
      | .Ok ss vs, hn, hne =>
        obtain ⟨n₂, d₂, g₂, hn₂⟩ := hXm (.Block sts) (.Ok ss vs) (by simpa [fragFS] using hf.2) hne
        simp only [runF, execF] at hn₂
        refine ⟨max n n₂, max d d₂, g + g₂, ?_⟩
        have a := liftX c (le_max_left n n₂) (le_max_left d d₂) hn
        have b := liftB c (le_max_right n n₂) (le_max_right d d₂) hn₂
        simp [execF, blockF, a, b, addGas]
      | .OutOfFuel, hn, _ => exact ⟨n, d, g, by simp [execF, blockF, hn]⟩
      | .Checkpoint j, hn, _ => exact ⟨n, d, g, by simp [execF, blockF, hn]⟩
  | .Let vars none => exact ⟨0, 0, 0, by simp [exec, execF]⟩
  | .Let vars (some (.Var x)) => exact ⟨0, 0, 0, by simp [exec, execF]⟩
  | .Let vars (some (.Lit v)) => exact ⟨0, 0, 0, by simp [exec, execF]⟩
  | .Let vars (some (.Call (.inl prim) args)) =>
    simp only [fragFS, fragFE, Bool.and_eq_true, decide_eq_true_eq] at hf
    simp only [exec] at hne ⊢
    simp only [execF]
    exact stmtPrim_complete c hE hf.1 hf.2 hne
  | .Let vars (some (.Call (.inr f) args)) =>
    simp only [fragFS, fragFE] at hf
    simp only [exec] at hne ⊢
    simp only [execF]
    exact stmtCall_complete c hAll hf hne
  | .ExprStmtCall (.Call (.inl prim) args) =>
    simp only [fragFS, fragFE, Bool.and_eq_true, decide_eq_true_eq] at hf
    simp only [exec] at hne ⊢
    simp only [execF]
    exact stmtPrim_complete c hE hf.1 hf.2 hne
  | .ExprStmtCall (.Call (.inr f) args) =>
    simp only [fragFS, fragFE] at hf
    simp only [exec] at hne ⊢
    simp only [execF]
    exact stmtCall_complete c hAll hf hne
  | .ExprStmtCall (.Var x) => exact ⟨0, 0, 0, by simp [exec, execF]⟩
  | .ExprStmtCall (.Lit v) => exact ⟨0, 0, 0, by simp [exec, execF]⟩
  | .If cond body =>
    simp only [fragFS, Bool.and_eq_true] at hf
    simp only [exec] at hne ⊢
    cases hc : eval m cond co s with
    | error e =>
      rw [hc] at hne; simp only at hne
      obtain ⟨n, d, g, h⟩ := hEm cond s hf.1 (by rw [hc]; exact err_ne_oof hne)
      rw [hc] at h
      exact ⟨n, d, g, by simp [execF, h]⟩
    | ok p =>
      obtain ⟨s₁, v⟩ := p
      obtain ⟨n, d, g, h⟩ := hEm cond s hf.1 (by rw [hc]; simp [OOF])
      rw [hc] at h hne
      simp only at hne ⊢
      by_cases hv : v = ⟨0⟩
      · simp only [hv, ne_eq, not_true_eq_false, if_false] at hne ⊢
        exact ⟨n, d, g + c.branch, by simp [execF, h, hv]⟩
      · simp only [hv, ne_eq, not_false_eq_true, if_true] at hne ⊢
        obtain ⟨n₂, d₂, gb, hn⟩ := hXm (.Block body) s₁ (by simpa [fragFS] using hf.2) hne
        simp only [runF, execF] at hn
        refine ⟨max n n₂, max d d₂, g + c.branch + gb, ?_⟩
        have a := liftE c (le_max_left n n₂) (le_max_left d d₂) h
        have b := liftB c (le_max_right n n₂) (le_max_right d d₂) hn
        simp [execF, a, hv, b, addGas]
  | .Switch cond cases dflt =>
    simp only [fragFS, Bool.and_eq_true] at hf
    obtain ⟨⟨hfc, hfcs⟩, hfd⟩ := hf
    simp only [exec] at hne ⊢
    cases hc : eval m cond co s with
    | error e =>
      rw [hc] at hne; simp only at hne
      obtain ⟨n, d, g, h⟩ := hEm cond s hfc (by rw [hc]; exact err_ne_oof hne)
      rw [hc] at h
      exact ⟨n, d, g, by simp [execF, h]⟩
    | ok p =>
      obtain ⟨s₁, v⟩ := p
      obtain ⟨n, d, g, h⟩ := hEm cond s hfc (by rw [hc]; simp [OOF])
      rw [hc] at h hne
      simp only at hne ⊢
      cases hsw : execSwitchCases m co s₁ cases with
      | error e =>
        rw [hsw] at hne; simp only at hne
        exact absurd (by rw [execSwitchCases_error hsw]) hne
      | ok branches =>
        rw [hsw] at hne; simp only at hne ⊢
        cases hd : exec m (.Block dflt) co s₁ with
        | error e =>
          rw [hd] at hne; simp only at hne
          obtain ⟨n₁, d₁, gd, hn⟩ := hXm (.Block dflt) s₁ (by simpa [fragFS] using hfd)
            (by rw [hd]; exact hne)
          rw [hd] at hn; simp only [runF, execF] at hn
          refine ⟨max n n₁, max d d₁, g + c.branch + gd, ?_⟩
          have a := liftE c (le_max_left n n₁) (le_max_left d d₁) h
          have b := liftB c (le_max_right n n₁) (le_max_right d d₁) hn
          simp [execF, a, b]
        | ok s₂ =>
          rw [hd] at hne; simp only at hne ⊢
          obtain ⟨n₁, d₁, gd, hn⟩ := hXm (.Block dflt) s₁ (by simpa [fragFS] using hfd)
            (by rw [hd]; simp [OOF])
          rw [hd] at hn; simp only [runF, execF] at hn
          change selectBranch v (.ok s₂) branches ≠ OOF at hne
          change ∃ n d g, execF c (callF c co n d) n (.Switch cond cases dflt) s =
            some (selectBranch v (.ok s₂) branches, g)
          rcases selectBranch_of_execSwitchCases (v := v) (d := .ok s₂) hsw with
            ⟨hsel, hres⟩ | ⟨body, m', hm', hsel, hres⟩
          · rw [hres]
            refine ⟨max n n₁, max d d₁, g + c.branch + gd, ?_⟩
            have a := liftE c (le_max_left n n₁) (le_max_left d d₁) h
            have b := liftB c (le_max_right n n₁) (le_max_right d d₁) hn
            simp [execF, a, b, casesF_of_selectCase_none c hsel]
          · rw [hres] at hne ⊢
            obtain ⟨n₂, d₂, gb, hn₂⟩ := (hAll m' (by omega)).2.1 (.Block body) s₁
              (by simpa [fragFS] using fragFB_of_selectCaseF hfcs hsel) hne
            simp only [runF, execF] at hn₂
            obtain ⟨N, hN⟩ : ∃ N, N = max (max n n₁) n₂ := ⟨_, rfl⟩
            obtain ⟨D, hD⟩ : ∃ D, D = max (max d d₁) d₂ := ⟨_, rfl⟩
            refine ⟨N, D, g + c.branch + gb, ?_⟩
            have a := liftE c (show n ≤ N by omega) (show d ≤ D by omega) h
            have b := liftB c (show n₁ ≤ N by omega) (show d₁ ≤ D by omega) hn
            have b2 := liftB c (show n₂ ≤ N by omega) (show d₂ ≤ D by omega) hn₂
            simp [execF, a, b, casesF_of_selectCase_some c hsel, b2]
  | .For cond post body =>
    simp only [fragFS, Bool.and_eq_true] at hf
    obtain ⟨⟨hfc, hfp⟩, hfb⟩ := hf
    have hfFor : fragFS (.For cond post body) = true := by simp [fragFS, hfc, hfp, hfb]
    simp only [exec] at hne ⊢
    simp only [execF]
    match m, hAll, hne with
    | 0, _, hne => exact absurd (by simp [loop]) hne
    | 1, _, hne => exact absurd (by simp [loop]) hne
    | m' + 2, hAll, hne =>
      have hEb : EvalC c co m' := (hAll m' (by omega)).1
      have hXb : ExecC c co m' := (hAll m' (by omega)).2.1
      simp only [loop] at hne ⊢
      cases hc : eval m' cond co (State.mkOk s) with
      | error e =>
        rw [hc] at hne; simp only at hne
        obtain ⟨n, d, g, h⟩ := hEb cond _ hfc (by rw [hc]; exact err_ne_oof hne)
        rw [hc] at h
        exact ⟨n, d, g, by unfold loopF; simp [h]⟩
      | ok p =>
        obtain ⟨s₁, x⟩ := p
        obtain ⟨n, d, g, h⟩ := hEb cond _ hfc (by rw [hc]; simp [OOF])
        rw [hc] at h hne
        simp only at hne ⊢
        by_cases hx : x = ⟨0⟩
        · simp only [hx, if_true] at hne ⊢
          exact ⟨n, d, g + c.branch, by unfold loopF; simp [h, hx]⟩
        · simp only [hx, if_false] at hne ⊢
          cases hb : exec m' (.Block body) co s₁ with
          | error e =>
            rw [hb] at hne; simp only at hne
            obtain ⟨n₁, d₁, gb, hn⟩ := hXb (.Block body) s₁ (by simpa [fragFS] using hfb)
              (by rw [hb]; exact hne)
            rw [hb] at hn; simp only [runF, execF] at hn
            obtain ⟨N, hN⟩ : ∃ N, N = max n n₁ := ⟨_, rfl⟩
            obtain ⟨D, hD⟩ : ∃ D, D = max d d₁ := ⟨_, rfl⟩
            have a := liftE c (show n ≤ N + 1 by omega) (show d ≤ D by omega) h
            have b := liftB c (show n₁ ≤ N + 1 by omega) (show d₁ ≤ D by omega) hn
            exact ⟨N + 1, D, g + c.branch + gb, by unfold loopF; simp [a, hx, b]⟩
          | ok s₂ =>
            rw [hb] at hne; simp only at hne ⊢
            obtain ⟨n₁, d₁, gb, hn⟩ := hXb (.Block body) s₁ (by simpa [fragFS] using hfb)
              (by rw [hb]; simp [OOF])
            rw [hb] at hn; simp only [runF, execF] at hn
            match s₂, hn, hne with
            | .OutOfFuel, hn, _ =>
              obtain ⟨N, hN⟩ : ∃ N, N = max n n₁ := ⟨_, rfl⟩
              obtain ⟨D, hD⟩ : ∃ D, D = max d d₁ := ⟨_, rfl⟩
              have a := liftE c (show n ≤ N + 1 by omega) (show d ≤ D by omega) h
              have b := liftB c (show n₁ ≤ N + 1 by omega) (show d₁ ≤ D by omega) hn
              exact ⟨N + 1, D, g + c.branch + gb, by unfold loopF; simp [a, hx, b]⟩
            | .Checkpoint (.Break ss vs), hn, _ =>
              obtain ⟨N, hN⟩ : ∃ N, N = max n n₁ := ⟨_, rfl⟩
              obtain ⟨D, hD⟩ : ∃ D, D = max d d₁ := ⟨_, rfl⟩
              have a := liftE c (show n ≤ N + 1 by omega) (show d ≤ D by omega) h
              have b := liftB c (show n₁ ≤ N + 1 by omega) (show d₁ ≤ D by omega) hn
              exact ⟨N + 1, D, g + c.branch + gb, by unfold loopF; simp [a, hx, b]⟩
            | .Checkpoint (.Leave ss vs), hn, _ =>
              obtain ⟨N, hN⟩ : ∃ N, N = max n n₁ := ⟨_, rfl⟩
              obtain ⟨D, hD⟩ : ∃ D, D = max d d₁ := ⟨_, rfl⟩
              have a := liftE c (show n ≤ N + 1 by omega) (show d ≤ D by omega) h
              have b := liftB c (show n₁ ≤ N + 1 by omega) (show d₁ ≤ D by omega) hn
              exact ⟨N + 1, D, g + c.branch + gb, by unfold loopF; simp [a, hx, b]⟩
            | .Checkpoint (.Continue ss vs), hn, hne =>
              simp only at hne ⊢
              cases hp : exec m' (.Block post) co (State.reviveJump (State.Checkpoint (.Continue ss vs))) with
              | error e =>
                rw [hp] at hne; simp only at hne
                obtain ⟨n₂, d₂, gp, hn₂⟩ := hXb (.Block post) _ (by simpa [fragFS] using hfp)
                  (by rw [hp]; exact hne)
                rw [hp] at hn₂; simp only [runF, execF] at hn₂
                obtain ⟨N, hN⟩ : ∃ N, N = max (max n n₁) n₂ := ⟨_, rfl⟩
                obtain ⟨D, hD⟩ : ∃ D, D = max (max d d₁) d₂ := ⟨_, rfl⟩
                have a := liftE c (show n ≤ N + 1 by omega) (show d ≤ D by omega) h
                have b := liftB c (show n₁ ≤ N + 1 by omega) (show d₁ ≤ D by omega) hn
                have b2 := liftB c (show n₂ ≤ N + 1 by omega) (show d₂ ≤ D by omega) hn₂
                exact ⟨N + 1, D, g + c.branch + gb + gp, by unfold loopF; simp [a, hx, b, b2]⟩
              | ok s₃ =>
                rw [hp] at hne; simp only at hne ⊢
                obtain ⟨n₂, d₂, gp, hn₂⟩ := hXb (.Block post) _ (by simpa [fragFS] using hfp)
                  (by rw [hp]; simp [OOF])
                rw [hp] at hn₂; simp only [runF, execF] at hn₂
                cases hr : exec m' (.For cond post body) co (s₃.overwrite? s) with
                  | error e =>
                    rw [hr] at hne; simp only at hne
                    obtain ⟨n₃, d₃, g₃, hn₃⟩ := hXb (.For cond post body) _ hfFor (by rw [hr]; exact hne)
                    rw [hr] at hn₃
                    obtain ⟨N, hN⟩ : ∃ N, N = max (max (max n n₁) n₂) n₃ := ⟨_, rfl⟩
                    obtain ⟨D, hD⟩ : ∃ D, D = max (max (max d d₁) d₂) d₃ := ⟨_, rfl⟩
                    have a := liftE c (show n ≤ N + 1 by omega) (show d ≤ D by omega) h
                    have b := liftB c (show n₁ ≤ N + 1 by omega) (show d₁ ≤ D by omega) hn
                    have b2 := liftB c (show n₂ ≤ N + 1 by omega) (show d₂ ≤ D by omega) hn₂
                    have c3 := liftFor c (show n₃ ≤ N + 1 by omega) (show d₃ ≤ D by omega)
                      (show n₃ ≤ N by omega) hn₃
                    exact ⟨N + 1, D, g + c.branch + gb + gp + g₃,
                      by unfold loopF; simp [a, hx, b, b2, c3, Except.map]⟩
                  | ok s₅ =>
                    obtain ⟨n₃, d₃, g₃, hn₃⟩ := hXb (.For cond post body) _ hfFor (by rw [hr]; simp [OOF])
                    rw [hr] at hn₃
                    obtain ⟨N, hN⟩ : ∃ N, N = max (max (max n n₁) n₂) n₃ := ⟨_, rfl⟩
                    obtain ⟨D, hD⟩ : ∃ D, D = max (max (max d d₁) d₂) d₃ := ⟨_, rfl⟩
                    have a := liftE c (show n ≤ N + 1 by omega) (show d ≤ D by omega) h
                    have b := liftB c (show n₁ ≤ N + 1 by omega) (show d₁ ≤ D by omega) hn
                    have b2 := liftB c (show n₂ ≤ N + 1 by omega) (show d₂ ≤ D by omega) hn₂
                    have c3 := liftFor c (show n₃ ≤ N + 1 by omega) (show d₃ ≤ D by omega)
                      (show n₃ ≤ N by omega) hn₃
                    exact ⟨N + 1, D, g + c.branch + gb + gp + g₃,
                      by unfold loopF; simp [a, hx, b, b2, c3, Except.map]⟩
            | .Ok ss vs, hn, hne =>
              simp only at hne ⊢
              cases hp : exec m' (.Block post) co (State.reviveJump (State.Ok ss vs)) with
              | error e =>
                rw [hp] at hne; simp only at hne
                obtain ⟨n₂, d₂, gp, hn₂⟩ := hXb (.Block post) _ (by simpa [fragFS] using hfp)
                  (by rw [hp]; exact hne)
                rw [hp] at hn₂; simp only [runF, execF] at hn₂
                obtain ⟨N, hN⟩ : ∃ N, N = max (max n n₁) n₂ := ⟨_, rfl⟩
                obtain ⟨D, hD⟩ : ∃ D, D = max (max d d₁) d₂ := ⟨_, rfl⟩
                have a := liftE c (show n ≤ N + 1 by omega) (show d ≤ D by omega) h
                have b := liftB c (show n₁ ≤ N + 1 by omega) (show d₁ ≤ D by omega) hn
                have b2 := liftB c (show n₂ ≤ N + 1 by omega) (show d₂ ≤ D by omega) hn₂
                exact ⟨N + 1, D, g + c.branch + gb + gp, by unfold loopF; simp [a, hx, b, b2]⟩
              | ok s₃ =>
                rw [hp] at hne; simp only at hne ⊢
                obtain ⟨n₂, d₂, gp, hn₂⟩ := hXb (.Block post) _ (by simpa [fragFS] using hfp)
                  (by rw [hp]; simp [OOF])
                rw [hp] at hn₂; simp only [runF, execF] at hn₂
                cases hr : exec m' (.For cond post body) co (s₃.overwrite? s) with
                  | error e =>
                    rw [hr] at hne; simp only at hne
                    obtain ⟨n₃, d₃, g₃, hn₃⟩ := hXb (.For cond post body) _ hfFor (by rw [hr]; exact hne)
                    rw [hr] at hn₃
                    obtain ⟨N, hN⟩ : ∃ N, N = max (max (max n n₁) n₂) n₃ := ⟨_, rfl⟩
                    obtain ⟨D, hD⟩ : ∃ D, D = max (max (max d d₁) d₂) d₃ := ⟨_, rfl⟩
                    have a := liftE c (show n ≤ N + 1 by omega) (show d ≤ D by omega) h
                    have b := liftB c (show n₁ ≤ N + 1 by omega) (show d₁ ≤ D by omega) hn
                    have b2 := liftB c (show n₂ ≤ N + 1 by omega) (show d₂ ≤ D by omega) hn₂
                    have c3 := liftFor c (show n₃ ≤ N + 1 by omega) (show d₃ ≤ D by omega)
                      (show n₃ ≤ N by omega) hn₃
                    exact ⟨N + 1, D, g + c.branch + gb + gp + g₃,
                      by unfold loopF; simp [a, hx, b, b2, c3, Except.map]⟩
                  | ok s₅ =>
                    obtain ⟨n₃, d₃, g₃, hn₃⟩ := hXb (.For cond post body) _ hfFor (by rw [hr]; simp [OOF])
                    rw [hr] at hn₃
                    obtain ⟨N, hN⟩ : ∃ N, N = max (max (max n n₁) n₂) n₃ := ⟨_, rfl⟩
                    obtain ⟨D, hD⟩ : ∃ D, D = max (max (max d d₁) d₂) d₃ := ⟨_, rfl⟩
                    have a := liftE c (show n ≤ N + 1 by omega) (show d ≤ D by omega) h
                    have b := liftB c (show n₁ ≤ N + 1 by omega) (show d₁ ≤ D by omega) hn
                    have b2 := liftB c (show n₂ ≤ N + 1 by omega) (show d₂ ≤ D by omega) hn₂
                    have c3 := liftFor c (show n₃ ≤ N + 1 by omega) (show d₃ ≤ D by omega)
                      (show n₃ ≤ N by omega) hn₃
                    exact ⟨N + 1, D, g + c.branch + gb + gp + g₃,
                      by unfold loopF; simp [a, hx, b, b2, c3, Except.map]⟩
  | .Continue => exact ⟨0, 0, 0, by simp [exec, execF]⟩
  | .Break => exact ⟨0, 0, 0, by simp [exec, execF]⟩
  | .Leave => exact ⟨0, 0, 0, by simp [exec, execF]⟩

/-! ## Main results -/

/-- Completeness of the meter at every fuel. -/
theorem complete_all {co : Option YulContract} (hfun : FunctionsInFragment co) :
    ∀ fuel, EvalC c co fuel ∧ ExecC c co fuel ∧ CallC c co fuel := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ih =>
    have hAll : AllBelow c co fuel := ih
    exact ⟨evalC_step c hAll, execC_step c hAll, callC_step c hfun hAll⟩

/-- **The interpreter is metered by `runF`.** On the fragment with user functions and nested loops,
when every function the interpreter can look up has its body in the fragment, every interpreter run
that does not run out of fuel is a `runF` run for some iteration budget `n` and call-depth budget
`d`. -/
theorem exec_complete_runF {fuel : ℕ} {st : Stmt} {co : Option YulContract} {s : State}
    (hf : InFnFragment st) (hfun : FunctionsInFragment co) (h : exec fuel st co s ≠ OOF) :
    ∃ n d g, runF c co n d st s = some (exec fuel st co s, g) :=
  (complete_all c hfun fuel).2.1 st s hf h

/-- **Yul gas bound with user-defined functions.** For a Yul program without contract calls, whose
loops may be nested and whose user functions may be (mutually) recursive, every interpreter run
that does not run out of fuel is metered by `runF`: there are budgets `n` (loop iterations per loop
entry) and `d` (call depth) at which `runF` returns the run's result `r` with gas
`g ≤ gasF c tbl n d st`, and all larger budgets give the same result and gas. `tbl` is any function
table that covers the functions the interpreter can look up (`TableCovers`). -/
theorem exec_fn_gas_bound {fuel : ℕ} {st : Stmt} {co : Option YulContract} {s : State} {r : Res}
    {tbl : FnTable} (hf : InFnFragment st) (hfun : FunctionsInFragment co)
    (htbl : TableCovers co tbl) (h : exec fuel st co s = r) (hr : r ≠ OOF) :
    ∃ n d g, runF c co n d st s = some (r, g) ∧ g ≤ gasF c tbl n d st ∧
      ∀ n' d', n ≤ n' → d ≤ d' → runF c co n' d' st s = some (r, g) := by
  obtain ⟨n, d, g, hn⟩ := exec_complete_runF c hf hfun (fuel := fuel) (h ▸ hr)
  rw [h] at hn
  exact ⟨n, d, g, hn, runF_gas_le c htbl n d st s hn,
    fun n' d' hn' hd' => runF_mono c hn' hd' hn⟩

/-- With a code override `some code`, the interpreter can only look functions up in `code`. -/
theorem functionsInFragment_some {code : YulContract}
    (hcode : ∀ f fd, code.functions.lookup f = some fd → fragFB fd.body = true) :
    FunctionsInFragment (some code) :=
  fun s f fd h => hcode f fd (tableCovers_some code s f fd h)

/-- **`exec_fn_gas_bound` for a fixed contract.** When the interpreter runs with code override
`some code` and every function of `code` is in the fragment, the bound uses `code`'s own function
table. -/
theorem exec_fn_gas_bound_code {fuel : ℕ} {st : Stmt} {code : YulContract} {s : State} {r : Res}
    (hf : InFnFragment st)
    (hcode : ∀ f fd, code.functions.lookup f = some fd → fragFB fd.body = true)
    (h : exec fuel st (some code) s = r) (hr : r ≠ OOF) :
    ∃ n d g, runF c (some code) n d st s = some (r, g) ∧
      g ≤ gasF c (fun f => code.functions.lookup f) n d st ∧
      ∀ n' d', n ≤ n' → d ≤ d' → runF c (some code) n' d' st s = some (r, g) :=
  exec_fn_gas_bound c hf (functionsInFragment_some hcode) (tableCovers_some code) h hr

/-! ## Conservative extension of the call-free layer -/

mutual

theorem evalF_of_fragE (rc : Runner) : (e : Expr) → (s : State) → fragE e = true →
    evalF c rc e s = some (evalG c.toCostModel e s)
  | .Lit _, _, _ => by simp [evalF, evalG]
  | .Var _, _, _ => by simp [evalF, evalG]
  | .Call (.inl prim) args, s, hf => by
    simp only [fragE, Bool.and_eq_true, decide_eq_true_eq] at hf
    simp only [evalF, evalG, argsF_of_fragArgs rc args s hf.2]
    rcases argsG c.toCostModel args s with ⟨_ | ⟨s₁, vs⟩, g⟩ <;> rfl
  | .Call (.inr _) _, _, hf => by simp [fragE] at hf

theorem argsF_of_fragArgs (rc : Runner) : (as : List Expr) → (s : State) → fragArgs as = true →
    argsF c rc as s = some (argsG c.toCostModel as s)
  | [], _, _ => by simp [argsF, argsG]
  | a :: as, s, hf => by
    simp only [fragArgs, Bool.and_eq_true] at hf
    simp only [argsF, argsG, argsF_of_fragArgs rc as s hf.2]
    rcases argsG c.toCostModel as s with ⟨_ | ⟨s₁, vs⟩, g⟩
    · rfl
    · simp only [evalF_of_fragE rc a s₁ hf.1]
      rcases evalG c.toCostModel a s₁ with ⟨_ | ⟨s₂, v⟩, g'⟩ <;> rfl

end

/-- With a condition runner that is `evalG` and the same body and post runners, `loopF` is the
call-free loop driver `loopWith`. -/
theorem loopF_eq_loopWith (cond : Expr) {rcd : State → Option (ResV × ℕ)}
    {rb rp : State → Option (Res × ℕ)} (hc : ∀ s, rcd s = some (evalG c.toCostModel cond s)) :
    ∀ k s, loopF c rcd rb rp k s = loopWith c.toCostModel cond rb rp k s := by
  intro k
  induction k with
  | zero =>
    intro s
    unfold loopF loopWith
    rw [hc]
    rcases evalG c.toCostModel cond (State.mkOk s) with ⟨_ | ⟨s₁, x⟩, g⟩ <;> rfl
  | succ k ih =>
    intro s
    unfold loopF loopWith
    rw [hc]
    rcases evalG c.toCostModel cond (State.mkOk s) with ⟨_ | ⟨s₁, x⟩, g⟩
    · rfl
    · simp only [ih]
      rfl

mutual

/-- On call-free programs (with nested loops), `execF` with any call runner is `execL`. -/
theorem execF_of_fragLS (rc : Runner) (n : ℕ) : (st : Stmt) → (s : State) → fragLS st = true →
    execF c rc n st s = execL c.toCostModel n st s
  | .Block sts, s, hf => by
    simp only [fragLS] at hf; simp only [execF, execL]; exact blockF_of_fragLB rc n sts s hf
  | .Let _ none, _, _ => by simp [execF, execL, execG]
  | .Let _ (some (.Var _)), _, _ => by simp [execF, execL, execG]
  | .Let _ (some (.Lit _)), _, _ => by simp [execF, execL, execG]
  | .Let vars (some (.Call (.inl prim) args)), s, hf => by
    simp only [fragLS, fragE, Bool.and_eq_true, decide_eq_true_eq] at hf
    simp only [execF, execL, execG, stmtPrimF, argsF_of_fragArgs c rc args s hf.2]
    rcases argsG c.toCostModel args s with ⟨_ | ⟨s₁, vs⟩, g⟩ <;> rfl
  | .Let _ (some (.Call (.inr _) _)), _, hf => by simp [fragLS, fragE] at hf
  | .ExprStmtCall (.Call (.inl prim) args), s, hf => by
    simp only [fragLS, fragE, Bool.and_eq_true, decide_eq_true_eq] at hf
    simp only [execF, execL, execG, stmtPrimF, argsF_of_fragArgs c rc args s hf.2]
    rcases argsG c.toCostModel args s with ⟨_ | ⟨s₁, vs⟩, g⟩ <;> rfl
  | .ExprStmtCall (.Call (.inr _) _), _, hf => by simp [fragLS, fragE] at hf
  | .ExprStmtCall (.Var _), _, _ => by simp [execF, execL, execG]
  | .ExprStmtCall (.Lit _), _, _ => by simp [execF, execL, execG]
  | .If cond body, s, hf => by
    simp only [fragLS, Bool.and_eq_true] at hf
    simp only [execF, execL, evalF_of_fragE c rc cond s hf.1, blockF_of_fragLB rc n body _ hf.2]
    rcases evalG c.toCostModel cond s with ⟨_ | ⟨s₁, v⟩, g⟩ <;> rfl
  | .Switch cond cases dflt, s, hf => by
    simp only [fragLS, Bool.and_eq_true] at hf
    obtain ⟨⟨hfc, hfcs⟩, hfd⟩ := hf
    simp only [execF, execL, evalF_of_fragE c rc cond s hfc]
    rcases evalG c.toCostModel cond s with ⟨_ | ⟨s₁, v⟩, g⟩
    · rfl
    · simp only [blockF_of_fragLB rc n dflt s₁ hfd, casesF_of_fragLCases rc n cases v s₁ hfcs]
      rcases blockL c.toCostModel n dflt s₁ with _ | ⟨_ | s₂, gd⟩
      · rfl
      · rfl
      · rcases casesL c.toCostModel n cases v s₁ with _ | _ | ⟨r, gb⟩ <;> rfl
  | .For cond post body, s, hf => by
    simp only [fragLS, Bool.and_eq_true] at hf
    obtain ⟨⟨hfc, hfp⟩, hfb⟩ := hf
    simp only [execF, execL]
    have hb : blockF c rc n body = blockL c.toCostModel n body :=
      funext fun s => blockF_of_fragLB rc n body s hfb
    have hp : blockF c rc n post = blockL c.toCostModel n post :=
      funext fun s => blockF_of_fragLB rc n post s hfp
    rw [hb, hp]
    exact loopF_eq_loopWith c cond (fun s => evalF_of_fragE c rc cond s hfc) n s
  | .Continue, _, _ => by simp [execF, execL]
  | .Break, _, _ => by simp [execF, execL]
  | .Leave, _, _ => by simp [execF, execL]

theorem blockF_of_fragLB (rc : Runner) (n : ℕ) : (sts : List Stmt) → (s : State) →
    fragLB sts = true → blockF c rc n sts s = blockL c.toCostModel n sts s
  | [], _, _ => by simp [blockF, blockL]
  | st :: sts, s, hf => by
    simp only [fragLB, Bool.and_eq_true] at hf
    simp only [blockF, blockL, execF_of_fragLS rc n st s hf.1]
    rcases execL c.toCostModel n st s with _ | ⟨_ | (⟨ss, vs⟩ | _ | j), g⟩
    · rfl
    · rfl
    · simp only [blockF_of_fragLB rc n sts _ hf.2]
    · rfl
    · rfl

theorem casesF_of_fragLCases (rc : Runner) (n : ℕ) : (cases : List (Literal × List Stmt)) →
    (v : Literal) → (s : State) → fragLCases cases = true →
    casesF c rc n cases v s = casesL c.toCostModel n cases v s
  | [], _, _, _ => by simp [casesF, casesL]
  | (l, body) :: rest, v, s, hf => by
    simp only [fragLCases, Bool.and_eq_true] at hf
    by_cases hl : l = v
    · simp [casesF, casesL, hl, blockF_of_fragLB rc n body s hf.1]
    · simp only [casesF, casesL, hl, if_false]; exact casesF_of_fragLCases rc n rest v s hf.2

end

/-- **Conservative extension.** On call-free programs, `runF` (with any call-depth budget) is the
nested-loop meter `execL`. -/
theorem runF_of_fragLS (co : Option YulContract) (n d : ℕ) {st : Stmt} (hf : fragLS st = true)
    (s : State) : runF c co n d st s = execL c.toCostModel n st s :=
  execF_of_fragLS c _ n st s hf

mutual

theorem gasFE_of_fragE (gc : YulFunctionName → ℕ) : (e : Expr) → fragE e = true →
    gasFE c gc e = gasE c.toCostModel e
  | .Lit _, _ => by simp [gasFE, gasE]
  | .Var _, _ => by simp [gasFE, gasE]
  | .Call (.inl prim) args, hf => by
    simp only [fragE, Bool.and_eq_true, decide_eq_true_eq] at hf
    simp [gasFE, gasE, gasFArgs_of_fragArgs gc args hf.2]
  | .Call (.inr _) _, hf => by simp [fragE] at hf

theorem gasFArgs_of_fragArgs (gc : YulFunctionName → ℕ) : (as : List Expr) → fragArgs as = true →
    gasFArgs c gc as = gasArgs c.toCostModel as
  | [], _ => by simp [gasFArgs, gasArgs]
  | a :: as, hf => by
    simp only [fragArgs, Bool.and_eq_true] at hf
    simp [gasFArgs, gasArgs, gasFE_of_fragE gc a hf.1, gasFArgs_of_fragArgs gc as hf.2]

end

mutual

theorem gasFS_of_fragLS (gc : YulFunctionName → ℕ) (n : ℕ) : (st : Stmt) → fragLS st = true →
    gasFS c gc n st = gasLS c.toCostModel n st
  | .Block sts, hf => by
    simp only [fragLS] at hf; simp only [gasFS, gasLS]; exact gasFB_of_fragLB gc n sts hf
  | .Let _ none, _ => by simp [gasFS, gasLS]
  | .Let _ (some e), hf => by
    simp only [fragLS] at hf; simp [gasFS, gasLS, gasFE_of_fragE c gc e hf]
  | .ExprStmtCall e, hf => by
    simp only [fragLS] at hf; simp [gasFS, gasLS, gasFE_of_fragE c gc e hf]
  | .If cond body, hf => by
    simp only [fragLS, Bool.and_eq_true] at hf
    simp [gasFS, gasLS, gasFE_of_fragE c gc cond hf.1, gasFB_of_fragLB gc n body hf.2]
  | .Switch cond cases dflt, hf => by
    simp only [fragLS, Bool.and_eq_true] at hf
    simp [gasFS, gasLS, gasFE_of_fragE c gc cond hf.1.1, gasFB_of_fragLB gc n dflt hf.2,
      gasFCases_of_fragLCases gc n cases hf.1.2]
  | .For cond post body, hf => by
    simp only [fragLS, Bool.and_eq_true] at hf
    simp [gasFS, gasLS, gasFE_of_fragE c gc cond hf.1.1, gasFB_of_fragLB gc n body hf.2,
      gasFB_of_fragLB gc n post hf.1.2]
  | .Continue, _ => by simp [gasFS, gasLS]
  | .Break, _ => by simp [gasFS, gasLS]
  | .Leave, _ => by simp [gasFS, gasLS]

theorem gasFB_of_fragLB (gc : YulFunctionName → ℕ) (n : ℕ) : (sts : List Stmt) →
    fragLB sts = true → gasFB c gc n sts = gasLB c.toCostModel n sts
  | [], _ => by simp [gasFB, gasLB]
  | st :: sts, hf => by
    simp only [fragLB, Bool.and_eq_true] at hf
    simp [gasFB, gasLB, gasFS_of_fragLS gc n st hf.1, gasFB_of_fragLB gc n sts hf.2]

theorem gasFCases_of_fragLCases (gc : YulFunctionName → ℕ) (n : ℕ) :
    (cases : List (Literal × List Stmt)) → fragLCases cases = true →
    gasFCases c gc n cases = gasLCases c.toCostModel n cases
  | [], _ => by simp [gasFCases, gasLCases]
  | (_, body) :: rest, hf => by
    simp only [fragLCases, Bool.and_eq_true] at hf
    simp [gasFCases, gasLCases, gasFB_of_fragLB gc n body hf.1,
      gasFCases_of_fragLCases gc n rest hf.2]

end

/-- **Conservative extension of the bound.** On call-free programs, `gasF` (for any table and any
call-depth budget) is the nested-loop bound `gasLS`. -/
theorem gasF_of_fragLS (tbl : FnTable) (n d : ℕ) {st : Stmt} (hf : fragLS st = true) :
    gasF c tbl n d st = gasLS c.toCostModel n st :=
  gasFS_of_fragLS c _ n st hf

end Gas
end Yul
end EvmYul
