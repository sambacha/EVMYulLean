module

public import EvmYul.Yul.Relational.Soundness

public section

/-!
# A weakest-precondition calculus for Yul, sound with respect to the relational semantics

`wp co stmt Q s` holds when **every** result the relational semantics allows for `stmt` from `s`
satisfies `Q` (partial correctness: a statement with no derivation satisfies every `wp`). Each rule
below is a theorem about `ExecR`, proved by inversion of the relation, so the calculus is sound by
construction. `wp_exec` then transfers a `wp` fact to the executable interpreter through
`exec_sound`: no fuel appears in the rules or in the proofs that use them.

The loop rule `wp_for` is the usual invariant rule. It is stated for loops whose states stay in
the `Ok` form (no `break`/`continue`/`leave` escapes the body, which the premises enforce), which is
the shape of loops produced by `solc` after `for`-initialiser hoisting.
-/

namespace EvmYul
namespace Yul
namespace Relational

open Ast

/-- Weakest precondition of a statement for postcondition `Q` (partial correctness). -/
@[expose] def wp (co : Option YulContract) (st : Stmt) (Q : Res → Prop) (s : State) : Prop :=
  ∀ r, ExecR co st s r → Q r

/-- Weakest precondition of an expression. -/
@[expose] def wpE (co : Option YulContract) (e : Expr) (Q : ResV → Prop) (s : State) : Prop :=
  ∀ r, EvalR co e s r → Q r

/-- Weakest precondition of an argument list (evaluated left to right). -/
@[expose] def wpA (co : Option YulContract) (args : List Expr) (Q : ResL → Prop) (s : State) : Prop :=
  ∀ r, ArgsR co args s r → Q r

/-- **Soundness of the calculus for the interpreter.** A `wp` fact holds for every terminating
run of the executable interpreter, at any fuel. -/
theorem wp_exec {co : Option YulContract} {st : Stmt} {Q : Res → Prop} {s : State}
    (h : wp co st Q s) {fuel : ℕ} {r : Res} (hrun : exec fuel st co s = r)
    (hr : r ≠ .error .OutOfFuel) : Q r :=
  h r (exec_sound hrun hr)

/-- `wp_exec` for successful runs. -/
theorem wp_exec_ok {co : Option YulContract} {st : Stmt} {Q : Res → Prop} {s s' : State}
    (h : wp co st Q s) {fuel : ℕ} (hrun : exec fuel st co s = .ok s') : Q (.ok s') :=
  wp_exec h hrun (by simp)

theorem wp_mono {co : Option YulContract} {st : Stmt} {Q Q' : Res → Prop} {s : State}
    (hQ : ∀ r, Q r → Q' r) (h : wp co st Q s) : wp co st Q' s :=
  fun r hr => hQ r (h r hr)

/-! ## The `Ok` form of states -/

/-- The state is an ordinary (non-checkpoint, non-diverged) state. -/
@[expose] def IsOk : State → Prop
  | .Ok _ _ => True
  | _ => False

theorem IsOk.mkOk {s : State} (h : IsOk s) : State.mkOk s = s := by
  cases s <;> simp_all [IsOk, State.mkOk]

theorem IsOk.overwrite {s : State} (h : IsOk s) (s₁ : State) : s₁.overwrite? s = s₁ := by
  cases s <;> simp_all [IsOk, State.overwrite?]

theorem IsOk.reviveJump {s : State} (h : IsOk s) : s.reviveJump = s := by
  cases s <;> simp_all [IsOk, State.reviveJump]

theorem IsOk.insert {s : State} (h : IsOk s) (x : Identifier) (v : Literal) :
    IsOk (s.insert x v) := by
  cases s <;> simp_all [IsOk, State.insert]

/-! ## Expressions and arguments -/

theorem wpE_lit {co : Option YulContract} {v : Literal} {Q : ResV → Prop} {s : State}
    (h : Q (.ok (s, v))) : wpE co (.Lit v) Q s := by
  intro r hr; cases hr; exact h

theorem wpE_var {co : Option YulContract} {x : Identifier} {Q : ResV → Prop} {s : State}
    (h : Q (.ok (s, s[x]!))) : wpE co (.Var x) Q s := by
  intro r hr; cases hr; exact h

theorem wpA_nil {co : Option YulContract} {Q : ResL → Prop} {s : State}
    (h : Q (.ok (s, []))) : wpA co [] Q s := by
  intro r hr; cases hr; exact h

theorem wpA_cons {co : Option YulContract} {a : Expr} {as : List Expr} {Q : ResL → Prop}
    {s : State}
    (h : wpE co a (fun rv => match rv with
      | .error e => Q (.error e)
      | .ok (s₁, v) => wpA co as (fun r => Q (cons' v r)) s₁) s) :
    wpA co (a :: as) Q s := by
  intro r hr
  cases hr with
  | consErr he => exact h _ he
  | cons he hrest => exact h _ he _ hrest

/-! ## Builtins

For every builtin other than the four contract-call opcodes, `primCallK` does not use its
dispatcher argument, so `PrimR` is a function of its inputs. -/

/-- The builtins that call another contract. -/
@[expose] def callFamily : List PrimOp := [.CALL, .STATICCALL, .CALLCODE, .DELEGATECALL]

/-- The result of a builtin that does not call another contract. -/
@[expose] def primResult (s : State) (prim : PrimOp) (args : List Literal) : ResL :=
  primCallK (fun _ _ => .error .OutOfFuel) s prim args

theorem primCallK_indep {prim : PrimOp} (hp : prim ∉ callFamily)
    (k k' : Option YulContract → State → ResL) (s : State) (args : List Literal) :
    primCallK k s prim args = primCallK k' s prim args := by
  cases prim with
  | System op =>
    cases op <;> first | rfl | (exfalso; simp [callFamily] at hp)
  | _ => rfl

theorem PrimR.eq_primResult {s : State} {prim : PrimOp} {args : List Literal} {r : ResL}
    (hp : prim ∉ callFamily) (h : PrimR s prim args r) : r = primResult s prim args := by
  cases h with
  | mk k _ _ => exact primCallK_indep hp _ _ s args

/-- `let vars := prim(args)` for a builtin that does not call another contract. -/
theorem wp_letPrim {co : Option YulContract} {vars : List Identifier} {prim : PrimOp}
    {args : List Expr} {Q : Res → Prop} {s : State} (hp : prim ∉ callFamily)
    (h : wpA co args.reverse (fun ra => match ra with
      | .error e => Q (.error e)
      | .ok (s₁, vs) => Q (multifill' vars (primResult s₁ prim vs.reverse))) s) :
    wp co (.Let vars (some (.Call (.inl prim) args))) Q s := by
  intro r hr
  cases hr with
  | letPrimArgsErr ha => exact h _ ha
  | letPrim ha hP =>
    have := h _ ha
    rwa [PrimR.eq_primResult hp hP]

/-- A builtin used as an expression, for a builtin that does not call another contract. -/
theorem wpE_prim {co : Option YulContract} {prim : PrimOp} {args : List Expr} {Q : ResV → Prop}
    {s : State} (hp : prim ∉ callFamily)
    (h : wpA co args.reverse (fun ra => match ra with
      | .error e => Q (.error e)
      | .ok (s₁, vs) => Q (head' (primResult s₁ prim vs.reverse))) s) :
    wpE co (.Call (.inl prim) args) Q s := by
  intro r hr
  cases hr with
  | primArgsErr ha => exact h _ ha
  | prim ha hP =>
    have := h _ ha
    rwa [PrimR.eq_primResult hp hP]

/-! ## Statements -/

theorem wp_blockNil {co : Option YulContract} {Q : Res → Prop} {s : State} (h : Q (.ok s)) :
    wp co (.Block []) Q s := by
  intro r hr; cases hr; exact h

/-- What has to hold after the first statement of a block. -/
@[expose] def blockK (co : Option YulContract) (sts : List Stmt) (Q : Res → Prop) : Res → Prop
  | .error e => Q (.error e)
  | .ok (.Ok ss vs) => wp co (.Block sts) Q (.Ok ss vs)
  | .ok s₁ => Q (.ok s₁)

theorem wp_blockCons {co : Option YulContract} {st : Stmt} {sts : List Stmt} {Q : Res → Prop}
    {s : State} (h : wp co st (blockK co sts Q) s) : wp co (.Block (st :: sts)) Q s := by
  intro r hr
  cases hr with
  | blockErr he => exact h _ he
  | blockCons h1 h2 => exact h _ h1 _ h2
  | blockJump h1 => exact h _ h1
  | blockOOF h1 => exact h _ h1

theorem wp_letLit {co : Option YulContract} {x : Identifier} {v : Literal} {Q : Res → Prop}
    {s : State} (h : Q (.ok (s.insert x v))) : wp co (.Let [x] (some (.Lit v))) Q s := by
  intro r hr; cases hr; exact h

theorem wp_letVar {co : Option YulContract} {x y : Identifier} {Q : Res → Prop} {s : State}
    (h : Q (.ok (s.insert x s[y]!))) : wp co (.Let [x] (some (.Var y))) Q s := by
  intro r hr; cases hr; exact h

theorem wp_if {co : Option YulContract} {cond : Expr} {body : List Stmt} {Q : Res → Prop}
    {s : State}
    (h : wpE co cond (fun rv => match rv with
      | .error e => Q (.error e)
      | .ok (s₁, c) => (c ≠ ⟨0⟩ → wp co (.Block body) Q s₁) ∧ (c = ⟨0⟩ → Q (.ok s₁))) s) :
    wp co (.If cond body) Q s := by
  intro r hr
  cases hr with
  | ifErr he => exact h _ he
  | ifTrue he hc hb => exact (h _ he).1 hc _ hb
  | ifFalse he hc => exact (h _ he).2 hc

/-! ## Loops -/

/-- Induction principle for loops: `LoopR` is the least relation closed under its eight rules,
where the recursive call goes through `ExecR.for_`. (The relations are mutually inductive, so this
is derived from the generated recursor.) -/
theorem LoopR.induct {co : Option YulContract} {cond : Expr} {post body : List Stmt}
    (P : State → Res → Prop)
    (condErr : ∀ {s e}, EvalR co cond (State.mkOk s) (.error e) → P s (.error e))
    (exit : ∀ {s s₁ x}, EvalR co cond (State.mkOk s) (.ok (s₁, x)) → x = ⟨0⟩ →
      P s (.ok (s₁.overwrite? s)))
    (bodyErr : ∀ {s s₁ x e}, EvalR co cond (State.mkOk s) (.ok (s₁, x)) → x ≠ ⟨0⟩ →
      ExecR co (.Block body) s₁ (.error e) → P s (.error e))
    (bodyOOF : ∀ {s s₁ x}, EvalR co cond (State.mkOk s) (.ok (s₁, x)) → x ≠ ⟨0⟩ →
      ExecR co (.Block body) s₁ (.ok .OutOfFuel) → P s (.ok (State.OutOfFuel.overwrite? s)))
    (break_ : ∀ {s s₁ x ss vs}, EvalR co cond (State.mkOk s) (.ok (s₁, x)) → x ≠ ⟨0⟩ →
      ExecR co (.Block body) s₁ (.ok (.Checkpoint (.Break ss vs))) →
      P s (.ok ((State.Checkpoint (.Break ss vs)).reviveJump.overwrite? s)))
    (leave : ∀ {s s₁ x ss vs}, EvalR co cond (State.mkOk s) (.ok (s₁, x)) → x ≠ ⟨0⟩ →
      ExecR co (.Block body) s₁ (.ok (.Checkpoint (.Leave ss vs))) →
      P s (.ok ((State.Checkpoint (.Leave ss vs)).overwrite? s)))
    (postErr : ∀ {s s₁ s₂ x e}, EvalR co cond (State.mkOk s) (.ok (s₁, x)) → x ≠ ⟨0⟩ →
      ExecR co (.Block body) s₁ (.ok s₂) → continuesLoop s₂ →
      ExecR co (.Block post) s₂.reviveJump (.error e) → P s (.error e))
    (next : ∀ {s s₁ s₂ s₃ x r}, EvalR co cond (State.mkOk s) (.ok (s₁, x)) → x ≠ ⟨0⟩ →
      ExecR co (.Block body) s₁ (.ok s₂) → continuesLoop s₂ →
      ExecR co (.Block post) s₂.reviveJump (.ok s₃) →
      ExecR co (.For cond post body) (s₃.overwrite? s) r → P (s₃.overwrite? s) r →
      P s (r.map (·.overwrite? s)))
    {s : State} {r : Res} (h : LoopR co cond post body s r) : P s r := by
  suffices H : co = co → cond = cond → post = post → body = body → P s r from H rfl rfl rfl rfl
  apply LoopR.rec
    (motive_1 := fun _ _ _ _ _ => True) (motive_2 := fun _ _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ => True) (motive_4 := fun _ _ _ _ => True)
    (motive_5 := fun _ _ _ _ _ => True) (motive_6 := fun _ _ _ _ _ => True)
    (motive_7 := fun co' st s r _ => co' = co → st = .For cond post body → P s r)
    (motive_8 := fun co' cond' post' body' s r _ =>
      co' = co → cond' = cond → post' = post → body' = body → P s r)
    (t := h)
  all_goals (beta_reduce; intros)
  all_goals first | trivial | (rename_i hst; cases hst; done) | skip
  case for_ =>
    rename_i ihl hco hst
    injection hst with h1 h2 h3
    exact ihl hco h1 h2 h3
  case condErr => subst_vars; exact condErr ‹_›
  case exit => subst_vars; exact exit ‹_› rfl
  case bodyErr => subst_vars; exact bodyErr ‹_› ‹_› ‹_›
  case bodyOOF => subst_vars; exact bodyOOF ‹_› ‹_› ‹_›
  case break_ => subst_vars; exact break_ ‹_› ‹_› ‹_›
  case leave => subst_vars; exact leave ‹_› ‹_› ‹_›
  case postErr => subst_vars; exact postErr ‹_› ‹_› ‹_› ‹_› ‹_›
  case next =>
    rename_i hE hx hB hc hP hF _ _ _ ihF _ _ _ _
    subst_vars
    exact next hE hx hB hc hP hF (ihF rfl rfl)

/-- **Loop invariant rule.** If the invariant `I` describes `Ok` states, and from any state
satisfying `I` the condition, body and post block either establish `Q` (when the loop exits or
fails) or re-establish `I` through `Ok` states, then every result of the loop satisfies `Q`. -/
theorem wp_for {co : Option YulContract} {cond : Expr} {post body : List Stmt}
    (I : State → Prop) {Q : Res → Prop}
    (hOk : ∀ s, I s → IsOk s)
    (hstep : ∀ s, I s → wpE co cond (fun rv => match rv with
      | .error e => Q (.error e)
      | .ok (s₁, x) => (x = ⟨0⟩ → Q (.ok s₁)) ∧
          (x ≠ ⟨0⟩ → wp co (.Block body) (fun r => match r with
            | .error e => Q (.error e)
            | .ok s₂ => IsOk s₂ ∧ wp co (.Block post) (fun r' => match r' with
                | .error e => Q (.error e)
                | .ok s₃ => I s₃) s₂) s₁)) s)
    {s : State} (hs : I s) : wp co (.For cond post body) Q s := by
  intro r hr
  cases hr with
  | for_ hl =>
    refine LoopR.induct (fun s r => I s → Q r) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hl hs
    · intro s e he hI
      rw [(hOk s hI).mkOk] at he
      exact hstep s hI _ he
    · intro s s₁ x he hx hI
      rw [(hOk s hI).mkOk] at he
      rw [(hOk s hI).overwrite]
      exact (hstep s hI _ he).1 hx
    · intro s s₁ x e he hx hb hI
      rw [(hOk s hI).mkOk] at he
      exact (hstep s hI _ he).2 hx _ hb
    · intro s s₁ x he hx hb hI
      rw [(hOk s hI).mkOk] at he
      exact absurd ((hstep s hI _ he).2 hx _ hb).1 id
    · intro s s₁ x ss vs he hx hb hI
      rw [(hOk s hI).mkOk] at he
      exact absurd ((hstep s hI _ he).2 hx _ hb).1 id
    · intro s s₁ x ss vs he hx hb hI
      rw [(hOk s hI).mkOk] at he
      exact absurd ((hstep s hI _ he).2 hx _ hb).1 id
    · intro s s₁ s₂ x e he hx hb _ hp hI
      rw [(hOk s hI).mkOk] at he
      obtain ⟨hOk₂, hpost⟩ := (hstep s hI _ he).2 hx _ hb
      rw [hOk₂.reviveJump] at hp
      exact hpost _ hp
    · intro s s₁ s₂ s₃ x r he hx hb _ hp _ ih hI
      rw [(hOk s hI).mkOk] at he
      obtain ⟨hOk₂, hpost⟩ := (hstep s hI _ he).2 hx _ hb
      rw [hOk₂.reviveJump] at hp
      have hI₃ : I s₃ := hpost _ hp
      rw [(hOk s hI).overwrite] at ih
      have hmap : r.map (·.overwrite? s) = r := by
        cases r <;> simp [Except.map, (hOk s hI).overwrite]
      rw [hmap]
      exact ih hI₃

end Relational
end Yul
end EvmYul
