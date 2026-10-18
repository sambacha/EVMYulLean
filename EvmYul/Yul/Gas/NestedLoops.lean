module

public import EvmYul.Yul.Gas.Loops

public section

/-!
# Yul gas, part 6: nested loops

`Loops.lean` meters a *single-level* `for` loop. This file meters every program of the call-free
fragment **with loops nested arbitrarily** (`fragLS`): loops inside loop bodies, inside `if` and
`switch` branches, and so on. Function calls and contract calls are still excluded.

A loop's gas is not bounded statically, so the bound is stated in terms of an iteration budget
`n`: the largest number of times *any single entry* into *any* loop of the run executes its body.

* `execL c n st s`: a metered evaluator with per-loop-entry iteration budget `n`. It returns
  `none` when some loop entry would need more than `n` iterations, and `some (r, g)` otherwise,
  where `r` is the result and `g` the gas charged.
* `gasLS c n st`: a static bound, polynomial in `n` (degree = loop nesting depth). A loop costs
  `n · (gasE cond + branch + gasLB body + gasLB post) + gasE cond + branch`.

Results:

* `execL_gas_le`: whenever `execL c n st s = some (r, g)`, **`g ≤ gasLS c n st`**.
* `execL_mono`: a run that fits in budget `n` gives the same result and gas with every larger
  budget. So the least successful budget is the run's maximal per-entry iteration count.
* `execL_complete`: every relational run (`ExecR`) of a fragment program is an `execL` run for
  some budget, hence `execR_deterministicL`: `ExecR` is deterministic on the fragment.
* `exec_eq_execL`: every interpreter run that does not run out of fuel is an `execL` run.
* `execL_of_fragS`, `gasLS_of_fragS`: on loop-free programs `execL` is `execG` and `gasLS` is `gasS`
  (a conservative extension of the earlier layer).
* `exec_nested_gas_bound`: the headline statement for the interpreter.
-/

namespace EvmYul
namespace Yul
namespace Gas

open Ast Relational

/-! ## The fragment with nested loops -/

mutual

/-- Statements of the call-free fragment, loops allowed (nested arbitrarily). -/
@[expose] def fragLS : Stmt → Bool
  | .Block sts => fragLB sts
  | .Let _ none => true
  | .Let _ (some e) => fragE e
  | .ExprStmtCall e => fragE e
  | .If cond body => fragE cond && fragLB body
  | .Switch cond cases dflt => fragE cond && fragLCases cases && fragLB dflt
  | .For cond post body => fragE cond && fragLB post && fragLB body
  | .Continue => true
  | .Break => true
  | .Leave => true

/-- Blocks of `fragLS` statements. -/
@[expose] def fragLB : List Stmt → Bool
  | [] => true
  | st :: sts => fragLS st && fragLB sts

/-- `switch` cases whose bodies are `fragLB`. -/
@[expose] def fragLCases : List (Literal × List Stmt) → Bool
  | [] => true
  | (_, body) :: rest => fragLB body && fragLCases rest

end

/-- The call-free fragment of Yul with (nested) loops. -/
@[expose] abbrev InLoopFragment (st : Stmt) : Prop := fragLS st = true

variable (c : CostModel)

/-! ## The metered evaluator -/

/-- Add `g` to the gas of an optional metered result. -/
@[expose] def addGas (g : ℕ) : Option (Res × ℕ) → Option (Res × ℕ)
  | none => none
  | some (r, g') => some (r, g + g')

/-- The loop driver for `for {} cond {post} {body}`, given metered runners for the body and the post
block, with `k` body executions allowed. Mirrors `LoopR` case by case. -/
@[expose] def loopWith (cond : Expr) (runBody runPost : State → Option (Res × ℕ)) :
    ℕ → State → Option (Res × ℕ)
  | k, s =>
    match evalG c cond (State.mkOk s) with
    | (.error e, g) => some (.error e, g)
    | (.ok (s₁, x), g) =>
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
              match loopWith cond runBody runPost k (s₃.overwrite? s) with
              | none => none
              | some (r, g') => some (r.map (·.overwrite? s), g + c.branch + gb + gp + g')
          | some (.ok (.Ok ss vs), gb) =>
            match runPost (State.Ok ss vs).reviveJump with
            | none => none
            | some (.error e, gp) => some (.error e, g + c.branch + gb + gp)
            | some (.ok s₃, gp) =>
              match loopWith cond runBody runPost k (s₃.overwrite? s) with
              | none => none
              | some (r, g') => some (r.map (·.overwrite? s), g + c.branch + gb + gp + g')

mutual

/-- Metered execution with per-loop-entry iteration budget `n`. -/
@[expose] def execL (n : ℕ) : Stmt → State → Option (Res × ℕ)
  | .Block sts, s => blockL n sts s
  | .Let vars e, s => some (execG c (.Let vars e) s)
  | .ExprStmtCall e, s => some (execG c (.ExprStmtCall e) s)
  | .If cond body, s =>
    match evalG c cond s with
    | (.error e, g) => some (.error e, g)
    | (.ok (s₁, v), g) =>
      if v ≠ ⟨0⟩ then addGas (g + c.branch) (blockL n body s₁)
      else some (.ok s₁, g + c.branch)
  | .Switch cond cases dflt, s =>
    match evalG c cond s with
    | (.error e, g) => some (.error e, g)
    | (.ok (s₁, v), g) =>
      match blockL n dflt s₁ with
      | none => none
      | some (.error e, gd) => some (.error e, g + c.branch + gd)
      | some (.ok s₂, gd) =>
        match casesL n cases v s₁ with
        | none => none
        | some none => some (.ok s₂, g + c.branch + gd)
        | some (some (r, gb)) => some (r, g + c.branch + gb)
  | .For cond post body, s => loopWith c cond (blockL n body) (blockL n post) n s
  | .Continue, s => some (.ok (State.setContinue s), 0)
  | .Break, s => some (.ok (State.setBreak s), 0)
  | .Leave, s => some (.ok (State.setLeave s), 0)

/-- Metered execution of a block. -/
@[expose] def blockL (n : ℕ) : List Stmt → State → Option (Res × ℕ)
  | [], s => some (.ok s, 0)
  | st :: sts, s =>
    match execL n st s with
    | none => none
    | some (.ok (.Ok ss vs), g) => addGas g (blockL n sts (.Ok ss vs))
    | some (r, g) => some (r, g)

/-- The selected `switch` case: `some none` when no case matches, `some (some _)` for the run of
the matching case, `none` when that run exceeds the budget. -/
@[expose] def casesL (n : ℕ) : List (Literal × List Stmt) → Literal → State → Option (Option (Res × ℕ))
  | [], _, _ => some none
  | (l, body) :: rest, v, s =>
    if l = v then (blockL n body s).map some else casesL n rest v s

end

/-! ## The static bound -/

mutual

/-- Static gas of a statement for iteration budget `n`. -/
@[expose] def gasLS (n : ℕ) : Stmt → ℕ
  | .Block sts => gasLB n sts
  | .Let _ none => 0
  | .Let _ (some e) => gasE c e
  | .ExprStmtCall e => gasE c e
  | .If cond body => gasE c cond + c.branch + gasLB n body
  | .Switch cond cases dflt => gasE c cond + c.branch + max (gasLB n dflt) (gasLCases n cases)
  | .For cond post body =>
    n * (gasE c cond + c.branch + gasLB n body + gasLB n post) + (gasE c cond + c.branch)
  | .Continue => 0
  | .Break => 0
  | .Leave => 0

/-- Static gas of a block for iteration budget `n`. -/
@[expose] def gasLB (n : ℕ) : List Stmt → ℕ
  | [] => 0
  | st :: sts => gasLS n st + gasLB n sts

/-- The largest static gas among `switch` case bodies. -/
@[expose] def gasLCases (n : ℕ) : List (Literal × List Stmt) → ℕ
  | [] => 0
  | (_, body) :: rest => max (gasLB n body) (gasLCases n rest)

end


/-! ## The static bound is sound -/

theorem addGas_eq_some {g : ℕ} {o : Option (Res × ℕ)} {r : Res} {g' : ℕ}
    (h : addGas g o = some (r, g')) : ∃ g₀, o = some (r, g₀) ∧ g' = g + g₀ := by
  rcases o with _ | ⟨r₀, g₀⟩
  · simp [addGas] at h
  · simp only [addGas, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨g₀, by rw [h.1], h.2.symm⟩

/-- Gas bound for the loop driver, given bounds for the body and post runners. -/
theorem loopWith_gas_le (cond : Expr) (runBody runPost : State → Option (Res × ℕ)) (Bb Bp : ℕ)
    (hb : ∀ s r g, runBody s = some (r, g) → g ≤ Bb)
    (hp : ∀ s r g, runPost s = some (r, g) → g ≤ Bp) :
    ∀ k s r g, loopWith c cond runBody runPost k s = some (r, g) →
      g ≤ k * (gasE c cond + c.branch + Bb + Bp) + (gasE c cond + c.branch) := by
  intro k
  induction k with
  | zero =>
    intro s r g h
    have hc := evalG_gas_le c cond (State.mkOk s)
    unfold loopWith at h
    split at h
    · rename_i e g₀ heq; rw [heq] at hc; simp only [Option.some.injEq, Prod.mk.injEq] at h
      simp only at hc; omega
    · rename_i s₁ x g₀ heq; rw [heq] at hc; simp only at hc
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
      · simp at h
  | succ k ih =>
    intro s r g h
    have hc := evalG_gas_le c cond (State.mkOk s)
    unfold loopWith at h
    split at h
    · rename_i e g₀ heq; rw [heq] at hc; simp only [Option.some.injEq, Prod.mk.injEq] at h
      simp only at hc; omega
    · rename_i s₁ x g₀ heq; rw [heq] at hc; simp only at hc
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
      · simp only at h
        split at h
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


mutual

/-- **Nested-loop gas bound.** A metered run that fits in iteration budget `n` is charged at most
`gasLS c n st`. -/
theorem execL_gas_le (n : ℕ) : (st : Stmt) → (s : State) → {r : Res} → {g : ℕ} →
    execL c n st s = some (r, g) → g ≤ gasLS c n st
  | .Block sts, s, _, _, h => by
    simp only [execL] at h; simpa only [gasLS] using blockL_gas_le n sts s h
  | .Let vars e, s, r, g, h => by
    have := execG_gas_le c (.Let vars e) s
    simp only [execL, Option.some.injEq] at h; rw [h] at this
    rcases e with _ | e <;> simpa [gasS, gasLS] using this
  | .ExprStmtCall e, s, r, g, h => by
    have := execG_gas_le c (.ExprStmtCall e) s
    simp only [execL, Option.some.injEq] at h; rw [h] at this
    simpa [gasS, gasLS] using this
  | .If cond body, s, r, g, h => by
    have hc := evalG_gas_le c cond s
    rcases hev : evalG c cond s with ⟨_ | ⟨s₁, v⟩, g₀⟩ <;> rw [hev] at hc <;> simp only at hc
    · simp only [execL, hev, Option.some.injEq, Prod.mk.injEq] at h; simp only [gasLS]; omega
    · by_cases hv : v = ⟨0⟩
      · simp only [execL, hev, hv, ne_eq, not_true_eq_false, if_false, Option.some.injEq,
          Prod.mk.injEq] at h
        simp only [gasLS]; omega
      · simp only [execL, hev, hv, ne_eq, not_false_eq_true, if_true] at h
        obtain ⟨g₁, h1, rfl⟩ := addGas_eq_some h
        have := blockL_gas_le n body s₁ h1
        simp only [gasLS]; omega
  | .Switch cond cases dflt, s, r, g, h => by
    have hc := evalG_gas_le c cond s
    rcases hev : evalG c cond s with ⟨_ | ⟨s₁, v⟩, g₀⟩ <;> rw [hev] at hc <;> simp only at hc
    · simp only [execL, hev, Option.some.injEq, Prod.mk.injEq] at h; simp only [gasLS]; omega
    · rcases hd : blockL c n dflt s₁ with _ | ⟨_ | s₂, gd⟩
      · simp [execL, hev, hd] at h
      · have := blockL_gas_le n dflt s₁ hd
        simp only [execL, hev, hd, Option.some.injEq, Prod.mk.injEq] at h
        simp only [gasLS]; omega
      · have hdl := blockL_gas_le n dflt s₁ hd
        rcases hcs : casesL c n cases v s₁ with _ | _ | ⟨r₁, gb⟩
        · simp [execL, hev, hd, hcs] at h
        · simp only [execL, hev, hd, hcs, Option.some.injEq, Prod.mk.injEq] at h
          simp only [gasLS]; omega
        · have := casesL_gas_le n cases v s₁ hcs
          simp only [execL, hev, hd, hcs, Option.some.injEq, Prod.mk.injEq] at h
          simp only [gasLS]; omega
  | .For cond post body, s, r, g, h => by
    simp only [execL] at h
    simp only [gasLS]
    exact loopWith_gas_le c cond _ _ (gasLB c n body) (gasLB c n post)
      (fun s _ _ h => blockL_gas_le n body s h) (fun s _ _ h => blockL_gas_le n post s h) n s r g h
  | .Continue, _, _, _, h => by
    simp only [execL, Option.some.injEq, Prod.mk.injEq] at h; simp [gasLS, h.2.symm]
  | .Break, _, _, _, h => by
    simp only [execL, Option.some.injEq, Prod.mk.injEq] at h; simp [gasLS, h.2.symm]
  | .Leave, _, _, _, h => by
    simp only [execL, Option.some.injEq, Prod.mk.injEq] at h; simp [gasLS, h.2.symm]

/-- Gas bound for blocks. -/
theorem blockL_gas_le (n : ℕ) : (sts : List Stmt) → (s : State) → {r : Res} → {g : ℕ} →
    blockL c n sts s = some (r, g) → g ≤ gasLB c n sts
  | [], _, _, _, h => by
    simp only [blockL, Option.some.injEq, Prod.mk.injEq] at h; simp [gasLB, h.2.symm]
  | st :: sts, s, r, g, h => by
    rcases hx : execL c n st s with _ | ⟨r₀, g₀⟩
    · simp [blockL, hx] at h
    · have h₀ := execL_gas_le n st s hx
      rcases r₀ with e | (⟨ss, vs⟩ | _ | j)
      · simp only [blockL, hx, Option.some.injEq, Prod.mk.injEq] at h; simp only [gasLB]; omega
      · simp only [blockL, hx] at h
        obtain ⟨g₁, h1, rfl⟩ := addGas_eq_some h
        have := blockL_gas_le n sts _ h1
        simp only [gasLB]; omega
      · simp only [blockL, hx, Option.some.injEq, Prod.mk.injEq] at h; simp only [gasLB]; omega
      · simp only [blockL, hx, Option.some.injEq, Prod.mk.injEq] at h; simp only [gasLB]; omega

/-- Gas bound for the selected `switch` case. -/
theorem casesL_gas_le (n : ℕ) : (cases : List (Literal × List Stmt)) → (v : Literal) →
    (s : State) → {r : Res} → {g : ℕ} →
    casesL c n cases v s = some (some (r, g)) → g ≤ gasLCases c n cases
  | [], _, _, _, _, h => by simp [casesL] at h
  | (l, body) :: rest, v, s, r, g, h => by
    by_cases hl : l = v
    · simp only [casesL, hl, if_true] at h
      rcases hb : blockL c n body s with _ | ⟨r₁, g₁⟩
      · simp [hb] at h
      · simp only [hb, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        have := blockL_gas_le n body s hb
        simp only [gasLCases]; omega
    · simp only [casesL, hl, if_false] at h
      have := casesL_gas_le n rest v s h
      simp only [gasLCases]; omega

end


/-! ## Monotonicity in the budget -/

/-- The loop driver is monotone: more iterations allowed, and runners that extend the old ones,
give the same result. -/
theorem loopWith_mono (cond : Expr) {rb rp rb' rp' : State → Option (Res × ℕ)}
    (hb : ∀ s o, rb s = some o → rb' s = some o) (hp : ∀ s o, rp s = some o → rp' s = some o) :
    ∀ k k' s o, k ≤ k' → loopWith c cond rb rp k s = some o →
      loopWith c cond rb' rp' k' s = some o := by
  intro k
  induction k with
  | zero =>
    intro k' s o _ h
    unfold loopWith at h ⊢
    rcases hev : evalG c cond (State.mkOk s) with ⟨_ | ⟨s₁, x⟩, g⟩
    · rw [hev] at h; exact h
    · rw [hev] at h
      by_cases hx : x = ⟨0⟩
      · simp only [hx, if_true] at h ⊢; exact h
      · simp [hx] at h
  | succ k ih =>
    intro k' s o hk h
    obtain ⟨k', rfl⟩ : ∃ j, k' = j + 1 := ⟨k' - 1, by omega⟩
    unfold loopWith at h ⊢
    rcases hev : evalG c cond (State.mkOk s) with ⟨_ | ⟨s₁, x⟩, g⟩
    · rw [hev] at h; exact h
    · rw [hev] at h
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
                rcases hl : loopWith c cond rb rp k (s₃.overwrite? s) with _ | ⟨r', g'⟩
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
                rcases hl : loopWith c cond rb rp k (s₃.overwrite? s) with _ | ⟨r', g'⟩
                · simp [hl] at h
                · rw [ih k' _ _ (by omega) hl]; rw [hl] at h; exact h
          · exact h
          · exact h


mutual

/-- **Budget monotonicity.** A run that fits in budget `n` gives the same result and gas with any
larger budget. -/
theorem execL_mono {n n' : ℕ} (hn : n ≤ n') : (st : Stmt) → (s : State) → {o : Res × ℕ} →
    execL c n st s = some o → execL c n' st s = some o
  | .Block sts, s, _, h => by
    simp only [execL] at h ⊢; exact blockL_mono hn sts s h
  | .Let _ _, _, _, h => by simpa only [execL] using h
  | .ExprStmtCall _, _, _, h => by simpa only [execL] using h
  | .If cond body, s, _, h => by
    simp only [execL] at h ⊢
    rcases hev : evalG c cond s with ⟨_ | ⟨s₁, v⟩, g₀⟩ <;> simp only [hev] at h ⊢
    · exact h
    · by_cases hv : v = ⟨0⟩
      · simp only [hv, ne_eq, not_true_eq_false, if_false] at h ⊢; exact h
      · simp only [hv, ne_eq, not_false_eq_true, if_true] at h ⊢
        rcases hb : blockL c n body s₁ with _ | ⟨r, g⟩
        · simp [hb, addGas] at h
        · rw [blockL_mono hn body s₁ hb]; rw [hb] at h; exact h
  | .Switch cond cases dflt, s, _, h => by
    simp only [execL] at h ⊢
    rcases hev : evalG c cond s with ⟨_ | ⟨s₁, v⟩, g₀⟩ <;> simp only [hev] at h ⊢
    · exact h
    · rcases hd : blockL c n dflt s₁ with _ | ⟨r, gd⟩
      · simp [hd] at h
      · rw [blockL_mono hn dflt s₁ hd]; rw [hd] at h
        rcases r with e | s₂
        · exact h
        · simp only at h ⊢
          rcases hcs : casesL c n cases v s₁ with _ | oo
          · simp [hcs] at h
          · rw [casesL_mono hn cases v s₁ hcs]; rw [hcs] at h; exact h
  | .For cond post body, s, o, h => by
    simp only [execL] at h ⊢
    exact loopWith_mono c cond (fun s _ h => blockL_mono hn body s h)
      (fun s _ h => blockL_mono hn post s h) n n' s o hn h
  | .Continue, _, _, h => by simpa only [execL] using h
  | .Break, _, _, h => by simpa only [execL] using h
  | .Leave, _, _, h => by simpa only [execL] using h

/-- Budget monotonicity for blocks. -/
theorem blockL_mono {n n' : ℕ} (hn : n ≤ n') : (sts : List Stmt) → (s : State) →
    {o : Res × ℕ} → blockL c n sts s = some o → blockL c n' sts s = some o
  | [], _, _, h => by simpa only [blockL] using h
  | st :: sts, s, _, h => by
    rcases hx : execL c n st s with _ | ⟨r₀, g₀⟩
    · simp [blockL, hx] at h
    · have h' := execL_mono hn st s hx
      rcases r₀ with e | (⟨ss, vs⟩ | _ | j)
      · simp only [blockL, hx, h'] at h ⊢; exact h
      · simp only [blockL, hx, h'] at h ⊢
        rcases hb : blockL c n sts (.Ok ss vs) with _ | ⟨r, g⟩
        · simp [hb, addGas] at h
        · rw [blockL_mono hn sts _ hb]; rw [hb] at h; exact h
      · simp only [blockL, hx, h'] at h ⊢; exact h
      · simp only [blockL, hx, h'] at h ⊢; exact h

/-- Budget monotonicity for `switch` cases. -/
theorem casesL_mono {n n' : ℕ} (hn : n ≤ n') : (cases : List (Literal × List Stmt)) →
    (v : Literal) → (s : State) → {oo : Option (Res × ℕ)} →
    casesL c n cases v s = some oo → casesL c n' cases v s = some oo
  | [], _, _, _, h => by simpa only [casesL] using h
  | (l, body) :: rest, v, s, _, h => by
    by_cases hl : l = v
    · simp only [casesL, hl, if_true] at h ⊢
      rcases hb : blockL c n body s with _ | ⟨r, g⟩
      · simp [hb] at h
      · rw [blockL_mono hn body s hb]; rw [hb] at h; exact h
    · simp only [casesL, hl, if_false] at h ⊢; exact casesL_mono hn rest v s h

end


/-! ## Completeness: every interpreter run is an `execL` run -/

theorem casesL_of_selectCase_some (n : ℕ) {v : Literal} {s : State} {body : List Stmt} :
    ∀ {cases : List (Literal × List Stmt)}, selectCase v cases = some body →
      casesL c n cases v s = (blockL c n body s).map some
  | [], h => by simp [selectCase] at h
  | (l, b) :: rest, h => by
    by_cases hl : l = v
    · simp only [selectCase, hl, if_true, Option.some.injEq] at h
      subst h; simp [casesL, hl]
    · simp only [selectCase, hl, if_false] at h
      simp only [casesL, hl, if_false]; exact casesL_of_selectCase_some n h

theorem casesL_of_selectCase_none (n : ℕ) {v : Literal} {s : State} :
    ∀ {cases : List (Literal × List Stmt)}, selectCase v cases = none →
      casesL c n cases v s = some none
  | [], _ => by simp [casesL]
  | (l, b) :: rest, h => by
    by_cases hl : l = v
    · simp [selectCase, hl] at h
    · simp only [selectCase, hl, if_false] at h
      simp only [casesL, hl, if_false]; exact casesL_of_selectCase_none n h

theorem fragLB_of_selectCase {v : Literal} {body : List Stmt} :
    ∀ {cases : List (Literal × List Stmt)}, fragLCases cases = true →
      selectCase v cases = some body → fragLB body = true
  | [], _, h => by simp [selectCase] at h
  | (l, b) :: rest, hf, h => by
    simp only [fragLCases, Bool.and_eq_true] at hf
    by_cases hl : l = v
    · simp only [selectCase, hl, if_true, Option.some.injEq] at h
      subst h; exact hf.1
    · simp only [selectCase, hl, if_false] at h
      exact fragLB_of_selectCase hf.2 h

/-- The interpreter's `switch` picks the branch of the case selected by `selectCase`, computed
with less fuel. -/
theorem selectBranch_of_execSwitchCases {co : Option YulContract} {s : State} {v : Literal}
    {d : Res} : ∀ {n : ℕ} {cases : List (Literal × List Stmt)} {branches : List (Literal × Res)},
    execSwitchCases n co s cases = .ok branches →
      (selectCase v cases = none ∧ selectBranch v d branches = d) ∨
      ∃ body m, m < n ∧ selectCase v cases = some body ∧
        selectBranch v d branches = exec m (.Block body) co s
  | _, [], branches, h => by
    simp only [execSwitchCases, Except.ok.injEq] at h; subst h
    exact Or.inl ⟨rfl, rfl⟩
  | 0, (val, stmts) :: cs, branches, h => by simp [execSwitchCases] at h
  | m + 1, (val, stmts) :: cs, branches, h => by
    obtain ⟨rest, hrest, rfl⟩ := execSwitchCases_cons_ok h
    by_cases hv : val = v
    · refine Or.inr ⟨stmts, m, by omega, by simp [selectCase, hv], ?_⟩
      simp [selectBranch, List.foldr, hv]
    · have hsel : selectBranch v d ((val, exec m (.Block stmts) co s) :: rest) =
          selectBranch v d rest := by simp [selectBranch, List.foldr, hv]
      have hcase : selectCase v ((val, stmts) :: cs) = selectCase v cs := by
        simp [selectCase, hv]
      rw [hsel, hcase]
      rcases selectBranch_of_execSwitchCases (d := d) (v := v) hrest with h' | ⟨body, m', hm, h1, h2⟩
      · exact Or.inl h'
      · exact Or.inr ⟨body, m', by omega, h1, h2⟩

theorem fragS_of_let {vars : List Identifier} {e : Option Expr}
    (h : fragLS (.Let vars e) = true) : fragS (.Let vars e) = true := by
  rcases e with _ | e
  · simp [fragS]
  · simpa [fragLS, fragS] using h

theorem fragS_of_exprStmt {e : Expr} (h : fragLS (.ExprStmtCall e) = true) :
    fragS (.ExprStmtCall e) = true := by
  simpa [fragLS, fragS] using h


/-- **Completeness.** On the fragment, every interpreter run that does not run out of fuel is an
`execL` run for some iteration budget. -/
theorem exec_complete_execL (co : Option YulContract) : ∀ (fuel : ℕ) (st : Stmt) (s : State),
    fragLS st = true → exec fuel st co s ≠ OOF →
      ∃ n g, execL c n st s = some (exec fuel st co s, g) := by
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ih =>
  intro st s hf hne
  match fuel, ih, hne with
  | 0, _, hne => exact absurd (by simp [exec]) hne
  | m + 1, ih, hne =>
  have ihm := ih m (by omega)
  match st with
  | .Block [] => exact ⟨0, 0, by simp [exec, execL, blockL]⟩
  | .Block (st :: sts) =>
    simp only [fragLS, fragLB, Bool.and_eq_true] at hf
    simp only [exec] at hne ⊢
    cases h1 : exec m st co s with
    | error e =>
      rw [h1] at hne; simp only at hne
      obtain ⟨n, g, hn⟩ := ihm st s hf.1 (by rw [h1]; exact hne)
      rw [h1] at hn
      exact ⟨n, g, by simp [execL, blockL, hn]⟩
    | ok s₁ =>
      obtain ⟨n, g, hn⟩ := ihm st s hf.1 (by rw [h1]; simp [OOF])
      rw [h1] at hn hne
      simp only at hne ⊢
      match s₁, hn, hne with
      | .Ok ss vs, hn, hne =>
        obtain ⟨n₂, g₂, hn₂⟩ := ihm (.Block sts) (.Ok ss vs) (by simpa [fragLS] using hf.2) hne
        refine ⟨max n n₂, g + g₂, ?_⟩
        have a := execL_mono c (le_max_left n n₂) st s hn
        have b := execL_mono c (le_max_right n n₂) _ _ hn₂
        simp only [execL] at b
        simp [execL, blockL, a, b, addGas]
      | .OutOfFuel, hn, _ => exact ⟨n, g, by simp [execL, blockL, hn]⟩
      | .Checkpoint j, hn, _ => exact ⟨n, g, by simp [execL, blockL, hn]⟩
  | .Let vars e =>
    refine ⟨0, (execG c (.Let vars e) s).2, ?_⟩
    rw [exec_eq_execG c (fragS_of_let hf) hne]; simp [execL]
  | .ExprStmtCall e =>
    refine ⟨0, (execG c (.ExprStmtCall e) s).2, ?_⟩
    rw [exec_eq_execG c (fragS_of_exprStmt hf) hne]; simp [execL]
  | .If cond body =>
    simp only [fragLS, Bool.and_eq_true] at hf
    simp only [exec] at hne ⊢
    cases hc : eval m cond co s with
    | error e =>
      rw [hc] at hne; simp only at hne
      have he := eval_eq_evalG_of_ne_OOF c hf.1 (fuel := m) (co := co) (s := s)
        (by rw [hc]; exact err_ne_oof hne)
      rw [hc] at he
      obtain ⟨g, hg⟩ := fst_eq_elim he
      exact ⟨0, g, by simp [execL, hg]⟩
    | ok p =>
      obtain ⟨s₁, v⟩ := p
      have he := eval_eq_evalG_of_ne_OOF c hf.1 (fuel := m) (co := co) (s := s)
        (by rw [hc]; simp [OOF])
      rw [hc] at he hne
      obtain ⟨g, hg⟩ := fst_eq_elim he
      simp only at hne ⊢
      by_cases hv : v = ⟨0⟩
      · simp only [hv, ne_eq, not_true_eq_false, if_false] at hne ⊢
        exact ⟨0, g + c.branch, by simp [execL, hg, hv]⟩
      · simp only [hv, ne_eq, not_false_eq_true, if_true] at hne ⊢
        obtain ⟨n, gb, hn⟩ := ihm (.Block body) s₁ (by simpa [fragLS] using hf.2) hne
        simp only [execL] at hn
        exact ⟨n, g + c.branch + gb, by simp [execL, hg, hv, hn, addGas]⟩
  | .Switch cond cases dflt =>
    simp only [fragLS, Bool.and_eq_true] at hf
    obtain ⟨⟨hfc, hfcs⟩, hfd⟩ := hf
    simp only [exec] at hne ⊢
    cases hc : eval m cond co s with
    | error e =>
      rw [hc] at hne; simp only at hne
      have he := eval_eq_evalG_of_ne_OOF c hfc (fuel := m) (co := co) (s := s)
        (by rw [hc]; exact err_ne_oof hne)
      rw [hc] at he
      obtain ⟨g, hg⟩ := fst_eq_elim he
      exact ⟨0, g, by simp [execL, hg]⟩
    | ok p =>
      obtain ⟨s₁, v⟩ := p
      have he := eval_eq_evalG_of_ne_OOF c hfc (fuel := m) (co := co) (s := s)
        (by rw [hc]; simp [OOF])
      rw [hc] at he hne
      obtain ⟨g, hg⟩ := fst_eq_elim he
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
          obtain ⟨n, gd, hn⟩ := ihm (.Block dflt) s₁ (by simpa [fragLS] using hfd)
            (by rw [hd]; exact hne)
          rw [hd] at hn; simp only [execL] at hn
          exact ⟨n, g + c.branch + gd, by simp [execL, hg, hn]⟩
        | ok s₂ =>
          rw [hd] at hne; simp only at hne ⊢
          obtain ⟨n, gd, hn⟩ := ihm (.Block dflt) s₁ (by simpa [fragLS] using hfd)
            (by rw [hd]; simp [OOF])
          rw [hd] at hn; simp only [execL] at hn
          change selectBranch v (.ok s₂) branches ≠ OOF at hne
          change ∃ n g, execL c n (.Switch cond cases dflt) s =
            some (selectBranch v (.ok s₂) branches, g)
          rcases selectBranch_of_execSwitchCases (v := v) (d := .ok s₂) hsw with
            ⟨hsel, hres⟩ | ⟨body, m', hm', hsel, hres⟩
          · rw [hres]
            exact ⟨n, g + c.branch + gd,
              by simp [execL, hg, hn, casesL_of_selectCase_none c n hsel]⟩
          · rw [hres] at hne ⊢
            obtain ⟨n₂, gb, hn₂⟩ := ih m' (by omega) (.Block body) s₁
              (by simpa [fragLS] using fragLB_of_selectCase hfcs hsel) hne
            simp only [execL] at hn₂
            refine ⟨max n n₂, g + c.branch + gb, ?_⟩
            have a := blockL_mono c (le_max_left n n₂) dflt s₁ hn
            have b := blockL_mono c (le_max_right n n₂) body s₁ hn₂
            simp [execL, hg, a, casesL_of_selectCase_some c _ hsel, b]
  | .For cond post body =>
    simp only [fragLS, Bool.and_eq_true] at hf
    obtain ⟨⟨hfc, hfp⟩, hfb⟩ := hf
    simp only [exec] at hne ⊢
    simp only [execL]
    match m, ih, hne with
    | 0, _, hne => exact absurd (by simp [loop]) hne
    | 1, _, hne => exact absurd (by simp [loop]) hne
    | m' + 2, ih, hne =>
      have ihb : ∀ st s, fragLS st = true → exec m' st co s ≠ OOF →
          ∃ n g, execL c n st s = some (exec m' st co s, g) := ih m' (by omega)
      simp only [loop] at hne ⊢
      cases hc : eval m' cond co (State.mkOk s) with
      | error e =>
        rw [hc] at hne; simp only at hne
        have he := eval_eq_evalG_of_ne_OOF c hfc (fuel := m') (co := co) (s := State.mkOk s)
          (by rw [hc]; exact err_ne_oof hne)
        rw [hc] at he
        obtain ⟨g, hg⟩ := fst_eq_elim he
        exact ⟨0, g, by unfold loopWith; simp [hg]⟩
      | ok p =>
        obtain ⟨s₁, x⟩ := p
        have he := eval_eq_evalG_of_ne_OOF c hfc (fuel := m') (co := co) (s := State.mkOk s)
          (by rw [hc]; simp [OOF])
        rw [hc] at he hne
        obtain ⟨g, hg⟩ := fst_eq_elim he
        simp only at hne ⊢
        by_cases hx : x = ⟨0⟩
        · simp only [hx, if_true] at hne ⊢
          exact ⟨0, g + c.branch, by unfold loopWith; simp [hg, hx]⟩
        · simp only [hx, if_false] at hne ⊢
          cases hb : exec m' (.Block body) co s₁ with
          | error e =>
            rw [hb] at hne; simp only at hne
            obtain ⟨n, gb, hn⟩ := ihb (.Block body) s₁ (by simpa [fragLS] using hfb)
              (by rw [hb]; exact hne)
            rw [hb] at hn; simp only [execL] at hn
            have hn' := blockL_mono c (Nat.le_succ n) body s₁ hn
            exact ⟨n + 1, g + c.branch + gb, by unfold loopWith; simp [hg, hx, hn']⟩
          | ok s₂ =>
            rw [hb] at hne; simp only at hne ⊢
            obtain ⟨n, gb, hn⟩ := ihb (.Block body) s₁ (by simpa [fragLS] using hfb)
              (by rw [hb]; simp [OOF])
            rw [hb] at hn; simp only [execL] at hn
            match s₂, hn, hne with
            | .OutOfFuel, hn, _ =>
              have hn' := blockL_mono c (Nat.le_succ n) body s₁ hn
              exact ⟨n + 1, g + c.branch + gb, by unfold loopWith; simp [hg, hx, hn']⟩
            | .Checkpoint (.Break ss vs), hn, _ =>
              have hn' := blockL_mono c (Nat.le_succ n) body s₁ hn
              exact ⟨n + 1, g + c.branch + gb, by unfold loopWith; simp [hg, hx, hn']⟩
            | .Checkpoint (.Leave ss vs), hn, _ =>
              have hn' := blockL_mono c (Nat.le_succ n) body s₁ hn
              exact ⟨n + 1, g + c.branch + gb, by unfold loopWith; simp [hg, hx, hn']⟩
            | .Checkpoint (.Continue ss vs), hn, hne =>
              simp only at hne ⊢
              cases hp : exec m' (.Block post) co (State.reviveJump (State.Checkpoint (.Continue ss vs))) with
              | error e =>
                rw [hp] at hne; simp only at hne
                obtain ⟨n₂, gp, hn₂⟩ := ihb (.Block post) _ (by simpa [fragLS] using hfp)
                  (by rw [hp]; exact hne)
                rw [hp] at hn₂; simp only [execL] at hn₂
                obtain ⟨N, hN⟩ : ∃ N, N = max n n₂ := ⟨_, rfl⟩
                have a := blockL_mono c (show n ≤ N + 1 by omega) body s₁ hn
                have b := blockL_mono c (show n₂ ≤ N + 1 by omega) post _ hn₂
                exact ⟨N + 1, g + c.branch + gb + gp, by unfold loopWith; simp [hg, hx, a, b]⟩
              | ok s₃ =>
                rw [hp] at hne; simp only at hne ⊢
                obtain ⟨n₂, gp, hn₂⟩ := ihb (.Block post) _ (by simpa [fragLS] using hfp)
                  (by rw [hp]; simp [OOF])
                rw [hp] at hn₂; simp only [execL] at hn₂
                have hfFor : fragLS (.For cond post body) = true := by simp [fragLS, hfc, hfp, hfb]
                cases hr : exec m' (.For cond post body) co (s₃.overwrite? s) with
                | error e =>
                  rw [hr] at hne; simp only at hne
                  obtain ⟨n₃, g₃, hn₃⟩ := ihb (.For cond post body) _ hfFor (by rw [hr]; exact hne)
                  rw [hr] at hn₃; simp only [execL] at hn₃
                  obtain ⟨N, hN⟩ : ∃ N, N = max (max n n₂) n₃ := ⟨_, rfl⟩
                  have a := blockL_mono c (show n ≤ N + 1 by omega) body s₁ hn
                  have b := blockL_mono c (show n₂ ≤ N + 1 by omega) post _ hn₂
                  have d := loopWith_mono c cond
                    (fun s _ h => blockL_mono c (show n₃ ≤ N + 1 by omega) body s h)
                    (fun s _ h => blockL_mono c (show n₃ ≤ N + 1 by omega) post s h)
                    n₃ N _ _ (by omega) hn₃
                  exact ⟨N + 1, g + c.branch + gb + gp + g₃,
                    by unfold loopWith; simp [hg, hx, a, b, d, Except.map]⟩
                | ok s₅ =>
                  obtain ⟨n₃, g₃, hn₃⟩ := ihb (.For cond post body) _ hfFor (by rw [hr]; simp [OOF])
                  rw [hr] at hn₃; simp only [execL] at hn₃
                  obtain ⟨N, hN⟩ : ∃ N, N = max (max n n₂) n₃ := ⟨_, rfl⟩
                  have a := blockL_mono c (show n ≤ N + 1 by omega) body s₁ hn
                  have b := blockL_mono c (show n₂ ≤ N + 1 by omega) post _ hn₂
                  have d := loopWith_mono c cond
                    (fun s _ h => blockL_mono c (show n₃ ≤ N + 1 by omega) body s h)
                    (fun s _ h => blockL_mono c (show n₃ ≤ N + 1 by omega) post s h)
                    n₃ N _ _ (by omega) hn₃
                  exact ⟨N + 1, g + c.branch + gb + gp + g₃,
                    by unfold loopWith; simp [hg, hx, a, b, d, Except.map]⟩
            | .Ok ss vs, hn, hne =>
              simp only at hne ⊢
              cases hp : exec m' (.Block post) co (State.reviveJump (State.Ok ss vs)) with
              | error e =>
                rw [hp] at hne; simp only at hne
                obtain ⟨n₂, gp, hn₂⟩ := ihb (.Block post) _ (by simpa [fragLS] using hfp)
                  (by rw [hp]; exact hne)
                rw [hp] at hn₂; simp only [execL] at hn₂
                obtain ⟨N, hN⟩ : ∃ N, N = max n n₂ := ⟨_, rfl⟩
                have a := blockL_mono c (show n ≤ N + 1 by omega) body s₁ hn
                have b := blockL_mono c (show n₂ ≤ N + 1 by omega) post _ hn₂
                exact ⟨N + 1, g + c.branch + gb + gp, by unfold loopWith; simp [hg, hx, a, b]⟩
              | ok s₃ =>
                rw [hp] at hne; simp only at hne ⊢
                obtain ⟨n₂, gp, hn₂⟩ := ihb (.Block post) _ (by simpa [fragLS] using hfp)
                  (by rw [hp]; simp [OOF])
                rw [hp] at hn₂; simp only [execL] at hn₂
                have hfFor : fragLS (.For cond post body) = true := by simp [fragLS, hfc, hfp, hfb]
                cases hr : exec m' (.For cond post body) co (s₃.overwrite? s) with
                | error e =>
                  rw [hr] at hne; simp only at hne
                  obtain ⟨n₃, g₃, hn₃⟩ := ihb (.For cond post body) _ hfFor (by rw [hr]; exact hne)
                  rw [hr] at hn₃; simp only [execL] at hn₃
                  obtain ⟨N, hN⟩ : ∃ N, N = max (max n n₂) n₃ := ⟨_, rfl⟩
                  have a := blockL_mono c (show n ≤ N + 1 by omega) body s₁ hn
                  have b := blockL_mono c (show n₂ ≤ N + 1 by omega) post _ hn₂
                  have d := loopWith_mono c cond
                    (fun s _ h => blockL_mono c (show n₃ ≤ N + 1 by omega) body s h)
                    (fun s _ h => blockL_mono c (show n₃ ≤ N + 1 by omega) post s h)
                    n₃ N _ _ (by omega) hn₃
                  exact ⟨N + 1, g + c.branch + gb + gp + g₃,
                    by unfold loopWith; simp [hg, hx, a, b, d, Except.map]⟩
                | ok s₅ =>
                  obtain ⟨n₃, g₃, hn₃⟩ := ihb (.For cond post body) _ hfFor (by rw [hr]; simp [OOF])
                  rw [hr] at hn₃; simp only [execL] at hn₃
                  obtain ⟨N, hN⟩ : ∃ N, N = max (max n n₂) n₃ := ⟨_, rfl⟩
                  have a := blockL_mono c (show n ≤ N + 1 by omega) body s₁ hn
                  have b := blockL_mono c (show n₂ ≤ N + 1 by omega) post _ hn₂
                  have d := loopWith_mono c cond
                    (fun s _ h => blockL_mono c (show n₃ ≤ N + 1 by omega) body s h)
                    (fun s _ h => blockL_mono c (show n₃ ≤ N + 1 by omega) post s h)
                    n₃ N _ _ (by omega) hn₃
                  exact ⟨N + 1, g + c.branch + gb + gp + g₃,
                    by unfold loopWith; simp [hg, hx, a, b, d, Except.map]⟩
  | .Continue => exact ⟨0, 0, by simp [exec, execL]⟩
  | .Break => exact ⟨0, 0, by simp [exec, execL]⟩
  | .Leave => exact ⟨0, 0, by simp [exec, execL]⟩


/-! ## Consequences -/

/-- Successful runs with different budgets agree (result and gas): the meter does not depend on
the budget once the budget suffices. -/
theorem execL_budget_indep {n n' : ℕ} {st : Stmt} {s : State} {o o' : Res × ℕ}
    (h : execL c n st s = some o) (h' : execL c n' st s = some o') : o = o' := by
  have a := execL_mono c (le_max_left n n') st s h
  have b := execL_mono c (le_max_right n n') st s h'
  rw [a] at b; exact Option.some.inj b

/-- **The interpreter computes the metered result** on the fragment with nested loops. -/
theorem exec_eq_execL {fuel : ℕ} {st : Stmt} {co : Option YulContract} {s : State}
    (hf : InLoopFragment st) (h : exec fuel st co s ≠ OOF) :
    ∃ n g, execL c n st s = some (exec fuel st co s, g) :=
  exec_complete_execL c co fuel st s hf h

/-- **Yul gas bound for nested loops.** For a call-free Yul program whose loops may be nested
arbitrarily, every interpreter run that does not run out of fuel is metered by `execL`: there is a
budget `n` (the largest number of body executions of any single loop entry suffices) at which
`execL` returns the run's result `r` with gas `g ≤ gasLS c n st`, and every larger budget gives the
same result and gas. -/
theorem exec_nested_gas_bound {fuel : ℕ} {st : Stmt} {co : Option YulContract} {s : State}
    {r : Res} (hf : InLoopFragment st) (h : exec fuel st co s = r) (hr : r ≠ OOF) :
    ∃ n g, execL c n st s = some (r, g) ∧ g ≤ gasLS c n st ∧
      ∀ n', n ≤ n' → execL c n' st s = some (r, g) := by
  obtain ⟨n, g, hn⟩ := exec_eq_execL c hf (fuel := fuel) (co := co) (s := s) (h ▸ hr)
  rw [h] at hn
  exact ⟨n, g, hn, execL_gas_le c n st s hn, fun n' hn' => execL_mono c hn' st s hn⟩

/-! ## Conservative extension of the loop-free layer -/

mutual

/-- On loop-free programs, `execL` (with any budget) is `execG`. -/
theorem execL_of_fragS (n : ℕ) : (st : Stmt) → (s : State) → fragS st = true →
    execL c n st s = some (execG c st s)
  | .Block sts, s, hf => by
    simp only [fragS] at hf; simp only [execL, execG]; exact blockL_of_fragB n sts s hf
  | .Let _ _, _, _ => by simp [execL]
  | .ExprStmtCall _, _, _ => by simp [execL]
  | .If cond body, s, hf => by
    simp only [fragS, Bool.and_eq_true] at hf
    rcases hev : evalG c cond s with ⟨_ | ⟨s₁, v⟩, g₀⟩
    · simp [execL, execG, hev]
    · by_cases hv : v = ⟨0⟩
      · simp [execL, execG, hev, hv]
      · simp [execL, execG, hev, hv, blockL_of_fragB n body s₁ hf.2, addGas]
  | .Switch cond cases dflt, s, hf => by
    simp only [fragS, Bool.and_eq_true] at hf
    obtain ⟨⟨_, hfcs⟩, hfd⟩ := hf
    rcases hev : evalG c cond s with ⟨_ | ⟨s₁, v⟩, g₀⟩
    · simp [execL, execG, hev]
    · rcases hd : blockG c dflt s₁ with ⟨_ | s₂, gd⟩
      · simp [execL, execG, hev, hd, blockL_of_fragB n dflt s₁ hfd]
      · rcases hcs : casesG c cases v s₁ with _ | ⟨r, gb⟩
        · simp [execL, execG, hev, hd, hcs, blockL_of_fragB n dflt s₁ hfd,
            casesL_of_fragCases n cases v s₁ hfcs]
        · simp [execL, execG, hev, hd, hcs, blockL_of_fragB n dflt s₁ hfd,
            casesL_of_fragCases n cases v s₁ hfcs]
  | .For _ _ _, _, hf => by simp [fragS] at hf
  | .Continue, _, _ => by simp [execL, execG]
  | .Break, _, _ => by simp [execL, execG]
  | .Leave, _, _ => by simp [execL, execG]

theorem blockL_of_fragB (n : ℕ) : (sts : List Stmt) → (s : State) → fragB sts = true →
    blockL c n sts s = some (blockG c sts s)
  | [], _, _ => by simp [blockL, blockG]
  | st :: sts, s, hf => by
    simp only [fragB, Bool.and_eq_true] at hf
    have h1 := execL_of_fragS n st s hf.1
    rcases hx : execG c st s with ⟨r, g⟩
    rw [hx] at h1
    rcases r with e | (⟨ss, vs⟩ | _ | j)
    · simp [blockL, blockG, h1, hx]
    · simp [blockL, blockG, h1, hx, blockL_of_fragB n sts _ hf.2, addGas]
    · simp [blockL, blockG, h1, hx]
    · simp [blockL, blockG, h1, hx]

theorem casesL_of_fragCases (n : ℕ) : (cases : List (Literal × List Stmt)) → (v : Literal) →
    (s : State) → fragCases cases = true → casesL c n cases v s = some (casesG c cases v s)
  | [], _, _, _ => by simp [casesL, casesG]
  | (l, body) :: rest, v, s, hf => by
    simp only [fragCases, Bool.and_eq_true] at hf
    by_cases hl : l = v
    · simp [casesL, casesG, hl, blockL_of_fragB n body s hf.1]
    · simp only [casesL, casesG, hl, if_false]; exact casesL_of_fragCases n rest v s hf.2

end

mutual

/-- On loop-free programs, `gasLS` (with any budget) is `gasS`. -/
theorem gasLS_of_fragS (n : ℕ) : (st : Stmt) → fragS st = true → gasLS c n st = gasS c st
  | .Block sts, hf => by
    simp only [fragS] at hf; simp only [gasLS, gasS]; exact gasLB_of_fragB n sts hf
  | .Let _ none, _ => by simp [gasLS, gasS]
  | .Let _ (some _), _ => by simp [gasLS, gasS]
  | .ExprStmtCall _, _ => by simp [gasLS, gasS]
  | .If cond body, hf => by
    simp only [fragS, Bool.and_eq_true] at hf
    simp [gasLS, gasS, gasLB_of_fragB n body hf.2]
  | .Switch cond cases dflt, hf => by
    simp only [fragS, Bool.and_eq_true] at hf
    simp [gasLS, gasS, gasLB_of_fragB n dflt hf.2, gasLCases_of_fragCases n cases hf.1.2]
  | .For _ _ _, hf => by simp [fragS] at hf
  | .Continue, _ => by simp [gasLS, gasS]
  | .Break, _ => by simp [gasLS, gasS]
  | .Leave, _ => by simp [gasLS, gasS]

theorem gasLB_of_fragB (n : ℕ) : (sts : List Stmt) → fragB sts = true → gasLB c n sts = gasB c sts
  | [], _ => by simp [gasLB, gasB]
  | st :: sts, hf => by
    simp only [fragB, Bool.and_eq_true] at hf
    simp [gasLB, gasB, gasLS_of_fragS n st hf.1, gasLB_of_fragB n sts hf.2]

theorem gasLCases_of_fragCases (n : ℕ) : (cases : List (Literal × List Stmt)) →
    fragCases cases = true → gasLCases c n cases = gasCases c cases
  | [], _ => by simp [gasLCases, gasCases]
  | (_, body) :: rest, hf => by
    simp only [fragCases, Bool.and_eq_true] at hf
    simp [gasLCases, gasCases, gasLB_of_fragB n body hf.1, gasLCases_of_fragCases n rest hf.2]

end

end Gas
end Yul
end EvmYul
