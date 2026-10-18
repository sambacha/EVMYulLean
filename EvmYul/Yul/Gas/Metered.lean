module

public import EvmYul.Yul.Gas.CostModel
public import EvmYul.Yul.Relational.Soundness
public import EvmYul.Yul.Relational.WP

public section

/-!
# Yul gas, part 2: a metered Yul semantics and a static gas bound (analysis, Approach B)

The gas analysis (§3.2 S6) notes that Yul has a `gasAvailable` field that is never updated, and
recommends (§5, Approach B; §6) a gas-carrying Yul semantics charged from the EVM cost table, with a
**sound upper bound** as the realistic deliverable: exact source-level gas depends on the compiler.

This file delivers that for the fragment of Yul that has no loops, no calls of user-defined
functions and no contract calls (`InFragment`): straight-line code with `let`, assignments of
builtin results, `if`, `switch`, `break`/`continue`/`leave`, and every builtin except
CALL/CALLCODE/DELEGATECALL/STATICCALL (whose cost is the callee's, which is unbounded statically).

* `execG c st s = (r, g)`: a metered evaluator. `r` is the result, `g` the gas charged under the
  cost model `c` (`CostModel.lean`): `c.prim op` per builtin call and `c.branch` per evaluated
  `if`/`switch` condition. It needs no fuel: on the fragment it is structurally recursive.
* `gasS c st`: a static (syntactic) gas bound.

Results (gas results here, semantic results in `EvmYul/Yul/Gas/MeteredSound.lean`):

* `execG_sound`: every result of `execG` (other than running out of fuel) is a run of the
  relational semantics `ExecR` (`EvmYul/Yul/Relational/Semantics.lean`).
* `execG_complete`: conversely, **every** `ExecR` run of a fragment program has exactly the result
  of `execG`. So the meter is attached to every run, not just to some, and `ExecR` is deterministic
  on the fragment.
* `exec_eq_execG`: hence every run of the executable interpreter `exec` (with any fuel) that does
  not run out of fuel returns exactly `(execG c st s).1`.
* `execG_gas_le`: the gas charged is at most `gasS c st`, for every start state.
* `execG_gas_eq_of_ok`: for programs without `if`/`switch` (`Straight`), when the run ends
  normally the gas charged is **exactly** `gasS c st`. So the bound is tight, not just sound.
* `exec_gas_bound`: the headline statement combining the above for the interpreter.

How the meter treats `switch`: the interpreter evaluates the default block even when a case
matches (the quirk documented in `Relational/Semantics.lean`). The meter charges what the Yul
specification runs: the selected case if one matches, the default block otherwise; when the default
block raises an error (which aborts the whole `switch` in the interpreter) its gas is charged.
-/

namespace EvmYul
namespace Yul
namespace Gas

open Ast Relational

/-! ## The fragment -/

mutual

/-- Expressions in the fragment: no user-defined calls, no contract calls. -/
@[expose] def fragE : Expr → Bool
  | .Lit _ => true
  | .Var _ => true
  | .Call (.inl prim) args => decide (prim ∉ callFamily) && fragArgs args
  | .Call (.inr _) _ => false

/-- Argument lists in the fragment. -/
@[expose] def fragArgs : List Expr → Bool
  | [] => true
  | a :: as => fragE a && fragArgs as

end

mutual

/-- Statements in the fragment: no `for`, no user-defined calls, no contract calls. -/
@[expose] def fragS : Stmt → Bool
  | .Block sts => fragB sts
  | .Let _ none => true
  | .Let _ (some e) => fragE e
  | .ExprStmtCall e => fragE e
  | .If cond body => fragE cond && fragB body
  | .Switch cond cases dflt => fragE cond && fragCases cases && fragB dflt
  | .For _ _ _ => false
  | .Continue => true
  | .Break => true
  | .Leave => true

/-- Blocks in the fragment. -/
@[expose] def fragB : List Stmt → Bool
  | [] => true
  | st :: sts => fragS st && fragB sts

/-- `switch` cases in the fragment. -/
@[expose] def fragCases : List (Literal × List Stmt) → Bool
  | [] => true
  | (_, body) :: rest => fragB body && fragCases rest

end

/-- The loop-free, call-free fragment of Yul. -/
@[expose] abbrev InFragment (st : Stmt) : Prop := fragS st = true

mutual

/-- Statements without `if` or `switch`. -/
@[expose] def straightS : Stmt → Bool
  | .Block sts => straightB sts
  | .If _ _ => false
  | .Switch _ _ _ => false
  | _ => true

/-- Blocks of `straightS` statements. -/
@[expose] def straightB : List Stmt → Bool
  | [] => true
  | st :: sts => straightS st && straightB sts

end

/-- Straight-line programs (no `if`, no `switch`). -/
@[expose] abbrev Straight (st : Stmt) : Prop := straightS st = true

/-! ## The metered evaluator -/

variable (c : CostModel)

mutual

/-- Evaluate an expression, returning the result and the gas charged. -/
@[expose] def evalG : Expr → State → ResV × ℕ
  | .Lit v, s => (.ok (s, v), 0)
  | .Var x, s => (.ok (s, s[x]!), 0)
  | .Call (.inl prim) args, s =>
    match argsG args s with
    | (.error e, g) => (.error e, g)
    | (.ok (s₁, vs), g) => (head' (primResult s₁ prim vs.reverse), g + c.prim prim)
  | .Call (.inr _) _, _ => (.error .OutOfFuel, 0)

/-- Evaluate the arguments of a call. Like the interpreter (`ArgsR co args.reverse`), the
arguments are evaluated **right to left**; the values come back in evaluation order. -/
@[expose] def argsG : List Expr → State → ResL × ℕ
  | [], s => (.ok (s, []), 0)
  | a :: as, s =>
    match argsG as s with
    | (.error e, g) => (.error e, g)
    | (.ok (s₁, vs), g) =>
      match evalG a s₁ with
      | (.error e, g') => (.error e, g + g')
      | (.ok (s₂, v), g') => (.ok (s₂, vs ++ [v]), g + g')

end

mutual

/-- Execute a statement, returning the result and the gas charged. -/
@[expose] def execG : Stmt → State → Res × ℕ
  | .Block sts, s => blockG sts s
  | .Let vars none, s => (.ok (List.foldr (λ var s ↦ s.insert var ⟨0⟩) s vars), 0)
  | .Let vars (some (.Var x)), s => (.ok (s.insert vars.head! s[x]!), 0)
  | .Let vars (some (.Lit v)), s => (.ok (s.insert vars.head! v), 0)
  | .Let vars (some (.Call (.inl prim) args)), s =>
    match argsG c args s with
    | (.error e, g) => (.error e, g)
    | (.ok (s₁, vs), g) => (multifill' vars (primResult s₁ prim vs.reverse), g + c.prim prim)
  | .Let _ (some (.Call (.inr _) _)), _ => (.error .OutOfFuel, 0)
  | .ExprStmtCall (.Call (.inl prim) args), s =>
    match argsG c args s with
    | (.error e, g) => (.error e, g)
    | (.ok (s₁, vs), g) => (multifill' [] (primResult s₁ prim vs.reverse), g + c.prim prim)
  | .ExprStmtCall (.Call (.inr _) _), _ => (.error .OutOfFuel, 0)
  | .ExprStmtCall (.Var _), _ => (.error .InvalidExpression, 0)
  | .ExprStmtCall (.Lit _), _ => (.error .InvalidExpression, 0)
  | .If cond body, s =>
    match evalG c cond s with
    | (.error e, g) => (.error e, g)
    | (.ok (s₁, v), g) =>
      if v ≠ ⟨0⟩ then
        match blockG body s₁ with
        | (r, g') => (r, g + c.branch + g')
      else (.ok s₁, g + c.branch)
  | .Switch cond cases dflt, s =>
    match evalG c cond s with
    | (.error e, g) => (.error e, g)
    | (.ok (s₁, v), g) =>
      match blockG dflt s₁ with
      | (.error e, gd) => (.error e, g + c.branch + gd)
      | (.ok s₂, gd) =>
        match casesG cases v s₁ with
        | some (r, gb) => (r, g + c.branch + gb)
        | none => (.ok s₂, g + c.branch + gd)
  | .For _ _ _, _ => (.error .OutOfFuel, 0)
  | .Continue, s => (.ok (State.setContinue s), 0)
  | .Break, s => (.ok (State.setBreak s), 0)
  | .Leave, s => (.ok (State.setLeave s), 0)

/-- Execute a block: stop at the first statement that does not end normally. -/
@[expose] def blockG : List Stmt → State → Res × ℕ
  | [], s => (.ok s, 0)
  | st :: sts, s =>
    match execG st s with
    | (.ok (.Ok ss vs), g) =>
      match blockG sts (.Ok ss vs) with
      | (r, g') => (r, g + g')
    | (r, g) => (r, g)

/-- Run the case body selected by `v` (as `selectCase`), if any. -/
@[expose] def casesG : List (Literal × List Stmt) → Literal → State → Option (Res × ℕ)
  | [], _, _ => none
  | (l, body) :: rest, v, s => if l = v then some (blockG body s) else casesG rest v s

end

/-! ## The static bound -/

mutual

/-- Static gas of an expression. -/
@[expose] def gasE : Expr → ℕ
  | .Call (.inl prim) args => gasArgs args + c.prim prim
  | _ => 0

/-- Static gas of an argument list. -/
@[expose] def gasArgs : List Expr → ℕ
  | [] => 0
  | a :: as => gasE a + gasArgs as

end

mutual

/-- Static gas of a statement: the sum along the program, the maximum over `switch` branches. -/
@[expose] def gasS : Stmt → ℕ
  | .Block sts => gasB sts
  | .Let _ none => 0
  | .Let _ (some e) => gasE c e
  | .ExprStmtCall e => gasE c e
  | .If cond body => gasE c cond + c.branch + gasB body
  | .Switch cond cases dflt => gasE c cond + c.branch + max (gasB dflt) (gasCases cases)
  | .For _ _ _ => 0
  | .Continue => 0
  | .Break => 0
  | .Leave => 0

/-- Static gas of a block. -/
@[expose] def gasB : List Stmt → ℕ
  | [] => 0
  | st :: sts => gasS st + gasB sts

/-- The largest static gas among `switch` case bodies. -/
@[expose] def gasCases : List (Literal × List Stmt) → ℕ
  | [] => 0
  | (_, body) :: rest => max (gasB body) (gasCases rest)

end

/-! ## The static bound is sound -/

mutual

theorem evalG_gas_le : (e : Expr) → (s : State) → (evalG c e s).2 ≤ gasE c e
  | .Lit _, _ => by simp [evalG, gasE]
  | .Var _, _ => by simp [evalG, gasE]
  | .Call (.inl prim) args, s => by
    have ih := argsG_gas_le args s
    rcases h : argsG c args s with ⟨_ | ⟨s₁, vs⟩, g⟩ <;> rw [h] at ih <;>
      simp only [evalG, gasE, h] <;> omega
  | .Call (.inr _) _, _ => by simp [evalG, gasE]

theorem argsG_gas_le : (as : List Expr) → (s : State) → (argsG c as s).2 ≤ gasArgs c as
  | [], _ => by simp [argsG, gasArgs]
  | a :: as, s => by
    have ih := argsG_gas_le as s
    rcases h : argsG c as s with ⟨_ | ⟨s₁, vs⟩, g⟩ <;> rw [h] at ih
    · simp only [argsG, gasArgs, h]; omega
    · have ih₂ := evalG_gas_le a s₁
      rcases h₂ : evalG c a s₁ with ⟨_ | ⟨s₂, v⟩, g'⟩ <;> rw [h₂] at ih₂ <;>
        simp only [argsG, gasArgs, h, h₂] <;> omega

end

mutual

theorem execG_gas_le : (st : Stmt) → (s : State) → (execG c st s).2 ≤ gasS c st
  | .Block sts, s => by simpa [execG, gasS] using blockG_gas_le sts s
  | .Let _ none, _ => by simp [execG, gasS]
  | .Let _ (some (.Var _)), _ => by simp [execG, gasS, gasE]
  | .Let _ (some (.Lit _)), _ => by simp [execG, gasS, gasE]
  | .Let vars (some (.Call (.inl prim) args)), s => by
    have ih := argsG_gas_le c args s
    rcases h : argsG c args s with ⟨_ | ⟨s₁, vs⟩, g⟩ <;> rw [h] at ih <;>
      simp only [execG, gasS, gasE, h] <;> omega
  | .Let _ (some (.Call (.inr _) _)), _ => by simp [execG, gasS, gasE]
  | .ExprStmtCall (.Call (.inl prim) args), s => by
    have ih := argsG_gas_le c args s
    rcases h : argsG c args s with ⟨_ | ⟨s₁, vs⟩, g⟩ <;> rw [h] at ih <;>
      simp only [execG, gasS, gasE, h] <;> omega
  | .ExprStmtCall (.Call (.inr _) _), _ => by simp [execG, gasS, gasE]
  | .ExprStmtCall (.Var _), _ => by simp [execG, gasS, gasE]
  | .ExprStmtCall (.Lit _), _ => by simp [execG, gasS, gasE]
  | .If cond body, s => by
    have ih := evalG_gas_le c cond s
    rcases h : evalG c cond s with ⟨_ | ⟨s₁, v⟩, g⟩ <;> rw [h] at ih
    · simp only [execG, gasS, h]; omega
    · have ih₂ := blockG_gas_le body s₁
      by_cases hv : v = ⟨0⟩
      · simp only [execG, gasS, h, hv, ne_eq, not_true_eq_false, if_false]; omega
      · rcases h₂ : blockG c body s₁ with ⟨r, g'⟩
        rw [h₂] at ih₂
        simp only [execG, gasS, h, h₂, hv, ne_eq, not_false_eq_true, if_true]; omega
  | .Switch cond cases dflt, s => by
    have ih := evalG_gas_le c cond s
    rcases h : evalG c cond s with ⟨_ | ⟨s₁, v⟩, g⟩ <;> rw [h] at ih
    · simp only [execG, gasS, h]; omega
    · have ihd := blockG_gas_le dflt s₁
      rcases hd : blockG c dflt s₁ with ⟨_ | s₂, gd⟩ <;> rw [hd] at ihd
      · simp only [execG, gasS, h, hd]; omega
      · rcases hc : casesG c cases v s₁ with _ | ⟨r, gb⟩
        · simp only [execG, gasS, h, hd, hc]; omega
        · have ihc := casesG_gas_le cases v s₁ hc
          simp only [execG, gasS, h, hd, hc]; omega
  | .For _ _ _, _ => by simp [execG, gasS]
  | .Continue, _ => by simp [execG, gasS]
  | .Break, _ => by simp [execG, gasS]
  | .Leave, _ => by simp [execG, gasS]

theorem blockG_gas_le : (sts : List Stmt) → (s : State) → (blockG c sts s).2 ≤ gasB c sts
  | [], _ => by simp [blockG, gasB]
  | st :: sts, s => by
    have ih := execG_gas_le st s
    rcases h : execG c st s with ⟨r, g⟩
    rw [h] at ih
    rcases r with e | (⟨ss, vs⟩ | _ | j)
    · simp only [blockG, gasB, h]; omega
    · have ih₂ := blockG_gas_le sts (.Ok ss vs)
      rcases h₂ : blockG c sts (.Ok ss vs) with ⟨r', g'⟩
      rw [h₂] at ih₂
      simp only [blockG, gasB, h, h₂]; omega
    · simp only [blockG, gasB, h]; omega
    · simp only [blockG, gasB, h]; omega

theorem casesG_gas_le : (cases : List (Literal × List Stmt)) → (v : Literal) → (s : State) →
    {rg : Res × ℕ} → casesG c cases v s = some rg → rg.2 ≤ gasCases c cases
  | [], _, _, _, h => by simp [casesG] at h
  | (l, body) :: rest, v, s, rg, h => by
    by_cases hl : l = v
    · simp only [casesG, hl, if_true, Option.some.injEq] at h
      subst h
      have := blockG_gas_le body s
      simp only [gasCases]; omega
    · simp only [casesG, hl, if_false] at h
      have := casesG_gas_le rest v s h
      simp only [gasCases]; omega

end

/-! ## The bound is exact on straight-line code -/

mutual

theorem evalG_gas_eq_of_ok : (e : Expr) → (s : State) → {p : State × Literal} →
    (evalG c e s).1 = .ok p → (evalG c e s).2 = gasE c e
  | .Lit _, _, _, _ => by simp [evalG, gasE]
  | .Var _, _, _, _ => by simp [evalG, gasE]
  | .Call (.inl prim) args, s, _, h => by
    rcases ha : argsG c args s with ⟨_ | ⟨s₁, vs⟩, g⟩
    · simp [evalG, ha] at h
    · have := argsG_gas_eq_of_ok args s (p := (s₁, vs)) (by rw [ha])
      rw [ha] at this
      simp only [evalG, gasE, ha]; omega
  | .Call (.inr _) _, _, _, h => by simp [evalG] at h

theorem argsG_gas_eq_of_ok : (as : List Expr) → (s : State) → {p : State × List Literal} →
    (argsG c as s).1 = .ok p → (argsG c as s).2 = gasArgs c as
  | [], _, _, _ => by simp [argsG, gasArgs]
  | a :: as, s, _, h => by
    rcases ha : argsG c as s with ⟨_ | ⟨s₁, vs⟩, g⟩
    · simp [argsG, ha] at h
    · have ih := argsG_gas_eq_of_ok as s (p := (s₁, vs)) (by rw [ha])
      rw [ha] at ih
      rcases he : evalG c a s₁ with ⟨_ | ⟨s₂, v⟩, g'⟩
      · simp [argsG, ha, he] at h
      · have ih₂ := evalG_gas_eq_of_ok a s₁ (p := (s₂, v)) (by rw [he])
        rw [he] at ih₂
        simp only [argsG, gasArgs, ha, he]; omega

end

mutual

theorem execG_gas_eq_of_ok : (st : Stmt) → (s : State) → straightS st = true →
    {ss : SharedState .Yul} → {vs : VarStore} →
    (execG c st s).1 = .ok (.Ok ss vs) → (execG c st s).2 = gasS c st
  | .Block sts, s, hst, _, _, h => by
    simp only [straightS] at hst
    simp only [execG, gasS] at h ⊢
    exact blockG_gas_eq_of_ok sts s hst h
  | .Let _ none, _, _, _, _, _ => by simp [execG, gasS]
  | .Let _ (some (.Var _)), _, _, _, _, _ => by simp [execG, gasS, gasE]
  | .Let _ (some (.Lit _)), _, _, _, _, _ => by simp [execG, gasS, gasE]
  | .Let vars (some (.Call (.inl prim) args)), s, _, _, _, h => by
    rcases ha : argsG c args s with ⟨_ | ⟨s₁, vs⟩, g⟩
    · simp [execG, ha] at h
    · have := argsG_gas_eq_of_ok c args s (p := (s₁, vs)) (by rw [ha])
      rw [ha] at this
      simp only [execG, gasS, gasE, ha]; omega
  | .Let _ (some (.Call (.inr _) _)), _, _, _, _, h => by simp [execG] at h
  | .ExprStmtCall (.Call (.inl prim) args), s, _, _, _, h => by
    rcases ha : argsG c args s with ⟨_ | ⟨s₁, vs⟩, g⟩
    · simp [execG, ha] at h
    · have := argsG_gas_eq_of_ok c args s (p := (s₁, vs)) (by rw [ha])
      rw [ha] at this
      simp only [execG, gasS, gasE, ha]; omega
  | .ExprStmtCall (.Call (.inr _) _), _, _, _, _, h => by simp [execG] at h
  | .ExprStmtCall (.Var _), _, _, _, _, h => by simp [execG] at h
  | .ExprStmtCall (.Lit _), _, _, _, _, h => by simp [execG] at h
  | .If _ _, _, hst, _, _, _ => by simp [straightS] at hst
  | .Switch _ _ _, _, hst, _, _, _ => by simp [straightS] at hst
  | .For _ _ _, _, _, _, _, h => by simp [execG] at h
  | .Continue, _, _, _, _, _ => by simp [execG, gasS]
  | .Break, _, _, _, _, _ => by simp [execG, gasS]
  | .Leave, _, _, _, _, _ => by simp [execG, gasS]

theorem blockG_gas_eq_of_ok : (sts : List Stmt) → (s : State) → straightB sts = true →
    {ss : SharedState .Yul} → {vs : VarStore} →
    (blockG c sts s).1 = .ok (.Ok ss vs) → (blockG c sts s).2 = gasB c sts
  | [], _, _, _, _, _ => by simp [blockG, gasB]
  | st :: sts, s, hst, _, _, h => by
    simp only [straightB, Bool.and_eq_true] at hst
    rcases he : execG c st s with ⟨r, g⟩
    rcases r with e | (⟨ss₁, vs₁⟩ | _ | j)
    · simp [blockG, he] at h
    · have ih := execG_gas_eq_of_ok st s hst.1 (ss := ss₁) (vs := vs₁) (by rw [he])
      rw [he] at ih
      rcases hb : blockG c sts (.Ok ss₁ vs₁) with ⟨r', g'⟩
      have ih₂ := blockG_gas_eq_of_ok sts (.Ok ss₁ vs₁) hst.2 (by
        simp only [blockG, he, hb] at h; rw [hb]; exact h)
      rw [hb] at ih₂
      simp only [blockG, gasB, he, hb]; omega
    · simp [blockG, he] at h
    · simp [blockG, he] at h

end

end Gas
end Yul
end EvmYul
