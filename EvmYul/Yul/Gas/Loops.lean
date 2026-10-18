module

public import EvmYul.Yul.Gas.MeteredSound

public section

/-!
# Yul gas, part 5: gas bounds for `for` loops

`execG` (`Metered.lean`) meters the loop-free, call-free fragment. This file extends the meter to a
`for` loop whose condition, body and post block are in that fragment (a *single-level* loop: the body
contains no further loop). A loop's gas is not bounded statically: it depends on how many times the
body runs. The results here bound it in terms of that number.

* `loopG c n cond post body s`: a metered evaluator for `for {} cond {post} {body}` with an
  iteration budget `n`. It follows the interpreter's `loop` step for step and returns a `LoopOut`:
  the result, the gas charged, the number of body executions `iters`, and a flag `clean` that is
  `true` when every body and post block ended normally and the loop left because its condition
  became `0`.
* `loopG_gas_le`: **gas ≤ iters · `loopIterGas` + `loopExitGas`**, where
  `loopIterGas = gasE cond + branch + gasB body + gasB post` is the static cost of one iteration and
  `loopExitGas = gasE cond + branch` is the cost of the final test.
* `loopG_gas_eq`: the bound is **exact** for clean runs of straight-line loops.
* `exec_for_eq_loopG`: every run of the interpreter `exec` on such a loop that does not run out of
  fuel returns exactly the result of `loopG` (for a suitable budget).
* `exec_for_gas_bound`: the headline statement combining the two for the interpreter.

The gas convention is the one `execG` uses for `if`: evaluating the condition costs its builtins
plus one `c.branch` for the jump; a condition that raises an error is charged without the jump.
-/

namespace EvmYul
namespace Yul
namespace Gas

open Ast Relational

variable (c : CostModel)

/-- Static gas of one loop iteration: test, jump, body, post block. -/
@[expose] def loopIterGas (cond : Expr) (post body : List Stmt) : ℕ :=
  gasE c cond + c.branch + gasB c body + gasB c post

/-- Static gas of the final loop test (condition and jump). -/
@[expose] def loopExitGas (cond : Expr) : ℕ := gasE c cond + c.branch

/-- `true` for states of the form `.Ok _ _`. -/
@[expose] def State.isOk : State → Bool
  | .Ok _ _ => true
  | _ => false

/-- Output of the metered loop evaluator. -/
structure LoopOut where
  /-- The result, as the interpreter returns it. -/
  res : Res
  /-- The gas charged. -/
  gas : ℕ
  /-- How many times the loop body was executed. -/
  iters : ℕ
  /-- Every body and post block ended normally and the loop left through its condition. -/
  clean : Bool

/-- Metered evaluation of `for {} cond {post} {body}` from `s` with iteration budget `n`. Mirrors
the interpreter's `loop` (and the relational `LoopR`) case by case. -/
@[expose] def loopG : ℕ → Expr → List Stmt → List Stmt → State → LoopOut
  | 0, _, _, _, _ => ⟨.error .OutOfFuel, 0, 0, false⟩
  | n + 1, cond, post, body, s =>
    match evalG c cond (State.mkOk s) with
    | (.error e, g) => ⟨.error e, g, 0, false⟩
    | (.ok (s₁, x), g) =>
      if x = ⟨0⟩ then ⟨.ok (s₁.overwrite? s), g + c.branch, 0, true⟩
      else
        match blockG c body s₁ with
        | (.error e, gb) => ⟨.error e, g + c.branch + gb, 1, false⟩
        | (.ok s₂, gb) =>
          match s₂ with
          | .OutOfFuel => ⟨.ok (State.OutOfFuel.overwrite? s), g + c.branch + gb, 1, false⟩
          | .Checkpoint (.Break ss vs) =>
            ⟨.ok ((State.Checkpoint (.Break ss vs)).reviveJump.overwrite? s), g + c.branch + gb, 1,
              false⟩
          | .Checkpoint (.Leave ss vs) =>
            ⟨.ok ((State.Checkpoint (.Leave ss vs)).overwrite? s), g + c.branch + gb, 1, false⟩
          | s₂ =>
            match blockG c post s₂.reviveJump with
            | (.error e, gp) => ⟨.error e, g + c.branch + gb + gp, 1, false⟩
            | (.ok s₃, gp) =>
              let o := loopG n cond post body (s₃.overwrite? s)
              ⟨o.res.map (·.overwrite? s), g + c.branch + gb + gp + o.gas, o.iters + 1,
                o.clean && State.isOk s₂ && State.isOk s₃⟩

/-- The number of body executions never exceeds the budget. -/
theorem loopG_iters_le : (n : ℕ) → (cond : Expr) → (post body : List Stmt) → (s : State) →
    (loopG c n cond post body s).iters ≤ n := by
  intro n
  induction n with
  | zero => intro _ _ _ _; simp [loopG]
  | succ n ih =>
    intro cond post body s
    simp only [loopG]
    repeat' split
    all_goals simp_all

/-- **Loop gas bound.** A loop run that executed its body `iters` times is charged at most
`iters · loopIterGas + loopExitGas`, for every start state and every budget. -/
theorem loopG_gas_le : (n : ℕ) → (cond : Expr) → (post body : List Stmt) → (s : State) →
    (loopG c n cond post body s).gas ≤
      (loopG c n cond post body s).iters * loopIterGas c cond post body + loopExitGas c cond := by
  intro n
  induction n with
  | zero => intro _ _ _ _; simp [loopG]
  | succ n ih =>
    intro cond post body s
    have hc := evalG_gas_le c cond (State.mkOk s)
    simp only [loopG]
    split
    · rename_i e g h; rw [h] at hc; simp [loopExitGas]; omega
    · rename_i s₁ x g h
      rw [h] at hc
      split
      · simp [loopExitGas]; omega
      · have hb := blockG_gas_le c body s₁
        split
        · rename_i e gb h2; rw [h2] at hb; simp [loopIterGas, loopExitGas]; omega
        · rename_i s₂ gb h2
          rw [h2] at hb
          split
          · simp [loopIterGas, loopExitGas]; omega
          · simp [loopIterGas, loopExitGas]; omega
          · simp [loopIterGas, loopExitGas]; omega
          · have hp := blockG_gas_le c post s₂.reviveJump
            split
            · rename_i e gp h3; rw [h3] at hp; simp [loopIterGas, loopExitGas]; omega
            · rename_i s₃ gp h3
              rw [h3] at hp
              have := ih cond post body (s₃.overwrite? s)
              simp only [loopIterGas, loopExitGas] at this ⊢
              simp only at hc hb hp; rw [Nat.add_mul, Nat.one_mul]; linarith

/-- **The loop bound is exact** on clean runs of loops whose body and post block are straight-line
code: such a run is charged exactly `iters · loopIterGas + loopExitGas`. -/
theorem loopG_gas_eq : (n : ℕ) → (cond : Expr) → (post body : List Stmt) → (s : State) →
    straightB body = true → straightB post = true → (loopG c n cond post body s).clean = true →
    (loopG c n cond post body s).gas =
      (loopG c n cond post body s).iters * loopIterGas c cond post body + loopExitGas c cond := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ h; simp [loopG] at h
  | succ n ih =>
    intro cond post body s hb hp hcl
    revert hcl
    simp only [loopG]
    split
    · simp
    · rename_i s₁ x g h
      have hc : g = gasE c cond := by
        have := evalG_gas_eq_of_ok c cond (State.mkOk s) (p := (s₁, x)) (by rw [h])
        rw [h] at this; exact this
      split
      · simp [loopExitGas, hc]
      · split
        · simp
        · rename_i s₂ gb h2
          split
          · simp
          · simp
          · simp
          · split
            · simp
            · rename_i s₃ gp h3
              intro hcl
              simp only [Bool.and_eq_true] at hcl
              obtain ⟨⟨hcl, h2ok⟩, h3ok⟩ := hcl
              cases s₂ with
              | OutOfFuel => simp [State.isOk] at h2ok
              | Checkpoint _ => simp [State.isOk] at h2ok
              | Ok ss vs =>
                cases s₃ with
                | OutOfFuel => simp [State.isOk] at h3ok
                | Checkpoint _ => simp [State.isOk] at h3ok
                | Ok ss₃ vs₃ =>
                  have egb : gb = gasB c body := by
                    have := blockG_gas_eq_of_ok c body s₁ hb (ss := ss) (vs := vs) (by rw [h2])
                    rw [h2] at this; exact this
                  have egp : gp = gasB c post := by
                    have := blockG_gas_eq_of_ok c post _ hp (ss := ss₃) (vs := vs₃) (by rw [h3])
                    rw [h3] at this; exact this
                  have := ih cond post body (State.overwrite? (.Ok ss₃ vs₃) s) hb hp hcl
                  simp only [loopIterGas, loopExitGas] at this ⊢
                  rw [this, egb, egp, hc, Nat.add_mul, Nat.one_mul]
                  ring

/-- On the fragment, every interpreter evaluation that does not run out of fuel equals the metered
result. -/
theorem eval_eq_evalG_of_ne_OOF {fuel : ℕ} {e : Expr} {co : Option YulContract} {s : State}
    (hf : fragE e = true) (h : eval fuel e co s ≠ OOF) : eval fuel e co s = (evalG c e s).1 :=
  evalG_complete c co e s hf (eval_sound rfl h)

/-- **The interpreter agrees with the loop meter.** For a loop whose condition, body and post block
are in the fragment, every run of `exec` that does not run out of fuel returns the result of
`loopG` for some budget. -/
theorem exec_for_eq_loopG {cond : Expr} {post body : List Stmt} {co : Option YulContract}
    (hc : fragE cond = true) (hb : fragB body = true) (hp : fragB post = true) :
    (fuel : ℕ) → (s : State) → exec fuel (.For cond post body) co s ≠ OOF →
      ∃ n, (loopG c n cond post body s).res = exec fuel (.For cond post body) co s := by
  have hbf : InFragment (.Block body) := by simpa [InFragment, fragS] using hb
  have hpf : InFragment (.Block post) := by simpa [InFragment, fragS] using hp
  intro fuel
  induction fuel using Nat.strong_induction_on with
  | _ fuel ih =>
  intro s hne
  match fuel, ih, hne with
  | 0, _, hne => exact absurd (by simp [exec]) hne
  | 1, _, hne => exact absurd (by simp [exec, loop]) hne
  | 2, _, hne => exact absurd (by simp [exec, loop]) hne
  | m + 3, ih, hne =>
    simp only [exec, loop] at hne ⊢
    revert hne
    cases hev : eval m cond co (State.mkOk s) with
    | error e =>
      intro hne
      simp only at hne ⊢
      have he := eval_eq_evalG_of_ne_OOF c hc (fuel := m) (co := co) (s := State.mkOk s)
        (by rw [hev]; rintro ⟨⟩; exact hne rfl)
      rw [hev] at he
      obtain ⟨g, hg⟩ := fst_eq_elim he
      exact ⟨1, by simp only [loopG, hg]⟩
    | ok p =>
      intro hne
      obtain ⟨s₁, x⟩ := p
      have he := eval_eq_evalG_of_ne_OOF c hc (fuel := m) (co := co) (s := State.mkOk s)
        (by rw [hev]; simp [OOF])
      rw [hev] at he
      obtain ⟨g, hg⟩ := fst_eq_elim he
      simp only at hne ⊢
      by_cases hx : x = ⟨0⟩
      · exact ⟨1, by simp only [loopG, hg, hx, if_true]⟩
      · simp only [hx, if_false] at hne ⊢
        revert hne
        cases hb' : exec m (.Block body) co s₁ with
        | error e =>
          intro hne
          simp only at hne ⊢
          have hbe := exec_eq_execG c hbf (fuel := m) (co := co) (s := s₁) (by rw [hb']; exact hne)
          rw [hb'] at hbe
          obtain ⟨gb, hgb⟩ := fst_eq_elim hbe
          simp only [execG] at hgb
          exact ⟨1, by simp only [loopG, hg, hx, if_false, hgb]⟩
        | ok s₂ =>
          intro hne
          have hbe := exec_eq_execG c hbf (fuel := m) (co := co) (s := s₁) (by rw [hb']; simp [OOF])
          rw [hb'] at hbe
          obtain ⟨gb, hgb⟩ := fst_eq_elim hbe
          simp only [execG] at hgb
          simp only at hne ⊢
          cases s₂ with
          | OutOfFuel => exact ⟨1, by simp only [loopG, hg, hx, if_false, hgb]⟩
          | Checkpoint j =>
            cases j with
            | Break ss vs => exact ⟨1, by simp only [loopG, hg, hx, if_false, hgb]⟩
            | Leave ss vs => exact ⟨1, by simp only [loopG, hg, hx, if_false, hgb]⟩
            | Continue ss vs =>
              simp only at hne ⊢
              revert hne
              cases hpo :
                  exec m (.Block post) co (State.reviveJump (State.Checkpoint (.Continue ss vs))) with
              | error e =>
                intro hne
                simp only at hne
                have hpe := exec_eq_execG c (st := .Block post) hpf
                  (fuel := m) (co := co) (s := State.reviveJump (State.Checkpoint (.Continue ss vs)))
                  (by rw [hpo]; exact hne)
                rw [hpo] at hpe
                obtain ⟨gp, hgp⟩ := fst_eq_elim hpe
                simp only [execG] at hgp
                refine ⟨1, ?_⟩
                simp only [loopG, hg, hx, if_false, hgb, hgp]
              | ok s₃ =>
                intro hne
                simp only at hne
                have hpe := exec_eq_execG c (st := .Block post) hpf
                  (fuel := m) (co := co) (s := State.reviveJump (State.Checkpoint (.Continue ss vs)))
                  (by rw [hpo]; simp [OOF])
                rw [hpo] at hpe
                obtain ⟨gp, hgp⟩ := fst_eq_elim hpe
                simp only [execG] at hgp
                revert hne
                cases hre : exec m (.For cond post body) co (s₃.overwrite? s) with
                | error e =>
                  intro hne
                  simp only at hne
                  obtain ⟨n', hn'⟩ := ih m (by omega) (s₃.overwrite? s) (by rw [hre]; exact hne)
                  rw [hre] at hn'
                  refine ⟨n' + 1, ?_⟩
                  simp only [loopG, hg, hx, if_false, hgb, hgp, hn']
                  rw [hre]; rfl
                | ok s₅ =>
                  intro hne
                  obtain ⟨n', hn'⟩ := ih m (by omega) (s₃.overwrite? s) (by rw [hre]; simp [OOF])
                  rw [hre] at hn'
                  refine ⟨n' + 1, ?_⟩
                  simp only [loopG, hg, hx, if_false, hgb, hgp, hn']
                  rw [hre]; rfl
          | Ok ss vs =>
            simp only at hne ⊢
            revert hne
            cases hpo : exec m (.Block post) co (State.reviveJump (State.Ok ss vs)) with
            | error e =>
              intro hne
              simp only at hne
              have hpe := exec_eq_execG c (st := .Block post) hpf
                (fuel := m) (co := co) (s := State.reviveJump (State.Ok ss vs))
                (by rw [hpo]; exact hne)
              rw [hpo] at hpe
              obtain ⟨gp, hgp⟩ := fst_eq_elim hpe
              simp only [execG] at hgp
              refine ⟨1, ?_⟩
              simp only [loopG, hg, hx, if_false, hgb, hgp]
            | ok s₃ =>
              intro hne
              simp only at hne
              have hpe := exec_eq_execG c (st := .Block post) hpf
                (fuel := m) (co := co) (s := State.reviveJump (State.Ok ss vs))
                (by rw [hpo]; simp [OOF])
              rw [hpo] at hpe
              obtain ⟨gp, hgp⟩ := fst_eq_elim hpe
              simp only [execG] at hgp
              revert hne
              cases hre : exec m (.For cond post body) co (s₃.overwrite? s) with
              | error e =>
                intro hne
                simp only at hne
                obtain ⟨n', hn'⟩ := ih m (by omega) (s₃.overwrite? s) (by rw [hre]; exact hne)
                rw [hre] at hn'
                refine ⟨n' + 1, ?_⟩
                simp only [loopG, hg, hx, if_false, hgb, hgp, hn']
                rw [hre]; rfl
              | ok s₅ =>
                intro hne
                obtain ⟨n', hn'⟩ := ih m (by omega) (s₃.overwrite? s) (by rw [hre]; simp [OOF])
                rw [hre] at hn'
                refine ⟨n' + 1, ?_⟩
                simp only [loopG, hg, hx, if_false, hgb, hgp, hn']
                rw [hre]; rfl

/-- **Yul loop gas bound for the interpreter.** For a single-level loop (condition, body and post
block in the loop-free, call-free fragment), every interpreter run that does not run out of fuel
is metered by `loopG`: it returns the metered result, its body ran `iters` times, and it is charged
at most `iters · loopIterGas + loopExitGas` (exactly that, for clean runs of straight-line loops). -/
theorem exec_for_gas_bound {fuel : ℕ} {cond : Expr} {post body : List Stmt}
    {co : Option YulContract} {s : State} {r : Res}
    (hc : fragE cond = true) (hb : fragB body = true) (hp : fragB post = true)
    (h : exec fuel (.For cond post body) co s = r) (hr : r ≠ OOF) :
    ∃ o : LoopOut, o.res = r ∧
      o.gas ≤ o.iters * loopIterGas c cond post body + loopExitGas c cond ∧
      (straightB body = true → straightB post = true → o.clean = true →
        o.gas = o.iters * loopIterGas c cond post body + loopExitGas c cond) := by
  obtain ⟨n, hn⟩ := exec_for_eq_loopG c hc hb hp fuel s (h ▸ hr)
  exact ⟨loopG c n cond post body s, hn.trans h, loopG_gas_le c n cond post body s,
    loopG_gas_eq c n cond post body s⟩

end Gas
end Yul
end EvmYul
