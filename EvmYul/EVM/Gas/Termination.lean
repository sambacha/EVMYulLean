module

public import EvmYul.EVM.Gas.CallBoundary
public section

/-!
# Termination by well-founded recursion on gas

## Generic gas machines

A `GasMachine` has a gas measure and a one-step function `next f s` (the fuel `f` is only passed
on to nested computations). If every continuing step strictly lowers the gas (`Decreasing`), then

* `GasMachine.run` executes the machine **without a fuel counter**, by well-founded recursion on
  the gas (`termination_by M.gas s`);
* `GasMachine.runFuel` (the fuel-indexed loop, shaped like the interpreter's `X`) agrees with it as
  soon as the fuel exceeds the gas, when `next` does not depend on the fuel (`runFuel_eq_run`); in
  particular the loop's own counter never runs out (`runFuel_ne_oof_of_const`);
* in general the loop's own counter never runs out when the fuel exceeds the gas by 2; then
  `OutOfFuel` can only come from a nested call of `next` that itself had more fuel than gas
  (`runFuel_ne_oof`).

## The interpreter's loop `X`

`X_ne_outOfFuel` is the same argument for the real `X`: if the fuel exceeds the gas by 2, `X`'s own
fuel counter is never exhausted. The decrease of the measure in each iteration is
`exceptionalHalt_charge_lt` (proved: every non-halting instruction is charged at least 1 gas).
Two properties of the rest of the mutual block `step`/`call`/`Θ`/`Λ`/`Ξ` enter as explicit
hypotheses, both stated only for a charge `c` that `Z` (`exceptionalHalt`) actually produced:

* `StepGasSoundZ`: executing the instruction either deducts at least the charge or strictly lowers
  the gas;
* `NestedFuelAdequateZ`: with more fuel than gas, the step does not run out of fuel (the induction
  hypothesis a whole-interpreter proof, by induction on gas over the mutual block, would discharge).

`GasStepFrame` proves both for every instruction except the six that open a nested frame
(CREATE, CREATE2, CALL, CALLCODE, DELEGATECALL, STATICCALL), so they remain open only there.

### Correction: the earlier, charge-free hypotheses were false

An earlier version of `X_ne_outOfFuel` assumed `StepGasSound` and `NestedFuelAdequate` below, which
quantify over *every* charge `c ≤ gas` and every fuel `f > gas + 1`. Both are refuted in
`GasStepFrame` by concrete CALL executions (`not_stepGasSound`, `not_nestedFuelAdequate`): with
charge 0 a value-transferring CALL that fails the balance check hands the caller the callee
allowance plus the 2300 stipend, raising its gas from 0 to 2400; and a CALL with fuel 2 reaches
`Θ` with fuel 0, which raises `OutOfFuel`. The earlier theorem was therefore vacuous. Real charges
exclude both witnesses: a CALL's `Z` charge includes `C_EXTRA ≥ 100`, which pays for the stipend
and leaves fuel for the nested frames. The definitions are kept so the refutations stay checked.
`X` itself still uses fuel; it is not replaced.
-/

namespace EvmYul

namespace EVM

open GasMeter ForkSchedule

/-! ## Generic gas machines -/

/-- A machine with a gas measure. `next f s` either continues (`.inl s'`), halts with a result
(`.inr r`) or raises; `f` is the fuel available to nested computations. -/
structure GasMachine (S R E : Type) where
  /-- The gas left in a state: the measure that every continuing step lowers. -/
  gas : S → ℕ
  /-- One step with nested fuel `f`: continue (`.inl s'`), halt with a result (`.inr r`) or raise. -/
  next : ℕ → S → Except E (S ⊕ R)

namespace GasMachine

variable {S R E : Type} (M : GasMachine S R E)

/-- Every continuing step strictly lowers the gas. -/
@[expose] def Decreasing : Prop := ∀ f s s', M.next f s = .ok (.inl s') → M.gas s' < M.gas s

/-- **Fuel-free execution** by well-founded recursion on the gas (nested fuel fixed to `F`). -/
@[expose] def run (hM : M.Decreasing) (F : ℕ) (s : S) : Except E R :=
  match h : M.next F s with
  | .error e => .error e
  | .ok (.inr r) => .ok r
  | .ok (.inl s') =>
    have : M.gas s' < M.gas s := hM F s s' h
    run hM F s'
termination_by M.gas s

/-- The fuel-indexed loop, shaped like the interpreter's `X`: fuel `0` raises `oof`, otherwise one
step is taken with the remaining fuel. -/
def runFuel (oof : E) : ℕ → S → Except E R
  | 0, _ => .error oof
  | f + 1, s =>
    match M.next f s with
    | .error e => .error e
    | .ok (.inr r) => .ok r
    | .ok (.inl s') => runFuel oof f s'

theorem run_eq (hM : M.Decreasing) (F : ℕ) (s : S) :
    M.run hM F s =
      match M.next F s with
      | .error e => .error e
      | .ok (.inr r) => .ok r
      | .ok (.inl s') => M.run hM F s' := by
  rw [run]
  split <;> rename_i h <;> simp [h]

/-- **Fuel adequacy, fuel-independent steps**: once the fuel exceeds the gas, the fuel-indexed loop
computes exactly the fuel-free `run`. -/
theorem runFuel_eq_run (hM : M.Decreasing) (F : ℕ) (hF : ∀ f, M.next f = M.next F) (oof : E) :
    ∀ f s, M.gas s < f → M.runFuel oof f s = M.run hM F s := by
  intro f
  induction f with
  | zero => intro s h; omega
  | succ n ih =>
    intro s hs
    rw [runFuel, run_eq, hF n]
    rcases h : M.next F s with e | (s' | r)
    · rfl
    · have := hM F s s' h
      exact ih s' (by omega)
    · rfl

/-- With fuel-independent steps, the loop's own counter never runs out once fuel exceeds gas
(`oof` can then only be raised by `next` itself). -/
theorem runFuel_ne_oof_of_const (hM : M.Decreasing) (F : ℕ) (hF : ∀ f, M.next f = M.next F)
    (oof : E) (hn : ∀ s, M.next F s ≠ .error oof) {f : ℕ} {s : S} (hs : M.gas s < f) :
    M.runFuel oof f s ≠ .error oof := by
  rw [runFuel_eq_run M hM F hF oof f s hs]
  clear hs
  induction s using (measure M.gas).wf.induction with
  | h s ih =>
    rw [run_eq]
    rcases h : M.next F s with e | (s' | r)
    · simp only; intro he; cases he; exact hn s h
    · exact ih s' (hM F s s' h)
    · simp

/-- **The loop's own counter never runs out** when the fuel exceeds the gas by 2: if
`runFuel oof f s` raises `oof`, then some nested `next f' s'` with `M.gas s' + 1 < f'` raised it. -/
theorem runFuel_ne_oof (hM : M.Decreasing) (oof : E)
    (hn : ∀ f s, M.gas s + 1 < f → M.next f s ≠ .error oof) :
    ∀ f s, M.gas s + 2 < f → M.runFuel oof f s ≠ .error oof := by
  intro f
  induction f with
  | zero => intro s h; omega
  | succ n ih =>
    intro s hs
    rw [runFuel]
    rcases h : M.next n s with e | (s' | r)
    · simp only; intro he; cases he; exact hn n s (by omega) h
    · have := hM n s s' h
      exact ih s' (by omega)
    · simp

end GasMachine

/-! ## The interpreter's loop `X` -/

/-- **Refuted** (`not_stepGasSound` in `GasStepFrame`): the earlier gas hypothesis, for an
arbitrary charge `c ≤ gas`. Kept only so that its refutation stays checked; use `StepGasSoundZ`. -/
@[expose] def StepGasSound : Prop :=
  ∀ (f c : ℕ) (i : Option (Operation .EVM × Option (UInt256 × Nat))) (s₁ s₂ : State),
    c ≤ s₁.gasAvailable.toNat → step f c i s₁ = .ok s₂ →
      s₂.gasAvailable.toNat ≤ (deductPrechecked s₁.gasAvailable c).toNat ∨
        s₂.gasAvailable.toNat < s₁.gasAvailable.toNat

/-- **Refuted** (`not_nestedFuelAdequate` in `GasStepFrame`): the earlier fuel hypothesis, for an
arbitrary charge. Kept only so that its refutation stays checked; use `NestedFuelAdequateZ`. -/
@[expose] def NestedFuelAdequate : Prop :=
  ∀ (f c : ℕ) (i : Option (Operation .EVM × Option (UInt256 × Nat))) (s₁ : State),
    s₁.gasAvailable.toNat + 1 < f → step f c i s₁ ≠ .error .OutOfFuel

/-- Executing a decoded instruction after `Z` accepted it with charge `c` either deducts at least
`c` or strictly lowers the gas. Proved outside the six spawning instructions
(`GasStepFrame.stepGasSoundZ_of_spawn`); for those too in `GasNested.stepGasSoundZ`. -/
@[expose] def StepGasSoundZ : Prop :=
  ∀ (f : ℕ) (vj : Array UInt256) (w : Operation .EVM) (arg : Option (UInt256 × Nat))
    (s s₁ : State) (c : ℕ) (s₂ : State),
    exceptionalHalt vj w s = .ok (s₁, c) → step f c (some (w, arg)) s₁ = .ok s₂ →
      s₂.gasAvailable.toNat ≤ (deductPrechecked s₁.gasAvailable c).toNat ∨
        s₂.gasAvailable.toNat < s₁.gasAvailable.toNat

/-- After `Z` accepted a decoded instruction with charge `c`, executing it with more fuel than gas
does not raise `OutOfFuel`. Proved outside the six spawning instructions
(`GasStepFrame.nestedFuelAdequateZ_of_spawn`); for those too in `GasNested.nestedFuelAdequateZ`. -/
@[expose] def NestedFuelAdequateZ : Prop :=
  ∀ (f : ℕ) (vj : Array UInt256) (w : Operation .EVM) (arg : Option (UInt256 × Nat))
    (s s₁ : State) (c : ℕ),
    exceptionalHalt vj w s = .ok (s₁, c) → s₁.gasAvailable.toNat + 1 < f →
      step f c (some (w, arg)) s₁ ≠ .error .OutOfFuel

/-- INVALID never passes `Z`: it has no price. -/
theorem exceptionalHalt_INVALID_ne_ok (vj : Array UInt256) (s s' : State) (c : ℕ) :
    exceptionalHalt vj .INVALID s ≠ .ok (s', c) := by
  intro h
  have := (exceptionalHalt_ok_parts h).2.2
  simp only [instrCost?] at this
  repeat rw [if_neg (by decide)] at this
  cases this

theorem halting_eq_false_of {w : Operation .EVM} (h1 : w ∉ [Operation.RETURN, .REVERT])
    (h2 : w ∉ [Operation.STOP, .SELFDESTRUCT]) (h3 : w ≠ .INVALID) : halting w = false := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h1 h2
  unfold halting
  simp [h1.1, h1.2, h2.1, h2.2, h3]

/-- **`X`'s own fuel counter is never exhausted** once the fuel exceeds the gas by 2, assuming
`StepGasSoundZ` and `NestedFuelAdequateZ`. The per-iteration decrease is the proved
`exceptionalHalt_charge_lt`. -/
theorem X_ne_outOfFuel (hS : StepGasSoundZ) (hN : NestedFuelAdequateZ) :
    ∀ (f : ℕ) (vj : Array UInt256) (s : State), s.gasAvailable.toNat + 2 < f →
      X f vj s ≠ .error .OutOfFuel := by
  intro f
  induction f with
  | zero => intro vj s h; omega
  | succ n ih =>
    intro vj s hs
    unfold X
    simp only [traceInstructions, Bool.false_eq_true, ↓reduceIte]
    generalize (decode s.executionEnv.code s.pc).getD (Operation.STOP, none) = instr
    obtain ⟨w, arg⟩ := instr
    simp only
    rcases hZ : exceptionalHalt vj w s with e | ⟨s₁, c⟩
    · simp only; intro he; cases he; exact exceptionalHalt_ne_outOfFuel hZ
    · obtain ⟨hs₁, hc, -⟩ := exceptionalHalt_ok_parts hZ
      have hg₁ : s₁.gasAvailable.toNat ≤ s.gasAvailable.toNat := by
        have := exceptionalHalt_ok_gas hZ
        omega
      simp only [bind, Except.bind]
      rcases hstep : step n c (some (w, arg)) s₁ with e | s₂
      · simp only; intro he; cases he; exact hN n vj w arg s s₁ c hZ (by omega) hstep
      · simp only
        split
        · rename_i hH
          split at hH
          · cases hH
          · rename_i h1
            split at hH
            · cases hH
            · rename_i h2
              have hw : halting w = false := halting_eq_false_of h1 h2 (by
                rintro rfl; exact exceptionalHalt_INVALID_ne_ok vj s s₁ c hZ)
              have hlt : s₂.gasAvailable.toNat < s.gasAvailable.toNat := by
                rcases hS n vj w arg s s₁ c s₂ hZ hstep with h | h
                · have := exceptionalHalt_charge_lt hw hZ
                  omega
                · omega
              exact ih vj s₂ (by omega)
        · split <;> simp

end EVM

end EvmYul
