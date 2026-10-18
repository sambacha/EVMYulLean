module

public import EvmYul.EVM.Gas.Atomicity
public import EvmYul.EVM.Gas.Classification
public import EvmYul.ProofTags
public section

/-!
# Reordering the exceptional-halting checks is behaviour-preserving

`exceptionalHalt` used to deduct the memory-expansion cost and compute `C'` **before** checking
`InvalidInstruction` and `StackUnderflow`. Both cost functions read stack operands with `getD`/`!`
defaults, so on a short stack they computed a cost from made-up operands (which could then raise
`OutOfGass` instead of `StackUnderflow`). The checks now come first.

This file keeps the previous body verbatim as `exceptionalHaltLegacy` (a specification-only copy;
the interpreter does not use it) and proves that the change is invisible to every caller:

* `exceptionalHalt_ok_iff_legacy`: the two versions succeed on exactly the same inputs, with exactly
  the same result (post-memory state and `cost₂`).
* `exceptionalHalt_isOk_iff_legacy`: hence they fail on exactly the same inputs.
* `exceptionalHalt_ne_outOfFuel`, `exceptionalHaltLegacy_ne_outOfFuel`: neither raises `OutOfFuel`,
  the only exception tag that `Lambda`/`Θ` treat differently from the others. So the tag change
  (e.g. `OutOfGass` ↦ `StackUnderflow` on an empty stack) cannot change any transaction outcome.
* `legacy_tag_differs`: the tag change is real (it is a deliberate behaviour change of the error
  *label*, recorded here and in the golden unit tests of `Gas/HaltOrderTests.lean`).
-/

namespace EvmYul

namespace EVM

open GasMeter UInt256

/-- The body of `exceptionalHalt` **before** the reordering: memory charge and `C'` first, then
the `InvalidInstruction` / `StackUnderflow` checks. Kept only as the reference for the
equivalence theorems below. -/
def exceptionalHaltLegacy (validJumps : Array UInt256) (w : Operation .EVM) (evmState : State) :
    Except EVM.ExecutionException (State × ℕ) := do
  let cost₁ := memoryExpansionCost evmState w
  let gasAvailable ← GasMeter.chargeGas evmState.gasAvailable cost₁
  let evmState := { evmState with gasAvailable := gasAvailable}
  let cost₂ := C' evmState w

  if evmState.gasAvailable.toNat < cost₂ then
    .error .OutOfGass

  if δ w = none then
    .error .InvalidInstruction

  if evmState.stack.length < (δ w).getD 0 then
    .error .StackUnderflow

  let invalidJump := jumpTargetNotIn evmState.stack[0]? validJumps

  if w = .JUMP ∧ invalidJump then
    .error .BadJumpDestination

  if w = .JUMPI ∧ (evmState.stack[1]? ≠ some ⟨0⟩) ∧ invalidJump then
    .error .BadJumpDestination

  if w = .RETURNDATACOPY ∧ (evmState.stack.getD 1 ⟨0⟩).toNat +
      (evmState.stack.getD 2 ⟨0⟩).toNat > evmState.returnData.size then
    .error .InvalidMemoryAccess

  if evmState.stack.length - (δ w).getD 0 + (α w).getD 0 > 1024 then
    .error .StackOverflow

  if (¬ evmState.executionEnv.perm) ∧ modifiesState w evmState.stack then
    .error .StaticModeViolation

  if (w = .SSTORE) ∧ evmState.gasAvailable.toNat ≤ GasConstants.Gcallstipend then
    .error .OutOfGass

  if
    w.isCreate ∧ evmState.stack.getD 2 ⟨0⟩ > ⟨49152⟩
  then
    .error .OutOfGass

  pure (evmState, cost₂)

variable {vj : Array UInt256} {w : Operation .EVM} {s : State}

theorem legacy_eq_chargeAndCheck (hδ : δ w ≠ none) (hst : (δ w).getD 0 ≤ s.stack.length) :
    exceptionalHaltLegacy vj w s = chargeAndCheck vj w s := by
  have hst' : ¬ s.stack.length < (δ w).getD 0 := by omega
  simp [exceptionalHaltLegacy, chargeAndCheck, hδ, hst']

theorem legacy_ok_valid {p : State × ℕ} (h : exceptionalHaltLegacy vj w s = .ok p) :
    δ w ≠ none ∧ (δ w).getD 0 ≤ s.stack.length := by
  unfold exceptionalHaltLegacy at h
  obtain ⟨g, -, h⟩ := except_bind_ok h
  obtain ⟨-, h⟩ := except_jp_ok h
  obtain ⟨h1, h⟩ := except_jp_ok h
  obtain ⟨h2, -⟩ := except_jp_ok h
  exact ⟨h1, Nat.le_of_not_lt h2⟩

/-- **Same successes.** The reordered `exceptionalHalt` succeeds exactly when the legacy body
does, with the same post-memory state and the same `cost₂`. -/
theorem exceptionalHalt_ok_iff_legacy {p : State × ℕ} :
    exceptionalHalt vj w s = .ok p ↔ exceptionalHaltLegacy vj w s = .ok p := by
  constructor
  · intro h
    obtain ⟨hδ, hst, h⟩ := exceptionalHalt_ok_operands h
    rwa [legacy_eq_chargeAndCheck hδ hst]
  · intro h
    obtain ⟨hδ, hst⟩ := legacy_ok_valid h
    rwa [exceptionalHalt_of_valid hδ hst, ← legacy_eq_chargeAndCheck hδ hst]

/-- **Same failures.** Hence the two versions fail on exactly the same inputs. -/
theorem exceptionalHalt_isOk_iff_legacy :
    (exceptionalHalt vj w s).isOk = (exceptionalHaltLegacy vj w s).isOk := by
  cases h₁ : exceptionalHalt vj w s with
  | ok p => rw [exceptionalHalt_ok_iff_legacy.1 h₁]
  | error e =>
    cases h₂ : exceptionalHaltLegacy vj w s with
    | ok p => rw [← exceptionalHalt_ok_iff_legacy] at h₂; rw [h₁] at h₂; cases h₂
    | error e' => rfl

/-- A `do`-block guard `if b then throw e'` (compiled to a join point `K`) that fails either raised
its own error `e'`, or passed and the continuation failed. -/
@[reviewed_generic "Except plumbing"]
theorem except_jp_cases {ε α : Type} {b : Prop} [Decidable b] {e e' : ε} {K : PUnit → Except ε α}
    (h : (if b then (do let y ← Except.error e'; K y) else (do let y ← pure PUnit.unit; K y)) =
      .error e) : e = e' ∨ K PUnit.unit = .error e := by
  by_cases hb : b
  · rw [if_pos hb] at h; cases h; exact .inl rfl
  · rw [if_neg hb] at h; exact .inr h

theorem chargeAndCheck_ne_outOfFuel : chargeAndCheck vj w s ≠ .error .OutOfFuel := by
  intro h
  unfold chargeAndCheck at h
  rcases except_bind_error h with hg | ⟨g, -, h⟩
  · unfold chargeGas at hg; split at hg <;> cases hg
  iterate 8 (rcases except_jp_cases h with he | h; · cases he)
  cases h

/-- `exceptionalHalt` never raises `OutOfFuel`. -/
theorem exceptionalHalt_ne_outOfFuel : exceptionalHalt vj w s ≠ .error .OutOfFuel := by
  rw [exceptionalHalt_eq_prev]; unfold exceptionalHaltPrev
  split_ifs
  · simp
  · simp
  · exact chargeAndCheck_ne_outOfFuel

/-- The legacy body never raised `OutOfFuel` either. -/
theorem exceptionalHaltLegacy_ne_outOfFuel :
    exceptionalHaltLegacy vj w s ≠ .error .OutOfFuel := by
  intro h
  unfold exceptionalHaltLegacy at h
  rcases except_bind_error h with hg | ⟨g, -, h⟩
  · unfold chargeGas at hg; split at hg <;> cases hg
  iterate 10 (rcases except_jp_cases h with he | h; · cases he)
  cases h

/-- **The tag change is real.** ADD on an empty stack with fewer than 3 gas: the reordered
`exceptionalHalt` reports `StackUnderflow` (as EELS does), the legacy body reported `OutOfGass`.
Both are exceptional halts, which consume all gas, so the transaction outcome is the same. -/
theorem legacy_tag_differs (hs : s.stack = []) (hg : s.gasAvailable.toNat < 3) :
    exceptionalHalt vj .ADD s = .error .StackUnderflow ∧
      exceptionalHaltLegacy vj .ADD s = .error .OutOfGass := by
  refine ⟨exceptionalHalt_underflow (by decide) (by rw [hs]; decide), ?_⟩
  cases hz : exceptionalHaltLegacy vj .ADD s with
  | ok p =>
    have := (legacy_ok_valid hz).2
    rw [hs] at this
    exact absurd this (by decide)
  | error e =>
    have hm : memoryExpansionCost s .ADD = 0 := by
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ']
    unfold exceptionalHaltLegacy at hz
    rcases except_bind_error hz with hc | ⟨g, hc, hz⟩
    · unfold chargeGas at hc; split at hc <;> cases hc; rfl
    · unfold chargeGas at hc
      rw [hm, if_neg (by omega)] at hc
      cases hc
      refine congrArg _ (except_jp_error hz ?_)
      rw [C'_eq_staticCost _ .ADD rfl, toNat_sub_ofNat_of_le (Nat.zero_le _)]
      exact hg

end EVM

end EvmYul
