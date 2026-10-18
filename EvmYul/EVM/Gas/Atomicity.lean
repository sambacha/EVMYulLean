module

public import EvmYul.EVM.Gas.ForkCostBridge
public import EvmYul.EVM.Gas.Lemmas
public import EvmYul.ProofTags
public section

/-!
# Deduction atomicity of one instruction (handoff PO-3 / PO-4, meter level)

`X` charges an instruction in two places: `exceptionalHalt` (the lifted `Z`) deducts the
memory-expansion cost with `chargeGas` and returns `cost₂ = C'` evaluated on the post-memory state,
and `step`/`call` later deduct `cost₂` with `GasMeter.deductPrechecked`. The handoff's WP-2 wants a
single deduction site and a translation-validation theorem that the change is harmless.

This file proves that the current two-stage deduction **is already** a single guarded charge of
`C_mem + C'`, for the current (EELS-compatible, see `Gas/CallReadings.lean`) reading in which `C'` is
evaluated on the post-memory state:

* `exceptionalHalt_ok`: on success the returned state is the input state with exactly `C_mem`
  removed, `cost₂ = C'` of that state, and `cost₂` fits (so `deductPrechecked` never wraps).
* `exceptionalHalt_two_stage_eq_single_charge`: the gas after both stages equals
  `chargeGas g (C_mem + C')` — one guarded charge of the sum.
* `exceptionalHalt_oog_of_lt`: for a valid instruction with its operands on the stack, if
  `C_mem + C'` does not fit, `exceptionalHalt` raises `OutOfGass` (before any of the later
  exceptional-halting checks).
* `exceptionalHalt_invalid`, `exceptionalHalt_underflow`, `exceptionalHalt_ok_operands`: the
  validity and stack-underflow checks run first, so the cost functions never read missing operands
  on any path that reaches them.
* `deductPrechecked_eq_gasSub`: whenever the pre-check held, `deductPrechecked` is the
  proof-carrying exact subtraction.
-/

namespace EvmYul

namespace EVM

open GasMeter UInt256

theorem deductPrechecked_eq_gasSub (g : UInt256) (c : ℕ) (h : c ≤ g.toNat) :
    deductPrechecked g c = (gasSub g c h).val := (gasSub_eq g c h).symm

theorem deductPrechecked_toNat {g : UInt256} {c : ℕ} (h : c ≤ g.toNat) :
    (deductPrechecked g c).toNat = g.toNat - c := toNat_sub_ofNat_of_le h

/-- Counterexample: without the pre-check `deductPrechecked` wraps around (so the pre-check in
`exceptionalHalt` is load-bearing). -/
theorem deductPrechecked_wraps : (deductPrechecked ⟨0⟩ 1).toNat = UInt256.size - 1 := by
  decide

/-! ### Two small `Except` lemmas used to walk through the do-notation join points -/

@[reviewed_generic "Except plumbing"]
theorem except_bind_ok {ε α β : Type} {m : Except ε α} {f : α → Except ε β} {v : β}
    (h : m >>= f = .ok v) : ∃ a, m = .ok a ∧ f a = .ok v := by
  cases m with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

@[reviewed_generic "Except plumbing"]
theorem except_bind_error {ε α β : Type} {m : Except ε α} {f : α → Except ε β} {e : ε}
    (h : m >>= f = .error e) : m = .error e ∨ ∃ a, m = .ok a ∧ f a = .error e := by
  cases m with
  | error e' => cases h; exact .inl rfl
  | ok a => exact .inr ⟨a, rfl, h⟩

/-- A `do`-block guard `if b then throw e'` (compiled to a join point `K`) that succeeds proves
`¬ b`. -/
@[reviewed_generic "Except plumbing"]
theorem except_jp_ok {ε α : Type} {b : Prop} [Decidable b] {e : ε} {K : PUnit → Except ε α}
    {v : α}
    (h : (if b then (do let y ← Except.error e; K y)
          else (do let y ← pure PUnit.unit; K y)) = .ok v) :
    ¬ b ∧ K PUnit.unit = .ok v := by
  by_cases hb : b
  · rw [if_pos hb] at h; cases h
  · rw [if_neg hb] at h; exact ⟨hb, h⟩

/-- A guard whose condition holds raises exactly its own error. -/
@[reviewed_generic "Except plumbing"]
theorem except_jp_error {ε α : Type} {b : Prop} [Decidable b] {e e' : ε} {K : PUnit → Except ε α}
    (h : (if b then (do let y ← Except.error e'; K y) else (do let y ← pure PUnit.unit; K y)) =
      .error e) (hb : b) : e = e' := by
  rw [if_pos hb] at h; cases h; rfl

section

variable {vj : Array UInt256} {w : Operation .EVM} {s : State}

/-- An instruction with no stack signature (`δ w = none`) halts with `InvalidInstruction` before
any gas is computed. -/
theorem exceptionalHalt_invalid (hδ : δ w = none) :
    exceptionalHalt vj w s = .error .InvalidInstruction := by
  rw [exceptionalHalt_eq_prev]; unfold exceptionalHaltPrev; rw [if_pos hδ]

/-- A valid instruction with too few operands halts with `StackUnderflow` before `C_mem` or `C'`
(which read the operands with defaults) is evaluated. -/
theorem exceptionalHalt_underflow (hδ : δ w ≠ none) (hst : s.stack.length < (δ w).getD 0) :
    exceptionalHalt vj w s = .error .StackUnderflow := by
  rw [exceptionalHalt_eq_prev]; unfold exceptionalHaltPrev; rw [if_neg hδ, if_pos hst]

/-- For a valid instruction with its operands on the stack, `exceptionalHalt` is `chargeAndCheck`. -/
theorem exceptionalHalt_of_valid (hδ : δ w ≠ none) (hst : (δ w).getD 0 ≤ s.stack.length) :
    exceptionalHalt vj w s = chargeAndCheck vj w s := by
  rw [exceptionalHalt_eq_prev]; unfold exceptionalHaltPrev; rw [if_neg hδ, if_neg (by omega)]

/-- On success the instruction was valid and all its operands were on the stack, so the operand
reads with defaults in `memoryExpansionCost` and `C'` only ever saw real stack entries; the result
is that of `chargeAndCheck`. -/
theorem exceptionalHalt_ok_operands {p : State × ℕ} (h : exceptionalHalt vj w s = .ok p) :
    δ w ≠ none ∧ (δ w).getD 0 ≤ s.stack.length ∧ chargeAndCheck vj w s = .ok p := by
  rw [exceptionalHalt_eq_prev] at h; unfold exceptionalHaltPrev at h
  split at h
  · cases h
  split at h
  · cases h
  exact ⟨by assumption, by omega, h⟩

/--
On success, `exceptionalHalt` has removed exactly the memory-expansion cost `C_mem` (which fit),
returns `cost₂ = C'` of the post-memory state, and `cost₂` fits into the remaining gas. This is
the pre-check that makes `deductPrechecked` in `step`/`call` an exact, non-wrapping subtraction.
-/
theorem exceptionalHalt_ok {s' : State} {c : ℕ} (h : exceptionalHalt vj w s = .ok (s', c)) :
    memoryExpansionCost s w ≤ s.gasAvailable.toNat ∧
      s' = { s with gasAvailable := s.gasAvailable - .ofNat (memoryExpansionCost s w) } ∧
      c = C' s' w ∧ c ≤ s'.gasAvailable.toNat := by
  replace h := (exceptionalHalt_ok_operands h).2.2
  unfold chargeAndCheck at h
  obtain ⟨g, hg, h⟩ := except_bind_ok h
  obtain ⟨hfit, h⟩ := except_jp_ok h
  iterate 7 (obtain ⟨_, h⟩ := except_jp_ok h)
  have hm : ¬ s.gasAvailable.toNat < memoryExpansionCost s w := by
    intro hlt; unfold chargeGas at hg; rw [if_pos hlt] at hg; cases hg
  unfold chargeGas at hg; rw [if_neg hm] at hg; cases hg
  cases h
  exact ⟨by omega, rfl, rfl, Nat.le_of_not_lt hfit⟩

/-- The gas left after the memory charge, as a natural number. -/
theorem exceptionalHalt_ok_gas {s' : State} {c : ℕ} (h : exceptionalHalt vj w s = .ok (s', c)) :
    s'.gasAvailable.toNat = s.gasAvailable.toNat - memoryExpansionCost s w := by
  obtain ⟨hm, rfl, -, -⟩ := exceptionalHalt_ok h
  exact toNat_sub_ofNat_of_le hm

/--
**Single-deduction equivalence (PO-3, meter level).** The two deductions of one instruction (memory
expansion in `exceptionalHalt`, then `cost₂` via `deductPrechecked` in `step`) leave exactly the gas
of **one** guarded charge of `C_mem + C'`. A refactor to a single deduction site that keeps `C'`
evaluated on the post-memory state is therefore behaviour-preserving for gas.
-/
theorem exceptionalHalt_two_stage_eq_single_charge {s' : State} {c : ℕ}
    (h : exceptionalHalt vj w s = .ok (s', c)) :
    chargeGas s.gasAvailable (memoryExpansionCost s w + c) =
      .ok (deductPrechecked s'.gasAvailable c) := by
  obtain ⟨hm, -, -, hc⟩ := exceptionalHalt_ok h
  have hg := exceptionalHalt_ok_gas h
  rw [chargeGas_ok_iff, deductPrechecked_toNat hc, hg]
  omega

/-- Total gas consumed by the instruction's charge is exactly `C_mem + C'`, and never more than
what was available (no wrap-around at either stage). -/
theorem exceptionalHalt_deduct_toNat {s' : State} {c : ℕ}
    (h : exceptionalHalt vj w s = .ok (s', c)) :
    (deductPrechecked s'.gasAvailable c).toNat =
        s.gasAvailable.toNat - (memoryExpansionCost s w + c) ∧
      memoryExpansionCost s w + c ≤ s.gasAvailable.toNat :=
  (chargeGas_ok_iff.1 (exceptionalHalt_two_stage_eq_single_charge h)).symm

/--
**OOG has priority over the operand-dependent checks.** For a valid instruction whose operands are
on the stack, if `C_mem + C'` (with `C'` evaluated after the memory charge) does not fit,
`exceptionalHalt` raises `OutOfGass`, regardless of every later exceptional-halting condition
(bad jump, return-data bounds, stack overflow, static-mode violation, …). The two hypotheses are
necessary: `InvalidInstruction` and `StackUnderflow` are checked first
(`exceptionalHalt_invalid`, `exceptionalHalt_underflow`).
-/
theorem exceptionalHalt_oog_of_lt (hδ : δ w ≠ none) (hst : (δ w).getD 0 ≤ s.stack.length)
    (h : s.gasAvailable.toNat < memoryExpansionCost s w +
      C' { s with gasAvailable := s.gasAvailable - .ofNat (memoryExpansionCost s w) } w) :
    exceptionalHalt vj w s = .error .OutOfGass := by
  cases hz : exceptionalHalt vj w s with
  | ok p =>
    obtain ⟨s', c⟩ := p
    obtain ⟨hm, rfl, rfl, hc⟩ := exceptionalHalt_ok hz
    have := toNat_sub_ofNat_of_le hm
    simp only at hc this
    omega
  | error e =>
    rw [exceptionalHalt_of_valid hδ hst] at hz
    unfold chargeAndCheck at hz
    rcases except_bind_error hz with hg | ⟨g, hg, hz⟩
    · unfold chargeGas at hg; split at hg <;> cases hg; rfl
    · have hm : ¬ s.gasAvailable.toNat < memoryExpansionCost s w := by
        intro hlt; unfold chargeGas at hg; rw [if_pos hlt] at hg; cases hg
      unfold chargeGas at hg; rw [if_neg hm] at hg; cases hg
      refine congrArg _ (except_jp_error hz ?_)
      have := toNat_sub_ofNat_of_le (Nat.le_of_not_lt hm)
      simp only [this]
      omega

end

end EVM

end EvmYul
