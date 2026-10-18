module

public import EvmYul.EVM.Gas.Fuel
public import EvmYul.EVM.Gas.HaltOrder
public section

/-!
# Gas laws: shared statements, congruences and independent oracles

The formal side of the testing conventions in `TESTING.md`. Each law here is stated **once** as a
`Prop`-valued definition with a `Decidable` instance (guideline F3), proved for every input, and
evaluated by the same definition on concrete inputs in `Gas/MeterConventionTests.lean`, so the proved
statement and the tested statement cannot drift apart.

* **F3 shared statements**: `ChargeLaw` (the guarded deduction), `HaltLaw` (one-instruction
  atomicity of `exceptionalHalt`).
* **C3 replay congruences** of a run of charges `chargeAll`: chunking
  (`chargeAll_append`), reordering (`chargeAll_perm`), no-op padding (`chargeAll_append_zeros`),
  all from the stronger `chargeAll_eq_of_sum_eq`: the outcome depends only on the total.
* **D1 independent oracle**: `L_eq_ceil` derives the 63/64 rule by a second route,
  `L n = ⌈63 n / 64⌉`.
* **D2 Galois round trip** between `UInt256` and `ℕ`: `ofNat_toNat`, `toNat_ofNat`,
  `toNat_ofNat_le` (the concretisation never claims more gas than was given).
-/

namespace EvmYul

namespace EVM

open GasMeter GasConstants UInt256

-- Exception tags are compared in the laws below (the interpreter only derives `BEq`).
deriving instance DecidableEq for ExecutionException

/-! ## F3: laws stated once, proved, and tested through the same definition -/

/-- The guarded-deduction law for one charge: success iff the cost fits, leaving the exact
difference; failure is always `OutOfGass`. -/
@[expose] def ChargeLaw (g : UInt256) (c : ℕ) : Prop :=
  match chargeGas g c with
  | .ok g' => c ≤ g.toNat ∧ g'.toNat = g.toNat - c
  | .error e => g.toNat < c ∧ e = .OutOfGass

@[expose] instance (g : UInt256) (c : ℕ) : Decidable (ChargeLaw g c) := by
  unfold ChargeLaw
  exact match chargeGas g c with
    | .ok _ => inferInstance
    | .error _ => inferInstance

theorem chargeLaw_holds (g : UInt256) (c : ℕ) : ChargeLaw g c := by
  unfold ChargeLaw
  split
  · next g' h => exact chargeGas_ok_iff.1 h
  · next e h =>
    unfold chargeGas at h
    split at h
    · cases h; exact ⟨by assumption, rfl⟩
    · cases h

/-- The one-instruction atomicity law of `exceptionalHalt`: on success, memory cost plus
instruction cost fit and are removed exactly, and the returned cost is `C'` of the post-memory
state. -/
@[expose] def HaltLaw (vj : Array UInt256) (w : Operation .EVM) (s : State) : Prop :=
  match exceptionalHalt vj w s with
  | .ok (s', k) =>
    memoryExpansionCost s w + k ≤ s.gasAvailable.toNat ∧
      (deductPrechecked s'.gasAvailable k).toNat =
        s.gasAvailable.toNat - (memoryExpansionCost s w + k) ∧
      k = C' s' w
  | .error e => e ≠ .OutOfFuel

@[expose] instance (vj : Array UInt256) (w : Operation .EVM) (s : State) : Decidable (HaltLaw vj w s) := by
  unfold HaltLaw
  exact match exceptionalHalt vj w s with
    | .ok (_, _) => inferInstance
    | .error _ => inferInstance

theorem haltLaw_holds (vj : Array UInt256) (w : Operation .EVM) (s : State) : HaltLaw vj w s := by
  unfold HaltLaw
  split
  · next s' k h =>
    obtain ⟨h1, h2⟩ := exceptionalHalt_deduct_toNat h
    exact ⟨h2, h1, (exceptionalHalt_ok h).2.2.1⟩
  · next e h =>
    rintro rfl; exact exceptionalHalt_ne_outOfFuel h

/-! ## C3: a run of charges is a congruence for the total -/

/-- Every failure of a run of charges is `OutOfGass`. -/
theorem chargeAll_error {g : UInt256} {cs : List ℕ} {e : ExecutionException}
    (h : chargeAll g cs = .error e) : e = .OutOfGass := by
  induction cs generalizing g with
  | nil => cases h
  | cons c cs ih =>
    unfold chargeAll at h
    split at h
    · exact ih h
    · next e' he =>
      cases h
      unfold chargeGas at he; split at he <;> cases he; rfl

/-- **The outcome of a run of charges depends only on the total cost.** -/
theorem chargeAll_eq_of_sum_eq {g : UInt256} {xs ys : List ℕ} (h : xs.sum = ys.sum) :
    chargeAll g xs = chargeAll g ys := by
  cases hx : chargeAll g xs with
  | ok gx =>
    obtain ⟨hfit, hval⟩ := (chargeAll_ok_iff xs).1 hx
    cases hy : chargeAll g ys with
    | ok gy =>
      obtain ⟨-, hval'⟩ := (chargeAll_ok_iff ys).1 hy
      congr 1
      apply UInt256.ext; apply Fin.ext
      change gx.toNat = gy.toNat
      omega
    | error e =>
      exfalso
      have hfit' : ys.sum ≤ g.toNat := h ▸ hfit
      have : (UInt256.ofNat (g.toNat - ys.sum)).toNat = g.toNat - ys.sum :=
        toNat_ofNat_of_lt (by have := toNat_lt_size g; omega)
      rw [((chargeAll_ok_iff ys).2 ⟨hfit', this⟩)] at hy
      cases hy
  | error e =>
    cases hy : chargeAll g ys with
    | ok gy =>
      exfalso
      obtain ⟨hfit, -⟩ := (chargeAll_ok_iff ys).1 hy
      have hfit' : xs.sum ≤ g.toNat := h ▸ hfit
      have : (UInt256.ofNat (g.toNat - xs.sum)).toNat = g.toNat - xs.sum :=
        toNat_ofNat_of_lt (by have := toNat_lt_size g; omega)
      rw [((chargeAll_ok_iff xs).2 ⟨hfit', this⟩)] at hx
      cases hx
    | error e' => rw [chargeAll_error hx, chargeAll_error hy]

/-- Chunking: running `xs ++ ys` is running `xs`, then `ys` on what is left. -/
theorem chargeAll_append (g : UInt256) (xs ys : List ℕ) :
    chargeAll g (xs ++ ys) = (chargeAll g xs).bind (chargeAll · ys) := by
  induction xs generalizing g with
  | nil => rfl
  | cons c cs ih =>
    simp only [List.cons_append, chargeAll]
    split
    · exact ih _
    · rfl

/-- Reordering independent charges does not change the outcome. -/
theorem chargeAll_perm {g : UInt256} {xs ys : List ℕ} (h : xs.Perm ys) :
    chargeAll g xs = chargeAll g ys :=
  chargeAll_eq_of_sum_eq h.sum_eq

/-- Padding a run with free steps does not change the outcome. -/
theorem chargeAll_append_zeros (g : UInt256) (xs : List ℕ) (n : ℕ) :
    chargeAll g (xs ++ List.replicate n 0) = chargeAll g xs :=
  chargeAll_eq_of_sum_eq (by simp)

/-! ## D1: an independent derivation of the 63/64 rule -/

/-- `L n = n − ⌊n/64⌋` (YP (331)) equals `⌈63 n / 64⌉`, the EIP-150 phrasing. -/
theorem L_eq_ceil (n : ℕ) : L n = (63 * n + 63) / 64 := by
  unfold L; omega

/-! ## D2: the `UInt256` ↔ `ℕ` round trip -/

/-- `ofNat ∘ toNat = id`: no gas value is changed by passing through `ℕ`. -/
theorem ofNat_toNat (a : UInt256) : UInt256.ofNat a.toNat = a := by
  apply UInt256.ext; apply Fin.ext
  exact toNat_ofNat_of_lt (toNat_lt_size a)

/-- `toNat ∘ ofNat` reduces modulo `2^256`. -/
theorem toNat_ofNat (n : ℕ) : (UInt256.ofNat n).toNat = n % UInt256.size := by
  simp [UInt256.ofNat, UInt256.toNat, Id.run, Fin.ofNat]

/-- Soundness of the round trip: converting a natural number to `UInt256` never *increases* it
(a cost of `2^256` or more is not silently turned into a larger one). -/
theorem toNat_ofNat_le (n : ℕ) : (UInt256.ofNat n).toNat ≤ n := by
  rw [toNat_ofNat]; exact Nat.mod_le _ _

/-- **The `2^256` wall (B1).** A cost of `2^256` or more always runs out of gas, so the wrapped
value `ofNat c = c mod 2^256` (which may be tiny) is never deducted. -/
theorem chargeGas_of_size_le {g : UInt256} {c : ℕ} (h : UInt256.size ≤ c) :
    chargeGas g c = .error .OutOfGass := by
  unfold chargeGas; rw [if_pos (lt_of_lt_of_le (toNat_lt_size g) h)]

/-- The round trip is exact precisely below `2^256`. -/
theorem toNat_ofNat_eq_iff (n : ℕ) : (UInt256.ofNat n).toNat = n ↔ n < UInt256.size := by
  rw [toNat_ofNat]
  constructor
  · intro h; rw [← h]; exact Nat.mod_lt _ (by decide)
  · exact Nat.mod_eq_of_lt

end EVM

end EvmYul
