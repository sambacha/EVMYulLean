module

public import EvmYul.EVM.Gas.Meter
public import EvmYul.ProofTags
public section

/-!
# Gas lemma battery (issue S1)

Machine-checked arithmetic facts about the gas model in `EvmYul/EVM/Gas/Costs.lean` and the combinators
in `EvmYul/EVM/Gas/Meter.lean`. Every lemma is about the definitions the interpreter actually runs.
`X` charges memory expansion through `chargeGas`, and `Υ` computes the refund through
`refundedGas`.

Contents:
* `UInt256` ↔ `ℕ` round-trip lemmas (the "obvious but tedious" tranche of §5.A).
* `chargeGas` / `gasSub`: guarded deduction never wraps, OOG exactly when `gas < cost`, and the
  two-phase (memory + `C'`) charge fails exactly when `gas < C_mem + C'`. The counterexample
  `not_forall_unguarded_sub_le` shows the guard is necessary.
* EIP-3529 refund cap: the applied refund is at most `⌊gasUsed/5⌋`, the final gas never exceeds the
  gas limit, and the final gas used is at least `4/5` of the pre-refund gas used.
* The 1/64 rule `L`, monotonicity of the memory cost `Cₘ`.
* CALL: `Cgascap ≤ requested`, `Cgascap ≤ L(μ_g − C_extra)`, forwarding identities, and the caller
  keeping at least `⌊(μ_g − C_extra)/64⌋`. The counterexample `not_Cgascap_mono_in_gas` refutes the
  conjecture that the cap is monotone in available gas.
* S4: post-memory-charge cap ≤ instruction-start cap, equal when there is no memory charge, and a
  universally quantified example where they differ by 630 gas.
* Intrinsic gas lower bounds.
-/

namespace EvmYul

namespace UInt256

theorem toNat_lt_size (a : UInt256) : a.toNat < UInt256.size := a.val.isLt

theorem toNat_ofNat_of_lt {n : ℕ} (h : n < UInt256.size) : (UInt256.ofNat n).toNat = n := by
  simp [UInt256.ofNat, UInt256.toNat, Id.run, Fin.ofNat, Nat.mod_eq_of_lt h]

theorem toNat_sub_of_le {a b : UInt256} (h : b.toNat ≤ a.toNat) :
    (a - b).toNat = a.toNat - b.toNat := by
  change ((a.val - b.val : Fin _) : ℕ) = _
  exact (Fin.coe_sub_iff_le).2 h

theorem toNat_sub_ofNat_of_le {g : UInt256} {c : ℕ} (h : c ≤ g.toNat) :
    (g - UInt256.ofNat c).toNat = g.toNat - c := by
  have hc : c < UInt256.size := lt_of_le_of_lt h g.toNat_lt_size
  rw [toNat_sub_of_le] <;> rw [toNat_ofNat_of_lt hc]; exact h

theorem toNat_div (a b : UInt256) : (a / b).toNat = a.toNat / b.toNat := by
  change ((a.val / b.val : Fin _) : ℕ) = _
  simp [Fin.div_val, UInt256.toNat]

theorem toNat_add_of_lt {a b : UInt256} (h : a.toNat + b.toNat < UInt256.size) :
    (a + b).toNat = a.toNat + b.toNat := by
  change ((a.val + b.val : Fin _) : ℕ) = _
  rw [Fin.val_add]; exact Nat.mod_eq_of_lt h

theorem toNat_min (a b : UInt256) : (min a b).toNat = min a.toNat b.toNat := by
  change (if a ≤ b then a else b).toNat = _
  by_cases h : a ≤ b
  · have : a.toNat ≤ b.toNat := h
    simp [h, this]
  · have : ¬ a.toNat ≤ b.toNat := h
    simp [h]; omega

/-- Counterexample (S3): raw `UInt256` subtraction of a cost that exceeds the gas wraps around. -/
theorem unguarded_sub_wraps :
    (UInt256.ofNat 0 - UInt256.ofNat 1).toNat = UInt256.size - 1 := by decide

end UInt256

namespace EVM

open GasConstants GasMeter UInt256

/-! ## Guarded deduction (S3, S5) -/

/-- `chargeGas` is exactly the guard-then-subtract shape that `X` used inline before the
refactor. -/
@[reviewed_rfl "the guard-then-subtract shape of `chargeGas`, by definition"]
theorem chargeGas_eq_guarded (g : UInt256) (c : ℕ) :
    chargeGas g c = (if g.toNat < c then .error .OutOfGass else .ok (g - .ofNat c)) := rfl

/--
Justification of the `X` refactor: binding `chargeGas` is the same computation as the
original inline guard followed by raw subtraction, for every continuation `k`.
-/
theorem chargeGas_bind_eq_guarded {α : Type} (g : UInt256) (c : ℕ)
    (k : UInt256 → Except ExecutionException α) :
    (chargeGas g c >>= k) =
      (do if g.toNat < c then .error .OutOfGass
          k (g - .ofNat c)) := by
  unfold chargeGas
  by_cases h : g.toNat < c <;> simp [h, bind, Except.bind, pure, Except.pure]

/-- Success of `chargeGas` means the cost fits, and the result is the true difference (no wrap). -/
theorem chargeGas_ok_iff {g g' : UInt256} {c : ℕ} :
    chargeGas g c = .ok g' ↔ c ≤ g.toNat ∧ g'.toNat = g.toNat - c := by
  unfold chargeGas
  by_cases h : g.toNat < c
  · simp [h]
  · simp only [h, if_false, Except.ok.injEq]
    constructor
    · rintro rfl; exact ⟨by omega, toNat_sub_ofNat_of_le (by omega)⟩
    · rintro ⟨hc, hg⟩
      apply UInt256.ext; apply Fin.ext
      change (g - UInt256.ofNat c).toNat = g'.toNat
      rw [toNat_sub_ofNat_of_le hc, hg]

/-- `chargeGas` signals `OutOfGass` exactly when the cost exceeds the available gas. -/
theorem chargeGas_error_iff {g : UInt256} {c : ℕ} :
    chargeGas g c = .error .OutOfGass ↔ g.toNat < c := by
  unfold chargeGas; by_cases h : g.toNat < c <;> simp [h]

theorem chargeGas_isOk_iff (g : UInt256) (c : ℕ) :
    (∃ g', chargeGas g c = .ok g') ↔ c ≤ g.toNat := by
  constructor
  · rintro ⟨g', h⟩; exact (chargeGas_ok_iff.1 h).1
  · intro h; exact ⟨_, if_neg (by omega)⟩

/-- Gas is non-increasing across a successful charge. -/
theorem chargeGas_le {g g' : UInt256} {c : ℕ} (h : chargeGas g c = .ok g') :
    g'.toNat ≤ g.toNat := by
  have := chargeGas_ok_iff.1 h; omega

/-- The proof-carrying subtraction agrees with the raw subtraction used throughout
`Semantics.lean`. -/
theorem gasSub_eq (g : UInt256) (c : ℕ) (h : c ≤ g.toNat) :
    (gasSub g c h).val = g - .ofNat c := by
  apply UInt256.ext; apply Fin.ext
  change g.toNat - c = (g - UInt256.ofNat c).toNat
  rw [toNat_sub_ofNat_of_le h]

@[reviewed_rfl "the value of `gasSub`, by definition"]
theorem gasSub_toNat (g : UInt256) (c : ℕ) (h : c ≤ g.toNat) :
    (gasSub g c h).val.toNat = g.toNat - c :=
  rfl

/-- The certificate carried by `gasSub`: remaining gas plus cost is the gas before. -/
theorem gasSub_add (g : UInt256) (c : ℕ) (h : c ≤ g.toNat) :
    (gasSub g c h).val.toNat + c = g.toNat :=
  (gasSub g c h).property

theorem chargeGas_eq_gasSub (g : UInt256) (c : ℕ) (h : c ≤ g.toNat) :
    chargeGas g c = .ok (gasSub g c h).val := by
  rw [gasSub_eq]; exact if_neg (by omega)

/--
Doc §4.1 "OOG exactly when `gas < C_mem + C'`": a two-phase charge succeeds iff the sum of the
costs fits, and then leaves exactly `gas − (c₁ + c₂)`.
-/
theorem chargeGas_bind_ok_iff {g g' : UInt256} {c₁ c₂ : ℕ} :
    (chargeGas g c₁ >>= fun g₁ => chargeGas g₁ c₂) = .ok g' ↔
      c₁ + c₂ ≤ g.toNat ∧ g'.toNat = g.toNat - (c₁ + c₂) := by
  by_cases h1 : g.toNat < c₁
  · rw [chargeGas_error_iff.2 h1]; simp [bind, Except.bind]; omega
  · obtain ⟨g₁, hg₁⟩ := (chargeGas_isOk_iff g c₁).2 (by omega)
    have := chargeGas_ok_iff.1 hg₁
    rw [hg₁]; simp only [bind, Except.bind]
    rw [chargeGas_ok_iff]; omega

theorem chargeGas_bind_error_iff {g : UInt256} {c₁ c₂ : ℕ} :
    (chargeGas g c₁ >>= fun g₁ => chargeGas g₁ c₂) = .error .OutOfGass ↔ g.toNat < c₁ + c₂ := by
  by_cases h1 : g.toNat < c₁
  · rw [chargeGas_error_iff.2 h1]; simp [bind, Except.bind]; omega
  · obtain ⟨g₁, hg₁⟩ := (chargeGas_isOk_iff g c₁).2 (by omega)
    have := chargeGas_ok_iff.1 hg₁
    rw [hg₁]; simp only [bind, Except.bind]
    rw [chargeGas_error_iff]; omega

/-- Refuted conjecture (S3): without the guard, "subtracting a cost never increases gas" is
false. -/
theorem not_forall_unguarded_sub_le :
    ¬ ∀ (g : UInt256) (c : ℕ), (g - UInt256.ofNat c).toNat ≤ g.toNat := by
  intro h
  have := h (UInt256.ofNat 0) 1
  rw [unguarded_sub_wraps] at this
  exact absurd this (by decide)

/-! ## EIP-3529 refund (YP (82)) -/

section Refund

variable {gl g' r : UInt256}

theorem refundApplied_toNat (h : g'.toNat ≤ gl.toNat) :
    (min ((gl - g') / ⟨5⟩) r).toNat = min ((gl.toNat - g'.toNat) / 5) r.toNat := by
  rw [toNat_min, toNat_div, toNat_sub_of_le h]; rfl

/-- The refund actually applied never exceeds `⌊gasUsed / 5⌋`. -/
theorem refundApplied_le_fifth (h : g'.toNat ≤ gl.toNat) :
    (min ((gl - g') / ⟨5⟩) r).toNat ≤ (gl.toNat - g'.toNat) / 5 := by
  rw [refundApplied_toNat h]; exact min_le_left _ _

/-- The refund actually applied never exceeds the accrued refund counter `A_r`. -/
theorem refundApplied_le_balance (h : g'.toNat ≤ gl.toNat) :
    (min ((gl - g') / ⟨5⟩) r).toNat ≤ r.toNat := by
  rw [refundApplied_toNat h]; exact min_le_right _ _

/-- Exact value of `g*` as a natural number (no `UInt256` overflow on the addition). -/
theorem refundedGas_toNat (h : g'.toNat ≤ gl.toNat) :
    (refundedGas gl g' r).toNat = g'.toNat + min ((gl.toNat - g'.toNat) / 5) r.toNat := by
  unfold refundedGas
  have h1 := refundApplied_le_fifth (r := r) h
  have h2 := gl.toNat_lt_size
  rw [toNat_add_of_lt, refundApplied_toNat h]
  omega

theorem le_refundedGas (h : g'.toNat ≤ gl.toNat) : g'.toNat ≤ (refundedGas gl g' r).toNat := by
  rw [refundedGas_toNat h]; omega

/-- The gas returned to the sender never exceeds the transaction gas limit. -/
theorem refundedGas_le_gasLimit (h : g'.toNat ≤ gl.toNat) :
    (refundedGas gl g' r).toNat ≤ gl.toNat := by
  rw [refundedGas_toNat h]; omega

/-- The final gas used (`T_g − g*`, the value returned by `Υ`) as a natural number. -/
theorem gasUsed_after_refund (h : g'.toNat ≤ gl.toNat) :
    (gl - refundedGas gl g' r).toNat =
      (gl.toNat - g'.toNat) - min ((gl.toNat - g'.toNat) / 5) r.toNat := by
  rw [toNat_sub_of_le (refundedGas_le_gasLimit h), refundedGas_toNat h]; omega

/-- Refunds can reduce the gas used by at most a fifth. -/
theorem gasUsed_after_refund_ge (h : g'.toNat ≤ gl.toNat) :
    4 * (gl.toNat - g'.toNat) ≤ 5 * (gl - refundedGas gl g' r).toNat := by
  rw [gasUsed_after_refund h]; omega

theorem refundedGas_zero_refund (h : g'.toNat ≤ gl.toNat) :
    (refundedGas gl g' (UInt256.ofNat 0)).toNat = g'.toNat := by
  rw [refundedGas_toNat h]; simp [toNat_ofNat_of_lt (show 0 < UInt256.size by decide)]

end Refund

/-! ## The 1/64 rule `L` (YP (331)) -/

theorem L_add_div (n : ℕ) : L n + n / 64 = n := by
  unfold L; omega

theorem L_le (n : ℕ) : L n ≤ n := Nat.sub_le _ _

/-- `L(n) ≥ 63n/64`. -/
theorem L_ge (n : ℕ) : 63 * n ≤ 64 * L n := by
  unfold L; omega

theorem L_mono {m n : ℕ} (h : m ≤ n) : L m ≤ L n := by
  unfold L; omega

theorem L_lt_of_ge {n : ℕ} (h : 64 ≤ n) : L n < n := by
  unfold L; omega

theorem L_eq_self_of_lt {n : ℕ} (h : n < 64) : L n = n := by
  unfold L; omega

/-- Refuted conjecture: `L` is not strictly below its argument for small positive inputs. -/
theorem not_forall_L_lt : ¬ ∀ n, 0 < n → L n < n := by
  intro h; exact absurd (h 1 (by decide)) (by decide)

/-! ## Memory cost `Cₘ` (YP (328)) -/

@[reviewed_rfl "restates the memory cost function (Yellow Paper equation form)"]
theorem Cₘ_eq (a : UInt256) : Cₘ a = Gmemory * a.toNat + a.toNat * a.toNat / 512 := rfl

/-- `Cₘ` is monotone in the number of active words. -/
theorem Cₘ_mono {a b : UInt256} (h : a.toNat ≤ b.toNat) : Cₘ a ≤ Cₘ b := by
  rw [Cₘ_eq, Cₘ_eq]; gcongr

/-- Memory expansion cost (`Cₘ μᵢ' − Cₘ μᵢ`) is an exact difference when memory grows. -/
theorem memoryExpansion_add {a b : UInt256} (h : a.toNat ≤ b.toNat) : Cₘ b - Cₘ a + Cₘ a = Cₘ b :=
  Nat.sub_add_cancel (Cₘ_mono h)

/-! ## CALL gas (YP H.1: `C_CALL`, `C_GASCAP`, `C_EXTRA`, `C_CALLGAS`) -/

theorem Caccess_ge (a : AccountAddress) (A : Substate) : Gwarmaccess ≤ Caccess a A := by
  unfold Caccess; split <;> simp [Gwarmaccess, Gcoldaccountaccess]

theorem Caccess_le (a : AccountAddress) (A : Substate) : Caccess a A ≤ Gcoldaccountaccess := by
  unfold Caccess; split <;> simp [Gwarmaccess, Gcoldaccountaccess]

section Call

/-! Following Mathlib style, the call context is **implicit** in lemmas with a hypothesis that
mentions it (it is recovered by unification, e.g. `rw [Cgascap_of_ge h]`), and explicit in
hypothesis-free lemmas, where nothing else determines it. -/

variable {t r : AccountAddress} {val g : UInt256} {σ : AccountMap .EVM} {μ : MachineState}
  {A : Substate}

variable (t r val σ A) in
theorem Cextra_ge : Gwarmaccess ≤ Cextra t r val σ A := by
  unfold Cextra; have := Caccess_ge t A; omega

variable (t r val σ A) in
theorem Cextra_le : Cextra t r val σ A ≤ Gcoldaccountaccess + Gcallvalue + Gnewaccount := by
  unfold Cextra Cxfer Cnew; have := Caccess_le t A
  split <;> split <;> omega

variable (t r val g σ μ A) in
/-- The callee never receives more than the requested gas `μₛ[0]` (stipend aside). -/
theorem Cgascap_le_requested : Cgascap t r val g σ μ A ≤ g.toNat := by
  unfold Cgascap; split
  · exact min_le_right _ _
  · exact le_rfl

theorem Cgascap_of_ge (h : Cextra t r val σ A ≤ μ.gasAvailable.toNat) :
    Cgascap t r val g σ μ A = min (L (μ.gasAvailable.toNat - Cextra t r val σ A)) g.toNat := by
  unfold Cgascap; rw [if_pos h]

theorem Cgascap_of_lt (h : μ.gasAvailable.toNat < Cextra t r val σ A) :
    Cgascap t r val g σ μ A = g.toNat := by
  unfold Cgascap; rw [if_neg (by omega)]

/-- All-but-one-64th (EIP-150): the forwarded cap is at most `L(μ_g − C_extra)`. -/
theorem Cgascap_le_L (h : Cextra t r val σ A ≤ μ.gasAvailable.toNat) :
    Cgascap t r val g σ μ A ≤ L (μ.gasAvailable.toNat - Cextra t r val σ A) := by
  rw [Cgascap_of_ge h]; exact min_le_left _ _

variable (t r val g σ μ A) in
@[reviewed_rfl "restates the CALL cost function (Yellow Paper equation form)"]
theorem Ccall_eq : Ccall t r val g σ μ A = Cgascap t r val g σ μ A + Cextra t r val σ A := rfl

variable (t r g σ μ A) in
@[reviewed_rfl "restates the CALL gas stipend for a zero value transfer"]
theorem Ccallgas_of_zero : Ccallgas t r ⟨0⟩ g σ μ A = Cgascap t r ⟨0⟩ g σ μ A := rfl

/-- A value-carrying call forwards the stipend `G_callstipend` on top of the cap. -/
theorem Ccallgas_of_ne_zero (h : val ≠ ⟨0⟩) :
    Ccallgas t r val g σ μ A = Cgascap t r val g σ μ A + Gcallstipend := by
  unfold Ccallgas; split
  · exact absurd rfl h
  · rfl

variable (t r val g σ μ A) in
theorem Ccall_ge : Gwarmaccess ≤ Ccall t r val g σ μ A := by
  rw [Ccall_eq]; have := Cextra_ge t r val σ A; omega

/--
If the CALL charge fits into the available gas, the caller keeps at least
`⌊(μ_g − C_extra)/64⌋` after paying it (the reason for the 1/64 rule).
-/
theorem Ccall_fits_retains (h : Ccall t r val g σ μ A ≤ μ.gasAvailable.toNat) :
    (μ.gasAvailable.toNat - Cextra t r val σ A) / 64 ≤
      μ.gasAvailable.toNat - Ccall t r val g σ μ A := by
  rw [Ccall_eq] at *
  by_cases hx : Cextra t r val σ A ≤ μ.gasAvailable.toNat
  · have := Cgascap_le_L (g := g) hx
    have := L_add_div (μ.gasAvailable.toNat - Cextra t r val σ A)
    omega
  · rw [Cgascap_of_lt (by omega)] at h; omega

theorem Ccallgas_le_forwarded (h : Cextra t r val σ A ≤ μ.gasAvailable.toNat) :
    Ccallgas t r val g σ μ A ≤ L (μ.gasAvailable.toNat - Cextra t r val σ A) + Gcallstipend := by
  have := Cgascap_le_L (g := g) h
  unfold Ccallgas; split <;> omega

end Call

/--
Refuted conjecture: `Cgascap` is **not** monotone in the available gas. Below `C_extra` the
`else` branch returns the full request. One more unit switches to `min (L 0) g = 0`. (In
`X` this is harmless, because `C_CALL = g + C_extra > μ_g` then raises `OutOfGass`.)
-/
theorem not_Cgascap_mono_in_gas :
    ¬ ∀ (t r : AccountAddress) (val g : UInt256) (σ : AccountMap .EVM) (μ₁ μ₂ : MachineState)
        (A : Substate),
        μ₁.gasAvailable.toNat ≤ μ₂.gasAvailable.toNat →
        Cgascap t r val g σ μ₁ A ≤ Cgascap t r val g σ μ₂ A := by
  intro hmono
  let t : AccountAddress := default
  let σ : AccountMap .EVM := default
  let A : Substate := default
  let e := Cextra t t ⟨0⟩ σ A
  have he1 : 100 ≤ e := Cextra_ge t t ⟨0⟩ σ A
  have he2 : e < UInt256.size := lt_of_le_of_lt (Cextra_le t t ⟨0⟩ σ A) (by decide)
  let μ₁ : MachineState := { (default : MachineState) with gasAvailable := UInt256.ofNat 0 }
  let μ₂ : MachineState := { (default : MachineState) with gasAvailable := UInt256.ofNat e }
  have h₁ : μ₁.gasAvailable.toNat = 0 := toNat_ofNat_of_lt (by decide)
  have h₂ : μ₂.gasAvailable.toNat = e := toNat_ofNat_of_lt he2
  have one : (UInt256.ofNat 1).toNat = 1 := toNat_ofNat_of_lt (by decide)
  have := hmono t t ⟨0⟩ (UInt256.ofNat 1) σ μ₁ μ₂ A (by omega)
  rw [Cgascap_of_lt (by omega), Cgascap_of_ge (by omega), h₂, one] at this
  simp [e, L] at this

/-! ## S4: `C_GASCAP` on post-memory-expansion gas vs. instruction-start gas -/

section S4

variable {t r : AccountAddress} {val g : UInt256} {σ : AccountMap .EVM} {μ : MachineState}
  {A : Substate}

/--
The model (cap computed after the memory charge) never forwards more than the YP reading (cap
computed on instruction-start gas). This holds whenever the call is not already out of gas.
-/
theorem Cgascap_post_le_pre (m : ℕ) (hm : m ≤ μ.gasAvailable.toNat)
    (hx : Cextra t r val σ A ≤ μ.gasAvailable.toNat - m) :
    Cgascap t r val g σ (afterMemoryCharge μ m) A ≤ Cgascap t r val g σ μ A := by
  have hpost : (afterMemoryCharge μ m).gasAvailable.toNat = μ.gasAvailable.toNat - m :=
    toNat_sub_ofNat_of_le hm
  rw [Cgascap_of_ge (by omega), Cgascap_of_ge (by omega), hpost]
  exact min_le_min_right _ (L_mono (by omega))

variable (t r val g σ μ A) in
/-- With no memory expansion the two readings coincide. -/
theorem Cgascap_post_eq_pre_of_zero :
    Cgascap t r val g σ (afterMemoryCharge μ 0) A = Cgascap t r val g σ μ A := by
  have : (afterMemoryCharge μ 0).gasAvailable.toNat = μ.gasAvailable.toNat := by
    rw [afterMemoryCharge, toNat_sub_ofNat_of_le (Nat.zero_le _)]; rfl
  unfold Cgascap; rw [this]

/--
The readings genuinely differ. For **every** call context with `μ_g = C_extra + 6400`, a
request of at least `6300` and a memory charge of `640`, the model forwards `5670` while the
instruction-start reading forwards `6300`. The ordering is therefore a semantic choice (a
documented deviation), not a refactoring detail.
-/
theorem Cgascap_post_ne_pre_example
    (hgas : μ.gasAvailable.toNat = Cextra t r val σ A + 6400) (hg : 6300 ≤ g.toNat) :
    Cgascap t r val g σ (afterMemoryCharge μ 640) A = 5670 ∧
      Cgascap t r val g σ μ A = 6300 := by
  have hpost : (afterMemoryCharge μ 640).gasAvailable.toNat = μ.gasAvailable.toNat - 640 :=
    toNat_sub_ofNat_of_le (by omega)
  rw [Cgascap_of_ge (by omega), Cgascap_of_ge (by omega), hpost, hgas]
  constructor
  · have : Cextra t r val σ A + 6400 - 640 - Cextra t r val σ A = 5760 := by omega
    rw [this]; simp [L]; omega
  · have : Cextra t r val σ A + 6400 - Cextra t r val σ A = 6400 := by omega
    rw [this]; simp [L]; omega

end S4

/-! ## Intrinsic gas `g₀` -/

/-- Every transaction pays at least `G_transaction = 21000`, so `gasUsed ≥ 21000`. -/
theorem intrinsicGas_ge_Gtransaction (T : Transaction) : Gtransaction ≤ intrinsicGas T := by
  unfold intrinsicGas; simp only; omega

/-- A contract-creation transaction additionally pays `G_txcreate`. -/
theorem intrinsicGas_ge_create (T : Transaction) (h : T.base.recipient = none) :
    Gtransaction + Gtxcreate ≤ intrinsicGas T := by
  unfold intrinsicGas; simp only [h]; simp; omega

end EVM

end EvmYul
