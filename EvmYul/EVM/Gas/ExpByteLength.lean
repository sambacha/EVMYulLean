module

public import EvmYul.EVM.Gas.ForkCost
public import Mathlib.Data.Nat.Digits.Lemmas

public section

/-!
# The byte length in the `EXP` cost (YP Appendix H.1)

The Yellow Paper charges `EXP` with exponent `μₛ[1]` as

  `G_exp` if `μₛ[1] = 0`, and `G_exp + G_expbyte × (1 + ⌊log₂₅₆ μₛ[1]⌋)` otherwise,

i.e. `G_expbyte` per byte of the big-endian encoding of the exponent. The interpreter (`C'`,
`EvmYul/EVM/Gas/Costs.lean`) and the fork-parametric cost (`ForkSchedule.instrCost?`,
`EvmYul/EVM/Gas/ForkCost.lean`) both compute `1 + Nat.log 256 e` for a non-zero exponent. `C'` carried
the note "TODO(check) I think this floors by itself": the question is whether `Nat.log` is the
*floor* logarithm the formula needs, so that the factor is the byte length. This file settles it.

**Conjecture (K-EXP).** For every exponent `e`, the `EXP` cost is `G_exp + G_expbyte × byteLength e`,
where `byteLength e` is the number of base-256 digits of `e` (`0` for `e = 0`).

**Lemmas.**
* `one_add_log_eq_byteLength`: `1 + Nat.log 256 n = byteLength n` for `n ≠ 0`. `Nat.log` is the floor
  logarithm, so the TODO's guess is right.
* `byteLength_eq_clog_succ`: `byteLength n = Nat.clog 256 (n + 1)`, the YP's other spelling
  `⌈log₂₅₆ (n + 1)⌉`, for every `n` (including `0`).
* `byteLength_eq_length_toBytesBigEndian`: it is also the length of the interpreter's own big-endian
  encoding `toBytesBigEndian`.
* `byteLength_eq_succ_iff`: `byteLength n = k + 1 ↔ 256 ^ k ≤ n < 256 ^ (k + 1)`.
* `byteLength_toNat_le`: a 256-bit exponent has at most 32 bytes.

**The conjecture, proved** for both cost functions: `C'_EXP` and `instrCost?_EXP`. Because
`byteLength 0 = 0`, one formula covers both branches; the zero test in the code is only needed
because `1 + Nat.log 256 0 = 1` (`one_add_log_zero_ne_byteLength`). Hence the maximum charge
`exp_cost_le` (`G_exp + 32 G_expbyte`).

**Negations / counterexamples** (each candidate reading of the TODO that is *wrong* is refuted):
* `not_forall_log_eq_byteLength`: the factor without the `1 +` is wrong (`n = 1`).
* `not_forall_clog_eq_byteLength`: the ceiling logarithm `⌈log₂₅₆ n⌉` as the byte count is wrong
  (`n = 256`: 2 bytes, but `Nat.clog 256 256 = 1`).
* `one_add_log_zero_ne_byteLength`: dropping the zero test is wrong (`e = 0` would be charged one
  byte).
-/

namespace EvmYul.EVM.ExpByteLength

open GasConstants

/-- The number of bytes of the minimal big-endian encoding of `n` (`0` for `n = 0`): the number of
its base-256 digits. -/
def byteLength (n : ℕ) : ℕ := (Nat.digits 256 n).length

@[simp] theorem byteLength_zero : byteLength 0 = 0 := by simp [byteLength]

/-- `Nat.log` is the floor logarithm, so `1 + log₂₅₆ n` counts the bytes of a non-zero `n`. -/
theorem one_add_log_eq_byteLength {n : ℕ} (hn : n ≠ 0) : 1 + Nat.log 256 n = byteLength n := by
  rw [byteLength, Nat.digits_len 256 n (by norm_num) hn, Nat.add_comm]

/-- Characterisation of the byte length of a non-zero number by powers of 256. -/
theorem byteLength_eq_succ_iff {n k : ℕ} : byteLength n = k + 1 ↔ 256 ^ k ≤ n ∧ n < 256 ^ (k + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [byteLength_zero]
    constructor
    · intro h; omega
    · rintro ⟨h, -⟩; exact absurd h (Nat.not_le.mpr (Nat.pow_pos (by norm_num)))
  · rw [← one_add_log_eq_byteLength hn.ne', Nat.add_comm, Nat.add_right_cancel_iff,
      Nat.log_eq_iff (Or.inr ⟨by norm_num, hn.ne'⟩)]

/-- The YP's other spelling, `⌈log₂₅₆ (n + 1)⌉`, is the same number, for every `n`. -/
theorem byteLength_eq_clog_succ (n : ℕ) : byteLength n = Nat.clog 256 (n + 1) := by
  apply le_antisymm
  · rw [byteLength, Nat.digits_length_le_iff (by norm_num)]
    exact Nat.lt_of_succ_le (Nat.le_pow_clog (by norm_num) _)
  · rw [Nat.clog_le_iff_le_pow (by norm_num)]
    exact Nat.succ_le_of_lt ((Nat.digits_length_le_iff (b := 256) (by norm_num) n).mp le_rfl)

/-- The byte length is the length of the interpreter's own big-endian encoding. -/
theorem byteLength_eq_length_toBytesBigEndian (n : ℕ) :
    byteLength n = (EvmYul.toBytesBigEndian n).length := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | n
    · simp [byteLength, EvmYul.toBytesBigEndian, EvmYul.toBytes']
    · have hlt : (n + 1) / 256 < n + 1 := Nat.div_lt_self (Nat.succ_pos n) (by norm_num)
      have h := ih _ hlt
      simp only [byteLength, EvmYul.toBytesBigEndian, Function.comp_apply, List.length_reverse]
        at h ⊢
      rw [Nat.digits_def' (by norm_num) (Nat.succ_pos n), List.length_cons, h, EvmYul.toBytes']
      rfl

/-- A 256-bit word has at most 32 bytes. -/
theorem byteLength_toNat_le (e : UInt256) : byteLength e.toNat ≤ 32 := by
  rw [byteLength, Nat.digits_length_le_iff (by norm_num)]
  exact e.val.isLt

/-- Byte length is monotone. -/
theorem byteLength_mono {m n : ℕ} (h : m ≤ n) : byteLength m ≤ byteLength n := by
  rw [byteLength_eq_clog_succ, byteLength_eq_clog_succ]
  exact Nat.clog_mono_right _ (Nat.succ_le_succ h)

/-! ## The conjecture K-EXP for both cost functions -/

/-- The interpreter's zero test on a word is a test of its numeric value. -/
theorem beq_zero_iff_toNat_eq_zero (e : UInt256) : (e == ⟨0⟩) = true ↔ e.toNat = 0 := by
  rcases e with ⟨v⟩
  constructor
  · intro h
    have h' : (v == 0) = true := h
    have hv : v = 0 := by simpa using h'
    simp [UInt256.toNat, hv]
  · intro h
    have hv : v = 0 := Fin.ext h
    subst hv; rfl

/-- The interpreter's `EXP` charge is `G_exp + G_expbyte` per byte of the exponent. -/
theorem C'_EXP (s : State) :
    C' s .EXP = Gexp + Gexpbyte * byteLength (s.stack[1]!).toNat := by
  simp only [C']
  by_cases h : (s.stack[1]! == ⟨0⟩) = true
  · rw [if_pos h, (beq_zero_iff_toNat_eq_zero _).mp h, byteLength_zero, Nat.mul_zero, Nat.add_zero]
  · rw [if_neg h, one_add_log_eq_byteLength (mt (beq_zero_iff_toNat_eq_zero _).mpr h)]

/-- The fork-parametric `EXP` charge is `fs.Gexp + fs.Gexpbyte` per byte of the exponent (and
`none` when the exponent operand is missing). -/
theorem instrCost?_EXP (fs : ForkSchedule) (gas : ℕ) (s : State) :
    fs.instrCost? gas s .EXP =
      s.stack[1]?.map (fun e => fs.Gexp + fs.Gexpbyte * byteLength e.toNat) := by
  simp only [ForkSchedule.instrCost?]
  cases s.stack[1]? with
  | none => rfl
  | some e =>
    show some _ = some (fs.Gexp + fs.Gexpbyte * byteLength e.toNat)
    by_cases h : (e == ⟨0⟩) = true
    · rw [if_pos h, (beq_zero_iff_toNat_eq_zero _).mp h, byteLength_zero, Nat.mul_zero,
        Nat.add_zero]
    · rw [if_neg h, one_add_log_eq_byteLength (mt (beq_zero_iff_toNat_eq_zero _).mpr h)]

/-- The largest `EXP` charge: 32 exponent bytes. -/
theorem exp_cost_le (s : State) : C' s .EXP ≤ Gexp + Gexpbyte * 32 := by
  rw [C'_EXP]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (byteLength_toNat_le _)) _

/-! ## Negations: the wrong readings of the TODO are refuted -/

/-- Counterexample `n = 1`: without the `1 +` the factor is one byte short. -/
theorem not_forall_log_eq_byteLength : ¬ ∀ n, n ≠ 0 → Nat.log 256 n = byteLength n := by
  intro h
  have h1 := h 1 one_ne_zero
  rw [← one_add_log_eq_byteLength one_ne_zero] at h1
  omega

/-- Counterexample `n = 256`: the ceiling logarithm `⌈log₂₅₆ n⌉` undercounts exact powers of 256
(`256` has two bytes, `Nat.clog 256 256 = 1`). -/
theorem not_forall_clog_eq_byteLength : ¬ ∀ n, n ≠ 0 → Nat.clog 256 n = byteLength n := by
  intro h
  have h256 := h 256 (by norm_num)
  rw [← one_add_log_eq_byteLength (by norm_num)] at h256
  have hlog : Nat.log 256 256 = 1 := by simpa using Nat.log_pow (b := 256) (by norm_num) 1
  have hclog : Nat.clog 256 256 = 1 := by
    simpa using Nat.clog_pow 256 1 (by norm_num)
  omega

/-- The zero test is needed: `1 + log₂₅₆ 0` charges one byte for the exponent `0`. -/
theorem one_add_log_zero_ne_byteLength : 1 + Nat.log 256 0 ≠ byteLength 0 := by
  simp

/-! ## Pinned values (each derived through `byteLength_eq_succ_iff`, not by evaluation) -/

theorem byteLength_255 : byteLength 255 = 1 := byteLength_eq_succ_iff.mpr (by norm_num)
theorem byteLength_256 : byteLength 256 = 2 := byteLength_eq_succ_iff.mpr (by norm_num)
theorem byteLength_two_pow_256_sub_one : byteLength (2 ^ 256 - 1) = 32 :=
  byteLength_eq_succ_iff.mpr (by norm_num)

end EvmYul.EVM.ExpByteLength
