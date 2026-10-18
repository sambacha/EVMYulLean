module

public import EvmYul.EVM.Gas.Lemmas
public section

/-!
# MO-4 / decision D-1: three readings of the CALL gas cap, compared by proof

The handoff (`EVMYulLean_Gas_Handoff.md`, claim C7 and counterexample CE-4) recommends switching the
`C_GASCAP` computation from post-memory-expansion gas (the current model) to instruction-start gas
(the literal Yellow Paper text), asserting that geth, revm and EELS do the latter. This file decides
the question with theorems instead of assertions.

All three readings are written as pure functions of four natural numbers:

* `g` — gas available at the start of the instruction (`μ_g`),
* `m` — the memory-expansion charge of the instruction (`C_mem(μ'_i) − C_mem(μ_i)`),
* `e` — `C_EXTRA` (access + value transfer + new account),
* `q` — the gas requested on the stack (`μ_s[0]`).

Each returns `none` for an exceptional halt with `OutOfGass`, or `some f` where `f` is `C_GASCAP`,
i.e. the gas forwarded to the callee before the stipend.

* `modelCallCharge`: what `X` in `EvmYul/EVM/Semantics.lean` does: it charges `m` (`chargeGas`),
  then evaluates `C' = Ccall = Cgascap + Cextra` on the **post-memory** state and halts if that does
  not fit. `modelCallCharge_bridge` proves the correspondence with the real `Cgascap`/`Ccall`.
* `eelsCallCharge`: a transcription of the Ethereum Execution Layer Specification (EELS),
  `calculate_message_call_gas` + `charge_gas(evm, message_call_gas.cost + extend_memory.cost)`:
  ```
  if gas_left < extra_gas + memory_cost: return MessageCallGas(gas + extra_gas, …)
  gas = min(gas, max_message_call_gas(gas_left - memory_cost - extra_gas))
  return MessageCallGas(gas + extra_gas, …)
  ```
  (EIP-150's own wording: the cap is all but one 64th of the gas "remaining in the parent after
  subtracting the gas cost of the call **and memory expansion**".)
* `ypCallCharge`: the literal YP text, where `C_GASCAP` reads instruction-start `μ_g`.

Results:
* `modelCallCharge_eq_eels`: the current model **equals** the EELS transcription on all inputs.
* `ypCallCharge_some_imp_model`: whenever the YP-literal reading succeeds, the model succeeds and
  forwards at most as much.
* `yp_ne_model_witness`, `not_forall_yp_eq_model`: the converse fails. With `μ_g = C_EXTRA + 6400`,
  a 640-gas memory charge and a "send all gas" request, the model (and EELS) forward 5670, while the
  YP-literal reading halts with `OutOfGass`. Adopting the handoff's D-1 default would therefore make
  ordinary calls fail that EELS executes.
* `ce4_band_both_oog`, `ce4_instance`: the handoff's CE-4 ("YP forwards 50, current code forwards
  10000") is not an observable divergence. In the whole band `g − m < e`, **both** readings halt
  with `OutOfGass` and nothing is forwarded.
-/

namespace EvmYul

namespace EVM

namespace CallReadings

open GasMeter GasConstants UInt256

/-- The current model (`X`): charge memory first, then evaluate `Ccall` on the post-memory gas. -/
def modelCallCharge (g m e q : ℕ) : Option ℕ :=
  if g < m then none else
  let g' := g - m
  let cap := if e ≤ g' then min (L (g' - e)) q else q
  if g' < cap + e then none else some cap

/-- Transcription of EELS `calculate_message_call_gas` followed by
`charge_gas(evm, message_call_gas.cost + extend_memory.cost)`. -/
def eelsCallCharge (g m e q : ℕ) : Option ℕ :=
  let cap := if g < e + m then q else min q (L (g - m - e))
  if g < cap + e + m then none else some cap

/-- The literal Yellow Paper reading: `C_GASCAP` is computed on instruction-start gas, and the
whole cost `C_mem + C_EXTRA + C_GASCAP` must fit into it. -/
def ypCallCharge (g m e q : ℕ) : Option ℕ :=
  let cap := if e ≤ g then min (L (g - e)) q else q
  if g < m + cap + e then none else some cap

/-- **D-1 evidence.** The current model coincides with the EELS reading on every input. -/
theorem modelCallCharge_eq_eels (g m e q : ℕ) :
    modelCallCharge g m e q = eelsCallCharge g m e q := by
  unfold modelCallCharge eelsCallCharge L
  by_cases h1 : g < m
  · have : g < e + m := by omega
    simp only [h1, if_true, this]
    rw [if_pos (by omega)]
  · simp only [h1, if_false]
    by_cases h2 : e ≤ g - m
    · have h3 : ¬ g < e + m := by omega
      simp only [h2, if_true, h3, if_false]
      rw [min_comm]
      have hsub : g - m - e = g - (m + e) := by omega
      by_cases h4 : g - m < min q (g - m - e - (g - m - e) / 64) + e
      · rw [if_pos h4, if_pos (by omega)]
      · rw [if_neg h4, if_neg (by omega)]
    · have h3 : g < e + m := by omega
      simp only [h2, if_false, h3, if_true]
      rw [if_pos (by omega), if_pos (by omega)]

/-- In the model, a successful charge leaves the caller at least the `C_EXTRA + cap + m` it
needs. -/
theorem modelCallCharge_some_iff (g m e q f : ℕ) :
    modelCallCharge g m e q = some f ↔
      m + e ≤ g ∧ f = min (L (g - m - e)) q := by
  unfold modelCallCharge
  by_cases h1 : g < m
  · simp only [h1, if_true, reduceCtorEq, false_iff]; omega
  · simp only [h1, if_false]
    by_cases h2 : e ≤ g - m
    · simp only [h2, if_true]
      have hL : L (g - m - e) ≤ g - m - e := L_le _
      have : min (L (g - m - e)) q ≤ g - m - e := le_trans (min_le_left _ _) hL
      rw [if_neg (by omega), Option.some.injEq]
      constructor
      · intro h; exact ⟨by omega, h.symm⟩
      · rintro ⟨-, rfl⟩; rfl
    · simp only [h2, if_false]
      rw [if_pos (by omega)]
      simp only [reduceCtorEq, false_iff]; omega

/-- In the YP-literal reading the call succeeds iff the full cost fits into instruction-start
gas. -/
theorem ypCallCharge_some_iff (g m e q f : ℕ) :
    ypCallCharge g m e q = some f ↔
      e ≤ g ∧ f = min (L (g - e)) q ∧ m + f + e ≤ g := by
  unfold ypCallCharge
  by_cases h2 : e ≤ g
  · simp only [h2, if_true, true_and]
    by_cases h3 : g < m + min (L (g - e)) q + e
    · rw [if_pos h3]; simp only [reduceCtorEq, false_iff]; omega
    · rw [if_neg h3, Option.some.injEq]; omega
  · simp only [h2, if_false, false_and, iff_false]
    rw [if_pos (by omega)]; simp

/-- The YP-literal reading is **more restrictive**: whenever it lets the call proceed, so does the
model, and the model never forwards more. -/
theorem ypCallCharge_some_imp_model {g m e q f : ℕ} (h : ypCallCharge g m e q = some f) :
    ∃ f', modelCallCharge g m e q = some f' ∧ f' ≤ f := by
  rw [ypCallCharge_some_iff] at h
  obtain ⟨he, rfl, hfit⟩ := h
  refine ⟨min (L (g - m - e)) q, ?_, ?_⟩
  · rw [modelCallCharge_some_iff]; exact ⟨by omega, rfl⟩
  · exact min_le_min_right _ (L_mono (by omega))

/-- The model never halts where it should not: if the model halts, so does the YP-literal
reading. -/
theorem modelCallCharge_none_imp_yp {g m e q : ℕ} (h : modelCallCharge g m e q = none) :
    ypCallCharge g m e q = none := by
  cases hy : ypCallCharge g m e q with
  | none => rfl
  | some f =>
    obtain ⟨f', hf', -⟩ := ypCallCharge_some_imp_model hy
    rw [h] at hf'; cases hf'

/-- With no memory expansion all three readings agree. -/
theorem modelCallCharge_eq_yp_of_zero (g e q : ℕ) :
    modelCallCharge g 0 e q = ypCallCharge g 0 e q := by
  cases hm : modelCallCharge g 0 e q with
  | none => exact (modelCallCharge_none_imp_yp hm).symm
  | some f =>
    rw [modelCallCharge_some_iff] at hm
    obtain ⟨h1, rfl⟩ := hm
    simp only [Nat.sub_zero]
    symm; rw [ypCallCharge_some_iff]
    have := L_le (g - e)
    refine ⟨by omega, by simp, ?_⟩
    have : min (L (g - e)) q ≤ g - e := le_trans (min_le_left _ _) (L_le _)
    omega

/--
**Refutes the handoff's D-1 default.** For *every* `C_EXTRA = e`, with `μ_g = e + 6400`, a memory
charge of 640 and a request of at least 6300 (e.g. Solidity's `gas()`), the model and EELS forward
`5670`, while the YP-literal reading halts with `OutOfGass`.
-/
theorem yp_ne_model_witness (e q : ℕ) (hq : 6300 ≤ q) :
    modelCallCharge (e + 6400) 640 e q = some 5670 ∧
      eelsCallCharge (e + 6400) 640 e q = some 5670 ∧
      ypCallCharge (e + 6400) 640 e q = none := by
  have hm : modelCallCharge (e + 6400) 640 e q = some 5670 := by
    rw [modelCallCharge_some_iff]
    refine ⟨by omega, ?_⟩
    have : e + 6400 - 640 - e = 5760 := by omega
    rw [this]; simp only [L]; omega
  refine ⟨hm, (modelCallCharge_eq_eels _ _ _ _) ▸ hm, ?_⟩
  cases hy : ypCallCharge (e + 6400) 640 e q with
  | none => rfl
  | some f =>
    rw [ypCallCharge_some_iff] at hy
    obtain ⟨-, rfl, hfit⟩ := hy
    have : e + 6400 - e = 6400 := by omega
    rw [this] at hfit; simp only [L] at hfit; omega

/-- Negation of "the YP-literal reading equals the model (so switching is behaviour-preserving)". -/
theorem not_forall_yp_eq_model : ¬ ∀ g m e q, ypCallCharge g m e q = modelCallCharge g m e q := by
  intro h
  obtain ⟨h1, -, h2⟩ := yp_ne_model_witness 2600 10000 (by omega)
  rw [h, h1] at h2
  cases h2

/--
**CE-4 re-falsified.** In the band `g − m < e` (with the memory charge itself affordable), both the
model and the YP-literal reading halt with `OutOfGass`, so no gas is forwarded by either.
-/
theorem ce4_band_both_oog {g m e q : ℕ} (hband : g < m + e) :
    modelCallCharge g m e q = none ∧ ypCallCharge g m e q = none := by
  constructor
  · cases h : modelCallCharge g m e q with
    | none => rfl
    | some f => rw [modelCallCharge_some_iff] at h; omega
  · cases h : ypCallCharge g m e q with
    | none => rfl
    | some f =>
      rw [ypCallCharge_some_iff] at h; omega

/-- The handoff's concrete CE-4 instance (cold CALL, `C_EXTRA = 2600`, `C_mem = 100`,
`μ₀ = 10000`, `g = 2650`): both readings halt; neither forwards 50 nor 10000. -/
theorem ce4_instance :
    modelCallCharge 2650 100 2600 10000 = none ∧ ypCallCharge 2650 100 2600 10000 = none ∧
      eelsCallCharge 2650 100 2600 10000 = none :=
  ⟨(ce4_band_both_oog (by omega)).1, (ce4_band_both_oog (by omega)).2,
    (modelCallCharge_eq_eels _ _ _ _) ▸ (ce4_band_both_oog (by omega)).1⟩

/-! ## Bridge to the definitions the interpreter runs -/

section Bridge

variable {t r : AccountAddress} {val q : UInt256} {σ : AccountMap .EVM} {μ : MachineState}
  {A : Substate}

/--
`modelCallCharge` is exactly what `X` computes for a CALL-family instruction once the memory charge
`m` has succeeded: `Cgascap` and `Ccall` evaluated on `afterMemoryCharge μ m`, followed by the
`gasAvailable < C'` check.
-/
theorem modelCallCharge_bridge (m : ℕ) (hm : m ≤ μ.gasAvailable.toNat) :
    modelCallCharge μ.gasAvailable.toNat m (Cextra t r val σ A) q.toNat =
      (if (afterMemoryCharge μ m).gasAvailable.toNat < Ccall t r val q σ (afterMemoryCharge μ m) A
       then none else some (Cgascap t r val q σ (afterMemoryCharge μ m) A)) := by
  have hpost : (afterMemoryCharge μ m).gasAvailable.toNat = μ.gasAvailable.toNat - m :=
    toNat_sub_ofNat_of_le hm
  unfold modelCallCharge
  rw [if_neg (by omega), Ccall_eq]
  unfold Cgascap
  simp only [hpost, ge_iff_le]

/-- When the memory charge itself does not fit, `X` halts (`chargeGas` fails) and so does the
model. -/
theorem modelCallCharge_of_mem_oog (m : ℕ) (hm : μ.gasAvailable.toNat < m) :
    modelCallCharge μ.gasAvailable.toNat m (Cextra t r val σ A) q.toNat = none ∧
      chargeGas μ.gasAvailable m = .error .OutOfGass := by
  refine ⟨by unfold modelCallCharge; rw [if_pos hm], ?_⟩
  unfold chargeGas; rw [if_pos hm]

end Bridge

end CallReadings

end EVM

end EvmYul
