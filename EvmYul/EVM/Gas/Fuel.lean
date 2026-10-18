module

public import EvmYul.EVM.Semantics
public import EvmYul.EVM.Gas.Lemmas
public section

/-!
# Fuel (handoff C13, CE-9, PO-10)

* `Υ_zero_fuel` (**CE-9 on the real interpreter**): with fuel `0`, `Υ` fails with `OutOfFuel` for
  every transaction, every state and every header. The conformance runner used to set
  `fuel := senderBalance`, so a valid zero-fee transaction from a zero-balance sender could never
  execute. `balanceFuel_zero_fails` packages this as a statement about that old fuel choice.
* `transactionFuel` (in `Gas/Meter.lean`, now used by `Conform/TestRunner.lean`) is never below the
  old choice (`balanceFuel_le_transactionFuel`) and always exceeds the gas limit
  (`gasLimit_lt_transactionFuel`), whatever the balance.
* PO-10, meter level: `chargeAll` runs a sequence of guarded charges. If every charge costs at least
  1 gas, a successful run has at most `g` steps (`chargeAll_length_le`). This is the per-step
  argument behind "fuel ≥ gas limit suffices": `C'_pos_of_valid` shows every executable
  instruction other than STOP/RETURN/REVERT (which halt) costs at least 1. The hypothesis is
  necessary: `not_chargeAll_length_le_without_min_cost` refutes the bound for zero-cost steps.
  The whole-interpreter fuel-sufficiency theorem (induction over `X`/`Θ`/`Ξ`/`Λ` and nested calls)
  is `GasNested.Υ_ne_outOfFuel` / `Υ_transactionFuel_ne_outOfFuel` (K1).
-/

namespace EvmYul

namespace EVM

open GasMeter UInt256

/-! ## CE-9: zero fuel -/

/-- With fuel `0`, `Υ` fails with `OutOfFuel`, for every transaction. -/
theorem Υ_zero_fuel (σ : AccountMap .EVM) (H_f : ℕ) (H genesis : BlockHeader)
    (blocks : ProcessedBlocks) (T : Transaction) (S_T : AccountAddress) :
    Υ 0 σ H_f H genesis blocks T S_T = .error (.ExecutionException .OutOfFuel) := by
  unfold Υ
  rcases T.base.recipient with _ | t <;> simp [Θ, Lambda, bind, Except.bind]

/-- The fuel the conformance runner used before (the sender's balance). -/
def balanceFuel (senderBalance : UInt256) : ℕ := senderBalance.toNat

/-- **CE-9.** Under the old fuel choice, a sender with balance `0` (possible on a zero-fee chain,
where validation requires no balance) can never execute any transaction. -/
theorem balanceFuel_zero_fails (σ : AccountMap .EVM) (H_f : ℕ) (H genesis : BlockHeader)
    (blocks : ProcessedBlocks) (T : Transaction) (S_T : AccountAddress) :
    Υ (balanceFuel ⟨0⟩) σ H_f H genesis blocks T S_T = .error (.ExecutionException .OutOfFuel) :=
  Υ_zero_fuel σ H_f H genesis blocks T S_T

/-- The new fuel is never smaller than the old one. -/
theorem balanceFuel_le_transactionFuel (T : Transaction) (b : UInt256) :
    balanceFuel b ≤ transactionFuel T b := le_max_left _ _

/-- The new fuel always exceeds the gas limit, independently of the balance. -/
theorem gasLimit_lt_transactionFuel (T : Transaction) (b : UInt256) :
    T.base.gasLimit.toNat < transactionFuel T b := by
  unfold transactionFuel fuelOverhead
  exact lt_of_lt_of_le (by omega) (le_max_right _ _)

theorem transactionFuel_pos (T : Transaction) (b : UInt256) : 0 < transactionFuel T b :=
  lt_of_le_of_lt (Nat.zero_le _) (gasLimit_lt_transactionFuel T b)

/-! ## PO-10 at the meter level -/

/-- Charge a sequence of costs one after the other, failing at the first that does not fit. -/
@[expose] def chargeAll (g : UInt256) : List ℕ → Except ExecutionException UInt256
  | [] => .ok g
  | c :: cs =>
    match chargeGas g c with
    | .ok g' => chargeAll g' cs
    | .error e => .error e

/-- A sequence of guarded charges succeeds iff the total fits, and leaves exactly `g − Σ cs`. -/
theorem chargeAll_ok_iff (cs : List ℕ) :
    ∀ {g g' : UInt256},
      chargeAll g cs = .ok g' ↔ cs.sum ≤ g.toNat ∧ g'.toNat = g.toNat - cs.sum := by
  induction cs with
  | nil =>
    intro g g'
    simp only [chargeAll, Except.ok.injEq, List.sum_nil, Nat.zero_le, Nat.sub_zero, true_and]
    exact ⟨fun h => h ▸ rfl, fun h => UInt256.ext (Fin.ext h.symm)⟩
  | cons c cs ih =>
    intro g g'
    simp only [chargeAll, List.sum_cons]
    cases hc : chargeGas g c with
    | error e =>
      simp only [reduceCtorEq, false_iff]
      have : g.toNat < c := by
        unfold chargeGas at hc; split at hc
        · assumption
        · cases hc
      omega
    | ok g₁ =>
      obtain ⟨h1, h2⟩ := chargeGas_ok_iff.1 hc
      simp only
      rw [ih, h2]
      omega

/-- **PO-10 (meter level).** If every step costs at least one unit of gas, a successful run of
charges has at most as many steps as there was gas. -/
theorem chargeAll_length_le {g g' : UInt256} {cs : List ℕ} (hmin : ∀ c ∈ cs, 1 ≤ c)
    (h : chargeAll g cs = .ok g') : cs.length ≤ g.toNat := by
  have hsum := ((chargeAll_ok_iff cs).1 h).1
  have : cs.length ≤ cs.sum := by
    clear h hsum
    induction cs with
    | nil => simp
    | cons c cs ih =>
      simp only [List.length_cons, List.sum_cons]
      have := hmin c (by simp)
      have := ih (fun x hx => hmin x (by simp [hx]))
      omega
  omega

/-- The minimum-cost hypothesis of `chargeAll_length_le` is necessary: with zero-cost steps the
number of successful steps is unbounded by the gas. -/
theorem not_chargeAll_length_le_without_min_cost :
    ¬ ∀ (g g' : UInt256) (cs : List ℕ), chargeAll g cs = .ok g' → cs.length ≤ g.toNat := by
  intro h
  obtain ⟨g', hg'⟩ : ∃ g', chargeAll ⟨0⟩ [0] = .ok g' := ⟨_, rfl⟩
  exact absurd (h _ _ _ hg') (by decide)

end EVM

end EvmYul
