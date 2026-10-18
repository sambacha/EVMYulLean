module

public import EvmYul.EVM.Gas.Lemmas
public section

/-!
# Exhaustiveness of the per-operation cost function (issue S2)

`C'` ends in a `0` fallthrough, so a misclassified or newly added opcode would silently cost
nothing. This file proves that, for the current `Operation` ADT, the fallthrough is only reached
by the zero-cost group:

* `C'_eq_staticCost`: for every operation with a static fee group, `C'` equals the group's
  cost **in every state** (differential check of `C'` against `GasMeter.feeGroup`).
* `C'_pos`: every operation outside the `zero` and `invalid` groups has **strictly positive** cost
  in every state.
* `feeGroup_zero_iff` / `feeGroup_invalid_iff`: the `zero` group is exactly `W_zero`
  (STOP, RETURN, REVERT), and the `invalid` group is exactly the operations with `δ = none`.
* `C'_pos_of_valid`: **no valid instruction other than STOP/RETURN/REVERT is free.**
* `feeGroup_eq_base_iff`, `feeGroup_eq_verylow_iff`, …: the new total classification agrees with
  the YP group lists `W_base`, `W_verylow`, … that `C'` consults.

Since `GasMeter.feeGroup` has no wildcard, a new `Operation` constructor fails to compile until
it is classified. These proofs then re-check `C'` for it.
-/

namespace EvmYul

namespace EVM

open GasConstants GasMeter InstructionGasGroups

theorem Csstore_ge (s : EVM.State) : Gwarmaccess ≤ Csstore s := by
  unfold Csstore; simp only; split_ifs <;> simp [Gwarmaccess, Gsset, Gsreset]

theorem Csload_ge (μₛ : Stack UInt256) (A : Substate) (I : ExecutionEnv .EVM) :
    Gwarmaccess ≤ Csload μₛ A I := by
  unfold Csload; split <;> simp [Gwarmaccess, Gcoldsload]

theorem Cselfdestruct_ge (s : EVM.State) : Gselfdestruct ≤ Cselfdestruct s := by
  unfold Cselfdestruct; simp only; omega

/-- For an operation with a static fee group, `C'` equals that cost in every state. -/
theorem C'_eq_staticCost (s : EVM.State) (w : Operation .EVM) {c : ℕ}
    (h : (feeGroup w).staticCost? = some c) : C' s w = c := by
  rcases w with op|op|op|op|op|op|op|op|op|op|op <;> cases op <;>
    simp only [feeGroup, FeeGroup.staticCost?, Option.some.injEq, reduceCtorEq] at h <;>
    subst h <;> rfl

/-- Discharges `0 < C' s w` for one concrete dynamically-priced operation `w`. -/
syntax "dyn_cost_pos" : tactic

macro_rules
  | `(tactic| dyn_cost_pos) => `(tactic| (
      simp only [C']
      first
        | (rw [if_pos (by decide)]; simp only [Gverylow]; omega)
        | (rw [if_neg (by decide), if_pos (by decide)]
           exact lt_of_lt_of_le (by decide) (Caccess_ge ..))
        | (split <;> simp [Gexp]; done)
        | exact lt_of_lt_of_le (by decide) (Ccall_ge ..)
        | exact lt_of_lt_of_le (by decide) (Csstore_ge ..)
        | exact lt_of_lt_of_le (by decide) (Csload_ge ..)
        | exact lt_of_lt_of_le (by decide) (Cselfdestruct_ge ..)
        | exact lt_of_lt_of_le (by decide) (le_trans (Caccess_ge _ _) (Nat.le_add_right _ _))
        | (simp only [Glog, Gkeccak256, Gcreate]; omega)))

set_option hygiene false in
/-- One opcode case of `C'_pos`: discharged by the `zero`/`invalid` exclusions `h0`/`hi`, by the
static cost, or by `dyn_cost_pos`. (Non-hygienic so that it can refer to `h0` and `hi`.) -/
macro "cost_pos_case" : tactic => `(tactic| first
  | exact absurd rfl h0
  | exact absurd rfl hi
  | (rw [C'_eq_staticCost s _ rfl]; decide)
  | dyn_cost_pos)

/-! `C'_pos`, split by opcode family (one lemma per `Operation` constructor) so that each proof
stays within the default heartbeat budget and a failure names the family it occurs in. -/

/-- `C'_pos` for the STOP … SIGNEXTEND (arithmetic) family. -/
theorem C'_pos_stopArith (s : EVM.State) (op : Operation.SAOp .EVM)
    (h0 : feeGroup (.StopArith op) ≠ .zero) (hi : feeGroup (.StopArith op) ≠ .invalid) :
    0 < C' s (.StopArith op) := by
  cases op <;> cost_pos_case

/-- `C'_pos` for the LT … SAR (comparison and bitwise) family. -/
theorem C'_pos_compBit (s : EVM.State) (op : Operation.CBLOp .EVM)
    (h0 : feeGroup (.CompBit op) ≠ .zero) (hi : feeGroup (.CompBit op) ≠ .invalid) :
    0 < C' s (.CompBit op) := by
  cases op <;> cost_pos_case

/-- `C'_pos` for the KECCAK256 family. -/
theorem C'_pos_keccak (s : EVM.State) (op : Operation.KOp .EVM)
    (h0 : feeGroup (.Keccak op) ≠ .zero) (hi : feeGroup (.Keccak op) ≠ .invalid) :
    0 < C' s (.Keccak op) := by
  cases op; cost_pos_case

/-- `C'_pos` for the ADDRESS … EXTCODEHASH (environment) family. -/
theorem C'_pos_env (s : EVM.State) (op : Operation.EOp .EVM)
    (h0 : feeGroup (.Env op) ≠ .zero) (hi : feeGroup (.Env op) ≠ .invalid) :
    0 < C' s (.Env op) := by
  cases op <;> cost_pos_case

/-- `C'_pos` for the BLOCKHASH … BLOBBASEFEE (block information) family. -/
theorem C'_pos_block (s : EVM.State) (op : Operation.BOp .EVM)
    (h0 : feeGroup (.Block op) ≠ .zero) (hi : feeGroup (.Block op) ≠ .invalid) :
    0 < C' s (.Block op) := by
  cases op <;> cost_pos_case

/-- `C'_pos` for the POP … MCOPY (stack, memory, storage, flow) family. -/
theorem C'_pos_stackMemFlow (s : EVM.State) (op : Operation.SMSFOp .EVM)
    (h0 : feeGroup (.StackMemFlow op) ≠ .zero) (hi : feeGroup (.StackMemFlow op) ≠ .invalid) :
    0 < C' s (.StackMemFlow op) := by
  cases op <;> cost_pos_case

/-- `C'_pos` for the PUSH0 … PUSH32 family. -/
theorem C'_pos_push (s : EVM.State) (op : Operation.POp)
    (h0 : feeGroup (.Push op) ≠ .zero) (hi : feeGroup (.Push op) ≠ .invalid) :
    0 < C' s (.Push op) := by
  cases op <;> cost_pos_case

/-- `C'_pos` for the DUP1 … DUP16 family. -/
theorem C'_pos_dup (s : EVM.State) (op : Operation.DOp)
    (h0 : feeGroup (.Dup op) ≠ .zero) (hi : feeGroup (.Dup op) ≠ .invalid) :
    0 < C' s (.Dup op) := by
  cases op <;> cost_pos_case

/-- `C'_pos` for the SWAP1 … SWAP16 family. -/
theorem C'_pos_exchange (s : EVM.State) (op : Operation.ExOp)
    (h0 : feeGroup (.Exchange op) ≠ .zero) (hi : feeGroup (.Exchange op) ≠ .invalid) :
    0 < C' s (.Exchange op) := by
  cases op <;> cost_pos_case

/-- `C'_pos` for the LOG0 … LOG4 family. -/
theorem C'_pos_log (s : EVM.State) (op : Operation.LOp .EVM)
    (h0 : feeGroup (.Log op) ≠ .zero) (hi : feeGroup (.Log op) ≠ .invalid) :
    0 < C' s (.Log op) := by
  cases op <;> cost_pos_case

/-- `C'_pos` for the CREATE … SELFDESTRUCT (system operations) family. -/
theorem C'_pos_system (s : EVM.State) (op : Operation.SOp .EVM)
    (h0 : feeGroup (.System op) ≠ .zero) (hi : feeGroup (.System op) ≠ .invalid) :
    0 < C' s (.System op) := by
  cases op <;> cost_pos_case

/-- Every operation outside the `zero` and `invalid` groups has strictly positive cost. -/
theorem C'_pos (s : EVM.State) (w : Operation .EVM)
    (h0 : feeGroup w ≠ .zero) (hi : feeGroup w ≠ .invalid) : 0 < C' s w := by
  cases w with
  | StopArith op => exact C'_pos_stopArith s op h0 hi
  | CompBit op => exact C'_pos_compBit s op h0 hi
  | Keccak op => exact C'_pos_keccak s op h0 hi
  | Env op => exact C'_pos_env s op h0 hi
  | Block op => exact C'_pos_block s op h0 hi
  | StackMemFlow op => exact C'_pos_stackMemFlow s op h0 hi
  | Push op => exact C'_pos_push s op h0 hi
  | Dup op => exact C'_pos_dup s op h0 hi
  | Exchange op => exact C'_pos_exchange s op h0 hi
  | Log op => exact C'_pos_log s op h0 hi
  | System op => exact C'_pos_system s op h0 hi

theorem feeGroup_zero_iff (w : Operation .EVM) : feeGroup w = .zero ↔ w ∈ Wzero := by
  rcases w with op|op|op|op|op|op|op|op|op|op|op <;> cases op <;> decide

theorem feeGroup_invalid_iff (w : Operation .EVM) : feeGroup w = .invalid ↔ δ w = none := by
  rcases w with op|op|op|op|op|op|op|op|op|op|op <;> cases op <;> decide

/-- **No free instructions**: every valid opcode except STOP, RETURN and REVERT costs gas. -/
theorem C'_pos_of_valid (s : EVM.State) (w : Operation .EVM) (hδ : δ w ≠ none) (hz : w ∉ Wzero) :
    0 < C' s w :=
  C'_pos s w (fun h => hz ((feeGroup_zero_iff w).1 h)) (fun h => hδ ((feeGroup_invalid_iff w).1 h))

/-- STOP, RETURN and REVERT are exactly the zero-cost instructions. -/
theorem C'_eq_zero_of_mem_Wzero (s : EVM.State) (w : Operation .EVM) (hz : w ∈ Wzero) :
    C' s w = 0 :=
  C'_eq_staticCost s w (by rw [(feeGroup_zero_iff w).2 hz]; rfl)

/-! The total classification agrees with the YP fee-group lists that `C'` consults. -/

theorem feeGroup_eq_base_iff (w : Operation .EVM) : feeGroup w = .base ↔ w ∈ Wbase := by
  rcases w with op|op|op|op|op|op|op|op|op|op|op <;> cases op <;> decide

theorem feeGroup_eq_verylow_iff (w : Operation .EVM) : feeGroup w = .verylow ↔ w ∈ Wverylow := by
  rcases w with op|op|op|op|op|op|op|op|op|op|op <;> cases op <;> decide

theorem feeGroup_eq_low_iff (w : Operation .EVM) : feeGroup w = .low ↔ w ∈ Wlow := by
  rcases w with op|op|op|op|op|op|op|op|op|op|op <;> cases op <;> decide

theorem feeGroup_eq_mid_iff (w : Operation .EVM) : feeGroup w = .mid ↔ w ∈ Wmid := by
  rcases w with op|op|op|op|op|op|op|op|op|op|op <;> cases op <;> decide

theorem feeGroup_eq_high_iff (w : Operation .EVM) : feeGroup w = .high ↔ w ∈ Whigh := by
  rcases w with op|op|op|op|op|op|op|op|op|op|op <;> cases op <;> decide

theorem feeGroup_eq_copy_iff (w : Operation .EVM) : feeGroup w = .copy ↔ w ∈ Wcopy := by
  rcases w with op|op|op|op|op|op|op|op|op|op|op <;> cases op <;> decide

theorem feeGroup_eq_extAccount_iff (w : Operation .EVM) :
    feeGroup w = .extAccount ↔ w ∈ Wextaccount := by
  rcases w with op|op|op|op|op|op|op|op|op|op|op <;> cases op <;> decide

theorem feeGroup_eq_call_iff (w : Operation .EVM) : feeGroup w = .call ↔ w ∈ Wcall := by
  rcases w with op|op|op|op|op|op|op|op|op|op|op <;> cases op <;> decide

end EVM

end EvmYul
