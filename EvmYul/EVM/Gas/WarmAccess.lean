module

public import EvmYul.EVM.Gas.Lemmas
public import EvmYul.State.SubstateLemmas
public import EvmYul.ProofTags
public section

/-!
# Warm access costs (handoff WP-5 pilot)

Proved through the substate interface of `EvmYul/State/SubstateLemmas.lean` only (no tree-set
internals in the proofs):

* after a slot has been warmed (as `SLOAD`/`SSTORE` do), `Csload` costs `G_warmaccess`;
* after an account has been warmed, `Caccess` costs `G_warmaccess`;
* `Csload_default_cold`: the warm-up is load-bearing; in the empty substate the same access costs
  `G_coldsload`.

EIP-2200 storage-tracking facts (CE-10) are out of scope.
-/

namespace EvmYul

namespace EVM

open GasConstants Substate

/-- **WP-5 pilot.** Once the slot has been warmed (e.g. by an earlier `SSTORE`/`SLOAD` of the same
slot), `SLOAD` costs `G_warmaccess = 100`. Proved only from the substate interface above. -/
theorem Csload_after_warm (μₛ : Stack UInt256) (A : Substate) (I : ExecutionEnv .EVM) :
    Csload μₛ (A.warmSlot (I.codeOwner, μₛ[0]!)) I = Gwarmaccess := by
  unfold Csload; rw [if_pos (warmSlot_contains _ _)]

/-- Warming is monotone: a warm slot stays warm when other slots are warmed. -/
theorem Csload_warm_stays_warm (μₛ : Stack UInt256) (A : Substate) (I : ExecutionEnv .EVM)
    (k : AccountAddress × UInt256)
    (h : A.accessedStorageKeys.contains (I.codeOwner, μₛ[0]!) = true) :
    Csload μₛ (A.warmSlot k) I = Gwarmaccess := by
  unfold Csload; rw [if_pos (warmSlot_contains_of_contains _ h)]

/-- After an account has been warmed, accessing it costs `G_warmaccess`. -/
theorem Caccess_after_warm (a : AccountAddress) (A : Substate) :
    Caccess a (A.warmAccount a) = Gwarmaccess := by
  unfold Caccess; rw [if_pos (warmAccount_contains _ _)]

/-- The warm-up is load-bearing: in the default (empty) substate the same `SLOAD` is cold. -/
@[reviewed_pin EvmYul.EVM.Csload_after_warm]
theorem Csload_default_cold (μₛ : Stack UInt256) (I : ExecutionEnv .EVM) :
    Csload μₛ default I = Gcoldsload := rfl

end EVM

end EvmYul
