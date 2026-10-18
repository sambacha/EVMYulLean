module

public import EvmYul.Semantics
public import EvmYul.ProofTags

/-!
# `SELFDESTRUCT`: one world-state effect for the EVM and Yul (EIP-6780)

Both cases of `EvmYul.step` for `SELFDESTRUCT` apply the same function, `State.selfDestruct`
(`EvmYul/State/BasicOps.lean`). Before, the Yul case had its own copy, which always put the code
owner in the self-destruct set and always burnt Ether sent to itself (the pre-Cancun rule), and it
kept executing afterwards.

* `step_EVM_SELFDESTRUCT`, `step_Yul_SELFDESTRUCT`: what each case of `EvmYul.step` computes. The
  EVM case writes back the account map and substate of `State.selfDestruct`; the Yul case writes
  back the whole world state of `State.selfDestruct` and **halts** (`YulHalt`), like `STOP`.
  Because `State.selfDestruct` is generic in the machine type `τ`, the two machines cannot apply
  different rules; `EvmYul/SelfDestructTests.lean` runs both on the same world state.
* The EIP-6780 rule itself, for both machines at once (the lemmas are generic in `τ`):
  `selfDestruct_selfDestructSet_of_not_created` (an account not created in this transaction is
  never scheduled for deletion), `selfDestruct_codeOwner_mem_of_created` (one created in it is),
  `selfDestruct_self_of_not_created` (sending to itself changes no balance),
  `selfDestruct_beneficiary_accessed` (the beneficiary becomes warm, EIP-2929) and
  `selfDestruct_preserves_createdAccounts`.

Executable checks, property tests and mutants of the old Yul behaviour are in
`EvmYul/SelfDestructTests.lean`.
-/

public section

namespace EvmYul

namespace State

variable {τ : OperationType}

/-- **EIP-6780.** If the code owner was not created in this transaction, `SELFDESTRUCT` leaves the
self-destruct set unchanged: the account is not deleted. -/
theorem selfDestruct_selfDestructSet_of_not_created (σ : State τ) (r : AccountAddress)
    (h : σ.createdAccounts.contains σ.executionEnv.codeOwner = false) :
    (σ.selfDestruct r).substate.selfDestructSet = σ.substate.selfDestructSet := by
  simp [selfDestruct, h]

/-- **EIP-6780.** If the code owner was created in this transaction, `SELFDESTRUCT` puts it in the
self-destruct set, so it is deleted at the end of the transaction. -/
theorem selfDestruct_codeOwner_mem_of_created (σ : State τ) (r : AccountAddress)
    (h : σ.createdAccounts.contains σ.executionEnv.codeOwner = true) :
    (σ.selfDestruct r).substate.selfDestructSet.contains σ.executionEnv.codeOwner = true := by
  simp [selfDestruct, h]

/-- **EIP-6780.** A contract that was not created in this transaction and names itself as the
beneficiary changes no balance: its Ether is not burnt. -/
theorem selfDestruct_self_of_not_created (σ : State τ)
    (h : σ.createdAccounts.contains σ.executionEnv.codeOwner = false) :
    (σ.selfDestruct σ.executionEnv.codeOwner).accountMap = σ.accountMap := by
  unfold selfDestruct
  cases hI : σ.lookupAccount σ.executionEnv.codeOwner <;> simp [h, hI]

/-- The beneficiary of `SELFDESTRUCT` becomes an accessed (warm) account (EIP-2929). -/
theorem selfDestruct_beneficiary_accessed (σ : State τ) (r : AccountAddress) :
    (σ.selfDestruct r).substate.accessedAccounts.contains r = true := by
  simp [selfDestruct]

/-- `SELFDESTRUCT` does not change which accounts count as created in this transaction. -/
@[reviewed_rfl "SELFDESTRUCT touches only the account map and substate, by definition"]
theorem selfDestruct_preserves_createdAccounts (σ : State τ) (r : AccountAddress) :
    (σ.selfDestruct r).createdAccounts = σ.createdAccounts := rfl

end State

/-- The EVM case of `SELFDESTRUCT`: pop the beneficiary and apply `State.selfDestruct`. -/
theorem step_EVM_SELFDESTRUCT (arg : Option (UInt256 × ℕ)) (s : EVM.State) (μ₁ : UInt256)
    (rest : Stack UInt256) (hs : s.stack = μ₁ :: rest) :
    EvmYul.step (τ := .EVM) .SELFDESTRUCT arg s =
      .ok ({s with
        accountMap := (s.toState.selfDestruct (AccountAddress.ofUInt256 μ₁)).accountMap
        substate := (s.toState.selfDestruct (AccountAddress.ofUInt256 μ₁)).substate
      }.replaceStackAndIncrPC rest) := by
  unfold EvmYul.step
  simp only [Id.run]
  rw [hs]
  rfl

/-- The Yul case of `SELFDESTRUCT`: apply `State.selfDestruct` to the world state and halt. -/
@[reviewed_rfl "API: the Yul SELFDESTRUCT case halts with the shared world-state effect"]
theorem step_Yul_SELFDESTRUCT (arg : Option (UInt256 × ℕ)) (y : Yul.State) (a : UInt256) :
    EvmYul.step (τ := .Yul) .SELFDESTRUCT arg y [a] =
      .error (Yul.Exception.YulHalt
        (y.setState (y.toState.selfDestruct (AccountAddress.ofUInt256 a))) ⟨0⟩) := rfl

end EvmYul
