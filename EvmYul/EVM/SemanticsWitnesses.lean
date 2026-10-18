module

public import EvmYul.EVM.Semantics
public import EvmYul.ProofTags

@[expose] public section

/-!
# Regression proofs for review findings O-1, O-2 and O-4 (`docs/REVIEW.md`, `docs/FALSIFICATION_AUDIT.md`)

This file used to hold *characterization* theorems of two interpreter bugs:

* `Θ_precompile_resets_createdAccounts` — a precompile call returned `∅` as the set of accounts
  created in the transaction (EIP-6780), whatever set went in;
* `create_outOfFuel_wipes` — running out of fuel inside CREATE made `step` *succeed* with an
  empty world state (it also needed a hypothesis `hpad` that was unprovable because padding used the
  opaque FFI primitive `ffi.ByteArray.zeroes`).

Both bugs are fixed in `EvmYul/EVM/Semantics.lean`, and padding now uses the pure-Lean
`ByteArray.zeroesPure`. The old statements are false about the current code; rather than deleting
them silently, this file proves their **negations** (`not_Θ_precompile_resets_createdAccounts`,
`not_create_outOfFuel_wipes`) together with the positive statements of the corrected behaviour.
Reintroducing either bug makes this file fail to build.
-/

namespace EvmYul.EVM.SemanticsWitnesses

open Batteries

/-! ## O-4: padding is now pure Lean, so its size is provable -/

/-- Reading zero bytes of memory gives zero bytes. This was the unprovable hypothesis `hpad` of the
old `create_outOfFuel_wipes`; it is a theorem now that padding is built by `ByteArray.zeroesPure`. -/
theorem readWithPadding_zero_size (m : ByteArray) (a : ℕ) :
    (m.readWithPadding a 0).size = 0 := by
  have hr : (m.readWithoutPadding a 0).size = 0 := by
    simp only [ByteArray.readWithoutPadding]
    split
    · rfl
    · simp
  rw [ByteArray.readWithPadding, if_neg (by norm_num), ByteArray.size_append, hr]
  simp only [ByteArray.zeroesUSize, ByteArray.zeroesPure, ByteArray.size, Array.size_replicate]
  simp

/-! ## O-1: a precompile call preserves the created-accounts set -/

/-- `Θ` on any precompiled callee returns the created-accounts set it was given (the precompile
itself runs in `precompileDispatch`, which never touches the set). -/
private theorem Θ_precompiled_cA
    (fuel : ℕ) (bvh : List ByteArray) (cA : Std.TreeSet AccountAddress compare)
    (gbh : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap .EVM) (A : Substate)
    (s o r pc : AccountAddress) (g p v v' : UInt256) (d : ByteArray) (e : ℕ) (H : BlockHeader)
    (w : Bool) (res)
    (h : Θ (fuel + 1) bvh cA gbh blocks σ σ₀ A s o r (.Precompiled pc) g p v v' d e H w
      = .ok res) :
    res.createdAccounts = cA := by
  simp only [Θ, bind, Except.bind, Except.ok.injEq] at h
  rw [← h]

/-- The precompile dispatcher never reports `REVERT`. -/
private theorem precompileDispatch_ne_revert (pc : AccountAddress) (σ₁ : AccountMap .EVM)
    (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM) :
    (precompileDispatch pc σ₁ g A I).1 ≠ .revert := by
  unfold precompileDispatch
  split
  all_goals first
    | exact FrameOutcome.ofSuccessFlag_ne_revert _
    | exact nofun

private theorem Θ_precompiled_ne_revert
    (fuel : ℕ) (bvh : List ByteArray) (cA : Std.TreeSet AccountAddress compare)
    (gbh : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap .EVM) (A : Substate)
    (s o r pc : AccountAddress) (g p v v' : UInt256) (d : ByteArray) (e : ℕ) (H : BlockHeader)
    (w : Bool) (res : FrameResult)
    (h : Θ (fuel + 1) bvh cA gbh blocks σ σ₀ A s o r (.Precompiled pc) g p v v' d e H w
      = .ok res) :
    res.outcome ≠ .revert := by
  simp only [Θ, bind, Except.bind, Except.ok.injEq] at h
  rw [← h]
  exact precompileDispatch_ne_revert _ _ _ _ _

private theorem Θ_precompile_1_cA
    (fuel : ℕ) (bvh : List ByteArray) (cA : Std.TreeSet AccountAddress compare)
    (gbh : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap .EVM) (A : Substate)
    (s o r : AccountAddress) (g p v v' : UInt256) (d : ByteArray) (e : ℕ) (H : BlockHeader)
    (w : Bool) (res)
    (h : Θ (fuel + 1) bvh cA gbh blocks σ σ₀ A s o r (.Precompiled 1) g p v v' d e H w
      = .ok res) :
    res.createdAccounts = cA := by
  exact Θ_precompiled_cA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h

private theorem Θ_precompile_2_cA
    (fuel : ℕ) (bvh : List ByteArray) (cA : Std.TreeSet AccountAddress compare)
    (gbh : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap .EVM) (A : Substate)
    (s o r : AccountAddress) (g p v v' : UInt256) (d : ByteArray) (e : ℕ) (H : BlockHeader)
    (w : Bool) (res)
    (h : Θ (fuel + 1) bvh cA gbh blocks σ σ₀ A s o r (.Precompiled 2) g p v v' d e H w
      = .ok res) :
    res.createdAccounts = cA := by
  exact Θ_precompiled_cA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h

private theorem Θ_precompile_3_cA
    (fuel : ℕ) (bvh : List ByteArray) (cA : Std.TreeSet AccountAddress compare)
    (gbh : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap .EVM) (A : Substate)
    (s o r : AccountAddress) (g p v v' : UInt256) (d : ByteArray) (e : ℕ) (H : BlockHeader)
    (w : Bool) (res)
    (h : Θ (fuel + 1) bvh cA gbh blocks σ σ₀ A s o r (.Precompiled 3) g p v v' d e H w
      = .ok res) :
    res.createdAccounts = cA := by
  exact Θ_precompiled_cA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h

private theorem Θ_precompile_4_cA
    (fuel : ℕ) (bvh : List ByteArray) (cA : Std.TreeSet AccountAddress compare)
    (gbh : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap .EVM) (A : Substate)
    (s o r : AccountAddress) (g p v v' : UInt256) (d : ByteArray) (e : ℕ) (H : BlockHeader)
    (w : Bool) (res)
    (h : Θ (fuel + 1) bvh cA gbh blocks σ σ₀ A s o r (.Precompiled 4) g p v v' d e H w
      = .ok res) :
    res.createdAccounts = cA := by
  exact Θ_precompiled_cA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h

private theorem Θ_precompile_5_cA
    (fuel : ℕ) (bvh : List ByteArray) (cA : Std.TreeSet AccountAddress compare)
    (gbh : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap .EVM) (A : Substate)
    (s o r : AccountAddress) (g p v v' : UInt256) (d : ByteArray) (e : ℕ) (H : BlockHeader)
    (w : Bool) (res)
    (h : Θ (fuel + 1) bvh cA gbh blocks σ σ₀ A s o r (.Precompiled 5) g p v v' d e H w
      = .ok res) :
    res.createdAccounts = cA := by
  exact Θ_precompiled_cA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h

private theorem Θ_precompile_6_cA
    (fuel : ℕ) (bvh : List ByteArray) (cA : Std.TreeSet AccountAddress compare)
    (gbh : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap .EVM) (A : Substate)
    (s o r : AccountAddress) (g p v v' : UInt256) (d : ByteArray) (e : ℕ) (H : BlockHeader)
    (w : Bool) (res)
    (h : Θ (fuel + 1) bvh cA gbh blocks σ σ₀ A s o r (.Precompiled 6) g p v v' d e H w
      = .ok res) :
    res.createdAccounts = cA := by
  exact Θ_precompiled_cA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h

private theorem Θ_precompile_7_cA
    (fuel : ℕ) (bvh : List ByteArray) (cA : Std.TreeSet AccountAddress compare)
    (gbh : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap .EVM) (A : Substate)
    (s o r : AccountAddress) (g p v v' : UInt256) (d : ByteArray) (e : ℕ) (H : BlockHeader)
    (w : Bool) (res)
    (h : Θ (fuel + 1) bvh cA gbh blocks σ σ₀ A s o r (.Precompiled 7) g p v v' d e H w
      = .ok res) :
    res.createdAccounts = cA := by
  exact Θ_precompiled_cA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h

private theorem Θ_precompile_8_cA
    (fuel : ℕ) (bvh : List ByteArray) (cA : Std.TreeSet AccountAddress compare)
    (gbh : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap .EVM) (A : Substate)
    (s o r : AccountAddress) (g p v v' : UInt256) (d : ByteArray) (e : ℕ) (H : BlockHeader)
    (w : Bool) (res)
    (h : Θ (fuel + 1) bvh cA gbh blocks σ σ₀ A s o r (.Precompiled 8) g p v v' d e H w
      = .ok res) :
    res.createdAccounts = cA := by
  exact Θ_precompiled_cA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h

private theorem Θ_precompile_9_cA
    (fuel : ℕ) (bvh : List ByteArray) (cA : Std.TreeSet AccountAddress compare)
    (gbh : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap .EVM) (A : Substate)
    (s o r : AccountAddress) (g p v v' : UInt256) (d : ByteArray) (e : ℕ) (H : BlockHeader)
    (w : Bool) (res)
    (h : Θ (fuel + 1) bvh cA gbh blocks σ σ₀ A s o r (.Precompiled 9) g p v v' d e H w
      = .ok res) :
    res.createdAccounts = cA := by
  exact Θ_precompiled_cA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h

private theorem Θ_precompile_10_cA
    (fuel : ℕ) (bvh : List ByteArray) (cA : Std.TreeSet AccountAddress compare)
    (gbh : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap .EVM) (A : Substate)
    (s o r : AccountAddress) (g p v v' : UInt256) (d : ByteArray) (e : ℕ) (H : BlockHeader)
    (w : Bool) (res)
    (h : Θ (fuel + 1) bvh cA gbh blocks σ σ₀ A s o r (.Precompiled 10) g p v v' d e H w
      = .ok res) :
    res.createdAccounts = cA := by
  exact Θ_precompiled_cA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h

/-- The ten precompile addresses `π = {1, …, 10}` (Yellow Paper (142)), as a list. -/
def precompileAddresses : List AccountAddress := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]

/-- **Corrected behaviour (O-1).** A successful message call to *any* precompile returns exactly the
set of created accounts it was given. `call` stores this set back into the caller's state, so the
transaction's EIP-6780 bookkeeping survives precompile calls. -/
theorem Θ_precompile_preserves_createdAccounts
    (fuel : ℕ) (bvh : List ByteArray) (cA : Std.TreeSet AccountAddress compare)
    (gbh : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap .EVM) (A : Substate)
    (s o r pc : AccountAddress) (g p v v' : UInt256) (d : ByteArray) (e : ℕ) (H : BlockHeader)
    (w : Bool) (res) (hpc : pc ∈ precompileAddresses)
    (h : Θ (fuel + 1) bvh cA gbh blocks σ σ₀ A s o r (.Precompiled pc) g p v v' d e H w
      = .ok res) :
    res.createdAccounts = cA := by
  simp only [precompileAddresses, List.mem_cons, List.not_mem_nil, or_false] at hpc
  rcases hpc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Θ_precompile_1_cA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h,
    Θ_precompile_2_cA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h,
    Θ_precompile_3_cA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h,
    Θ_precompile_4_cA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h,
    Θ_precompile_5_cA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h,
    Θ_precompile_6_cA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h,
    Θ_precompile_7_cA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h,
    Θ_precompile_8_cA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h,
    Θ_precompile_9_cA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h,
    Θ_precompile_10_cA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h]

/-- **Corrected behaviour (O-1), at the opcode level.** When the callee of `call` (used by CALL,
CALLCODE, DELEGATECALL and STATICCALL) is a precompile, the caller's created-accounts set after the
call equals the set before it — whether the call goes ahead or is refused (insufficient balance or
depth limit). `call` itself just stores whatever set `Θ` returns; the fix lives in `Θ`, whose
precompile branches had violated `Θ`'s own contract (return the post-call set). -/
theorem call_precompile_preserves_createdAccounts (fuel gasCost : ℕ) (bvh : List ByteArray)
    (gas source recipient t value value' inOffset inSize outOffset outSize : UInt256)
    (permission : Bool) (evmState : State) (x : UInt256) (s' : State) (pc : AccountAddress)
    (hpc : pc ∈ precompileAddresses)
    (hc : toExecute .EVM evmState.accountMap (AccountAddress.ofUInt256 t) = .Precompiled pc)
    (h : call (fuel + 2) gasCost bvh gas source recipient t value value' inOffset inSize outOffset
      outSize permission evmState = .ok (x, s')) :
    s'.createdAccounts = evmState.createdAccounts := by
  simp only [call, hc, bind, Except.bind, pure, Except.pure] at h
  split at h
  · split at h
    · cases h
    · rename_i v hΘ
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact Θ_precompile_preserves_createdAccounts _ _ _ _ _ _ _ _ _ _ _ pc _ _ _ _ _ _ _ _ _ hpc hΘ
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    rfl

/-- A call to the identity precompile (address 4) always succeeds, so
`Θ_precompile_preserves_createdAccounts` is not vacuous. -/
theorem Θ_precompile_ok
    (fuel : ℕ) (bvh : List ByteArray) (cA : Std.TreeSet AccountAddress compare)
    (gbh : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap .EVM) (A : Substate)
    (s o r : AccountAddress) (g p v v' : UInt256) (d : ByteArray) (e : ℕ) (H : BlockHeader)
    (w : Bool) :
    ∃ res, Θ (fuel + 1) bvh cA gbh blocks σ σ₀ A s o r (.Precompiled 4) g p v v' d e H w
      = .ok res := by
  simp only [Θ]
  split <;> simp_all [bind, Except.bind]

/-- A one-element created-accounts set (address `0x77`). -/
def oneCreated : Std.TreeSet AccountAddress compare := Std.TreeSet.ofList [Fin.ofNat _ 0x77] compare

theorem oneCreated_ne_empty : oneCreated ≠ ∅ := by
  intro h
  have : oneCreated.toList = (∅ : Std.TreeSet AccountAddress compare).toList := by rw [h]
  revert this
  decide

/-- **Negation of the old characterization theorem.** The pre-fix statement
"every successful precompile call returns `∅` as the created-accounts set" is false about the
current interpreter. -/
theorem not_Θ_precompile_resets_createdAccounts :
    ¬ ∀ (fuel : ℕ) (bvh : List ByteArray) (cA : Std.TreeSet AccountAddress compare)
      (gbh : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap .EVM) (A : Substate)
      (s o r : AccountAddress) (g p v v' : UInt256) (d : ByteArray) (e : ℕ) (H : BlockHeader)
      (w : Bool) (res),
      Θ (fuel + 1) bvh cA gbh blocks σ σ₀ A s o r (.Precompiled 4) g p v v' d e H w = .ok res →
      res.createdAccounts = ∅ := by
  intro hall
  obtain ⟨res, hres⟩ := Θ_precompile_ok 0 [] oneCreated default default ∅ ∅ default 1 1 4
    ⟨0⟩ ⟨0⟩ ⟨0⟩ ⟨0⟩ .empty 0 default true
  have h1 := Θ_precompile_4_cA _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hres
  have h2 := hall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hres
  exact oneCreated_ne_empty (h1.symm.trans h2)

/-! ## O-2: running out of fuel inside CREATE/CREATE2 is reported, not turned into `σ = ∅` -/

/-- **Corrected behaviour (O-2), CREATE.** Whenever CREATE gets as far as calling `Lambda`
(enough balance for the endowment, depth below 1024, init code at most 49152 bytes, nonce not
saturated), and there is no fuel left for `Lambda`, `step` fails with `OutOfFuel`. Before the fix it
*succeeded* with an empty account map. -/
theorem create_outOfFuel_propagates (gasCost : ℕ) (s : State)
    (μ₀ μ₁ μ₂ : UInt256) (rest : Stack UInt256)
    (hstack : s.stack = μ₀ :: μ₁ :: μ₂ :: rest)
    (hbal : μ₀ ≤ (s.accountMap.get? s.executionEnv.codeOwner).option ⟨0⟩ (·.balance))
    (hpad : (s.memory.readWithPadding μ₁.toNat μ₂.toNat).size ≤ 49152)
    (hdepth : s.executionEnv.depth < 1024)
    (hnonce : ((s.accountMap.get? s.executionEnv.codeOwner).getD default).nonce.toNat < 2^64-1) :
    step 1 gasCost (some (.CREATE, none)) s = .error .OutOfFuel := by
  have hn :
      ¬ (((s.accountMap.get? s.executionEnv.codeOwner).getD default).nonce.toNat ≥ 2^64-1) := by
    omega
  simp only [step, hstack, Stack.pop3, Lambda, bind, Except.bind, pure, Except.pure]
  simp only [hn, hbal, hpad, hdepth, if_false, and_self, if_true]

/-- **Corrected behaviour (O-2), CREATE2.** Same statement for CREATE2. -/
theorem create2_outOfFuel_propagates (gasCost : ℕ) (s : State)
    (μ₀ μ₁ μ₂ μ₃ : UInt256) (rest : Stack UInt256)
    (hstack : s.stack = μ₀ :: μ₁ :: μ₂ :: μ₃ :: rest)
    (hbal : μ₀ ≤ (s.accountMap.get? s.executionEnv.codeOwner).option ⟨0⟩ (·.balance))
    (hpad : (s.memory.readWithPadding μ₁.toNat μ₂.toNat).size ≤ 49152)
    (hdepth : s.executionEnv.depth < 1024)
    (hnonce : ((s.accountMap.get? s.executionEnv.codeOwner).getD default).nonce.toNat < 2^64-1) :
    step 1 gasCost (some (.CREATE2, none)) s = .error .OutOfFuel := by
  have hn :
      ¬ (((s.accountMap.get? s.executionEnv.codeOwner).getD default).nonce.toNat ≥ 2^64-1) := by
    omega
  simp only [step, hstack, Stack.pop4, Lambda, bind, Except.bind, pure, Except.pure]
  simp only [hn, hbal, hpad, hdepth, if_false, and_self, if_true]

/-- The hypotheses of `create_outOfFuel_propagates` are satisfiable for every state whose stack is
`[0, 0, 0]` (the hypothesis `hpad` is now discharged by `readWithPadding_zero_size`). -/
theorem create_outOfFuel_zeroStack (gasCost : ℕ) (s : State)
    (hstack : s.stack = [⟨0⟩, ⟨0⟩, ⟨0⟩])
    (hdepth : s.executionEnv.depth < 1024)
    (hnonce : ((s.accountMap.get? s.executionEnv.codeOwner).getD default).nonce.toNat < 2^64-1) :
    step 1 gasCost (some (.CREATE, none)) s = .error .OutOfFuel := by
  refine create_outOfFuel_propagates gasCost s ⟨0⟩ ⟨0⟩ ⟨0⟩ [] hstack ?_ ?_ hdepth hnonce
  · show (0 : ℕ) ≤ _; exact Nat.zero_le _
  · change (s.memory.readWithPadding 0 0).size ≤ 49152
    rw [readWithPadding_zero_size]; omega

/-- **Negation of the old characterization theorem** `create_outOfFuel_wipes` (stated here without
its formerly unprovable hypothesis `hpad`, which is now a theorem): no CREATE that runs out of fuel
succeeds, let alone with an empty account map. -/
theorem not_create_outOfFuel_wipes (gasCost : ℕ) (s : State)
    (hstack : s.stack = [⟨0⟩, ⟨0⟩, ⟨0⟩])
    (hdepth : s.executionEnv.depth < 1024)
    (hnonce : ((s.accountMap.get? s.executionEnv.codeOwner).getD default).nonce.toNat < 2^64-1) :
    ¬ ∃ s', step 1 gasCost (some (.CREATE, none)) s = .ok s' ∧ s'.accountMap = ∅ := by
  rintro ⟨s', h, -⟩
  rw [create_outOfFuel_zeroStack gasCost s hstack hdepth hnonce] at h
  cases h


/-! ## O-3: named frame results (`FrameOutcome`, `FrameResult`, `CreateResult`)

`Θ` and `Lambda` now return records whose `outcome` field distinguishes success, `REVERT` and
exceptional halt (`EvmYul/EVM/FrameOutcome.lean`). The O-1/O-2 theorems above were re-proved
against the new result types (`res.createdAccounts` instead of the tuple projection `res.1`). The
theorems below state properties that the old `Bool` could not express. -/

private theorem Θ_precompile_1_ne_revert
    (fuel : ℕ) (bvh : List ByteArray) (cA : Std.TreeSet AccountAddress compare)
    (gbh : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap .EVM) (A : Substate)
    (s o r : AccountAddress) (g p v v' : UInt256) (d : ByteArray) (e : ℕ) (H : BlockHeader)
    (w : Bool) (res : FrameResult)
    (h : Θ (fuel + 1) bvh cA gbh blocks σ σ₀ A s o r (.Precompiled 1) g p v v' d e H w
      = .ok res) :
    res.outcome ≠ .revert := by
  exact Θ_precompiled_ne_revert _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h

private theorem Θ_precompile_2_ne_revert
    (fuel : ℕ) (bvh : List ByteArray) (cA : Std.TreeSet AccountAddress compare)
    (gbh : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap .EVM) (A : Substate)
    (s o r : AccountAddress) (g p v v' : UInt256) (d : ByteArray) (e : ℕ) (H : BlockHeader)
    (w : Bool) (res : FrameResult)
    (h : Θ (fuel + 1) bvh cA gbh blocks σ σ₀ A s o r (.Precompiled 2) g p v v' d e H w
      = .ok res) :
    res.outcome ≠ .revert := by
  exact Θ_precompiled_ne_revert _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h

private theorem Θ_precompile_3_ne_revert
    (fuel : ℕ) (bvh : List ByteArray) (cA : Std.TreeSet AccountAddress compare)
    (gbh : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap .EVM) (A : Substate)
    (s o r : AccountAddress) (g p v v' : UInt256) (d : ByteArray) (e : ℕ) (H : BlockHeader)
    (w : Bool) (res : FrameResult)
    (h : Θ (fuel + 1) bvh cA gbh blocks σ σ₀ A s o r (.Precompiled 3) g p v v' d e H w
      = .ok res) :
    res.outcome ≠ .revert := by
  exact Θ_precompiled_ne_revert _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h

private theorem Θ_precompile_4_ne_revert
    (fuel : ℕ) (bvh : List ByteArray) (cA : Std.TreeSet AccountAddress compare)
    (gbh : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap .EVM) (A : Substate)
    (s o r : AccountAddress) (g p v v' : UInt256) (d : ByteArray) (e : ℕ) (H : BlockHeader)
    (w : Bool) (res : FrameResult)
    (h : Θ (fuel + 1) bvh cA gbh blocks σ σ₀ A s o r (.Precompiled 4) g p v v' d e H w
      = .ok res) :
    res.outcome ≠ .revert := by
  exact Θ_precompiled_ne_revert _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h

private theorem Θ_precompile_5_ne_revert
    (fuel : ℕ) (bvh : List ByteArray) (cA : Std.TreeSet AccountAddress compare)
    (gbh : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap .EVM) (A : Substate)
    (s o r : AccountAddress) (g p v v' : UInt256) (d : ByteArray) (e : ℕ) (H : BlockHeader)
    (w : Bool) (res : FrameResult)
    (h : Θ (fuel + 1) bvh cA gbh blocks σ σ₀ A s o r (.Precompiled 5) g p v v' d e H w
      = .ok res) :
    res.outcome ≠ .revert := by
  exact Θ_precompiled_ne_revert _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h

private theorem Θ_precompile_6_ne_revert
    (fuel : ℕ) (bvh : List ByteArray) (cA : Std.TreeSet AccountAddress compare)
    (gbh : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap .EVM) (A : Substate)
    (s o r : AccountAddress) (g p v v' : UInt256) (d : ByteArray) (e : ℕ) (H : BlockHeader)
    (w : Bool) (res : FrameResult)
    (h : Θ (fuel + 1) bvh cA gbh blocks σ σ₀ A s o r (.Precompiled 6) g p v v' d e H w
      = .ok res) :
    res.outcome ≠ .revert := by
  exact Θ_precompiled_ne_revert _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h

private theorem Θ_precompile_7_ne_revert
    (fuel : ℕ) (bvh : List ByteArray) (cA : Std.TreeSet AccountAddress compare)
    (gbh : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap .EVM) (A : Substate)
    (s o r : AccountAddress) (g p v v' : UInt256) (d : ByteArray) (e : ℕ) (H : BlockHeader)
    (w : Bool) (res : FrameResult)
    (h : Θ (fuel + 1) bvh cA gbh blocks σ σ₀ A s o r (.Precompiled 7) g p v v' d e H w
      = .ok res) :
    res.outcome ≠ .revert := by
  exact Θ_precompiled_ne_revert _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h

private theorem Θ_precompile_8_ne_revert
    (fuel : ℕ) (bvh : List ByteArray) (cA : Std.TreeSet AccountAddress compare)
    (gbh : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap .EVM) (A : Substate)
    (s o r : AccountAddress) (g p v v' : UInt256) (d : ByteArray) (e : ℕ) (H : BlockHeader)
    (w : Bool) (res : FrameResult)
    (h : Θ (fuel + 1) bvh cA gbh blocks σ σ₀ A s o r (.Precompiled 8) g p v v' d e H w
      = .ok res) :
    res.outcome ≠ .revert := by
  exact Θ_precompiled_ne_revert _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h

private theorem Θ_precompile_9_ne_revert
    (fuel : ℕ) (bvh : List ByteArray) (cA : Std.TreeSet AccountAddress compare)
    (gbh : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap .EVM) (A : Substate)
    (s o r : AccountAddress) (g p v v' : UInt256) (d : ByteArray) (e : ℕ) (H : BlockHeader)
    (w : Bool) (res : FrameResult)
    (h : Θ (fuel + 1) bvh cA gbh blocks σ σ₀ A s o r (.Precompiled 9) g p v v' d e H w
      = .ok res) :
    res.outcome ≠ .revert := by
  exact Θ_precompiled_ne_revert _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h

private theorem Θ_precompile_10_ne_revert
    (fuel : ℕ) (bvh : List ByteArray) (cA : Std.TreeSet AccountAddress compare)
    (gbh : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap .EVM) (A : Substate)
    (s o r : AccountAddress) (g p v v' : UInt256) (d : ByteArray) (e : ℕ) (H : BlockHeader)
    (w : Bool) (res : FrameResult)
    (h : Θ (fuel + 1) bvh cA gbh blocks σ σ₀ A s o r (.Precompiled 10) g p v v' d e H w
      = .ok res) :
    res.outcome ≠ .revert := by
  exact Θ_precompiled_ne_revert _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h

/-- **Precompiles never `REVERT`.** A successful message call to any of the ten precompiles ends
in `success` or `exceptionalHalt`; `revert` is impossible. The old `Bool` flag conflated revert and
halt, so this could not be stated. -/
theorem Θ_precompile_outcome_ne_revert
    (fuel : ℕ) (bvh : List ByteArray) (cA : Std.TreeSet AccountAddress compare)
    (gbh : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap .EVM) (A : Substate)
    (s o r pc : AccountAddress) (g p v v' : UInt256) (d : ByteArray) (e : ℕ) (H : BlockHeader)
    (w : Bool) (res : FrameResult) (hpc : pc ∈ precompileAddresses)
    (h : Θ (fuel + 1) bvh cA gbh blocks σ σ₀ A s o r (.Precompiled pc) g p v v' d e H w
      = .ok res) :
    res.outcome ≠ .revert := by
  simp only [precompileAddresses, List.mem_cons, List.not_mem_nil, or_false] at hpc
  rcases hpc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [Θ_precompile_1_ne_revert _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h,
    Θ_precompile_2_ne_revert _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h,
    Θ_precompile_3_ne_revert _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h,
    Θ_precompile_4_ne_revert _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h,
    Θ_precompile_5_ne_revert _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h,
    Θ_precompile_6_ne_revert _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h,
    Θ_precompile_7_ne_revert _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h,
    Θ_precompile_8_ne_revert _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h,
    Θ_precompile_9_ne_revert _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h,
    Θ_precompile_10_ne_revert _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h]

/-- **A failed code frame rolls back (YP (127)/(129)).** If a message call into ordinary code
returns but did not succeed (`revert` or `exceptionalHalt`), the caller gets back exactly the world
state, substate and created-accounts set it passed in. -/
theorem Θ_code_failure_rollsBack
    (fuel : ℕ) (bvh : List ByteArray) (cA : Std.TreeSet AccountAddress compare)
    (gbh : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap .EVM) (A : Substate)
    (s o r : AccountAddress) (code : ByteArray) (g p v v' : UInt256) (d : ByteArray) (e : ℕ)
    (H : BlockHeader) (w : Bool) (res : FrameResult)
    (h : Θ (fuel + 1) bvh cA gbh blocks σ σ₀ A s o r (.Code code) g p v v' d e H w = .ok res)
    (hfail : res.outcome ≠ .success) :
    res.accountMap = σ ∧ res.substate = A ∧ res.createdAccounts = cA := by
  simp only [Θ, bind, Except.bind, pure, Except.pure] at h
  split at h
  · split at h
    · cases h
    · cases h; simp
  · cases h; simp
  · cases h; simp at hfail

/-- **O-2 at the `Θ` boundary.** A message call into code with no fuel left for `Ξ` reports
`OutOfFuel`; it is never turned into a (failed or successful) `FrameResult`. -/
theorem Θ_code_outOfFuel
    (bvh : List ByteArray) (cA : Std.TreeSet AccountAddress compare)
    (gbh : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap .EVM) (A : Substate)
    (s o r : AccountAddress) (code : ByteArray) (g p v v' : UInt256) (d : ByteArray) (e : ℕ)
    (H : BlockHeader) (w : Bool) :
    Θ 1 bvh cA gbh blocks σ σ₀ A s o r (.Code code) g p v v' d e H w = .error .OutOfFuel := by
  simp [Θ, Ξ, bind, Except.bind]
  intro h
  exact absurd h (by decide)

/-- **A failed contract creation keeps the caller's world state (YP (115)).** Whether the init
code reverted, halted exceptionally, or the code deposit failed (`F`), the returned world state is
the one `Lambda` was given. -/
theorem Lambda_failure_rollsBack
    (fuel : ℕ) (bvh : List ByteArray) (cA : Std.TreeSet AccountAddress compare)
    (gbh : BlockHeader) (blocks : ProcessedBlocks) (σ σ₀ : AccountMap .EVM) (A : Substate)
    (s o : AccountAddress) (g p v : UInt256) (i : ByteArray) (e : UInt256) (ζ : Option ByteArray)
    (H : BlockHeader) (w : Bool) (res : CreateResult)
    (h : Lambda fuel bvh cA gbh blocks σ σ₀ A s o g p v i e ζ H w = .ok res)
    (hfail : res.outcome ≠ .success) :
    res.accountMap = σ := by
  unfold Lambda at h
  split at h
  · cases h
  · simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · split at h
      · split at h
        · cases h
        · cases h; rfl
      · cases h; rfl
      · cases h
        simp only at hfail ⊢
        split_ifs at hfail ⊢ <;> simp_all

/-- The success flag `z` that `call`, CREATE and `Υ` read is exactly `outcome = success`. -/
theorem FrameResult.z_iff (res : FrameResult) : res.z = true ↔ res.outcome = .success :=
  FrameOutcome.isSuccess_iff _

/-! ## CC-4: what proofs can say about the Python bridge -/

/-- **Proof-meaning witness (O-4 / CC-4).** In the logic, `totallySafePerformIO` *is* `default`:
this holds by `rfl`, whatever the Python helper prints at run time (the compiled program runs
`unsafePerformIO` instead, via `@[implemented_by]`). Any theorem that unfolds a precompile backed by
the Python bridge (ECRECOVER, BN254, SNARKV, point evaluation, the trie root) is therefore a theorem
about `default`, not about the program's output. The axiom audit's ban on `Lean.ofReduceBool`
(`native_decide`) is what stops this disagreement from being turned into a proof of `False`. -/
@[reviewed_pin EvmYul.EVM.SemanticsWitnesses.readWithPadding_zero_size]
theorem totallySafePerformIO_eq_default {τ : Type} [Inhabited τ] (io : IO τ) :
    totallySafePerformIO io = default := rfl

end EvmYul.EVM.SemanticsWitnesses
