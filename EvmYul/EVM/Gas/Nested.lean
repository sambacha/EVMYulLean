module

public import EvmYul.EVM.Gas.StepFrame
public import EvmYul.EVM.Gas.Laws
public import EvmYul.ProofTags
public section

/-!
# Nested frames: gas returned and fuel adequacy (K8, K1)

`GasStepFrame` proved the per-step gas and fuel facts for every instruction except the six that
open a nested frame (CREATE, CREATE2, CALL, CALLCODE, DELEGATECALL, STATICCALL), leaving them as
`SpawnStepGasSoundZ` / `SpawnNestedFuelAdequateZ`. This module (gas returned) and its continuation
`EvmYul/EVM/Gas/NestedFuel.lean` (fuel adequacy) close them, and with them K8 and K1.

**Gas returned** (`allGasBounds`, by induction on the fuel, simultaneously for `X`, `Ξ`, `Θ`, `Λ`,
`call` and `step`): a nested frame never hands back more gas than it was given.
* `Ξ_gas_le`, `Θ_gasLeft_le`, `Lambda_gasLeft_le`, `X_gas_le` (the precompiles: `Ξ_*_gas_le`,
  `precompileDispatch_gas_le`).
* `call` leaves at most `deduct(gas, charge) + C_CALLGAS` (`CallGasBound`); since `Z`'s charge for a
  CALL-family instruction is at least `C_CALLGAS + 100` (`charge_covers_of_instrCost`), the caller's
  gas strictly drops (`step_CALL_gas_lt` and siblings). CREATE/CREATE2 leave at most the deducted gas
  (`step_CREATE_gas_le`), because `Λ` returns at most the `L(·)` it was given.
* Hence `stepGasSoundZ : StepGasSoundZ` with no hypothesis.

**Fuel adequacy** (`allFuelAdequate`, a second simultaneous induction): with fuel above the gas by a
fixed margin (`X`: 2, `Ξ`: 3, `Θ`/`Λ`: 4, `call`: 5 above `C_CALLGAS`, `step`: 1), no frame raises
`OutOfFuel`. The margin is paid by the strict gas decrease above and `G_create ≥ 5`.
* `nestedFuelAdequateZ`, `X_ne_outOfFuel_unconditional` (**K8**), `Θ_ne_outOfFuel`,
  `Lambda_ne_outOfFuel`.
* `Υ_ne_outOfFuel` / `Υ_transactionFuel_ne_outOfFuel` (**K1**): a transaction with fuel above
  `gasLimit + 4` — in particular the conformance runner's `transactionFuel` — never fails with
  `OutOfFuel`.

**Negations** (the statements are not vacuous and the hypotheses are needed):
`not_X_ne_outOfFuel_of_gas_lt_fuel` (fuel = gas + 1 is not enough for `X`),
`not_Θ_ne_outOfFuel_margin_two`, and `not_Θ_gasLeft_lt` (the gas bound is tight: an empty callee
returns everything). Executable checks with code-running callees: `NestedTests`.

Scope: Cancun schedule only (the interpreter's `Z` charges with `cancun`).
-/

namespace EvmYul

namespace EVM

open GasMeter UInt256 ForkSchedule

theorem toNat_add_le (a b : UInt256) : (a + b).toNat ≤ a.toNat + b.toNat := by
  change ((a.val + b.val : Fin _) : ℕ) ≤ _
  rw [Fin.val_add]; exact Nat.mod_le _ _

@[reviewed_generic "ℕ arithmetic helper"]
theorem ite_zero_sub_le (p : Prop) [Decidable p] (x y : ℕ) : (if p then 0 else x - y) ≤ x := by
  split <;> omega

theorem sub_ofNat_toNat_le_of_guard {g : UInt256} {n : ℕ} (h : ¬ g.toNat < n) :
    (g - UInt256.ofNat n).toNat ≤ g.toNat := by
  rw [toNat_sub_ofNat_of_le (by omega)]; omega

/-- Closes `(Ξ_… σ g A I).2.2.1.toNat ≤ g.toNat` after unfolding a precompile: split every branch;
each one returns `0`, `g` unchanged, or `g - n` behind the guard `¬ g.toNat < n`. -/
macro "precompile_gas_tac" : tactic => `(tactic| (
  dsimp only
  repeat' split
  all_goals first
    | exact Nat.zero_le _
    | exact le_refl _
    | (rw [dbgTrace_eq]; exact Nat.zero_le _)
    | (apply sub_ofNat_toNat_le_of_guard; assumption)))

theorem Ξ_ECREC_gas_le (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM) :
    (Ξ_ECREC σ g A I).2.2.1.toNat ≤ g.toNat := by unfold Ξ_ECREC; precompile_gas_tac
theorem Ξ_SHA256_gas_le (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM) :
    (Ξ_SHA256 σ g A I).2.2.1.toNat ≤ g.toNat := by unfold Ξ_SHA256; precompile_gas_tac
theorem Ξ_RIP160_gas_le (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM) :
    (Ξ_RIP160 σ g A I).2.2.1.toNat ≤ g.toNat := by unfold Ξ_RIP160; precompile_gas_tac
theorem Ξ_ID_gas_le (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM) :
    (Ξ_ID σ g A I).2.2.1.toNat ≤ g.toNat := by unfold Ξ_ID; precompile_gas_tac
theorem Ξ_EXPMOD_gas_le (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM) :
    (Ξ_EXPMOD σ g A I).2.2.1.toNat ≤ g.toNat := by unfold Ξ_EXPMOD; precompile_gas_tac
theorem Ξ_BN_ADD_gas_le (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM) :
    (Ξ_BN_ADD σ g A I).2.2.1.toNat ≤ g.toNat := by unfold Ξ_BN_ADD; precompile_gas_tac
theorem Ξ_BN_MUL_gas_le (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM) :
    (Ξ_BN_MUL σ g A I).2.2.1.toNat ≤ g.toNat := by unfold Ξ_BN_MUL; precompile_gas_tac
theorem Ξ_SNARKV_gas_le (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM) :
    (Ξ_SNARKV σ g A I).2.2.1.toNat ≤ g.toNat := by
  rw [Ξ_SNARKV.eq_1]
  dsimp only
  generalize 34000 * (I.calldata.size / 192) + 45000 = n
  generalize SNARKV I.calldata = o
  split
  · exact Nat.zero_le _
  · cases o with
    | error => simp only [dbgTrace_eq]; exact Nat.zero_le _
    | ok => apply sub_ofNat_toNat_le_of_guard; assumption
theorem Ξ_BLAKE2_F_gas_le (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM) :
    (Ξ_BLAKE2_F σ g A I).2.2.1.toNat ≤ g.toNat := by unfold Ξ_BLAKE2_F; precompile_gas_tac
theorem Ξ_PointEval_gas_le (σ : AccountMap .EVM) (g : UInt256) (A : Substate) (I : ExecutionEnv .EVM) :
    (Ξ_PointEval σ g A I).2.2.1.toNat ≤ g.toNat := by unfold Ξ_PointEval; precompile_gas_tac

@[reviewed_rfl "gas projection of the frame outcome, by definition"]
theorem ofPrecompile_gasLeft (r : Bool × AccountMap .EVM × UInt256 × Substate × ByteArray) :
    (FrameOutcome.ofPrecompile r).2.2.1 = r.2.2.1 := rfl

/-! Forms with the precompile result abstracted (the kernel must never unfold a precompile). -/

theorem Ξ_ECREC_gas_le' {σ : AccountMap .EVM} {g : UInt256} {A : Substate} {I : ExecutionEnv .EVM}
    {G : UInt256} (h : (FrameOutcome.ofPrecompile (Ξ_ECREC σ g A I)).2.2.1 = G) :
    G.toNat ≤ g.toNat := by
  rw [← h, ofPrecompile_gasLeft]; exact Ξ_ECREC_gas_le σ g A I
theorem Ξ_SHA256_gas_le' {σ : AccountMap .EVM} {g : UInt256} {A : Substate} {I : ExecutionEnv .EVM}
    {G : UInt256} (h : (FrameOutcome.ofPrecompile (Ξ_SHA256 σ g A I)).2.2.1 = G) :
    G.toNat ≤ g.toNat := by
  rw [← h, ofPrecompile_gasLeft]; exact Ξ_SHA256_gas_le σ g A I
theorem Ξ_RIP160_gas_le' {σ : AccountMap .EVM} {g : UInt256} {A : Substate} {I : ExecutionEnv .EVM}
    {G : UInt256} (h : (FrameOutcome.ofPrecompile (Ξ_RIP160 σ g A I)).2.2.1 = G) :
    G.toNat ≤ g.toNat := by
  rw [← h, ofPrecompile_gasLeft]; exact Ξ_RIP160_gas_le σ g A I
theorem Ξ_ID_gas_le' {σ : AccountMap .EVM} {g : UInt256} {A : Substate} {I : ExecutionEnv .EVM}
    {G : UInt256} (h : (FrameOutcome.ofPrecompile (Ξ_ID σ g A I)).2.2.1 = G) :
    G.toNat ≤ g.toNat := by
  rw [← h, ofPrecompile_gasLeft]; exact Ξ_ID_gas_le σ g A I
theorem Ξ_EXPMOD_gas_le' {σ : AccountMap .EVM} {g : UInt256} {A : Substate} {I : ExecutionEnv .EVM}
    {G : UInt256} (h : (FrameOutcome.ofPrecompile (Ξ_EXPMOD σ g A I)).2.2.1 = G) :
    G.toNat ≤ g.toNat := by
  rw [← h, ofPrecompile_gasLeft]; exact Ξ_EXPMOD_gas_le σ g A I
theorem Ξ_BN_ADD_gas_le' {σ : AccountMap .EVM} {g : UInt256} {A : Substate} {I : ExecutionEnv .EVM}
    {G : UInt256} (h : (FrameOutcome.ofPrecompile (Ξ_BN_ADD σ g A I)).2.2.1 = G) :
    G.toNat ≤ g.toNat := by
  rw [← h, ofPrecompile_gasLeft]; exact Ξ_BN_ADD_gas_le σ g A I
theorem Ξ_BN_MUL_gas_le' {σ : AccountMap .EVM} {g : UInt256} {A : Substate} {I : ExecutionEnv .EVM}
    {G : UInt256} (h : (FrameOutcome.ofPrecompile (Ξ_BN_MUL σ g A I)).2.2.1 = G) :
    G.toNat ≤ g.toNat := by
  rw [← h, ofPrecompile_gasLeft]; exact Ξ_BN_MUL_gas_le σ g A I
theorem Ξ_SNARKV_gas_le' {σ : AccountMap .EVM} {g : UInt256} {A : Substate} {I : ExecutionEnv .EVM}
    {G : UInt256} (h : (FrameOutcome.ofPrecompile (Ξ_SNARKV σ g A I)).2.2.1 = G) :
    G.toNat ≤ g.toNat := by
  rw [← h, ofPrecompile_gasLeft]; exact Ξ_SNARKV_gas_le σ g A I
theorem Ξ_BLAKE2_F_gas_le' {σ : AccountMap .EVM} {g : UInt256} {A : Substate} {I : ExecutionEnv .EVM}
    {G : UInt256} (h : (FrameOutcome.ofPrecompile (Ξ_BLAKE2_F σ g A I)).2.2.1 = G) :
    G.toNat ≤ g.toNat := by
  rw [← h, ofPrecompile_gasLeft]; exact Ξ_BLAKE2_F_gas_le σ g A I
theorem Ξ_PointEval_gas_le' {σ : AccountMap .EVM} {g : UInt256} {A : Substate} {I : ExecutionEnv .EVM}
    {G : UInt256} (h : (FrameOutcome.ofPrecompile (Ξ_PointEval σ g A I)).2.2.1 = G) :
    G.toNat ≤ g.toNat := by
  rw [← h, ofPrecompile_gasLeft]; exact Ξ_PointEval_gas_le σ g A I


/-! ## The charge of a call covers the gas it forwards -/

/-- **Under Cancun a call's charge exceeds the gas it forwards by at least 100**: `C_CALL` is
`C_GASCAP + C_EXTRA` and the callee gets `C_GASCAP` plus, for a value transfer, the 2300 stipend;
`C_EXTRA` contains the access cost (≥ 100) and, for a value transfer, the 9000 surcharge. -/
theorem cancun_callGas_add_le_callCost (gas : ℕ) (t r : AccountAddress) (v g : UInt256)
    (σ : AccountMap .EVM) (A : Substate) :
    cancun.callGas gas t r v g σ A + 100 ≤ cancun.callCost gas t r v g σ A := by
  unfold ForkSchedule.callGas ForkSchedule.callCost
  rw [callExtra_cancun]
  have hacc : 100 ≤ Caccess t A := by
    unfold Caccess; split <;> decide
  unfold Cextra Cxfer
  split
  · omega
  · rename_i hv
    have : (v != ⟨0⟩) = true := bne_zero_of_ne hv
    simp only [this, ↓reduceIte]
    have : cancun.Gcallstipend = 2300 := rfl
    have : GasConstants.Gcallvalue = 9000 := rfl
    omega

/-- The interpreter passes the code owner to `call` as `UInt256.ofNat`; converting back is the
identity (addresses are below `2^160 < 2^256`). -/
theorem ofUInt256_ofNat_address (a : AccountAddress) :
    AccountAddress.ofUInt256 (UInt256.ofNat a.val) = a := by
  have h1 : a.val < AccountAddress.size := a.isLt
  have h2 : AccountAddress.size < UInt256.size := by decide
  apply Fin.ext
  simp only [AccountAddress.ofUInt256, UInt256.ofNat, Id.run, Fin.ofNat, Fin.val_mk]
  rw [Nat.mod_eq_of_lt (show a.val < UInt256.size by omega)]
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h1]

/-! ## Gas bounds, fuel-indexed -/

attribute [local irreducible] Ξ_ECREC Ξ_SHA256 Ξ_RIP160 Ξ_ID Ξ_EXPMOD Ξ_BN_ADD Ξ_BN_MUL Ξ_SNARKV
  Ξ_BLAKE2_F Ξ_PointEval

/-- **Every precompile hands back at most the gas it was given.** -/
theorem precompileDispatch_gas_le (p : AccountAddress) (σ₁ : AccountMap .EVM) (g : UInt256)
    (A : Substate) (I : ExecutionEnv .EVM) :
    (precompileDispatch p σ₁ g A I).2.2.1.toNat ≤ g.toNat := by
  unfold precompileDispatch
  split <;> first
    | exact Ξ_ECREC_gas_le' rfl
    | exact Ξ_SHA256_gas_le' rfl
    | exact Ξ_RIP160_gas_le' rfl
    | exact Ξ_ID_gas_le' rfl
    | exact Ξ_EXPMOD_gas_le' rfl
    | exact Ξ_BN_ADD_gas_le' rfl
    | exact Ξ_BN_MUL_gas_le' rfl
    | exact Ξ_SNARKV_gas_le' rfl
    | exact Ξ_BLAKE2_F_gas_le' rfl
    | exact Ξ_PointEval_gas_le' rfl
    | exact Nat.zero_le _

/-- The gas a finished `X` run hands back. -/
def xResultGas : ExecutionResult State → ℕ
  | .success s _ => s.gasAvailable.toNat
  | .revert g _ => g.toNat

/-- The gas a finished `Ξ` run hands back. -/
def ξResultGas :
    ExecutionResult (Std.TreeSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate) → ℕ
  | .success (_, _, g, _) _ => g.toNat
  | .revert g _ => g.toNat

/-- At fuel `n`, every finished `X` run hands back at most the gas it started with. -/
@[expose] def XGasBound (n : ℕ) : Prop :=
  ∀ (vj : Array UInt256) (s : State) (r : ExecutionResult State),
    X n vj s = .ok r → xResultGas r ≤ s.gasAvailable.toNat

/-- At fuel `n`, every finished `Ξ` run hands back at most the gas `g` it was given. -/
@[expose] def ΞGasBound (n : ℕ) : Prop :=
  ∀ cA gbh bl σ σ₀ (g : UInt256) A I r,
    Ξ n cA gbh bl σ σ₀ g A I = .ok r → ξResultGas r ≤ g.toNat

/-- At fuel `n`, every finished message call `Θ` leaves at most the gas `g` it was given. -/
@[expose] def ΘGasBound (n : ℕ) : Prop :=
  ∀ bvh cA gbh bl σ σ₀ A s o r c (g : UInt256) p v v' d e H w res,
    Θ n bvh cA gbh bl σ σ₀ A s o r c g p v v' d e H w = .ok res → res.gasLeft.toNat ≤ g.toNat

/-- At fuel `n`, every finished contract creation `Lambda` leaves at most the gas `g` it was given. -/
@[expose] def ΛGasBound (n : ℕ) : Prop :=
  ∀ bvh cA gbh bl σ σ₀ A s o (g : UInt256) p v i e ζ H w res,
    Lambda n bvh cA gbh bl σ σ₀ A s o g p v i e ζ H w = .ok res → res.gasLeft.toNat ≤ g.toNat

/-- At fuel `n`, a finished `CALL`-family instruction leaves at most the gas after its charge plus
the callee's allowance `Ccallgas`. -/
@[expose] def CallGasBound (n : ℕ) : Prop :=
  ∀ gasCost bvh (gas source recipient t value value' inO inS outO outS : UInt256) perm
    (st : State) x st',
    call n gasCost bvh gas source recipient t value value' inO inS outO outS perm st = .ok (x, st') →
      st'.gasAvailable.toNat ≤ (deductPrechecked st.gasAvailable gasCost).toNat +
        Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient) value gas
          st.accountMap st.toMachineState st.substate

/-- At fuel `n`, a step after the exceptional-halt checks either leaves at most the gas after its
charge or strictly less gas than before. -/
@[expose] def StepGasBound (n : ℕ) : Prop :=
  ∀ (vj : Array UInt256) (w : Operation .EVM) (arg : Option (UInt256 × Nat))
    (s s₁ : State) (c : ℕ) (s₂ : State),
    exceptionalHalt vj w s = .ok (s₁, c) → step n c (some (w, arg)) s₁ = .ok s₂ →
      s₂.gasAvailable.toNat ≤ (deductPrechecked s₁.gasAvailable c).toNat ∨
        s₂.gasAvailable.toNat < s₁.gasAvailable.toNat

theorem ξGasBound_succ {n : ℕ} (h : XGasBound n) : ΞGasBound (n + 1) := by
  intro cA gbh bl σ σ₀ g A I r hr
  simp only [Ξ, bind, Except.bind] at hr
  split at hr
  · cases hr
  · rename_i v hv
    have := h _ _ _ hv
    split at hr <;> cases hr <;> simpa [xResultGas, ξResultGas] using this

@[reviewed_generic "Except plumbing"]
theorem except_bind_ok_inv {ε α β : Type} {M : Except ε α} {k : α → Except ε β} {b : β}
    (h : M >>= k = .ok b) : ∃ a, M = .ok a ∧ k a = .ok b := by
  cases M with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem θGasBound_succ {n : ℕ} (h : ΞGasBound n) : ΘGasBound (n + 1) := by
  intro bvh cA gbh bl σ σ₀ A s o r c g p v v' d e H w res hr
  cases c with
  | Precompiled p =>
    simp only [Θ, bind, Except.bind, Except.ok.injEq] at hr
    rw [← hr]
    exact precompileDispatch_gas_le _ _ _ _ _
  | Code code =>
    simp only [Θ, bind, Except.bind] at hr
    split at hr
    · split at hr
      · cases hr
      · cases hr; exact Nat.zero_le _
    · rename_i heq
      cases hr
      simpa [ξResultGas] using h _ _ _ _ _ _ _ _ _ heq
    · rename_i heq
      cases hr
      simpa [ξResultGas] using h _ _ _ _ _ _ _ _ _ heq

theorem lambdaGasBound_succ {n : ℕ} (h : ΞGasBound n) : ΛGasBound (n + 1) := by
  intro bvh cA gbh bl σ σ₀ A s o g p v i e ζ H w res hr
  simp only [Lambda, bind, Except.bind] at hr
  split at hr
  · cases hr
  split at hr
  · split at hr
    · cases hr
    split at hr
    · cases hr
    · cases hr; exact Nat.zero_le _
  · rename_i heq
    cases hr
    simpa [ξResultGas] using h _ _ _ _ _ _ _ _ _ heq
  · rename_i heq
    cases hr
    have hg := h _ _ _ _ _ _ _ _ _ heq
    simp only [ξResultGas] at hg
    refine le_trans (toNat_ofNat_le _) (le_trans ?_ hg)
    split <;> exact ite_zero_sub_le _ _ _

theorem callGasBound_succ {n : ℕ} (h : ΘGasBound n) : CallGasBound (n + 1) := by
  intro gasCost bvh gas source recipient t value value' inO inS outO outS perm st x st' hr
  simp only [call, bind, Except.bind] at hr
  have hcg := toNat_ofNat_le (Ccallgas (AccountAddress.ofUInt256 t)
    (AccountAddress.ofUInt256 recipient) value gas st.accountMap st.toMachineState st.substate)
  split at hr
  · split at hr
    · cases hr
    rename_i v hΘ
    have hv := h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hΘ
    split at hr
    · cases hr
    rename_i v' hv'
    cases hv'
    cases hr
    refine le_trans (toNat_add_le _ _) ?_
    simp only [writeBytes, FrameResult.toTuple]
    omega
  · cases hr
    refine le_trans (toNat_add_le _ _) ?_
    simp only [writeBytes]
    omega

theorem charge_covers_of_instrCost {vj : Array UInt256} {w : Operation .EVM} {s s₁ : State} {c : ℕ}
    {t r : AccountAddress} {v g : UInt256} (hZ : exceptionalHalt vj w s = .ok (s₁, c))
    (hc : cancun.instrCost? s₁.gasAvailable.toNat s w =
      some (cancun.callCost s₁.gasAvailable.toNat t r v g s.accountMap s.substate)) :
    Ccallgas t r v g s₁.accountMap s₁.toMachineState s₁.substate + 100 ≤ c ∧
      c ≤ s₁.gasAvailable.toNat := by
  obtain ⟨hs', hle, hcost⟩ := exceptionalHalt_ok_parts hZ
  rw [hc] at hcost
  cases hcost
  have hσ : s₁.accountMap = s.accountMap := by rw [hs']
  have hA : s₁.substate = s.substate := by rw [hs']
  rw [hσ, hA, ← callGas_cancun]
  exact ⟨cancun_callGas_add_le_callCost _ _ _ _ _ _ _, hle⟩

theorem call_gas_lt {n c : ℕ} (hC : CallGasBound n) {bvh : List ByteArray}
    {gas source recipient t value value' inO inS outO outS : UInt256} {perm : Bool}
    {st : State} {x : UInt256} {st' : State}
    (hcall : call n c bvh gas source recipient t value value' inO inS outO outS perm st = .ok (x, st'))
    (hcov : Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient) value gas
      st.accountMap st.toMachineState st.substate + 100 ≤ c)
    (hle : c ≤ st.gasAvailable.toNat) :
    st'.gasAvailable.toNat < st.gasAvailable.toNat := by
  have h := hC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hcall
  rw [deductPrechecked_toNat hle] at h
  omega

@[reviewed_rfl "a stack update leaves the gas unchanged, by definition"]
theorem replaceStackAndIncrPC_gas (st : State) (stk : Stack UInt256) :
    (st.replaceStackAndIncrPC stk).gasAvailable = st.gasAvailable := rfl

theorem pop7_eq_some {α : Type} {s tl : Stack α} {a0 a1 a2 a3 a4 a5 a6 : α}
    (h : s.pop7 = some (tl, a0, a1, a2, a3, a4, a5, a6)) :
    s = a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: tl := by
  unfold Stack.pop7 at h
  split at h <;> cases h
  rfl

theorem pop6_eq_some {α : Type} {s tl : Stack α} {a0 a1 a2 a3 a4 a5 : α}
    (h : s.pop6 = some (tl, a0, a1, a2, a3, a4, a5)) :
    s = a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: tl := by
  unfold Stack.pop6 at h
  split at h <;> cases h
  rfl

theorem step_CALL_gas_lt {n : ℕ} (hC : CallGasBound n) {vj : Array UInt256} {arg : Option (UInt256 × Nat)}
    {s s₁ s₂ : State} {c : ℕ} (hZ : exceptionalHalt vj .CALL s = .ok (s₁, c))
    (hs : step (n + 1) c (some (.CALL, arg)) s₁ = .ok s₂) :
    s₂.gasAvailable.toNat < s₁.gasAvailable.toNat := by
  simp only [step, bind, Except.bind, pure, Except.pure] at hs
  obtain ⟨hs', -, -⟩ := exceptionalHalt_ok_parts hZ
  have hstk : s₁.stack = s.stack := by rw [hs']
  rcases h7 : s.stack.pop7 with _ | ⟨tl, a0, a1, a2, a3, a4, a5, a6⟩
  · rw [hstk, h7] at hs
    simp [liftM, monadLift, MonadLift.monadLift, instMonadLiftOptionExceptExecutionException,
      Option.option] at hs
  · have hst := pop7_eq_some h7
    rw [hstk, hst] at hs
    simp only [Stack.pop7, liftM, monadLift, MonadLift.monadLift, instMonadLiftOptionExceptExecutionException, Option.option] at hs
    split at hs
    · cases hs
    rename_i v hcall
    obtain ⟨x, st'⟩ := v
    cases hs
    have hc : cancun.instrCost? s₁.gasAvailable.toNat s .CALL =
        some (cancun.callCost s₁.gasAvailable.toNat (.ofUInt256 a1) (.ofUInt256 a1) a2 a0
          s.accountMap s.substate) := by
      simp [instrCost?, hst]
    obtain ⟨hcov, hle⟩ := charge_covers_of_instrCost hZ hc
    have h := call_gas_lt hC hcall (by exact hcov) (by exact hle)
    exact h

theorem step_CALLCODE_gas_lt {n : ℕ} (hC : CallGasBound n) {vj : Array UInt256}
    {arg : Option (UInt256 × Nat)} {s s₁ s₂ : State} {c : ℕ}
    (hZ : exceptionalHalt vj .CALLCODE s = .ok (s₁, c))
    (hs : step (n + 1) c (some (.CALLCODE, arg)) s₁ = .ok s₂) :
    s₂.gasAvailable.toNat < s₁.gasAvailable.toNat := by
  simp only [step, bind, Except.bind, pure, Except.pure] at hs
  obtain ⟨hs', -, -⟩ := exceptionalHalt_ok_parts hZ
  have hstk : s₁.stack = s.stack := by rw [hs']
  have hI : s₁.executionEnv = s.executionEnv := by rw [hs']
  rcases h7 : s.stack.pop7 with _ | ⟨tl, a0, a1, a2, a3, a4, a5, a6⟩
  · rw [hstk, h7] at hs
    simp [liftM, monadLift, MonadLift.monadLift, instMonadLiftOptionExceptExecutionException,
      Option.option] at hs
  · have hst := pop7_eq_some h7
    rw [hstk, hst] at hs
    simp only [Stack.pop7, liftM, monadLift, MonadLift.monadLift,
      instMonadLiftOptionExceptExecutionException, Option.option] at hs
    split at hs
    · cases hs
    rename_i v hcall
    obtain ⟨x, st'⟩ := v
    cases hs
    have hc : cancun.instrCost? s₁.gasAvailable.toNat s .CALLCODE =
        some (cancun.callCost s₁.gasAvailable.toNat (.ofUInt256 a1) s.executionEnv.codeOwner a2 a0
          s.accountMap s.substate) := by
      simp [instrCost?, hst]
    obtain ⟨hcov, hle⟩ := charge_covers_of_instrCost hZ hc
    have h := call_gas_lt hC hcall (by simpa only [hI, ofUInt256_ofNat_address] using hcov)
      (by exact hle)
    exact h

theorem step_DELEGATECALL_gas_lt {n : ℕ} (hC : CallGasBound n) {vj : Array UInt256}
    {arg : Option (UInt256 × Nat)} {s s₁ s₂ : State} {c : ℕ}
    (hZ : exceptionalHalt vj .DELEGATECALL s = .ok (s₁, c))
    (hs : step (n + 1) c (some (.DELEGATECALL, arg)) s₁ = .ok s₂) :
    s₂.gasAvailable.toNat < s₁.gasAvailable.toNat := by
  simp only [step, bind, Except.bind, pure, Except.pure] at hs
  obtain ⟨hs', -, -⟩ := exceptionalHalt_ok_parts hZ
  have hstk : s₁.stack = s.stack := by rw [hs']
  have hI : s₁.executionEnv = s.executionEnv := by rw [hs']
  rcases h7 : s.stack.pop6 with _ | ⟨tl, a0, a1, a3, a4, a5, a6⟩
  · rw [hstk, h7] at hs
    simp [liftM, monadLift, MonadLift.monadLift, instMonadLiftOptionExceptExecutionException,
      Option.option] at hs
  · have hst := pop6_eq_some h7
    rw [hstk, hst] at hs
    simp only [Stack.pop6, liftM, monadLift, MonadLift.monadLift,
      instMonadLiftOptionExceptExecutionException, Option.option] at hs
    split at hs
    · cases hs
    rename_i v hcall
    obtain ⟨x, st'⟩ := v
    cases hs
    have hc : cancun.instrCost? s₁.gasAvailable.toNat s .DELEGATECALL =
        some (cancun.callCost s₁.gasAvailable.toNat (.ofUInt256 a1) s.executionEnv.codeOwner ⟨0⟩ a0
          s.accountMap s.substate) := by
      simp [instrCost?, hst]
    obtain ⟨hcov, hle⟩ := charge_covers_of_instrCost hZ hc
    have h := call_gas_lt hC hcall (by simpa only [hI, ofUInt256_ofNat_address] using hcov)
      (by exact hle)
    exact h

theorem step_STATICCALL_gas_lt {n : ℕ} (hC : CallGasBound n) {vj : Array UInt256}
    {arg : Option (UInt256 × Nat)} {s s₁ s₂ : State} {c : ℕ}
    (hZ : exceptionalHalt vj .STATICCALL s = .ok (s₁, c))
    (hs : step (n + 1) c (some (.STATICCALL, arg)) s₁ = .ok s₂) :
    s₂.gasAvailable.toNat < s₁.gasAvailable.toNat := by
  simp only [step, bind, Except.bind, pure, Except.pure] at hs
  obtain ⟨hs', -, -⟩ := exceptionalHalt_ok_parts hZ
  have hstk : s₁.stack = s.stack := by rw [hs']
  have hI : s₁.executionEnv = s.executionEnv := by rw [hs']
  rcases h7 : s.stack.pop6 with _ | ⟨tl, a0, a1, a3, a4, a5, a6⟩
  · rw [hstk, h7] at hs
    simp [liftM, monadLift, MonadLift.monadLift, instMonadLiftOptionExceptExecutionException,
      Option.option] at hs
  · have hst := pop6_eq_some h7
    rw [hstk, hst] at hs
    simp only [Stack.pop6, liftM, monadLift, MonadLift.monadLift,
      instMonadLiftOptionExceptExecutionException, Option.option] at hs
    split at hs
    · cases hs
    rename_i v hcall
    obtain ⟨x, st'⟩ := v
    cases hs
    have hc : cancun.instrCost? s₁.gasAvailable.toNat s .STATICCALL =
        some (cancun.callCost s₁.gasAvailable.toNat (.ofUInt256 a1) (.ofUInt256 a1) ⟨0⟩ a0
          s.accountMap s.substate) := by
      simp [instrCost?, hst]
    obtain ⟨hcov, hle⟩ := charge_covers_of_instrCost hZ hc
    have h := call_gas_lt hC hcall (by simpa only [hI, ofUInt256_ofNat_address] using hcov)
      (by exact hle)
    exact h

theorem step_CREATE_gas_le {n : ℕ} (hL : ΛGasBound n) {arg : Option (UInt256 × Nat)}
    {s₁ s₂ : State} {c : ℕ}
    (hs : step (n + 1) c (some (.CREATE, arg)) s₁ = .ok s₂) :
    s₂.gasAvailable.toNat ≤ (deductPrechecked s₁.gasAvailable c).toNat := by
  simp only [step, bind, Except.bind, pure, Except.pure] at hs
  split at hs
  · split at hs
    · cases hs
    rename_i v heq
    split at hs
    · cases hs
    cases hs
    have hg : v.2.2.1.toNat ≤ L (deductPrechecked s₁.gasAvailable c).toNat := by
      split at heq
      · cases heq; exact toNat_ofNat_le _
      split at heq
      · split at heq
        · cases heq; exact le_trans (hL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ‹_›) (toNat_ofNat_le _)
        · cases heq
        · cases heq; exact Nat.zero_le _
      · cases heq; exact toNat_ofNat_le _
    rw [replaceStackAndIncrPC_gas]
    refine le_trans (toNat_ofNat_le _) ?_
    have : L (deductPrechecked s₁.gasAvailable c).toNat ≤ (deductPrechecked s₁.gasAvailable c).toNat :=
      Nat.sub_le _ _
    exact le_trans (Nat.add_le_add_left hg _) (le_of_eq (Nat.sub_add_cancel this))
  · cases hs

theorem step_CREATE2_gas_le {n : ℕ} (hL : ΛGasBound n) {arg : Option (UInt256 × Nat)}
    {s₁ s₂ : State} {c : ℕ}
    (hs : step (n + 1) c (some (.CREATE2, arg)) s₁ = .ok s₂) :
    s₂.gasAvailable.toNat ≤ (deductPrechecked s₁.gasAvailable c).toNat := by
  simp only [step, bind, Except.bind, pure, Except.pure] at hs
  split at hs
  · split at hs
    · cases hs
    rename_i v heq
    split at hs
    · cases hs
    cases hs
    have hg : v.2.2.1.toNat ≤ L (deductPrechecked s₁.gasAvailable c).toNat := by
      split at heq
      · cases heq; exact toNat_ofNat_le _
      split at heq
      · split at heq
        · cases heq; exact le_trans (hL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ‹_›) (toNat_ofNat_le _)
        · cases heq
        · cases heq; exact Nat.zero_le _
      · cases heq; exact toNat_ofNat_le _
    rw [replaceStackAndIncrPC_gas]
    refine le_trans (toNat_ofNat_le _) ?_
    have : L (deductPrechecked s₁.gasAvailable c).toNat ≤ (deductPrechecked s₁.gasAvailable c).toNat :=
      Nat.sub_le _ _
    exact le_trans (Nat.add_le_add_left hg _) (le_of_eq (Nat.sub_add_cancel this))
  · cases hs

theorem stepGasBound_succ {n : ℕ} (hC : CallGasBound n) (hL : ΛGasBound n) :
    StepGasBound (n + 1) := by
  intro vj w arg s s₁ c s₂ hZ hs
  by_cases hw : w ∈ spawnOps
  · simp only [spawnOps, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (step_CREATE_gas_le hL hs)
    · exact Or.inl (step_CREATE2_gas_le hL hs)
    · exact Or.inr (step_CALL_gas_lt hC hZ hs)
    · exact Or.inr (step_CALLCODE_gas_lt hC hZ hs)
    · exact Or.inr (step_DELEGATECALL_gas_lt hC hZ hs)
    · exact Or.inr (step_STATICCALL_gas_lt hC hZ hs)
  · have := step_some_gasSafe (f := n) (c := c) (arg := arg) s₁ hw
    rw [hs] at this
    exact Or.inl (le_of_eq (congrArg UInt256.toNat this.ok_eq))
/-- What one accepted step leaves: at most the gas `Z` handed to `step`. -/
theorem step_gas_le_of_bound {n : ℕ} (hS : StepGasBound n) {vj : Array UInt256} {w : Operation .EVM}
    {arg : Option (UInt256 × Nat)} {s s₁ s₂ : State} {c : ℕ}
    (hZ : exceptionalHalt vj w s = .ok (s₁, c)) (hs : step n c (some (w, arg)) s₁ = .ok s₂) :
    s₂.gasAvailable.toNat ≤ s.gasAvailable.toNat := by
  obtain ⟨-, hc, -⟩ := exceptionalHalt_ok_parts hZ
  have hg₁ : s₁.gasAvailable.toNat ≤ s.gasAvailable.toNat := by
    have := exceptionalHalt_ok_gas hZ
    omega
  rcases hS vj w arg s s₁ c s₂ hZ hs with h | h
  · rw [deductPrechecked_toNat hc] at h; omega
  · omega

theorem xGasBound_succ {n : ℕ} (hS : StepGasBound n) (hX : XGasBound n) : XGasBound (n + 1) := by
  intro vj s r hr
  unfold X at hr
  simp only [traceInstructions, Bool.false_eq_true, ↓reduceIte] at hr
  generalize (decode s.executionEnv.code s.pc).getD (Operation.STOP, none) = instr at hr
  obtain ⟨w, arg⟩ := instr
  simp only at hr
  rcases hZ : exceptionalHalt vj w s with e | ⟨s₁, c⟩
  · rw [hZ] at hr; cases hr
  · rw [hZ] at hr
    simp only [bind, Except.bind] at hr
    rcases hstep : step n c (some (w, arg)) s₁ with e | s₂
    · rw [hstep] at hr; cases hr
    · rw [hstep] at hr
      have hg := step_gas_le_of_bound hS hZ hstep
      simp only at hr
      split at hr
      · exact le_trans (hX _ _ _ hr) hg
      · split at hr <;> cases hr <;> simpa [xResultGas] using hg

/-! ## All gas bounds, at every fuel -/

theorem allGasBounds (n : ℕ) :
    XGasBound n ∧ ΞGasBound n ∧ ΘGasBound n ∧ ΛGasBound n ∧ CallGasBound n ∧ StepGasBound n := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro _ _ _ h; cases h
    · intro _ _ _ _ _ _ _ _ _ h; cases h
    · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h; cases h
    · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h; cases h
    · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h; cases h
    · intro _ _ _ _ _ _ _ _ h; cases h
  | succ n ih =>
    obtain ⟨hX, hΞ, hΘ, hΛ, hC, hS⟩ := ih
    exact ⟨xGasBound_succ hS hX, ξGasBound_succ hX, θGasBound_succ hΞ, lambdaGasBound_succ hΞ,
      callGasBound_succ hΘ, stepGasBound_succ hC hΛ⟩

/-- **K8, gas half (`StepGasSoundZ`), now unconditional**: executing an instruction that `Z`
accepted with charge `c` either deducts at least `c` or strictly lowers the gas — including the six
instructions that open a nested frame. -/
theorem stepGasSoundZ : StepGasSoundZ := fun f => (allGasBounds f).2.2.2.2.2

/-- **A nested message call returns at most the gas it was given** (`Θ`, any fuel). -/
theorem Θ_gasLeft_le {f : ℕ} {bvh cA gbh bl σ σ₀ A s o r c} {g : UInt256} {p v v' d e H w res}
    (h : Θ f bvh cA gbh bl σ σ₀ A s o r c g p v v' d e H w = .ok res) :
    res.gasLeft.toNat ≤ g.toNat :=
  (allGasBounds f).2.2.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h

/-- **A contract creation returns at most the gas it was given** (`Λ`, any fuel). -/
theorem Lambda_gasLeft_le {f : ℕ} {bvh cA gbh bl σ σ₀ A s o} {g : UInt256} {p v i e ζ H w res}
    (h : Lambda f bvh cA gbh bl σ σ₀ A s o g p v i e ζ H w = .ok res) :
    res.gasLeft.toNat ≤ g.toNat :=
  (allGasBounds f).2.2.2.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h

/-- **Code execution returns at most the gas it was given** (`Ξ`, any fuel). -/
theorem Ξ_gas_le {f : ℕ} {cA gbh bl σ σ₀} {g : UInt256} {A I r}
    (h : Ξ f cA gbh bl σ σ₀ g A I = .ok r) : ξResultGas r ≤ g.toNat :=
  (allGasBounds f).2.1 _ _ _ _ _ _ _ _ _ h

/-- **`X` never hands back more gas than it started with** (any fuel). -/
theorem X_gas_le {f : ℕ} {vj : Array UInt256} {s : State} {r : ExecutionResult State}
    (h : X f vj s = .ok r) : xResultGas r ≤ s.gasAvailable.toNat :=
  (allGasBounds f).1 _ _ _ h

end EVM

end EvmYul
