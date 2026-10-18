module

public import Mathlib.Data.List.Intervals

public import EvmYul.UInt256
public import EvmYul.EVM.State
public import EvmYul.State.AccountOps
public import EvmYul.State.BasicOps
public import EvmYul.EVM.Gas.Constants

/-!
# Operations on the EVM state

Program-counter and stack updates, the lifting of world-state operations to `EVM.State`, and
`SSTORE` (priced by the EVM fee schedule, so it lives here and not in `State/BasicOps`).
-/

public section

namespace EvmYul

namespace EVM

namespace State

section Instructions

@[expose] def incrPC (I : EVM.State) (pcΔ : ℕ := 1) : EVM.State :=
  { I with pc := I.pc + .ofNat pcΔ }

@[expose] def replaceStackAndIncrPC (I : EVM.State) (s : Stack UInt256) (pcΔ : ℕ := 1) : EVM.State :=
  incrPC { I with stack := s } pcΔ

end Instructions

@[expose] def liftMState {m} [Monad m] (f : EvmYul.State .EVM → m (EvmYul.State .EVM)) : EVM.State → m EVM.State :=
  λ s ↦ do pure { s with toState := ← f s.toState }

@[expose] instance {m} [Monad m] : CoeFun (EvmYul.State .EVM → m (EvmYul.State .EVM)) (λ _ ↦ EVM.State → m EVM.State) := ⟨liftMState⟩

@[expose] def liftState (f : EvmYul.State .EVM → EvmYul.State .EVM) : EVM.State → EVM.State :=
  liftMState (m := Id) f

@[expose] instance : CoeFun (EvmYul.State .EVM → EvmYul.State .EVM) (λ _ ↦ EVM.State → EVM.State) := ⟨liftState⟩

@[expose] def initialiseAccount (addr : AccountAddress) : EVM.State → EVM.State :=
  EvmYul.State.initialiseAccount addr

@[expose] def updateAccount (addr : AccountAddress) (act : Account .EVM) : EVM.State → EVM.State :=
  EvmYul.State.updateAccount addr act

@[expose] def isEmpty (self : EVM.State) : Bool := self.toState.accountMap == ∅

end State

end EVM

namespace State

/-- `SSTORE` on the world state: write `sval` at `spos` of the current account's storage, mark the
key accessed and adjust the refund counter by the EIP-2200/EIP-3529 rule. It is generic in `τ` (the
Yul interpreter uses it too) but lives here, not in the root `EvmYul/State/BasicOps.lean`, because the
refund amounts come from the EVM fee schedule (`GasConstants`, `EVM/Gas/Constants.lean`): a root
module importing `EVM/` while `EVM/` imports it would make the two nodes import each other
(`GUIDELINES.md` Rule 6). -/
@[expose] def sstore {τ} (self : State τ) (spos sval : UInt256) : State τ :=
  let Iₐ := self.executionEnv.codeOwner
  let { storage := σ_Iₐ, .. } := self.accountMap.get! Iₐ
  let v₀ :=
    match self.σ₀.get? Iₐ with
      | none => ⟨0⟩
      | some acc => acc.storage.getD spos ⟨0⟩
  let v := σ_Iₐ.getD spos ⟨0⟩
  let v' := sval

  let r_dirtyclear : ℤ :=
    if v₀ ≠ .ofNat 0 && v = .ofNat 0 then - GasConstants.Rsclear else
    if v₀ ≠ .ofNat 0 && v' = .ofNat 0 then GasConstants.Rsclear else
    0

  let r_dirtyreset : ℤ :=
    if v₀ = v' && v₀ = .ofNat 0 then GasConstants.Gsset - GasConstants.Gwarmaccess else
    if v₀ = v' && v₀ ≠ .ofNat 0 then GasConstants.Gsreset - GasConstants.Gwarmaccess else
    0

  let ΔAᵣ : ℤ :=
    if v ≠ v' && v₀ = v && v' = .ofNat 0 then GasConstants.Rsclear else
    if v ≠ v' && v₀ ≠ v then r_dirtyclear + r_dirtyreset else
    0

  let newAᵣ : UInt256 :=
    match ΔAᵣ with
      | .ofNat n => self.substate.refundBalance + .ofNat n
      | .negSucc n => self.substate.refundBalance - .ofNat n - ⟨1⟩
  self.lookupAccount Iₐ |>.option self λ acc ↦
    let self' :=
      self.setAccount Iₐ (acc.updateStorage spos sval)
        |>.addAccessedStorageKey (Iₐ, spos)
    { self' with substate.refundBalance := newAᵣ }

end State

end EvmYul
