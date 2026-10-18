module

public import Mathlib.Data.Nat.Log

public import EvmYul.EVM.State
public import EvmYul.State.BasicOps
public import EvmYul.MachineStateOps
public import EvmYul.EVM.Gas.Constants
public section

namespace EvmYul

namespace EVM

/-!
# Gas costs (Yellow Paper, Appendix G and H.1)

The instruction fee groups `W_*`, the dynamic cost components `C_*`, the per-instruction cost `C'`,
the memory-expansion cost and the intrinsic transaction cost `g₀`. The constants they are built from
are in `EvmYul/EVM/Gas/Constants.lean`.
-/

namespace InstructionGasGroups

/-- `W_zero`: instructions that cost `G_zero` (nothing). -/
@[expose] def Wzero : List (Operation .EVM) := [.STOP, .RETURN, .REVERT]

/-- `W_base`: instructions that cost `G_base`. -/
@[expose] def Wbase : List (Operation .EVM) := [
  .ADDRESS, .ORIGIN, .CALLER, .CALLVALUE, .CALLDATASIZE, .CODESIZE, .GASPRICE, .COINBASE,
  .TIMESTAMP, .NUMBER, .PREVRANDAO, .GASLIMIT, .CHAINID, .RETURNDATASIZE, .POP, .PC, .MSIZE, .GAS,
  .BASEFEE, .BLOBBASEFEE, .PUSH0]

/-- `W_verylow`: instructions that cost `G_verylow`, including PUSH1..32, DUP and SWAP. -/
@[expose] def Wverylow : List (Operation .EVM) := [
  .ADD, .SUB, .NOT, .LT, .GT, .SLT, .SGT, .EQ, .ISZERO, .AND, .OR, .XOR, .BYTE, .SHL, .SHR, .SAR,
  .CALLDATALOAD, .MLOAD, .MSTORE, .MSTORE8
  ] ++ pushInstrsWithoutZero
    ++ dupInstrs
    ++ swapInstrs
  where
    /-- PUSH1 … PUSH32 (PUSH0 is in `W_base`). -/
    pushInstrsWithoutZero : List (Operation .EVM) := [
      .PUSH1, .PUSH2, .PUSH3, .PUSH4, .PUSH5,
      .PUSH6, .PUSH7, .PUSH8, .PUSH9, .PUSH10,
      .PUSH11, .PUSH12, .PUSH13, .PUSH14, .PUSH15,
      .PUSH16, .PUSH17, .PUSH18, .PUSH19, .PUSH20,
      .PUSH21, .PUSH22, .PUSH23, .PUSH24, .PUSH25,
      .PUSH26, .PUSH27, .PUSH28, .PUSH29, .PUSH30,
      .PUSH31, .PUSH32
    ]
    /-- DUP1 … DUP16. -/
    dupInstrs : List (Operation .EVM) := [
      .DUP1, .DUP2, .DUP3, .DUP4, .DUP5,
      .DUP6, .DUP7, .DUP8, .DUP9, .DUP10,
      .DUP11, .DUP12, .DUP13, .DUP14, .DUP15,
      .DUP16
    ]
    /-- SWAP1 … SWAP16. -/
    swapInstrs : List (Operation .EVM) := [
      .SWAP1, .SWAP2, .SWAP3, .SWAP4, .SWAP5,
      .SWAP6, .SWAP7, .SWAP8, .SWAP9, .SWAP10,
      .SWAP11, .SWAP12, .SWAP13, .SWAP14, .SWAP15,
      .SWAP16
    ]

/-- `W_low`: instructions that cost `G_low`. -/
@[expose] def Wlow : List (Operation .EVM) := [
  .MUL, .DIV, .SDIV, .MOD, .SMOD, .SIGNEXTEND, .SELFBALANCE
]

/-- `W_mid`: instructions that cost `G_mid`. -/
@[expose] def Wmid : List (Operation .EVM) := [
  .ADDMOD, .MULMOD, .JUMP
]

/-- `W_high`: instructions that cost `G_high`. -/
@[expose] def Whigh : List (Operation .EVM) := [
  .JUMPI
]

/-- `W_copy`: copy instructions, costing `G_verylow + G_copy · ⌈size / 32⌉`. -/
@[expose] def Wcopy : List (Operation .EVM) := [
  .CALLDATACOPY, .CODECOPY, .RETURNDATACOPY, .MCOPY
]

/-- `W_call`: the message-call instructions, priced by `Ccall`. -/
@[expose] def Wcall : List (Operation .EVM) := [
  .CALL, .CALLCODE, .DELEGATECALL, .STATICCALL
]

/-- `W_extaccount`: instructions that read another account, priced by `Caccess`. -/
@[expose] def Wextaccount : List (Operation .EVM) := [
  .BALANCE, .EXTCODESIZE, .EXTCODEHASH
]

end InstructionGasGroups

section Gas

open GasConstants InstructionGasGroups

/--
YP (328): memory cost of `a` active 32-byte words, `G_memory · a + ⌊a² / 512⌋`. The expansion
cost of an instruction is the difference of `Cₘ` after and before it.
-/
@[expose] def Cₘ (a : UInt256) : ℕ :=
  let a : ℕ := a.toNat
  Gmemory * a + ((a * a) / QuadraticCeofficient)
  where
  /-- Divisor of the quadratic term of the memory cost. -/
  QuadraticCeofficient : ℕ := 512

/--
NB we currently run in 'this' monad because of the way YP interleaves the definition of `C`
with the definition of `C_<>` functions that are described inline along with their operations.

It would be worth restructing everything to obtain cleaner separation of concerns.
-/
@[expose] def Csstore (s : EVM.State) : ℕ :=
  let { stack := μₛ, accountMap := σ, σ₀ := σ₀, executionEnv.codeOwner := Iₐ, .. } := s
  let { storage := σ_Iₐ, .. } := σ.get! Iₐ
  let storeAddr := μₛ[0]!
  let v₀ :=
    match σ₀.get? Iₐ with
      | none => ⟨0⟩
      | some acc => acc.storage.getD storeAddr ⟨0⟩
  let v := σ_Iₐ.getD storeAddr ⟨0⟩
  let v' := μₛ[1]!
  let loadComponent :=
    if s.substate.accessedStorageKeys.contains (Iₐ, storeAddr) then
      0
    else
      Gcoldsload
  let storeComponent := if v = v' || v₀ ≠ v             then Gwarmaccess else
                        if v ≠ v' && v₀ = v && v₀ = ⟨0⟩ then Gsset else
                        /- v ≠ v' ∧ v₀ = v ∧ v₀ ≠ 0 -/     Gsreset
  loadComponent + storeComponent

/-- Cost of TSTORE (EIP-1153): always `G_warmaccess`; transient storage is never cold. -/
@[expose] def Ctstore : ℕ :=
  let loadComponent := 0
  let storeComponent := Gwarmaccess
  loadComponent + storeComponent

/--
YP (328): account-access cost: `G_warmaccess` if `a` is in the accessed-accounts set of `A`,
`G_coldaccountaccess` otherwise (EIP-2929).
-/
@[expose] def Caccess (a : AccountAddress) (A : Substate) : ℕ :=
  if A.accessedAccounts.contains a
  then Gwarmaccess
  else Gcoldaccountaccess

/--
CHECK -
In YP we have `Cselfdestruct(σ, μ)`; if we were to compute `Aₐ` that we need, we would need an
address in `σ` - is this address supposed to be obvious?
CURRENT SOLUTION -
We take `EVM.State`.
-/
@[expose] def Cselfdestruct (s : EVM.State) : ℕ :=
  let r := AccountAddress.ofUInt256 s.stack[0]!
  let { substate.accessedAccounts := Aₐ, accountMap := σ, executionEnv.codeOwner := Iₐ, .. } := s
  let c_cold := if Aₐ.contains r then 0 else Gcoldaccountaccess
  let c_new :=
    if State.dead σ r ∧ (σ.get? Iₐ |>.option ⟨0⟩ (·.balance)) ≠ ⟨0⟩ then
      Gnewaccount
    else 0
  Gselfdestruct + c_cold + c_new

/--
NB Assumes stack coherency.
-/
@[expose] def Csload (μₛ : Stack UInt256) (A : Substate) (I : ExecutionEnv .EVM) : ℕ :=
  if A.accessedStorageKeys.contains (I.codeOwner, μₛ[0]!)
  then Gwarmaccess
  else Gcoldsload

/-- Cost of TLOAD (EIP-1153): always `G_warmaccess`. -/
@[expose] def Ctload : ℕ :=
  Gwarmaccess

/--
YP (331): "all but one 64th" (EIP-150), the most gas a call or create may pass on out of `n`.
-/
@[expose] def L (n : ℕ) : ℕ := n - (n / 64)

/-- `C_NEW`: `G_newaccount` if the call transfers value to a dead account `t`, otherwise 0. -/
@[expose] def Cnew (t : AccountAddress) (val : UInt256) (σ : AccountMap .EVM) : ℕ :=
  if EvmYul.State.dead σ t && val != ⟨0⟩ then Gnewaccount else 0

/-- `C_XFER`: `G_callvalue` for a value-transferring call, otherwise 0. -/
@[expose] def Cxfer (val : UInt256) : ℕ :=
  if val != ⟨0⟩ then Gcallvalue else 0

/-- `C_EXTRA`: the part of a call's cost not forwarded to the callee: access cost of the target
`t`, value transfer, and account creation for the recipient `r`. -/
@[expose] def Cextra (t r : AccountAddress) (val : UInt256) (σ : AccountMap .EVM) (A : Substate) : ℕ :=
  Caccess t A + Cxfer val + Cnew r val σ

/--
`C_GASCAP`: gas forwarded to the callee (before the stipend). If the remaining gas covers
`C_EXTRA`, the requested `g` capped by `L(μ_g − C_EXTRA)`; otherwise the request itself (the
call is then out of gas anyway, since `C_CALL = g + C_EXTRA > μ_g`).
-/
@[expose] def Cgascap (t r : AccountAddress) (val g : UInt256) (σ : AccountMap .EVM) (μ : MachineState) (A : Substate) :=
  if μ.gasAvailable.toNat >= Cextra t r val σ A then
    min (L <| (μ.gasAvailable.toNat - Cextra t r val σ A)) g.toNat
  else
    g.toNat

/-- `C_CALLGAS`: gas the callee actually receives: `C_GASCAP`, plus `G_callstipend` for a
value-transferring call. -/
@[expose] def Ccallgas (t r : AccountAddress) (val g : UInt256) (σ : AccountMap .EVM) (μ : MachineState) (A : Substate) : ℕ :=
  match val with
    | ⟨0⟩ => Cgascap t r val g σ μ A
    | _ => Cgascap t r val g σ μ A + GasConstants.Gcallstipend

/--
`C_CALL`: the total charge of a message call, `C_GASCAP + C_EXTRA`.

NB Assumes stack coherence.
-/
@[expose] def Ccall (t r : AccountAddress) (val g : UInt256) (σ : AccountMap .EVM) (μ : MachineState) (A : Substate) : ℕ :=
  Cgascap t r val g σ μ A + Cextra t r val σ A

/--
YP (65), EIP-3860: initcode cost, `G_initcodeword` per 32-byte word of `x` bytes of initcode.
-/
@[expose] def R (x : ℕ) : ℕ := Ginitcodeword * ((x + 31) / 32)

/--
YP: intrinsic gas `g₀` of a transaction, paid before execution: data bytes, contract
creation (with initcode words), the base `G_transaction`, and the access list.
-/
@[expose] def intrinsicGas (T : Transaction) : ℕ :=
  let g₀_data :=
    T.base.data.foldl
      (λ acc b ↦
        acc +
          if b == 0 then
            GasConstants.Gtxdatazero
          else GasConstants.Gtxdatanonzero
      )
      0
  let g₀_create : ℕ :=
    if T.base.recipient == none then
      GasConstants.Gtxcreate + R (T.base.data.size)
    else 0

  let g₀_accessList : ℕ :=
    T.getAccessList.foldl
      (λ acc (_, s) ↦
        acc + GasConstants.Gaccesslistaddress + s.size * GasConstants.Gaccessliststorage
      )
      0
  g₀_data + g₀_create + GasConstants.Gtransaction + g₀_accessList

/--
H.1. Gas Cost - the third summand.

NB Stack accesses are assumed guarded here and we access with `!`.
This is for keeping in sync with the way the YP is structures, at least for the time being.
-/
@[expose] def C' (s : State) (instr : Operation .EVM) : ℕ :=
  let { accountMap := σ, stack := μₛ, substate := A, toMachineState := μ, executionEnv := I, ..} := s
  match instr with
    | .SSTORE => Csstore s
    | .TSTORE => Ctstore
    | .EXP => let μ₁ := μₛ[1]!; if μ₁ == ⟨0⟩ then Gexp else Gexp + Gexpbyte * (1 + Nat.log 256 μ₁.toNat) -- `Nat.log` floors, so the factor is the byte length of `μ₁` (`ExpByteLength.C'_EXP`)
    | .EXTCODECOPY => Caccess (AccountAddress.ofUInt256 μₛ[0]!) A + Gcopy * ((μₛ[3]!.toNat + 31) / 32)
    | .LOG0 => Glog + Glogdata * μₛ[1]!.toNat
    | .LOG1 => Glog + Glogdata * μₛ[1]!.toNat +     Glogtopic
    | .LOG2 => Glog + Glogdata * μₛ[1]!.toNat + 2 * Glogtopic
    | .LOG3 => Glog + Glogdata * μₛ[1]!.toNat + 3 * Glogtopic
    | .LOG4 => Glog + Glogdata * μₛ[1]!.toNat + 4 * Glogtopic
    | .SELFDESTRUCT => Cselfdestruct s
    | .CREATE => Gcreate + R μₛ[2]!.toNat
    | .CREATE2 => let μ₂ := μₛ[2]!; Gcreate + Gkeccak256word * ((μ₂.toNat + 31) / 32) + R μ₂.toNat
    | .KECCAK256 => Gkeccak256 + Gkeccak256word * ((μₛ[1]!.toNat + 31) / 32)
    | .JUMPDEST => Gjumpdest
    | .SLOAD => Csload μₛ A I
    | .TLOAD => Ctload
    | .BLOCKHASH => Gblockhash
    /-
      By `μₛ[2]` the YP means the value that is to be transferred,
      not what happens to be on the stack at index 2. Therefore it is 0 for
      `DELEGATECALL` and `STATICCALL`.
    -/
    | .CALL =>         Ccall (AccountAddress.ofUInt256 μₛ[1]!) (AccountAddress.ofUInt256 μₛ[1]!) μₛ[2]! μₛ[0]! σ μ A
    | .CALLCODE =>     Ccall (AccountAddress.ofUInt256 μₛ[1]!)          s.executionEnv.codeOwner μₛ[2]! μₛ[0]! σ μ A
    | .DELEGATECALL => Ccall (AccountAddress.ofUInt256 μₛ[1]!)          s.executionEnv.codeOwner    ⟨0⟩ μₛ[0]! σ μ A
    | .STATICCALL =>   Ccall (AccountAddress.ofUInt256 μₛ[1]!) (AccountAddress.ofUInt256 μₛ[1]!)    ⟨0⟩ μₛ[0]! σ μ A
    | .BLOBHASH => HASH_OPCODE_GAS
    | w =>
      if w ∈ Wcopy then Gverylow + Gcopy * ((μₛ[2]!.toNat + 31) / 32) else
      if w ∈ Wextaccount then Caccess (AccountAddress.ofUInt256 μₛ[0]!) A else
      if w ∈ Wzero then Gzero else
      if w ∈ Wbase then Gbase else
      if w ∈ Wverylow then Gverylow else
      if w ∈ Wlow then Glow else
      if w ∈ Wmid then Gmid else
      if w ∈ Whigh then Ghigh else
      0

/--
H.1. Gas Cost

NB this differs ever so slightly from how it is defined in the YP, please refer to
`EVM/Semantics.lean`, function `X` for further discussion.
-/

@[expose] def memoryExpansionCost (s : EVM.State) (instr : Operation .EVM) : ℕ :=
  Cₘ μᵢ' - Cₘ s.toMachineState.activeWords
 where
  /-- Active words after the instruction (YP `μ'ᵢ`), from the operands' memory ranges. -/
  μᵢ' : UInt256 :=
    match instr with
      | .KECCAK256 => .ofNat <| MachineState.M s.toMachineState.activeWords.toNat s.stack[0]!.toNat s.stack[1]!.toNat
      | .CALLDATACOPY | .CODECOPY => .ofNat <| MachineState.M s.toMachineState.activeWords.toNat s.stack[0]!.toNat s.stack[2]!.toNat
      | .MCOPY => .ofNat <| MachineState.M s.toMachineState.activeWords.toNat (max s.stack[0]!.toNat s.stack[1]!.toNat) s.stack[2]!.toNat
      | .EXTCODECOPY => .ofNat <| MachineState.M s.toMachineState.activeWords.toNat s.stack[1]!.toNat s.stack[3]!.toNat
      | .RETURNDATACOPY => .ofNat <| MachineState.M s.toMachineState.activeWords.toNat s.stack[0]!.toNat s.stack[2]!.toNat
      | .MLOAD | .MSTORE => .ofNat <| MachineState.M s.toMachineState.activeWords.toNat s.stack[0]!.toNat 32
      | .MSTORE8 => .ofNat <| MachineState.M s.toMachineState.activeWords.toNat s.stack[0]!.toNat 1
      | .LOG0 | .LOG1 | .LOG2 | .LOG3 | .LOG4 =>
        .ofNat <| MachineState.M s.toMachineState.activeWords.toNat s.stack[0]!.toNat s.stack[1]!.toNat
      | .CREATE | .CREATE2 => .ofNat <| MachineState.M s.toMachineState.activeWords.toNat s.stack[1]!.toNat s.stack[2]!.toNat
      | .CALL | .CALLCODE =>
        let m : ℕ := MachineState.M s.toMachineState.activeWords.toNat s.stack[3]!.toNat s.stack[4]!.toNat
        .ofNat <| MachineState.M m s.stack[5]!.toNat s.stack[6]!.toNat
      | .DELEGATECALL | .STATICCALL =>
        let m : ℕ:= MachineState.M s.toMachineState.activeWords.toNat s.stack[2]!.toNat s.stack[3]!.toNat
        .ofNat <| MachineState.M m s.stack[4]!.toNat s.stack[5]!.toNat
      | .RETURN | .REVERT => .ofNat <| MachineState.M s.toMachineState.activeWords.toNat s.stack[0]!.toNat s.stack[1]!.toNat
      | _ => s.toMachineState.activeWords

end Gas

end EVM

end EvmYul
