module

public import EvmYul.State.SubstateOps
public import EvmYul.State.AccountOps

public import EvmYul.State.AccountMap
public import EvmYul.State.Basic
public import EvmYul.Wheels

/-!
# Operations on the world state

Account lookup and update, the accessed-account and accessed-storage-key sets (EIP-2929), dead
accounts, and the world-state reads and writes (balance, nonce, code, storage, transient storage,
block data) that both interpreters use.
-/
public section

namespace EvmYul

namespace State

@[expose] def addAccessedAccount {τ} (self : State τ) (addr : AccountAddress) : State τ :=
  { self with substate := self.substate.addAccessedAccount addr }

@[expose] def addAccessedStorageKey {τ} (self : State τ) (sk : AccountAddress × UInt256) : State τ :=
  { self with substate := self.substate.addAccessedStorageKey sk }

/--
DEAD(σ, a). Section 4.1., equation 15.
-/
@[expose] def dead {τ} (σ : AccountMap τ) (addr : AccountAddress) : Bool :=
  σ.get? addr |>.option True Account.emptyAccount

def accountExists {τ} (self : State τ) (addr : AccountAddress) : Bool := self.accountMap.get? addr |>.isSome

@[expose] def lookupAccount {τ} (self : State τ) (addr : AccountAddress) : Option (Account τ) :=
  self.accountMap.get? addr

@[expose] def updateAccount {τ} (addr : AccountAddress) (act : Account τ) (self : State τ) : State τ :=
  { self with accountMap := self.accountMap.insert addr act }

@[expose] def setAccount {τ} (self : State τ) (addr : AccountAddress) (acc : Account τ) : State τ :=
  { self with accountMap := self.accountMap.insert addr acc }

def setSelfAccount {τ} (self : State τ) (acc : Account τ := default) : State τ :=
  self.setAccount self.executionEnv.codeOwner acc

def updateAccount! {τ} (self : State τ) (addr : AccountAddress) (f : Account τ → Account τ) : State τ :=
  let acc! := self.lookupAccount addr |>.getD default
  self.setAccount addr (f acc!)

def updateSelfAccount! {τ} (self : State τ) : (Account τ → Account τ) → State τ :=
  self.updateAccount! self.executionEnv.codeOwner

@[expose] def balance {τ} (self : State τ) (k : UInt256) : State τ × UInt256 :=
  let addr := AccountAddress.ofUInt256 k
  (self.addAccessedAccount addr, self.accountMap.get? addr |>.elim ⟨0⟩ (·.balance))

def initialiseAccount (addr : AccountAddress) (self : State .EVM) : State .EVM :=
  if self.accountExists addr then self else self.updateAccount addr default

@[expose] def calldataload {τ} (self : State τ) (v : UInt256) : UInt256 :=
  uInt256OfByteArray <| self.executionEnv.calldata.readBytes v.toNat 32

def setNonce! {τ} (self : State τ) (addr : AccountAddress) (nonce : UInt256) : State τ :=
  self.updateAccount! addr (λ acc ↦ { acc with nonce := nonce })

def setSelfNonce! {τ} (self : State τ) (nonce : UInt256) : State τ :=
  self.setNonce! self.executionEnv.codeOwner nonce

def selfStorage! {τ} (self : State τ) : Storage :=
  self.lookupAccount self.executionEnv.codeOwner |>.getD default |>.storage

section CodeCopy

@[expose] def extCodeSize (self : State .EVM) (a : UInt256) : State .EVM × UInt256 :=
  let addr := AccountAddress.ofUInt256 a
  let s := self.lookupAccount addr |>.option ⟨0⟩ (.ofNat ∘ ByteArray.size ∘ (·.code))
  (self.addAccessedAccount addr, s)

@[expose] def extCodeHash (self : State .EVM) (v : UInt256) : State .EVM × UInt256 :=
  let addr := AccountAddress.ofUInt256 v
  let newState := self.addAccessedAccount addr
  if dead self.accountMap addr then (newState, ⟨0⟩) else
  let r := self.lookupAccount (AccountAddress.ofUInt256 v) |>.option ⟨0⟩ Account.codeHash
  (newState, r)

end CodeCopy

section Blocks

@[expose] def blockHash {τ} (self : State τ) (blockNumber : UInt256) : UInt256 :=
  let v := self.executionEnv.header.number
  if v ≤ blockNumber.toNat || blockNumber.toNat + 256 < v then ⟨0⟩
  else
    let hashes := self.blockHashes
    hashes.getD blockNumber.toNat ⟨0⟩

@[expose] def coinBase {τ} (self : State τ) : AccountAddress :=
  self.executionEnv.header.beneficiary

@[expose] def timeStamp {τ} (self : State τ) : UInt256 :=
  .ofNat self.executionEnv.header.timestamp

@[expose] def number {τ} (self : State τ) : UInt256 :=
  .ofNat self.executionEnv.header.number

def difficulty {τ} (self : State τ) : UInt256 :=
  .ofNat self.executionEnv.header.difficulty

@[expose] def gasLimit {τ} (self : State τ) : UInt256 :=
  .ofNat self.executionEnv.header.gasLimit

@[expose] def chainId {τ} (_ : State τ) : UInt256 := .ofNat EvmYul.chainId

@[expose] def selfbalance {τ} (self : State τ) : UInt256 :=
  Std.TreeMap.get? self.accountMap self.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance)

def setCode (self : State .EVM) (code : ByteArray) : State .EVM :=
  { self with executionEnv.code := code }

end Blocks

section Storage

def setStorage! {τ} (self : State τ) (addr : AccountAddress) (strg : Storage) : State τ :=
  self.updateAccount! addr (λ acc ↦ { acc with storage := strg })

def setSelfStorage! {τ} (self : State τ) : Storage → State τ :=
  self.setStorage! self.executionEnv.codeOwner

@[expose] def sload {τ} (self : State τ) (spos : UInt256) : State τ × UInt256 :=
  let Iₐ := self.executionEnv.codeOwner
  let v := self.lookupAccount Iₐ |>.option ⟨0⟩ (Account.lookupStorage (k := spos))
  let state' := self.addAccessedStorageKey (Iₐ, spos)
  (state', v)

@[expose] def tload {τ} (self : State τ) (spos : UInt256) : State τ × UInt256 :=
  let Iₐ := self.executionEnv.codeOwner
  let v := self.lookupAccount Iₐ |>.option ⟨0⟩ (Account.lookupTransientStorage (k := spos))
  (self, v)

@[expose] def tstore {τ} (self : State τ) (spos sval : UInt256) : State τ :=
  let Iₐ := self.executionEnv.codeOwner
  self.lookupAccount Iₐ |>.option self λ acc ↦
    self.updateAccount Iₐ (acc.updateTransientStorage spos sval)

end Storage

/--
The effect of `SELFDESTRUCT` with beneficiary `r` on the world state, after EIP-6780 (Cancun).
Shared by the EVM and the Yul case of `EvmYul.step`, so that the two cannot drift apart.

Let `Iₐ` be the code owner. The beneficiary `r` becomes accessed (EIP-2929), and the whole balance
of `Iₐ` moves to `r`.
* If `Iₐ` was created in this transaction (`Iₐ ∈ createdAccounts`), `Iₐ` joins the self-destruct
  set, so it is deleted at the end of the transaction; if `r = Iₐ`, its Ether is burnt.
* Otherwise the account survives, the self-destruct set is unchanged, and `r = Iₐ` changes no
  balance at all.
-/
@[expose] def selfDestruct {τ} (self : State τ) (r : AccountAddress) : State τ :=
  let Iₐ := self.executionEnv.codeOwner
  let createdHere := self.createdAccounts.contains Iₐ
  let A' : Substate :=
    { self.substate with
        selfDestructSet :=
          if createdHere then self.substate.selfDestructSet.insert Iₐ
          else self.substate.selfDestructSet
        accessedAccounts := self.substate.accessedAccounts.insert r }
  let accountMap' :=
    match self.lookupAccount Iₐ with
      | none => self.accountMap
      | some σ_Iₐ =>
        match self.lookupAccount r with
          | none =>
            if σ_Iₐ.balance == ⟨0⟩ then
              self.accountMap
            else
              self.accountMap.insert r {(default : Account τ) with balance := σ_Iₐ.balance}
                |>.insert Iₐ {σ_Iₐ with balance := ⟨0⟩}
          | some σ_r =>
            if r ≠ Iₐ then
              self.accountMap.insert r {σ_r with balance := σ_r.balance + σ_Iₐ.balance}
                |>.insert Iₐ {σ_Iₐ with balance := ⟨0⟩}
            else if createdHere then
              -- Created in this transaction and sending to itself: the Ether is burnt.
              self.accountMap.insert r {σ_r with balance := ⟨0⟩}
                |>.insert Iₐ {σ_Iₐ with balance := ⟨0⟩}
            else
              -- Not created in this transaction and sending to itself: no net change (EIP-6780).
              self.accountMap
  { self with accountMap := accountMap', substate := A' }

end State

end EvmYul
