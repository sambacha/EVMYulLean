module

public import EvmYul.State.Account

public import EvmYul.Maps.StorageMap

public import EvmYul.Pretty

/-!
# Operations on accounts

Storage and transient-storage reads and writes, and emptiness (EIP-161).
-/

public section

namespace EvmYul

namespace Account

@[expose] def lookupStorage {τ} (self : Account τ) (k : UInt256) : UInt256 :=
  self.storage.getD k ⟨0⟩

@[expose] def updateStorage {τ} (self : Account τ) (k v : UInt256) : Account τ :=
  if v == default then
    { self with storage := self.storage.erase k }
  else
    { self with storage := self.storage.insert k v }

@[expose] def lookupTransientStorage {τ} (self : Account τ) (k : UInt256) : UInt256 :=
  self.tstorage.getD k ⟨0⟩

@[expose] def updateTransientStorage {τ} (self : Account τ) (k v : UInt256) : Account τ :=
  if v == default then
    { self with tstorage := self.tstorage.erase k }
  else
    { self with tstorage := self.tstorage.insert k v }

/--
EMPTY(σ, a). Section 4.1., equation 14.
-/
@[expose] def emptyAccount {τ} (self : Account τ) : Bool :=
  match τ with
    | .EVM => self.code.isEmpty ∧ self.nonce = ⟨0⟩ ∧ self.balance = ⟨0⟩
    | .Yul => false -- Yul statements always hold code.

def addBalance {τ} (self : Account τ) (balance : UInt256) : Option (Account τ) :=
  let overflow : Bool := self.balance + balance < self.balance
  if overflow then .none
  else .some { self with balance := self.balance + balance }

def subBalance {τ} (self : Account τ) (balance : UInt256) : Option (Account τ) :=
  let underflow : Bool := self.balance < balance
  if underflow then .none
  else .some { self with balance := self.balance - balance }

end Account

end EvmYul
