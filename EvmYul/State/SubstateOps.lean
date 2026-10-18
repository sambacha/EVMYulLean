module

public import EvmYul.State.Substate

/-!
# Operations on the substate

Adding an accessed account or storage key (EIP-2929).
-/

public section

namespace EvmYul

namespace Substate

@[expose] def addAccessedAccount (self : Substate) (addr : AccountAddress) : Substate :=
  { self with accessedAccounts := self.accessedAccounts.insert addr }

@[expose] def addAccessedStorageKey (self : Substate) (sk : AccountAddress × UInt256) : Substate :=
  { self with accessedStorageKeys := self.accessedStorageKeys.insert sk }

end Substate

end EvmYul
