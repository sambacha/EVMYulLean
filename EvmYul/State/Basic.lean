module

public import Std.Data.TreeSet
public import Mathlib.Data.Finset.Basic

public import EvmYul.State.ExecutionEnv
public import EvmYul.State.Substate
public import EvmYul.State.Account
public import EvmYul.State.Block
public import EvmYul.State.Substate
public import EvmYul.State.Transaction

public import EvmYul.State.AccountMap
public import EvmYul.UInt256
public import EvmYul.Wheels

/-!
# World state

`State τ`: the account map, the substate, the execution environment, the block data and the
transaction, i.e. `σ` and `A` of the Yellow Paper with their context.
-/

public section

namespace EvmYul

@[expose] section

/--
The `State`. Section 9.3.

- `accountMap`   `σ`
- `substate`     `A`
- `executionEnv` `I`
- `totalGasUsedInBlock` `Υᵍ`
-/
structure State (τ : OperationType) where
  accountMap          : AccountMap τ
  σ₀                  : AccountMap .EVM
  totalGasUsedInBlock : ℕ
  transactionReceipts  : Array TransactionReceipt
  substate            : Substate
  executionEnv        : ExecutionEnv τ
  blocks              : ProcessedBlocks
  genesisBlockHeader  : BlockHeader
  createdAccounts     : Std.TreeSet AccountAddress compare
deriving Inhabited

end

@[expose] def State.blockHashes {τ} (self : State τ) : Array UInt256 :=
  self.blocks.map ProcessedBlock.hash

end EvmYul
