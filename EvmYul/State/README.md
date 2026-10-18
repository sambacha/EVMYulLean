# `EvmYul/State/`: World state

Accounts, the world state, blocks, transactions, the substate and the execution environment, each as an `X.lean` / `XOps.lean` / `XLemmas.lean` family (Rule 3).

## Files

The library children of this folder (layout check L13 keeps this list complete):

- `Account.lean`: Accounts.
- `AccountOps.lean`: Operations on accounts.
- `Basic.lean`: World state.
- `BasicOps.lean`: Operations on the world state.
- `Block.lean`: Blocks.
- `BlockHeader.lean`: Block headers.
- `ExecutionEnv.lean`: Execution environment.
- `Substate.lean`: Substate.
- `SubstateOps.lean`: Operations on the substate.
- `Transaction.lean`: Transactions.
- `TransactionOps.lean`: Operations on transactions.
- `Withdrawal.lean`: Withdrawals.
- `AccountMap.lean`: Account maps.
- `SubstateLemmas.lean`: Substate interface lemmas (handoff WP-5, PO-9).
- `AccountMapLemmas.lean`: Reasoning principles for the account maps.
