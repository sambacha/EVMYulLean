import EvmYul.ArbOS.Version
import EvmYul.ArbOS.Exception
import EvmYul.UInt256
import EvmYul.Wheels

/-!
# ArbOS state

The state model deliberately keeps three contexts apart (RFC §7):

* the Ethereum-style *execution header* of the L2 block (`EvmYul.BlockHeader`);
* the *Arbitrum L2 execution context* (`ArbOSState`);
* the *L1 origin / data-availability context* (`L1Context`).

Only values that are observable through L2 execution are modelled; Nitro internals that
the state transition cannot expose are deliberately absent.
-/

namespace EvmYul

namespace ArbOS

/-- The L1 origin context that ArbOS exposes to L2 execution. -/
structure L1Context where
  /-- The L1 block number that ArbOS currently reports through `block.number`. -/
  l1BlockNumber : UInt256
  /-- The L1 timestamp associated with `l1BlockNumber`. -/
  l1Timestamp   : UInt256
  /-- The L1 base fee estimate used by the data-availability fee model. -/
  l1BaseFee     : UInt256
  /-- The chain id of the settlement layer. -/
  l1ChainId     : UInt256
  deriving DecidableEq, Repr, BEq, Inhabited

/--
The Arbitrum fee state.

The EVM instruction gas model and the Arbitrum transaction fee model are distinct
(RFC §12): `l2BaseFee` prices execution, while `l1DataFee` prices posting the transaction
to the settlement layer.  Keeping them in separate fields is what makes the
"never charge the L1 data fee twice" invariant statable.
-/
structure GasState where
  /-- The L2 base fee (wei per gas) charged for execution. -/
  l2BaseFee              : UInt256
  /-- The current L1 base fee estimate (wei per L1 gas). -/
  l1BaseFeeEstimate      : UInt256
  /-- The L1 data fee already attributed to the transaction in flight (wei). -/
  l1DataFee              : UInt256
  /-- The minimum gas price the chain will accept (wei per gas). -/
  minimumGasPrice        : UInt256
  /-- Fixed L2 charge per transaction, in wei. -/
  perL2Tx                : UInt256
  /-- Charge per byte of L1 calldata, in wei. -/
  perL1CalldataByte      : UInt256
  /-- Charge per storage allocation, in wei. -/
  perStorageAllocation   : UInt256
  /-- Congestion component of the ArbGas price, in wei. -/
  perArbGasCongestion    : UInt256
  /-- The chain's speed limit, in gas per second. -/
  speedLimitPerSecond    : UInt256
  /-- The maximum gas limit a single transaction may request. -/
  maxTxGasLimit          : UInt256
  deriving DecidableEq, Repr, BEq, Inhabited

/-- The total ArbGas price is the base component plus the congestion component. -/
def GasState.perArbGasTotal (g : GasState) : UInt256 :=
  g.l2BaseFee + g.perArbGasCongestion

/-- The lifecycle of a retryable ticket that is observable from L2 (RFC §14.3). -/
inductive RetryableStatus where
  | created
  | redeemable
  | redeemedSuccessfully
  | redeemedFailed
  | expired
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Where an L2 message came from. -/
inductive MessageOrigin where
  /-- An ordinary L2 transaction. -/
  | localOrigin
  /-- A message deposited by an L1 contract; its L2 sender is the *aliased* address. -/
  | l1Contract (address : AccountAddress)
  /-- The redemption of a retryable ticket. -/
  | retryable (id : UInt256)
  | other
  deriving DecidableEq, Repr, BEq, Inhabited

/-- A message delivered from L1 to L2 through the delayed inbox. -/
structure L1ToL2Message where
  origin   : MessageOrigin
  target   : AccountAddress
  value    : UInt256
  data     : ByteArray
  gasLimit : UInt256
  deriving Repr, BEq, Inhabited

/-- A logical L2 → L1 message, as created by `ArbSys.sendTxToL1` / `withdrawEth`. -/
structure L2ToL1Message where
  sender      : AccountAddress
  destination : AccountAddress
  value       : UInt256
  data        : ByteArray
  index       : UInt256
  deriving Repr, BEq, Inhabited

/-- A retryable ticket in the modelled (observable) part of its lifecycle. -/
structure RetryableTicket where
  id          : UInt256
  /-- The L2 sender the redemption will execute as (already aliased when L1-originated). -/
  sender      : AccountAddress
  target      : AccountAddress
  value       : UInt256
  data        : ByteArray
  beneficiary : AccountAddress
  /-- L2 timestamp after which the ticket can no longer be redeemed. -/
  timeout     : UInt256
  status      : RetryableStatus
  deriving Repr, BEq, Inhabited

/--
The ArbOS state exposed to L2 execution.

`l2BlockNumber` is the Arbitrum block height reported by `ArbSys.arbBlockNumber`; it is
*not* what the `NUMBER` opcode returns under an Arbitrum profile — see
`EvmYul.Chain.arbitrumBlockNumber`.
-/
structure State where
  version        : Version
  /-- The L2 block height (`ArbSys.arbBlockNumber`). -/
  l2BlockNumber  : UInt256
  l1Context      : L1Context
  gas            : GasState
  /-- Number of L1 → L2 messages consumed so far. -/
  messageCount   : UInt256
  /-- Append-only stream of L2 → L1 messages created in this execution. -/
  outbox         : Array L2ToL1Message
  /-- Retryable tickets tracked by the model, most recent first. -/
  retryables     : List RetryableTicket
  /-- `true` while executing the top-level call of a transaction. -/
  topLevelCall   : Bool
  /-- `true` when the current caller was aliased on the way in from L1. -/
  callerAliased  : Bool
  deriving Repr, BEq, Inhabited

/-- Append an L2 → L1 message; its index is its position in the (append-only) outbox. -/
def State.pushL2ToL1
    (st : State) (sender destination : AccountAddress) (value : UInt256) (data : ByteArray) :
    State × L2ToL1Message :=
  let msg : L2ToL1Message :=
    { sender, destination, value, data, index := .ofNat st.outbox.size }
  ({ st with outbox := st.outbox.push msg }, msg)

@[simp]
theorem State.pushL2ToL1_index
    (st : State) (s d : AccountAddress) (v : UInt256) (data : ByteArray) :
    (st.pushL2ToL1 s d v data).2.index = .ofNat st.outbox.size := rfl

@[simp]
theorem State.pushL2ToL1_outbox_size
    (st : State) (s d : AccountAddress) (v : UInt256) (data : ByteArray) :
    (st.pushL2ToL1 s d v data).1.outbox.size = st.outbox.size + 1 := by
  simp [State.pushL2ToL1]

/-- Creating an L2 → L1 message never touches the L2 block height or the fee state. -/
@[simp]
theorem State.pushL2ToL1_preserves
    (st : State) (s d : AccountAddress) (v : UInt256) (data : ByteArray) :
    ((st.pushL2ToL1 s d v data).1.l2BlockNumber = st.l2BlockNumber) ∧
    ((st.pushL2ToL1 s d v data).1.gas = st.gas) ∧
    ((st.pushL2ToL1 s d v data).1.l1Context = st.l1Context) :=
  ⟨rfl, rfl, rfl⟩

end ArbOS

end EvmYul
