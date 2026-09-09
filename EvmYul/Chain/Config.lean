import EvmYul.ArbOS.Version
import EvmYul.ArbOS.State
import EvmYul.State.BlockHeader

/-!
# Chain configuration

A `ChainConfig` is the *data* of an execution profile: identity, protocol version, the
limits it imposes and how it interprets block context.  It carries no functions, so it can
be compared and printed, which is what makes configuration regressions detectable
(RFC §28, PR 2).

`ChainEnv` is the slice of execution state that chain-specific accessors may look at.  It
is independent of the interpreter's `OperationType` (EVM or Yul), and it exposes the
Arbitrum L2 context, because `block.number` under an Arbitrum profile is an L1-derived
value that cannot be computed from an Ethereum header alone (RFC §8.1).
-/

namespace EvmYul

/-- The native (gas) token of a chain. -/
inductive NativeToken where
  | ETH
  | custom (symbol : String)
  deriving DecidableEq, Repr, BEq, Inhabited

/-- What the `NUMBER` opcode reports. -/
inductive BlockNumberSource where
  /-- The execution header's own height (Ethereum). -/
  | headerNumber
  /-- The L1 block number held in ArbOS state (Nitro). -/
  | l1BlockNumber
  deriving DecidableEq, Repr, BEq, Inhabited

/-- What the `COINBASE` opcode reports. -/
inductive CoinbaseSource where
  /-- The header's beneficiary field.  On Nitro this is the network fee account. -/
  | headerBeneficiary
  /-- A fixed fee account configured for the chain. -/
  | feeAccount (address : AccountAddress)
  deriving DecidableEq, Repr, BEq, Inhabited

/--
What the `PREVRANDAO` opcode reports.

Treating an L2 value as beacon-chain randomness would invalidate security analyses
(RFC §32.3), so the profile has to say explicitly which semantics apply.
-/
inductive RandaoSemantics where
  /-- Ethereum: the beacon chain's RANDAO value carried in the header. -/
  | beaconRandao
  /-- A chain-configured constant. -/
  | constant (value : UInt256)
  deriving DecidableEq, Repr, BEq, Inhabited

/-- How a profile interprets the block-context opcodes. -/
structure BlockContextSemantics where
  blockNumber : BlockNumberSource
  coinbase    : CoinbaseSource
  randao      : RandaoSemantics
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Ethereum block-context interpretation. -/
def BlockContextSemantics.ethereum : BlockContextSemantics where
  blockNumber := .headerNumber
  coinbase := .headerBeneficiary
  randao := .beaconRandao

/-- Static configuration of an execution profile. -/
structure ChainConfig where
  name            : String
  chainId         : UInt64
  /-- `none` for a plain Ethereum-style chain; `some v` for a Nitro chain running ArbOS `v`. -/
  arbOSVersion    : Option ArbOS.Version
  /-- Scheduled ArbOS upgrades, used to resolve the version active at a given height. -/
  arbOSSchedule   : List ArbOS.ProtocolUpgrade := []
  /-- EIP-170 style deployed-code limit, in bytes. -/
  maxCodeSize     : Nat
  /-- EIP-3860 style init-code limit, in bytes. -/
  maxInitCodeSize : Nat
  nativeToken     : NativeToken
  blockContext    : BlockContextSemantics := .ethereum
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Whether the profile is a Nitro/ArbOS profile. -/
def ChainConfig.isArbitrum (c : ChainConfig) : Bool := c.arbOSVersion.isSome

/-- The ArbOS version in force at `blockNumber` under this configuration. -/
def ChainConfig.arbOSAt (c : ChainConfig) (blockNumber : Nat) : Option ArbOS.Version :=
  c.arbOSVersion.map (fun base => ArbOS.activeArbOS base c.arbOSSchedule blockNumber)

/--
The execution context visible to chain-specific accessors: the L2 block header, the
effective gas price and — for Nitro profiles — the ArbOS state.
-/
structure ChainEnv where
  header   : BlockHeader
  gasPrice : Nat
  arbOS    : Option ArbOS.State
  deriving Inhabited

end EvmYul
