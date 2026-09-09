import EvmYul.Chain.Arbitrum

/-!
# Robinhood Chain profiles

Robinhood Chain is an Arbitrum Nitro chain running ArbOS 61, with ETH as its native gas
token, chain id `4663` (mainnet) and `46630` (testnet), and a published node configuration
of 96 KiB maximum deployed code and 192 KiB maximum init code.

Nothing here is a special case in the interpreter: a Robinhood profile is a Nitro profile
with identity and limits filled in (RFC §37).
-/

namespace EvmYul

namespace Robinhood

/-- Robinhood Chain mainnet chain id. -/
def mainnetChainId : UInt64 := 4663

/-- Robinhood Chain testnet chain id. -/
def testnetChainId : UInt64 := 46630

/-- 96 KiB. -/
def maxCodeSize : Nat := 98304

/-- 192 KiB. -/
def maxInitCodeSize : Nat := 196608

/-- Robinhood Chain mainnet configuration. -/
def mainnetConfig : ChainConfig :=
  Chain.nitroConfig "Robinhood Chain" mainnetChainId ArbOS.v61 maxCodeSize maxInitCodeSize

/--
Robinhood Chain testnet configuration.

Only identity is shared with mainnet by construction; rollup addresses and genesis
parameters are deliberately *not* assumed to be shared (RFC §9.2).
-/
def testnetConfig : ChainConfig :=
  { mainnetConfig with
      name := "Robinhood Chain Testnet"
      chainId := testnetChainId }

/-- Robinhood Chain mainnet semantics. -/
def mainnet : ChainSemantics := Chain.nitroSemantics mainnetConfig

/-- Robinhood Chain testnet semantics. -/
def testnet : ChainSemantics := Chain.nitroSemantics testnetConfig

/-! ### Identity (RFC §20.1, vectors A and B) -/

theorem mainnet_chainId : mainnetConfig.chainId = 4663 := rfl
theorem testnet_chainId : testnetConfig.chainId = 46630 := rfl

theorem mainnet_chainIdWord : mainnet.chainIdWord = .ofNat 4663 := rfl
theorem testnet_chainIdWord : testnet.chainIdWord = .ofNat 46630 := rfl

theorem mainnet_arbOS : mainnetConfig.arbOSVersion = some ArbOS.v61 := rfl
theorem testnet_arbOS : testnetConfig.arbOSVersion = some ArbOS.v61 := rfl

/-- Mainnet and testnet are distinct profiles. -/
theorem mainnet_ne_testnet : mainnetConfig ≠ testnetConfig := by decide

/-! ### Limits (RFC §16) -/

theorem mainnet_codeSizeLimits :
    mainnet.maxCodeSize = 98304 ∧ mainnet.maxInitCodeSize = 196608 := ⟨rfl, rfl⟩

theorem testnet_codeSizeLimits :
    testnet.maxCodeSize = 98304 ∧ testnet.maxInitCodeSize = 196608 := ⟨rfl, rfl⟩

/-- The Robinhood limits are strictly larger than Ethereum's. -/
theorem robinhood_limits_gt_ethereum :
    Chain.ethereumMainnet.maxCodeSize < mainnet.maxCodeSize ∧
    Chain.ethereumMainnet.maxInitCodeSize < mainnet.maxInitCodeSize := by
  constructor <;> decide

/-! ### Block context (RFC §8, vector C) -/

/-- Robinhood `block.number` is the L1-derived value carried by ArbOS. -/
theorem mainnet_blockNumber (header : BlockHeader) (gasPrice : Nat) (st : ArbOS.State) :
    mainnet.blockNumber ⟨header, gasPrice, some st⟩ = st.l1Context.l1BlockNumber := rfl

/-- The L2 height is *not* what `block.number` reports; `ArbSys.arbBlockNumber` exposes it. -/
theorem mainnet_blockNumber_ignores_l2
    (header : BlockHeader) (gasPrice : Nat) (st : ArbOS.State) (n : UInt256) :
    mainnet.blockNumber ⟨header, gasPrice, some { st with l2BlockNumber := n }⟩ =
      mainnet.blockNumber ⟨header, gasPrice, some st⟩ := rfl

/-- Robinhood exposes the ArbOS system contracts. -/
theorem mainnet_hasArbSys :
    (mainnet.systemContract? ArbOS.ArbSysAddress).isSome = true := rfl

theorem mainnet_hasArbGasInfo :
    (mainnet.systemContract? ArbOS.ArbGasInfoAddress).isSome = true := rfl

/-- Robinhood keeps the Ethereum precompiles. -/
theorem mainnet_keeps_ethereum_precompiles :
    ∀ a ∈ (List.range 11).tail, mainnet.isPrecompile (AccountAddress.ofNat a) := by
  decide

end Robinhood

end EvmYul
