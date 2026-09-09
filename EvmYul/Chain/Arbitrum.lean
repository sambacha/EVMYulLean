import EvmYul.Chain.Ethereum

/-!
# Generic Arbitrum (Nitro) execution profile

A Nitro chain is the generic EVM plus:

* an ArbOS version;
* `block.number` derived from the L1 context rather than from the L2 header height
  (the L2 height is exposed separately through `ArbSys.arbBlockNumber`);
* the ArbOS system contracts on top of the Ethereum precompiles;
* chain-configured code-size limits.

`Robinhood` is built from this by supplying identity and limits, so no Robinhood-specific
conditional appears anywhere in the interpreter (RFC §37).
-/

namespace EvmYul

namespace Chain

/--
`PREVRANDAO` under Nitro.

Nitro does not have beacon-chain randomness; it reports a fixed value.  The constant is
part of the *configuration* so that it can be corrected per ArbOS version without touching
opcode semantics (RFC §8.2), and it is surfaced in the support matrix as a value that must
be confirmed against the deployed ArbOS configuration.
-/
def nitroPrevRandao : UInt256 := ⟨1⟩

/-- Build a Nitro chain configuration. -/
def nitroConfig
    (name : String) (chainId : UInt64) (arbOS : ArbOS.Version)
    (maxCodeSize maxInitCodeSize : Nat)
    (schedule : List ArbOS.ProtocolUpgrade := []) : ChainConfig where
  name := name
  chainId := chainId
  arbOSVersion := some arbOS
  arbOSSchedule := schedule
  maxCodeSize := maxCodeSize
  maxInitCodeSize := maxInitCodeSize
  nativeToken := .ETH
  blockContext :=
    { blockNumber := .l1BlockNumber
      -- On Nitro the header's beneficiary *is* the network fee account, so reading it is
      -- correct for replayed headers; a chain that publishes a fixed fee account can
      -- override this with `CoinbaseSource.feeAccount`.
      coinbase := .headerBeneficiary
      randao := .constant nitroPrevRandao }

/-- Semantics of a Nitro chain: Ethereum precompiles extended with ArbOS system contracts. -/
def nitroSemantics (c : ChainConfig) : ChainSemantics :=
  ChainSemantics.ofConfig c arbitrumPrecompiles

/-- A Nitro profile is an ArbOS profile. -/
@[simp]
theorem nitroConfig_isArbitrum
    (n : String) (id : UInt64) (v : ArbOS.Version) (mc mic : Nat)
    (s : List ArbOS.ProtocolUpgrade) :
    (nitroConfig n id v mc mic s).isArbitrum = true := rfl

/-- Under a Nitro profile, `NUMBER` reports the L1 block number from ArbOS state. -/
theorem nitro_blockNumber
    (c : ChainConfig) (header : BlockHeader) (gasPrice : Nat) (st : ArbOS.State)
    (n : String) (id : UInt64) (v : ArbOS.Version) (mc mic : Nat)
    (s : List ArbOS.ProtocolUpgrade) (hc : c = nitroConfig n id v mc mic s) :
    (nitroSemantics c).blockNumber ⟨header, gasPrice, some st⟩ = st.l1Context.l1BlockNumber := by
  subst hc
  exact ChainSemantics.blockNumber_l1BlockNumber _ _ _ _ rfl

/-- Under a Nitro profile, `PREVRANDAO` is the configured constant, not header randomness. -/
theorem nitro_prevRandao
    (header : BlockHeader) (gasPrice : Nat) (arbOS : Option ArbOS.State)
    (n : String) (id : UInt64) (v : ArbOS.Version) (mc mic : Nat)
    (s : List ArbOS.ProtocolUpgrade) :
    (nitroSemantics (nitroConfig n id v mc mic s)).prevRandao ⟨header, gasPrice, arbOS⟩
      = nitroPrevRandao := rfl

/-- A Nitro profile routes `0x64` to `ArbSys`. -/
theorem nitro_hasArbSys (c : ChainConfig) :
    ((nitroSemantics c).systemContract? ArbOS.ArbSysAddress).isSome = true := rfl

end Chain

end EvmYul
