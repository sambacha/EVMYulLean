import EvmYul.Chain.Semantics

/-!
# The Ethereum execution profile

This profile must reproduce the pre-existing behaviour of the model exactly: the
conformance suite is the regression test for the whole refactor (RFC §20.12, §28 PR 1).
Every constant below is the value that was previously hardcoded in the interpreter:

* chain id `1` (`EvmYul.chainId`);
* `MAX_CODE_SIZE = 24576` (EIP-170) and `MAX_INIT_CODE_SIZE = 49152` (EIP-3860);
* `NUMBER`/`COINBASE`/`PREVRANDAO` read the execution header.
-/

namespace EvmYul

namespace Chain

/-- Ethereum mainnet configuration. -/
def ethereumMainnetConfig : ChainConfig where
  name := "Ethereum"
  chainId := 1
  arbOSVersion := none
  maxCodeSize := 24576
  maxInitCodeSize := 49152
  nativeToken := .ETH
  blockContext := .ethereum

/-- Ethereum mainnet semantics. -/
def ethereumMainnet : ChainSemantics :=
  ChainSemantics.ofConfig ethereumMainnetConfig ethereumPrecompiles

instance : Inhabited ChainSemantics := ⟨ethereumMainnet⟩

/-- The Ethereum profile keeps the chain id the model used before the refactor. -/
theorem ethereumMainnet_chainId : ethereumMainnet.chainIdWord = .ofNat EvmYul.chainId := rfl

/-- The Ethereum profile keeps the EIP-170 / EIP-3860 limits. -/
theorem ethereumMainnet_limits :
    ethereumMainnet.maxCodeSize = 24576 ∧ ethereumMainnet.maxInitCodeSize = 49152 :=
  ⟨rfl, rfl⟩

/-- The Ethereum profile reads block context straight from the header. -/
theorem ethereumMainnet_blockContext (e : ChainEnv) :
    ethereumMainnet.blockNumber e = .ofNat e.header.number ∧
    ethereumMainnet.coinbase e = e.header.beneficiary ∧
    ethereumMainnet.prevRandao e = e.header.prevRandao ∧
    ethereumMainnet.timestamp e = .ofNat e.header.timestamp ∧
    ethereumMainnet.gasPrice e = .ofNat e.gasPrice :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The Ethereum profile is not an ArbOS profile, so every `ChainEnv` is well formed. -/
theorem ethereumMainnet_wellFormed (e : ChainEnv) : ethereumMainnet.wellFormedEnv e := by
  intro h
  exact absurd h (by decide)

end Chain

end EvmYul
