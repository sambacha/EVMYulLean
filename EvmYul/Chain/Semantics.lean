import EvmYul.Chain.Config
import EvmYul.Chain.Precompiles

/-!
# Chain semantics

`ChainSemantics` is the interface the interpreter consults instead of branching on a chain
id (RFC §6.1, §19.4).  It is deliberately small: everything to do with ArbOS state and
message mechanics lives in `EvmYul/ArbOS/*`.

The accessors are *derived from* `ChainConfig` (`ChainSemantics.ofConfig`) rather than
being arbitrary functions, so a profile is fully described by comparable, printable data
and two profiles with equal configuration are extensionally equal.
-/

namespace EvmYul

/-- The block-context accessor for `NUMBER` under a given profile. -/
def chainBlockNumber (c : ChainConfig) (e : ChainEnv) : UInt256 :=
  match c.blockContext.blockNumber with
    | .headerNumber => .ofNat e.header.number
    | .l1BlockNumber =>
      match e.arbOS with
        | some st => st.l1Context.l1BlockNumber
        -- Unreachable for a well-formed state: `ChainSemantics.wellFormedEnv` requires an
        -- ArbOS state whenever the profile is a Nitro profile, and admission rejects
        -- states that are not well formed.
        | none => .ofNat e.header.number

/-- The block-context accessor for `COINBASE` under a given profile. -/
def chainCoinbase (c : ChainConfig) (e : ChainEnv) : AccountAddress :=
  match c.blockContext.coinbase with
    | .headerBeneficiary => e.header.beneficiary
    | .feeAccount a => a

/-- The block-context accessor for `PREVRANDAO` under a given profile. -/
def chainPrevRandao (c : ChainConfig) (e : ChainEnv) : UInt256 :=
  match c.blockContext.randao with
    | .beaconRandao => e.header.prevRandao
    | .constant v => v

/-- The `TIMESTAMP` accessor.  Nitro reports the L2 timestamp, which is the header field. -/
def chainTimestamp (_c : ChainConfig) (e : ChainEnv) : UInt256 := .ofNat e.header.timestamp

/-- The `GASPRICE` accessor. -/
def chainGasPrice (_c : ChainConfig) (e : ChainEnv) : UInt256 := .ofNat e.gasPrice

/--
The chain-semantics interface consulted by the interpreter.

Keep this small; see RFC §6.1.
-/
structure ChainSemantics where
  config      : ChainConfig
  blockNumber : ChainEnv → UInt256
  timestamp   : ChainEnv → UInt256
  coinbase    : ChainEnv → AccountAddress
  prevRandao  : ChainEnv → UInt256
  gasPrice    : ChainEnv → UInt256
  precompiles : PrecompileRegistry

namespace ChainSemantics

/-- Derive the semantics of a profile from its configuration. -/
def ofConfig (c : ChainConfig) (precompiles : PrecompileRegistry) : ChainSemantics where
  config := c
  blockNumber := chainBlockNumber c
  timestamp := chainTimestamp c
  coinbase := chainCoinbase c
  prevRandao := chainPrevRandao c
  gasPrice := chainGasPrice c
  precompiles := precompiles

/-- The chain id, as a 256-bit word, for the `CHAINID` opcode. -/
def chainIdWord (s : ChainSemantics) : UInt256 := .ofNat s.config.chainId.toNat

def maxCodeSize (s : ChainSemantics) : Nat := s.config.maxCodeSize
def maxInitCodeSize (s : ChainSemantics) : Nat := s.config.maxInitCodeSize

def isPrecompile (s : ChainSemantics) (a : AccountAddress) : Bool :=
  s.precompiles.isPrecompile a

def systemContract? (s : ChainSemantics) (a : AccountAddress) : Option ArbOS.SystemContract :=
  s.precompiles.systemContract? a

/--
A `ChainEnv` is well formed for a profile when a Nitro profile is accompanied by ArbOS
state.  This is checked at the admission boundary (`EvmYul.Chain.admitTransaction`), which
is what makes the `none` branch of `chainBlockNumber` unreachable in practice.
-/
def wellFormedEnv (s : ChainSemantics) (e : ChainEnv) : Prop :=
  s.config.isArbitrum = true → e.arbOS.isSome = true

instance (s : ChainSemantics) (e : ChainEnv) : Decidable (s.wellFormedEnv e) :=
  inferInstanceAs (Decidable (_ → _))

/-! ### Block-context laws -/

@[simp]
theorem blockNumber_ofConfig (c : ChainConfig) (p : PrecompileRegistry) (e : ChainEnv) :
    (ofConfig c p).blockNumber e = chainBlockNumber c e := rfl

/-- Under a header-number profile, `NUMBER` is the header height. -/
theorem blockNumber_headerNumber
    (c : ChainConfig) (e : ChainEnv) (h : c.blockContext.blockNumber = .headerNumber) :
    chainBlockNumber c e = .ofNat e.header.number := by
  simp [chainBlockNumber, h]

/-- Under an L1-derived profile with ArbOS state present, `NUMBER` is the L1 height. -/
theorem blockNumber_l1BlockNumber
    (c : ChainConfig) (header : BlockHeader) (gasPrice : Nat) (st : ArbOS.State)
    (h : c.blockContext.blockNumber = .l1BlockNumber) :
    chainBlockNumber c ⟨header, gasPrice, some st⟩ = st.l1Context.l1BlockNumber := by
  simp [chainBlockNumber, h]

/--
RFC §20.5 — context separation.  Changing the L2 block height leaves `NUMBER` untouched
under an L1-derived profile: only `ArbSys.arbBlockNumber` moves.
-/
theorem blockNumber_indep_of_l2BlockNumber
    (c : ChainConfig) (header : BlockHeader) (gasPrice : Nat) (st : ArbOS.State)
    (n : UInt256) (h : c.blockContext.blockNumber = .l1BlockNumber) :
    chainBlockNumber c ⟨header, gasPrice, some { st with l2BlockNumber := n }⟩ =
      chainBlockNumber c ⟨header, gasPrice, some st⟩ := by
  simp [chainBlockNumber, h]

/-- Conversely, changing the L1 context does move `NUMBER`. -/
theorem blockNumber_tracks_l1
    (c : ChainConfig) (header : BlockHeader) (gasPrice : Nat) (st : ArbOS.State)
    (n : UInt256) (h : c.blockContext.blockNumber = .l1BlockNumber) :
    chainBlockNumber c
        ⟨header, gasPrice, some { st with l1Context := { st.l1Context with l1BlockNumber := n } }⟩
      = n := by
  simp [chainBlockNumber, h]

@[simp]
theorem prevRandao_constant (c : ChainConfig) (e : ChainEnv) (v : UInt256)
    (h : c.blockContext.randao = .constant v) :
    chainPrevRandao c e = v := by
  simp [chainPrevRandao, h]

@[simp]
theorem coinbase_feeAccount (c : ChainConfig) (e : ChainEnv) (a : AccountAddress)
    (h : c.blockContext.coinbase = .feeAccount a) :
    chainCoinbase c e = a := by
  simp [chainCoinbase, h]

end ChainSemantics

end EvmYul
