module

public import EvmYul.Wheels
public import EvmYul.UInt256
public import EvmYul.State.BlockHeader
public import EvmYul.Yul.Ast

/-!
# Execution environment

`ExecutionEnv τ` (`I` of the Yellow Paper): code owner, caller, value, calldata, code, depth,
permission to modify state, the header and the blob hashes.
-/

public section

namespace EvmYul

@[expose] section

/--
The execution envorinment `I` `ExecutionEnv`. Section 9.3.
- `codeOwner` `Iₐ`
- `sender`    `Iₒ`
- `source`    `Iₛ`
- `weiValue`  `Iᵥ`
- `calldata` `I_d`
- `code`      `I_b`
- `gasPrice`  `Iₚ`
- `header`    `I_H`
- `depth`     `Iₑ`
- `perm`      `I_w`
-/
structure ExecutionEnv (τ : OperationType) where
  codeOwner : AccountAddress
  sender    : AccountAddress
  source    : AccountAddress
  weiValue  : UInt256
  calldata : ByteArray
  code      : (Yul.Ast.contractCode τ)
  gasPrice  : ℕ
  header    : BlockHeader
  depth     : ℕ
  perm      : Bool
  blobVersionedHashes : List ByteArray
  deriving BEq, Inhabited, Repr

end

@[expose] def prevRandao {τ} (e : ExecutionEnv τ) : UInt256 :=
  e.header.prevRandao

@[expose] def basefee {τ} (e : ExecutionEnv τ) : UInt256 :=
  .ofNat e.header.baseFeePerGas

@[expose] def ExecutionEnv.getBlobGasprice {τ} (e : ExecutionEnv τ) : UInt256 :=
  .ofNat e.header.getBlobGasprice

@[expose] def blobhash {τ} (e : ExecutionEnv τ) (i : UInt256) : UInt256 :=
  e.blobVersionedHashes[i.toNat]?.option ⟨0⟩
    (.ofNat ∘ fromByteArrayBigEndian)

end EvmYul
