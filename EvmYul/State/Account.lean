module

public import EvmYul.FFI.Primitives
public import Std.Data.TreeSet
public import EvmYul.Maps.StorageMap
public import EvmYul.SpongeHash.Keccak256

public import EvmYul.UInt256
public import EvmYul.Wheels

public import EvmYul.Yul.Ast

/-!
# Accounts

`Account τ`: nonce, balance, storage, transient storage and code (EVM bytecode or a Yul contract),
and the persistent part that is committed to the state trie.
-/

public section

namespace EvmYul

/--
  Precompiled contract addresses.
  (142) `π ≡ {1, 2, 3, 4, 5, 6, 7, 8, 9, 10}`
-/
@[expose] def π : Std.TreeSet AccountAddress compare :=
  Std.TreeSet.ofList ((List.range 11).tail.map (Fin.ofNat _)) compare

inductive ToExecute (τ : OperationType) where
  | Code (code : Yul.Ast.contractCode τ)
  | Precompiled (precompiled : AccountAddress)

@[expose] section

structure PersistentAccountState (τ : OperationType) where
  nonce    : UInt256
  balance  : UInt256
  storage  : Storage
  code     : (Yul.Ast.contractCode τ)
  deriving BEq, Inhabited, Repr

end

@[expose] section

/--
The `Account` data. Section 4.1.

Suppose `a` is some address.

- `nonce`    -- σ[a]ₙ.
- `balance`  -- σ[a]_b.

In the yellow paper it is supposed to be a 256-bit hash of the root node of
a Merkle Tree. KEVM implemets it as just an key/value map.
- `storage`  -- σ[a]_s.
- `tstorage` -- Transiont storage; added in EIP-1153
- `codeHash` -- σ[a]_c.

For now, we assume no global map `GM` with which `GM[code_hash] ≡ code`.
- `code`
-/
structure Account (τ : OperationType) extends PersistentAccountState τ where
  tstorage : Storage
deriving BEq, Inhabited

end

@[expose] def PersistentAccountState.codeHash (self : PersistentAccountState .EVM) : UInt256 :=
  .ofNat <| fromByteArrayBigEndian (ffi.KEC self.code)

@[expose] def Account.codeHash (self : (Account .EVM)) : UInt256 :=
  self.toPersistentAccountState.codeHash

end EvmYul
