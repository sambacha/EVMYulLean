module

public import Mathlib.Data.List.AList

public import EvmYul.UInt256
public import EvmYul.Wheels
public import EvmYul.Maps.TrieRoot
public import EvmYul.State.Substate

/-!
# Transactions

The transaction types (legacy, access-list EIP-2930, dynamic-fee EIP-1559, blob EIP-4844) with
their common fields, access lists and receipts.
-/

public section

namespace EvmYul


-- "All transaction types specify a number of common fields:"
@[expose] section

/--
`BaseTransaction`. Section 4.3.

- `nonce`     `n`
- `gasLimit`  `g`
- `recipinet` `t`
- `value`     `v`
- `r`         `r`
- `s`         `s`
- `data`      `d/i`
-/
structure Transaction.Base where
  nonce           : UInt256
  gasLimit        : UInt256
  recipient       : Option AccountAddress
  value           : UInt256
  r               : ByteArray
  s               : ByteArray
  data            : ByteArray
deriving BEq, Repr

end

-- "EIP-2930 (type 1) and EIP-1559 (type 2) transactions also have:""
@[expose] section

/--
`AccessList`. EIP-2930.
- `chainId`    `c`
- `accessList` `A`
- `yParity`    `y`
-/
structure Transaction.WithAccessList where
  chainId : UInt256
  accessList : List (AccountAddress × Array UInt256)
  yParity : UInt256
deriving BEq, Repr

end

-- "type 0 and type 1 transactions specify gas price as a single value:"
@[expose] section

/--
`WithGasPrice`. Section 4.3.
- `gasPrice` `p`
-/
structure Transaction.WithGasPrice where
  gasPrice : UInt256
deriving BEq, Repr

end

-- Legacy transactions do not have an `accessList`, while `chainId` and `yParity` for legacy transactions are combined into a single value:
@[expose] section

/--
Type 0: `LegacyTransaction`. Section 4.3.
- `nonce`     `n`
- `gasLimit`  `g`
- `recipinet` `t`
- `value`     `v`
- `r`         `r`
- `s`         `s`
- `data`      `d/i`
- `gasPrice` `p`
- `w` `w`
-/
structure LegacyTransaction extends Transaction.Base, Transaction.WithGasPrice where
  w: UInt256
deriving BEq, Repr

end

@[expose] section

/-- Type 1: `AccessListTransaction`
- `nonce`     `n`
- `gasLimit`  `g`
- `recipinet` `t`
- `value`     `v`
- `r`         `r`
- `s`         `s`
- `data`      `d/i`
- `chainId`    `c`
- `accessList` `A`
- `yParity`    `y`
- `gasPrice` `p`
-/
structure AccessListTransaction
  extends Transaction.Base, Transaction.WithAccessList, Transaction.WithGasPrice
deriving BEq, Repr

end

@[expose] section

/--
Type 2: `DynamicFeeTransaction`
- `nonce`                `n`
- `gasLimit`             `g`
- `recipinet`            `t`
- `value`                `v`
- `r`                    `r`
- `s`                    `s`
- `data`                 `d/i`
- `chainId`              `c`
- `accessList`           `A`
- `yParity`              `y`
- `maxFeePerGas`         `m`
- `maxPriorityFeePerGas` `f`
-/
structure DynamicFeeTransaction extends Transaction.Base, Transaction.WithAccessList where
  maxFeePerGas         : UInt256
  maxPriorityFeePerGas : UInt256
deriving BEq, Repr

end

@[expose] section

structure BlobTransaction extends DynamicFeeTransaction where
  maxFeePerBlobGas  : UInt256
  blobVersionedHashes : List ByteArray
deriving BEq, Repr

end

@[expose] section

inductive Transaction where
  | legacy  : LegacyTransaction → Transaction
  | access  : AccessListTransaction → Transaction
  | dynamic : DynamicFeeTransaction → Transaction
  | blob    : BlobTransaction → Transaction
deriving BEq, Repr

end

def Transaction.base : Transaction → Transaction.Base
  | legacy t => t.toBase
  | access t => t.toBase
  | dynamic t => t.toBase
  | blob t => t.toBase

def Transaction.getAccessList : Transaction → List (AccountAddress × Array UInt256)
  | legacy _ => []
  | access t => t.accessList
  | dynamic t => t.accessList
  | blob t => t.accessList

def Transaction.type : Transaction → UInt8
  | .legacy  _ => 0
  | .access  _ => 1
  | .dynamic _ => 2
  | .blob _ => 3

def Transaction.toBlobs (t : ℕ × ByteArray) : Option (String × String) := do
  let rlpᵢ ← RLP (.𝔹 (BE t.1))
  let rlp := t.2
  pure (EvmYul.toHex rlpᵢ, EvmYul.toHex rlp)

@[expose] def Transaction.computeTrieRoot (ts : Array ByteArray) : Option ByteArray := do
  match Array.mapM Transaction.toBlobs ((Array.range ts.size).zip ts) with
    | none => .none
    | some ws => (ByteArray.ofBlob (blobComputeTrieRoot ws)).toOption

@[expose] section

structure TransactionReceipt where
  type                     : UInt8     /- R_x -/
  statusCode               : Bool      /- R_z -/
  cumulativeGasUsedInBlock : ℕ         /- R_u -/
  bloomFilter              : ByteArray /- R_b -/
  logSeries                : LogSeries /- R_l -/
deriving BEq, Inhabited, Repr

end

def L_R : TransactionReceipt → 𝕋
  | ⟨_, statusCode, cumulativeGasUsedInBlock, bloomFilter, logSeries⟩ =>
  .𝕃
    [ if statusCode then .𝔹 (BE 1) else .𝔹 (BE 0)
    , .𝔹 (BE cumulativeGasUsedInBlock)
    , .𝔹 bloomFilter
    , logSeries.to𝕋
    ]

def TransactionReceipt.toBlobs (w : ℕ × ByteArray) : Option (String × String) := do
  let rlpᵢ ← RLP (.𝔹 (BE w.1))
  let rlp ← w.2
  pure (EvmYul.toHex rlpᵢ, EvmYul.toHex rlp)

-- EIP-4895
@[expose] def TransactionReceipt.computeTrieRoot (ws : Array ByteArray) : Option ByteArray := do
  match Array.mapM TransactionReceipt.toBlobs ((Array.range ws.size).zip ws) with
    | none => .none
    | some ws => (ByteArray.ofBlob (blobComputeTrieRoot ws)).toOption

def TransactionReceipt.toTrieValue (r : TransactionReceipt) : ByteArray :=
  let rlp := Option.get! ∘ RLP ∘ L_R <| r
  if r.type = 0 then rlp else ⟨#[r.type]⟩ ++ rlp

end EvmYul
