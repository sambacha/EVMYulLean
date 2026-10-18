module

public import EvmYul.State.Transaction
public import EvmYul.State.BlockHeader
public import EvmYul.State.ExecutionEnv

/-!
# Operations on transactions

Recipient, data and the blob constants of EIP-4844 (`GAS_PER_BLOB`, `MAX_BLOB_GAS_PER_BLOCK`).
-/

public section

namespace EvmYul

def Transaction.to? : Transaction → Option AccountAddress
  | .legacy t | .access t | .dynamic t | .blob t => t.recipient

@[expose] def Transaction.data : Transaction → ByteArray
  | .legacy t | .access t | .dynamic t | .blob t => t.data

def GAS_PER_BLOB := 2^17
/-- EIP-4844 (Cancun): the most blob gas one block may use (six blobs of `GAS_PER_BLOB`). -/
def MAX_BLOB_GAS_PER_BLOCK : ℕ := 786432
def VERSIONED_HASH_VERSION_KZG : UInt8 := 1

def getTotalBlobGas (t : Transaction) : ℕ :=
  match t with
  | .blob t => GAS_PER_BLOB * t.blobVersionedHashes.length
  | _ => 0

def Transaction.blobVersionedHashes (t : Transaction) : List ByteArray :=
  match t with
  | .blob t => t.blobVersionedHashes
  | _ => []

def calcBlobFee (header: BlockHeader) (t : Transaction) : ℕ :=
  let totalBlobGas := getTotalBlobGas t
  totalBlobGas * header.getBlobGasprice

end EvmYul
