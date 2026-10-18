module

public import Std.Data.TreeMap
public import Mathlib.Data.Multiset.Sort

public import EvmYul.Wheels
public import EvmYul.Maps.TrieRoot
public import EvmYul.SpongeHash.Keccak256

public import EvmYul.FFI.Primitives
/-!
# Account storage

`Storage` (account storage, `UInt256 → UInt256`) is a `Std.TreeMap` ordered by `compare`.

`Std.TreeMap` is maintained in Lean core and is what Batteries recommends instead of
`Batteries.RBMap`. Its lemma library (`Std.TreeMap.getElem?_insert`, `Std.TreeMap.contains_erase`,
...) only assumes a lawful comparator (`Std.TransOrd`, `Std.LawfulEqOrd`); those instances for
`UInt256` and `AccountAddress` are proved next to the types. Iteration (`foldl`, `toList`,
`toArray`) visits keys in increasing order, exactly as the former `Batteries.RBMap` did, so the trie
roots computed from these maps do not change. See `EvmYul.Maps.TreeMapTests`.
-/

public section

namespace EvmYul

section RemoveLater

abbrev Storage : Type := Std.TreeMap UInt256 UInt256 compare

def Storage.toFinmap (self : Storage) : Finmap (λ _ : UInt256 ↦ UInt256) :=
  self.foldl (init := ∅) λ acc k v ↦ acc.insert (UInt256.ofNat k.1) v

def Storage.toEvmYulStorage (self : Storage) : EvmYul.Storage :=
  self.foldl (init := ∅) λ acc k v ↦ acc.insert (UInt256.ofNat k.1) v

def toBlobs (pair : UInt256 × UInt256) : Option (String × String) := do
  let kec := ffi.KEC pair.1.toByteArray
  let rlp ← RLP (.𝔹 (BE pair.2.toNat))
  pure (EvmYul.toHex kec, EvmYul.toHex rlp)

@[expose] def computeTrieRoot (storage : Storage) : Option ByteArray :=
  match Array.mapM toBlobs storage.toArray with
    | none => .none
    | some pairs => (ByteArray.ofBlob (blobComputeTrieRoot pairs)).toOption

end RemoveLater

end EvmYul
