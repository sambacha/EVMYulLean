module

public import EvmYul.Wheels.Hex
public import EvmYul.Wheels.Address

public section

/-!
# Blobs

A `Blob` is a lower-case hex string without the `0x` prefix, the form in which the conformance
fixtures and the precompile helpers exchange byte strings: parsing (`getBlob?`), conversion to
bytes, and decoding to words, naturals and addresses. The decoders were in `Conform/Wheels.lean`;
they are used by the model itself (transactions, precompiles), so they live here, below both the
model and the runner (`GUIDELINES.md` Rule 6).
-/

@[expose] def Blob := String

@[expose] instance : Inhabited Blob := inferInstanceAs (Inhabited String)

def Blob.toString : Blob → String := λ blob ↦ blob

@[expose] instance : ToString Blob := ⟨Blob.toString⟩

def getBlob? (s : String) : Except String Blob :=
  if isHex s then
    let rest := (s.drop HexPrefix.length).toString
    if rest.any (not ∘ isHexDigitChar)
    then .error "Blobs must consist of valid hex digits."
    else .ok rest.toLower
  else .error "Input does not begin with 0x."
  where
    isHex (s : String) := s.startsWith HexPrefix

def getBlob! (s : String) : Blob := getBlob? s |>.toOption.get!

def ByteArray.ofBlob (self : Blob) : Except String ByteArray := do
  let chunks ← self.toList.toChunks 2 |>.mapM ofHex?
  pure ⟨chunks.toArray⟩

namespace EvmYul

namespace Conform

end Conform

section WithConform

open Conform

namespace UInt256

def fromBlob? (blob : Blob) : Except String UInt256 :=
  .ofNat <$> ((·.1) <| blob.foldr (init := (.ok 0, 0)) λ digit (acc, exp) ↦
    (do pure <| (←acc) + (16 ^ exp) * (←cToHex? digit), exp + 1))

def fromBlob! (blob : Blob) : UInt256 := fromBlob? blob |>.toOption.get!

end UInt256

def Nat.fromBlob? (blob : Blob) : Except String ℕ :=
  ((·.1) <| blob.foldr (init := (.ok 0, 0)) λ digit (acc, exp) ↦
    (do pure <| (←acc) + (16 ^ exp) * (←cToHex? digit), exp + 1))

namespace AccountAddress

def fromBlob? (s : Blob) : Except String AccountAddress := (Fin.ofNat _ ·.toNat) <$> UInt256.fromBlob? s

def fromBlob! (blob : Blob) : AccountAddress := fromBlob? blob |>.toOption.get!

end AccountAddress

end WithConform

end EvmYul
