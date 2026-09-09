import EvmYul.UInt256
import EvmYul.Wheels

/-!
# A minimal, pure ABI codec for ArbOS system contracts

ArbOS system contracts are called with ordinary Solidity ABI calldata, so the model needs
a decoder/encoder for the fragment of the ABI those methods use: a 4-byte selector
followed by 32-byte words holding `uint256`, `address` and `bool` values, plus the
`(offset, length, payload)` layout for a single trailing `bytes` argument.

The codec is deliberately *pure* (no FFI, no `panic!`): it is used inside dispatch, so it
has to reduce during evaluation and be provable.  It is built on the byte conversions that
already exist in `EvmYul.UInt256` rather than re-deriving base-256 arithmetic.
-/

namespace EvmYul

namespace ABI

/-- The 32-byte big-endian, left zero-padded representation of `n`. -/
def wordBytes (n : Nat) : List UInt8 :=
  List.replicate (32 - (toBytesBigEndian n).length) 0 ++ toBytesBigEndian n

theorem toBytesBigEndian_length (n : Nat) :
    (toBytesBigEndian n).length = (toBytes' n).length := by
  simp [toBytesBigEndian]

theorem toBytesBigEndian_length_le_32 {n : Nat} (h : n < UInt256.size) :
    (toBytesBigEndian n).length ≤ 32 := by
  rw [toBytesBigEndian_length]
  exact toBytes'_le (k := 32) (by simpa [UInt256.size] using h)

@[simp]
theorem wordBytes_length {n : Nat} (h : n < UInt256.size) : (wordBytes n).length = 32 := by
  have h32 := toBytesBigEndian_length_le_32 h
  simp [wordBytes]
  omega

/-- Reading back a `wordBytes` encoding recovers the number. -/
@[simp]
theorem fromBytesBigEndian_wordBytes (n : Nat) :
    fromBytesBigEndian (wordBytes n) = n := by
  simp [wordBytes, fromBytesBigEndian, toBytesBigEndian, List.reverse_append,
    extend_bytes_zero, fromBytes'_toBytes']

/-- A 32-byte ABI word holding `v`. -/
def encodeWord (v : UInt256) : ByteArray := ⟨(wordBytes v.toNat).toArray⟩

/-- A 32-byte ABI word holding the (left zero-padded) address `a`. -/
def encodeAddress (a : AccountAddress) : ByteArray := ⟨(wordBytes a.val).toArray⟩

/-- A 32-byte ABI word holding a boolean. -/
def encodeBool (b : Bool) : ByteArray := encodeWord (if b then ⟨1⟩ else ⟨0⟩)

/-- Concatenate a list of ABI words into a return buffer. -/
def encodeWords (vs : List UInt256) : ByteArray :=
  vs.foldl (fun acc v => acc ++ encodeWord v) .empty

/-- `UInt256.ofNat` is a left inverse of `UInt256.toNat`. -/
theorem _root_.EvmYul.UInt256.ofNat_toNat (v : UInt256) : UInt256.ofNat v.toNat = v := by
  apply UInt256.ext
  simp [UInt256.ofNat, UInt256.toNat, Fin.ofNat, Id.run, Nat.mod_eq_of_lt v.val.isLt]

@[simp]
theorem encodeWord_bytes (v : UInt256) : (encodeWord v).data.toList = wordBytes v.toNat := by
  simp [encodeWord]

@[simp]
theorem encodeWord_size (v : UInt256) : (encodeWord v).size = 32 := by
  have : v.toNat < UInt256.size := v.val.isLt
  simpa [encodeWord, ByteArray.size] using wordBytes_length this

/-- Decode the `i`-th 32-byte word of a byte list; `none` if the list is too short. -/
def decodeWordList (bs : List UInt8) (i : Nat) : Option UInt256 :=
  let w := (bs.drop (32 * i)).take 32
  if w.length = 32 then some (.ofNat (fromBytesBigEndian w)) else none

/-- Decode the `i`-th 32-byte ABI word of `data`. -/
def decodeWord (data : ByteArray) (i : Nat) : Option UInt256 :=
  decodeWordList data.data.toList i

/--
Decode the `i`-th word as an address.

Nitro's precompile dispatch uses go-ethereum's ABI unpacker, which takes the low 20 bytes
of the word and ignores the high 12; the model reproduces that truncation rather than
inventing a stricter validation rule.
-/
def decodeAddress (data : ByteArray) (i : Nat) : Option AccountAddress :=
  (decodeWord data i).map (fun v => AccountAddress.ofNat (v.toNat % AccountAddress.size))

/-- Decode the `i`-th word as a boolean (nonzero is `true`, as in Solidity). -/
def decodeBool (data : ByteArray) (i : Nat) : Option Bool :=
  (decodeWord data i).map (fun v => v.toNat ≠ 0)

@[simp]
theorem decodeWord_encodeWord (v : UInt256) : decodeWord (encodeWord v) 0 = some v := by
  have hlen : (wordBytes v.toNat).length = 32 := wordBytes_length v.val.isLt
  simp only [decodeWord, encodeWord_bytes, decodeWordList, Nat.mul_zero, List.drop_zero,
    List.take_of_length_le (le_of_eq hlen), hlen, fromBytesBigEndian_wordBytes]
  exact congrArg some (UInt256.ofNat_toNat v)

/-- The 4-byte method selector of `data`, if it is at least 4 bytes long. -/
def selector (data : ByteArray) : Option UInt32 :=
  match data.data.toList with
    | b₀ :: b₁ :: b₂ :: b₃ :: _ =>
      some <| (b₀.toUInt32 <<< 24) ||| (b₁.toUInt32 <<< 16) ||| (b₂.toUInt32 <<< 8) ||| b₃.toUInt32
    | _ => none

/-- The argument section of ABI calldata, i.e. everything after the selector. -/
def arguments (data : ByteArray) : ByteArray := ⟨(data.data.toList.drop 4).toArray⟩

/--
Decode a single trailing dynamic `bytes` argument located at head word `i`.

The head word holds the offset (relative to the start of the argument section) of a length
word followed by the payload.
-/
def decodeBytes (data : ByteArray) (i : Nat) : Option ByteArray := do
  let off ← decodeWord data i
  let len ← decodeWordList data.data.toList (off.toNat / 32)
  let start := off.toNat + 32
  let payload := (data.data.toList.drop start).take len.toNat
  if payload.length = len.toNat then some ⟨payload.toArray⟩ else none

/-- Encode a dynamic `bytes` argument as `(offset, length, right-padded payload)`. -/
def encodeBytes (bs : ByteArray) : ByteArray :=
  let len := bs.size
  let padding := (32 - len % 32) % 32
  encodeWord (.ofNat 32) ++ encodeWord (.ofNat len) ++ bs ++
    ⟨(List.replicate padding (0 : UInt8)).toArray⟩

/--
The Solidity method identifier of a signature: the first four bytes of its Keccak-256
hash.  This uses the repository's Keccak FFI, so it is the same hash the EVM uses; the
selector constants in `EvmYul.ArbOS.Precompiles` are cross-checked against it by the test
executable.
-/
def methodId (signature : String) : UInt32 :=
  match selector (ffi.KEC ⟨signature.toUTF8.data⟩) with
    | some s => s
    | none => 0

end ABI

end EvmYul
