module

public import EvmYul.SpongeHash.Sponge
public meta import EvmYul.SpongeHash.Sponge
public import EvmYul.FFI.Primitives
public meta import EvmYul.FFI.Primitives
public import EvmYul.Testing.Counted
public meta import EvmYul.Testing.Counted
public import Plausible
public meta import Plausible

@[expose] public meta section

/-!
# Keccak-256: the Lean specification against the C implementation the interpreter uses

Run during `lake build EvmYulGasTests` (whose FFI dynlib lets `#eval` call `ffi.KEC`, the hash behind
the `SHA3` opcode, storage-trie keys and account addresses). Any failing check fails the build.

1. **Business known-answer vectors** for the specification `EvmYul.SpongeHash.keccak256`: the
   Ethereum empty-code hash, the empty-trie root, the ERC-20 `transfer` selector and `Transfer`
   event topic, and the published Keccak-256 vectors for `""`, `"abc"` and the "quick brown fox".
2. **Independent oracle for the permutation and sponge**: `sha3_256` (same code, domain byte `0x06`)
   against digests produced by Python's `hashlib.sha3_256`, at lengths `0, 3, 135, 136, 137, 256`
   (both sides of the one-block / two-block boundary).
3. **Length sweep**: specification = `ffi.KEC` for **every** input length `0 … 400` (every padding
   case, including the merged `0x81` pad byte at lengths `135` and `271`).
4. **Differential property** (Plausible, seeded, counted): specification = `ffi.KEC` on random byte
   strings up to 300 bytes.
5. **Mutation tests**: SHA3 padding, 23 rounds, and an unmerged pad byte must each be caught. The last
   one is invisible to random inputs of most lengths; it is caught by the sweep at exactly
   `len % 136 = 135`, which shows the sweep is load-bearing.
-/

namespace EvmYul.SpongeHash.SpongeTests

open Plausible Plausible.Decorations

/-- Lower-case hex of a byte string. -/
def hex (b : ByteArray) : String :=
  String.join <| b.toList.map fun x =>
    let s := Nat.toDigits 16 x.toNat
    String.ofList (if s.length == 1 then '0' :: s else s)

/-- A deterministic byte string of length `n` (not all-equal, so lane order matters). -/
def pattern (n : ℕ) : ByteArray := ⟨(Array.range n).map fun i => (i * 31 + 7).toUInt8⟩

/-- `n` copies of `'a'`. -/
def aa (n : ℕ) : ByteArray := ⟨Array.replicate n 97⟩

/-- Known-answer vectors, `(name, input, expected hex digest)`. -/
def keccakVectors : List (String × ByteArray × String) :=
  [ ("empty-code hash: KEC(\"\") (Yellow Paper, codeHash of an account without code)",
      .empty, "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"),
    ("empty-trie root: KEC(RLP(\"\")) = KEC(0x80)",
      ⟨#[0x80]⟩, "56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"),
    ("KEC(\"abc\")",
      "abc".toUTF8, "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45"),
    ("KEC(\"The quick brown fox jumps over the lazy dog\")",
      "The quick brown fox jumps over the lazy dog".toUTF8,
      "4d741b6f1eb29cb2a9b9911c82f56fa8d73b04959d3d9d222895df6c0b28aa15"),
    ("ERC-20 Transfer event topic: KEC(\"Transfer(address,address,uint256)\")",
      "Transfer(address,address,uint256)".toUTF8,
      "ddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef") ]

/-- SHA3-256 digests from Python's `hashlib.sha3_256` (an implementation independent of both the
Lean specification and SHA3IUF). -/
def sha3Vectors : List (ByteArray × String) :=
  [ (.empty, "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a"),
    ("abc".toUTF8, "3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532"),
    (aa 135, "8094bb53c44cfb1e67b7c30447f9a1c33696d2463ecc1d9c92538913392843c9"),
    (aa 136, "3fc5559f14db8e453a0a3091edbd2bc25e11528d81c66fa570a4efdcc2695ee1"),
    (aa 137, "f8d6846cedd2ccfadf15c5879ef95af724d799eed7391fb1c91f95344e738614"),
    (⟨(Array.range 256).map (·.toUInt8)⟩,
      "9b04c091da96b997afb8f2585d608aebe9c4a904f7d52c8f28c7e4d2dd9fba5f") ]

/-! ## Mutants -/

/-- Mutant: FIPS 202 SHA3 padding instead of Keccak's (the classic Ethereum mix-up). -/
def mutSha3Pad (b : ByteArray) : ByteArray := sha3_256 b

/-- Mutant: one round short. -/
def mutRounds23 (b : ByteArray) : ByteArray := ⟨(spongeCore 0x01 23 b.toList).toArray⟩

/-- Mutant: never merges the domain byte and the final bit, i.e. always appends `0x01 … 0x80` as
two bytes. Wrong only when exactly one byte of the block is left (`len % 136 = 135`). -/
def mutUnmergedPad (b : ByteArray) : ByteArray :=
  let msg := b.toList
  let k := rate - msg.length % rate
  let pad := if k = 1 then [0x01] ++ List.replicate (rate - 1) 0 ++ [0x80]
             else 0x01 :: List.replicate (k - 2) 0 ++ [0x80]
  ⟨(squeeze <| (blocks (msg ++ pad)).foldl (absorbBlock 24) State.zero).toArray⟩

/-- Lengths swept against the C implementation. -/
def sweepLengths : List ℕ := List.range 401

/-- Lengths in the sweep at which `f` disagrees with `ffi.KEC`. -/
def sweepDisagreements (f : ByteArray → ByteArray) : List ℕ :=
  sweepLengths.filter fun n => f (pattern n) != ffi.KEC (pattern n)

/-- `f` and the C implementation agree on the bytes `l` (each taken mod 256; Plausible generates
`Nat`s, whose small values bias the bytes towards `0x00`, the classic lane-packing trap). -/
def agreesWithFFI (f : ByteArray → ByteArray) (l : List Nat) : Bool :=
  let b : ByteArray := ⟨(l.map (·.toUInt8)).toArray⟩
  f b == ffi.KEC b

/-- Seeded configuration; `maxSize := 300` makes the random lists cross the 136-byte block size. -/
def cfg : Configuration := { numInst := 150, maxSize := 300, randomSeed := some 20261008,
                             quiet := true }

/-- Fail the build on a counterexample, or when fewer than `minValid` inputs (default: half of the
samples) satisfied the property's guards; print `total/valid/discarded` (`CountedTesting`). -/
def expectHolds (name : String) (p : Prop)
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p']
    (minValid : Nat := CountedTesting.defaultMinValid cfg) : IO Unit :=
  discard <| CountedTesting.holdsCore cfg name p' minValid

/-- Mutation test: fail the build unless a counterexample is found (counts printed). -/
def expectRefuted (name : String) (p : Prop)
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] : IO Unit :=
  discard <| CountedTesting.refutedCore cfg name p'

/-- Run every check; throws on the first failure. -/
def runAll : IO Unit := do
  -- 1. Business known-answer vectors.
  for (name, input, expected) in keccakVectors do
    let got := hex (keccak256 input)
    unless got == expected do
      throw <| IO.userError s!"KAT failed: {name}: got {got}, expected {expected}"
    unless hex (ffi.KEC input) == expected do
      throw <| IO.userError s!"KAT failed for ffi.KEC: {name}"
  let selector := (keccak256 "transfer(address,uint256)".toUTF8).extract 0 4
  unless hex selector == "a9059cbb" do
    throw <| IO.userError s!"ERC-20 transfer selector is {hex selector}, expected a9059cbb"
  IO.println s!"{keccakVectors.length + 1} Keccak-256 business vectors pass (spec and ffi.KEC)"
  -- 2. Independent oracle.
  for (input, expected) in sha3Vectors do
    unless hex (sha3_256 input) == expected do
      throw <| IO.userError s!"SHA3-256 vector failed at length {input.size}"
  unless sha3Vectors.all fun (i, _) => (sha3_256 i).size == 32 && (keccak256 i).size == 32 do
    throw <| IO.userError "digest size is not 32 bytes"
  IO.println s!"{sha3Vectors.length} SHA3-256 vectors from hashlib pass (lengths 0, 3, 135, 136, \
    137, 256): permutation and sponge validated independently of ffi.KEC"
  -- 3. Length sweep.
  let bad := sweepDisagreements keccak256
  unless bad.isEmpty do
    throw <| IO.userError s!"spec and ffi.KEC disagree at lengths {bad}"
  IO.println s!"sweep: spec = ffi.KEC at all {sweepLengths.length} lengths 0 … 400"
  -- 4. Differential property.
  expectHolds "keccak256 spec = ffi.KEC on random byte strings"
    (∀ l : List Nat, agreesWithFFI keccak256 l = true) (minValid := cfg.numInst)
  -- 5. Mutants.
  expectRefuted "mutant: SHA3 padding (0x06)"
    (∀ l : List Nat, agreesWithFFI mutSha3Pad l = true)
  expectRefuted "mutant: 23 rounds"
    (∀ l : List Nat, agreesWithFFI mutRounds23 l = true)
  let unmerged := sweepDisagreements mutUnmergedPad
  unless unmerged == [135, 271] do
    throw <| IO.userError s!"mutant unmerged pad byte: sweep caught it at {unmerged}, expected \
      exactly [135, 271]"
  IO.println "mutant: unmerged pad byte caught by the sweep at exactly lengths [135, 271]"

#eval runAll

end EvmYul.SpongeHash.SpongeTests
