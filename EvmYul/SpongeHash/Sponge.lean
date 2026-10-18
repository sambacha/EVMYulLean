module

public import Mathlib.Tactic.Common

public section

/-!
# Keccak-256 as a pure Lean specification (the `SpongeHash` library)

The interpreter hashes with the C implementation behind `ffi.KEC` (`EvmYul/FFI/Primitives.lean`, SHA3IUF).
Lean cannot look inside that `opaque`, so until now nothing in the repository said *what* it should
compute. This module is that statement: the Keccak-f[1600] permutation and the sponge construction
of FIPS 202, written as ordinary total Lean functions over `List UInt8`.

* `keccak256` uses the original Keccak padding (domain byte `0x01`), which is what Ethereum calls
  `KEC` (Yellow Paper, Appendix H.1 / `SHA3` opcode).
* `sha3_256` uses the FIPS 202 domain byte `0x06`. It shares every component with `keccak256`
  except that one byte, so it can be checked against an independent oracle (Python's
  `hashlib.sha3_256`) and thereby validate the permutation and the sponge separately from the C code.

Nothing here replaces the FFI: no `@[implemented_by]`, no `@[extern]`. The specification is tied to
the C implementation by tests (`EvmYul.SpongeHash.SpongeTests`, run in `lake build EvmYulGasTests`):
known-answer vectors, a sweep over every input length `0 … 400` and a seeded Plausible differential
property, with mutants that must be refuted.

Proved here (proof obligations of the construction, not of Keccak's security):
* `padTail_length_pos`, `padTail_length_le_rate`: the padding adds between `1` and `rate` bytes;
* `padTail_aligned`: message plus padding is a whole number of `rate`-byte blocks;
* `blocks_length`: every absorbed block has exactly `rate` bytes;
* `squeeze_length`, `keccak256_size`, `sha3_256_size`: the digest has exactly 32 bytes.
-/

namespace EvmYul.SpongeHash

/-- Rate of Keccak-256 / SHA3-256 in bytes: `1600 - 2·256` bits = 136 bytes = 17 lanes. -/
def rate : ℕ := 136

/-- The 24 round constants of the ι step (FIPS 202, Algorithm 5). -/
def roundConstants : Array UInt64 :=
  #[0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
    0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
    0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-- Rotation offsets of the ρ step, lane `(x, y)` at index `x + 5·y`. -/
def rotationOffsets : Array UInt64 :=
  #[ 0,  1, 62, 28, 27,
    36, 44,  6, 55, 20,
     3, 10, 43, 25, 39,
    41, 45, 15, 21,  8,
    18,  2, 61, 56, 14]

/-- Left rotation of a 64-bit lane (shift amounts are taken modulo 64, so `rotl a 0 = a`). -/
def rotl (a n : UInt64) : UInt64 := (a <<< n) ||| (a >>> (64 - n))

/-- The Keccak state: 25 lanes, lane `(x, y)` at index `x + 5·y`. -/
@[expose] abbrev State := Array UInt64

/-- The all-zero initial state. -/
def State.zero : State := Array.replicate 25 0

/-- θ: XOR every lane with the parities of two neighbouring columns. -/
def theta (a : State) : State :=
  let c := fun x => a[x]! ^^^ a[x + 5]! ^^^ a[x + 10]! ^^^ a[x + 15]! ^^^ a[x + 20]!
  let d := fun x => c ((x + 4) % 5) ^^^ rotl (c ((x + 1) % 5)) 1
  Array.ofFn (n := 25) fun i => a[i.val]! ^^^ d (i.val % 5)

/-- ρ and π: `B[y, 2x+3y] = rotl(A[x, y], r[x, y])`, computed from the target index: lane
`(X, Y)` of the result comes from lane `(X + 3Y mod 5, X)` of the input. -/
def rhoPi (a : State) : State :=
  Array.ofFn (n := 25) fun j =>
    let bx := j.val % 5
    let by_ := j.val / 5
    let src := (bx + 3 * by_) % 5 + 5 * bx
    rotl a[src]! rotationOffsets[src]!

/-- χ: the only non-linear step, `A[x] ^= ¬A[x+1] ∧ A[x+2]` along each row. -/
def chi (b : State) : State :=
  Array.ofFn (n := 25) fun i =>
    let x := i.val % 5
    let y5 := i.val - x
    b[i.val]! ^^^ ((~~~ b[(x + 1) % 5 + y5]!) &&& b[(x + 2) % 5 + y5]!)

/-- ι: XOR round constant `i` into lane `(0, 0)`. -/
def iota (i : ℕ) (a : State) : State := a.modify 0 (· ^^^ roundConstants[i]!)

/-- One round `ι ∘ χ ∘ π ∘ ρ ∘ θ`. -/
def round (a : State) (i : ℕ) : State := iota i (chi (rhoPi (theta a)))

/-- The first `n` rounds of Keccak-f[1600]; the permutation itself is `permuteRounds 24`.
(Exposed so that tests can check that a reduced-round variant is detected.) -/
def permuteRounds (n : ℕ) (a : State) : State := (List.range n).foldl round a

/-- Keccak-f[1600]. -/
def permute : State → State := permuteRounds 24

/-- The padding appended to a message of `len` bytes: domain byte `suffix`, zeros, and a final
`0x80` bit, merged into one byte `suffix ||| 0x80` when only one byte is left in the block. -/
def padTail (suffix : UInt8) (len : ℕ) : List UInt8 :=
  if rate - len % rate = 1 then [suffix ||| 0x80]
  else suffix :: List.replicate (rate - len % rate - 2) 0 ++ [0x80]

/-- Split a byte list into consecutive `rate`-byte blocks (the last one shorter if the length is not
a multiple of `rate`; `blocks_length` shows this never happens for padded input). -/
def blocks : List UInt8 → List (List UInt8)
  | [] => []
  | b :: bs => (b :: bs).take rate :: blocks ((b :: bs).drop rate)
termination_by l => l.length
decreasing_by simp only [List.length_drop, List.length_cons]; unfold rate; omega

/-- Little-endian 64-bit lane `i` of a block. -/
def lane (blk : List UInt8) (i : ℕ) : UInt64 :=
  (List.range 8).foldl (fun acc k => acc ||| ((blk.getD (8 * i + k) 0).toUInt64 <<< (8 * k).toUInt64)) 0

/-- XOR a block into the first 17 lanes and apply the permutation (`rounds` rounds). -/
def absorbBlock (rounds : ℕ) (s : State) (blk : List UInt8) : State :=
  permuteRounds rounds <| Array.ofFn (n := 25) fun i =>
    if i.val < rate / 8 then s[i.val]! ^^^ lane blk i.val else s[i.val]!

/-- The first 32 output bytes: lanes 0–3, little-endian. -/
def squeeze (s : State) : List UInt8 :=
  (List.range 32).map fun j => (s[j / 8]! >>> (8 * (j % 8)).toUInt64).toUInt8

/-- The sponge with domain byte `suffix` and `rounds` permutation rounds (24 for the real hash). -/
def spongeCore (suffix : UInt8) (rounds : ℕ) (msg : List UInt8) : List UInt8 :=
  squeeze <| (blocks (msg ++ padTail suffix msg.length)).foldl (absorbBlock rounds) State.zero

/-- **Keccak-256** (Ethereum's `KEC`): original Keccak padding `0x01`, 24 rounds. -/
@[expose] def keccak256 (b : ByteArray) : ByteArray := ⟨(spongeCore 0x01 24 b.toList).toArray⟩

/-- **SHA3-256** (FIPS 202): identical to `keccak256` except for the domain byte `0x06`. -/
def sha3_256 (b : ByteArray) : ByteArray := ⟨(spongeCore 0x06 24 b.toList).toArray⟩

/-! ## Proof obligations of the construction -/

theorem rate_pos : 0 < rate := by decide

/-- The padding is never empty: even a block-aligned message gets a full block of padding. -/
theorem padTail_length_pos (suffix : UInt8) (len : ℕ) : 0 < (padTail suffix len).length := by
  unfold padTail; split <;> simp

/-- The padding adds exactly `rate - len % rate` bytes. -/
theorem padTail_length (suffix : UInt8) (len : ℕ) :
    (padTail suffix len).length = rate - len % rate := by
  have hlt : len % rate < rate := Nat.mod_lt _ rate_pos
  unfold padTail; split <;> simp <;> omega

/-- The padding adds at most one block. -/
theorem padTail_length_le_rate (suffix : UInt8) (len : ℕ) : (padTail suffix len).length ≤ rate := by
  rw [padTail_length]; omega

/-- Message plus padding is a whole number of blocks. -/
theorem padTail_aligned (suffix : UInt8) (msg : List UInt8) :
    (msg ++ padTail suffix msg.length).length % rate = 0 := by
  have hlt : msg.length % rate < rate := Nat.mod_lt _ rate_pos
  rw [List.length_append, padTail_length]
  have h := Nat.div_add_mod msg.length rate
  have : msg.length + (rate - msg.length % rate) = rate * (msg.length / rate + 1) := by
    rw [Nat.mul_add, Nat.mul_one]; omega
  rw [this, Nat.mul_mod_right]

/-- On an aligned input, every block has exactly `rate` bytes (nothing is absorbed short). -/
theorem blocks_length (l : List UInt8) (h : l.length % rate = 0) :
    ∀ b ∈ blocks l, b.length = rate := by
  induction l using blocks.induct with
  | case1 => simp [blocks]
  | case2 x xs ih =>
    intro b hb
    rw [blocks, List.mem_cons] at hb
    generalize hl : x :: xs = l at h hb ih
    have hpos : 0 < l.length := by rw [← hl]; simp
    have hge : rate ≤ l.length := by
      rcases Nat.lt_or_ge l.length rate with hlt | hge
      · rw [Nat.mod_eq_of_lt hlt] at h; omega
      · exact hge
    rcases hb with rfl | hb
    · simp only [List.length_take]; omega
    · refine ih ?_ b hb
      rw [List.length_drop]
      have : l.length - rate + rate = l.length := by omega
      rw [← this, Nat.add_mod_right] at h; exact h

/-- The squeeze produces exactly 32 bytes. -/
theorem squeeze_length (s : State) : (squeeze s).length = 32 := by simp [squeeze]

/-- A Keccak-256 digest has 32 bytes, for every input. -/
theorem keccak256_size (b : ByteArray) : (keccak256 b).size = 32 := by
  simp [keccak256, spongeCore, ByteArray.size, squeeze_length]

/-- A SHA3-256 digest has 32 bytes, for every input. -/
theorem sha3_256_size (b : ByteArray) : (sha3_256 b).size = 32 := by
  simp [sha3_256, spongeCore, ByteArray.size, squeeze_length]

end EvmYul.SpongeHash
