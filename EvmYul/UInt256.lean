module

public import Init.Data.Nat.Div
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Vector.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.Ring.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Tactic.Ring
public import EvmYul.ProofTags

/-!
# 256-bit words

`UInt256`, the machine word of the EVM: arithmetic modulo `2 ^ 256`, signed operations, bitwise and
byte operations, and the conversions to and from `ℕ` and bytes.
-/

public section

namespace EvmYul

/-- The size of type `UInt256`, that is, `2^256`. -/
@[expose] def UInt256.size : ℕ :=
  115792089237316195423570985008687907853269984665640564039457584007913129639936

instance : NeZero UInt256.size where
  out := (by unfold UInt256.size; simp)

@[expose] section

structure UInt256 where
  val : Fin UInt256.size
  deriving BEq, Ord

end

@[expose] instance : ToString UInt256 where
  toString a := toString a.val

namespace UInt256

@[expose] def ofNat (n : ℕ) : UInt256 := Id.run do
  ⟨Fin.ofNat _ n⟩

@[expose] def toNat (u : UInt256) : ℕ := u.val.val

@[expose] instance : Repr UInt256 where
  reprPrec n _ := repr n.toNat

@[expose] instance {n : ℕ} : OfNat (Fin UInt256.size) n := ⟨Fin.ofNat _ n⟩
@[expose] instance : Inhabited UInt256 := ⟨ofNat 0⟩

/-! ### The order used by `Std.TreeMap UInt256 _ compare`

The derived `Ord` compares the underlying `Fin` values. The tree-map lemmas (`getElem?_insert`,
`contains_erase`, …) need the comparator to be transitive and to identify equal keys; both facts are
inherited from `Fin` (and hence `Nat`) through `compare_eq_compareOn`. -/

theorem compare_def (a b : UInt256) : compare a b = compare a.val b.val := by
  cases a; cases b; simp [compare, instOrdUInt256.ord]

theorem compare_eq_compareOn : (compare : UInt256 → UInt256 → Ordering) = compareOn UInt256.val :=
  funext₂ compare_def

instance : Std.TransOrd UInt256 := by
  unfold Std.TransOrd; rw [compare_eq_compareOn]; infer_instance

instance : Std.LawfulEqOrd UInt256 where
  eq_of_compare {a b} h := by
    rw [compare_def] at h; cases a; cases b; simpa using Std.LawfulEqCmp.eq_of_compare h

end UInt256

end EvmYul

section CastUtils

open EvmYul UInt256

@[expose] abbrev Nat.toUInt256 : ℕ → UInt256 := ofNat
@[expose] abbrev UInt8.toUInt256 (a : UInt8) : UInt256 :=
  ⟨a.toNat, Nat.lt_trans a.toFin.2 (by decide)⟩
@[expose] def Bool.toUInt256 (b : Bool) : UInt256 :=
  if b then UInt256.ofNat 1 else UInt256.ofNat 0

@[simp, reviewed_rfl "word encoding of a Boolean, by definition"]
lemma Bool.toUInt256_true : true.toUInt256 = UInt256.ofNat 1 := rfl

@[simp, reviewed_rfl "word encoding of a Boolean, by definition"]
lemma Bool.toUInt256_false : false.toUInt256 = UInt256.ofNat 0 := rfl

end CastUtils

namespace EvmYul

namespace UInt256

@[expose] def add (a b : UInt256) : UInt256 := ⟨a.val + b.val⟩
@[expose] def sub (a b : UInt256) : UInt256 := ⟨a.val - b.val⟩
@[expose] def mul (a b : UInt256) : UInt256 := ⟨a.val * b.val⟩
@[expose] def div (a b : UInt256) : UInt256 := ⟨a.val / b.val⟩
@[expose] def mod (a b : UInt256) : UInt256 := if b.val == 0 then ⟨0⟩ else ⟨a.val % b.val⟩
@[expose] def modn (a : UInt256) (n : ℕ) : UInt256 := ⟨Fin.modn a.val n⟩
@[expose] def land (a b : UInt256) : UInt256  := ⟨Fin.land a.val b.val⟩
@[expose] def lor (a b : UInt256) : UInt256   := ⟨Fin.lor a.val b.val⟩
@[expose] def xor (a b : UInt256) : UInt256   := ⟨Fin.xor a.val b.val⟩
@[expose] def shiftLeft (a b : UInt256) : UInt256  :=
  if b.val >= 256 then ⟨0⟩ else ⟨a.val <<< b.val⟩
@[expose] def shiftRight (a b : UInt256) : UInt256 :=
  if b.val >= 256 then ⟨0⟩ else ⟨a.val >>> b.val⟩
-- def lt (a b : UInt256) : Prop := a.1 < b.1
-- def le (a b : UInt256) : Prop := a.1 ≤ b.1
@[expose] def log2 (a : UInt256) : UInt256 := ⟨Fin.log2 a.val⟩

@[expose] instance : Add UInt256 := ⟨UInt256.add⟩
@[expose] instance : Sub UInt256 := ⟨UInt256.sub⟩
@[expose] instance : Mul UInt256 := ⟨UInt256.mul⟩
@[expose] instance : Div UInt256 := ⟨UInt256.div⟩
@[expose] instance : Mod UInt256 := ⟨UInt256.mod⟩
@[expose] instance : HMod UInt256 ℕ UInt256 := ⟨UInt256.modn⟩

@[expose] instance : LT UInt256 where
  lt a b := LT.lt a.val b.val

@[expose] instance : LE UInt256 where
  le a b := LE.le a.val b.val

@[expose] instance : Preorder UInt256 where
  le_refl := by intro; apply Nat.le_refl
  le_trans := by intro _ _ _ h₁ h₂ ; apply Nat.le_trans h₁ h₂
  lt := fun a b => a ≤ b ∧ ¬b ≤ a
  lt_iff_le_not_ge := by intros; rfl

@[expose] def complement (a : UInt256) : UInt256 := ⟨0 - (a.val + 1)⟩

@[expose] def lnot (a : UInt256) : UInt256 := ofNat (UInt256.size - 1) - a

@[expose] def abs (a : UInt256) : UInt256 :=
  if 2 ^ 255 <= a.toNat
  then ⟨a.val * (-1)⟩
  else a

@[expose] def fromSigned (a : UInt256) : ℤ :=
  if a.toNat < 2^255 then a.val else - (Nat.xor (UInt256.size - 1) a.val) - 1

@[expose] def toSigned (i : ℤ) : UInt256 :=
  match i with
    | .ofNat n => ofNat n
    | .negSucc n => ofNat (UInt256.size - 1 - n)

@[expose] instance : Complement UInt256 := ⟨EvmYul.UInt256.complement⟩

@[expose] def powAux (a : UInt256) (c : UInt256) : ℕ → UInt256
  | 0 => a
  | n@(k + 1) => if n % 2 == 1
                 then powAux (a * c) (c * c) (n / 2)
                 else powAux a       (c * c) (n / 2)

@[expose] def pow (b : UInt256) (n : UInt256) := powAux ⟨1⟩ b n.1

@[expose] instance : HPow UInt256 UInt256 UInt256 := ⟨pow⟩
@[expose] instance : AndOp UInt256 := ⟨UInt256.land⟩
@[expose] instance : OrOp UInt256 := ⟨UInt256.lor⟩
@[expose] instance : XorOp UInt256 := ⟨UInt256.xor⟩
@[expose] instance : ShiftLeft UInt256 := ⟨UInt256.shiftLeft⟩
@[expose] instance : ShiftRight UInt256 := ⟨UInt256.shiftRight⟩

@[expose] instance : DecidableEq UInt256 := λ a b ↦
  match decEq a.val b.val with
    | isTrue h => isTrue (congrArg UInt256.mk h)
    | isFalse h => by
      have neq : ¬ a = b := by
        intro eq
        have eq' : a.val = b.val := congrArg UInt256.val eq
        contradiction
      exact isFalse neq

@[expose] def decLt (a b : UInt256) : Decidable (a < b) :=
  match a, b with
    | n, m => inferInstanceAs (Decidable (n < m))

@[expose] def decLe (a b : UInt256) : Decidable (a ≤ b) :=
  match a, b with
    | n, m => inferInstanceAs (Decidable (n <= m))

@[expose] instance (a b : UInt256) : Decidable (a < b) := decLt _ _
@[expose] instance (a b : UInt256) : Decidable (a ≤ b) := UInt256.decLe a b
@[expose] instance : Max UInt256 := maxOfLe
@[expose] instance : Min UInt256 := minOfLe

@[expose] def eq0 (a : UInt256) : Bool := a == ⟨0⟩

@[expose] def byteAt (a b : UInt256) : UInt256 :=
  if a > ⟨31⟩ then ⟨0⟩ else
    b >>> (UInt256.ofNat ((31 - a.toNat) * 8)) &&& ⟨0xFF⟩

@[expose] def sgn (a : UInt256) : ℤ :=
  if 2 ^ 255 <= a.toNat then
    -1
  else
    if eq0 a then 0 else 1

@[expose] def bigUInt : UInt256 := ofNat 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff

@[expose] def sdiv (a b : UInt256) : UInt256 :=
  if 2 ^ 255 <= a.toNat then
    if 2 ^ 255 <= b.toNat then
      abs a / abs b
    else ⟨(abs a / b).val * -1⟩
  else
    if 2 ^ 255 <= b.toNat then
      ⟨(a / abs b).val * -1⟩
    else a / b

@[expose] def smod (a b : UInt256) : UInt256 :=
  if b.toNat == 0 then ⟨0⟩
  else
    toSigned <| sgn a * (abs a % abs b).toNat

@[expose] def sltBool (a b : UInt256) : Bool :=
  if a.toNat ≥ 2 ^ 255 then
    if b.toNat ≥ 2 ^ 255 then
      a < b
    else true
  else
    if b.toNat ≥ 2 ^ 255 then false
    else a < b

@[expose] def sgtBool (a b : UInt256) : Bool :=
  if a.toNat ≥ 2 ^ 255 then
    if b.toNat ≥ 2 ^ 255 then
      a > b
    else false
  else
    if b.toNat ≥ 2 ^ 255 then true
    else a > b

@[expose] abbrev fromBool := Bool.toUInt256

@[expose] def slt (a b : UInt256) :=
  fromBool (sltBool a b)

@[expose] def sgt (a b : UInt256) :=
  fromBool (sgtBool a b)

@[expose] def sar (a b : UInt256) : UInt256 :=
  if sltBool b ⟨0⟩
  then UInt256.complement (UInt256.complement b >>> a)
  else b >>> a

partial def dbg_toHex (n : Nat) : String :=
  if n < 16
  then hexDigitRepr n
  else (dbg_toHex (n / 16)) ++ hexDigitRepr (n % 16)

@[expose] def signextend (a b : UInt256) : UInt256 :=
  if a.toNat ≤ 31 then
    let test_bit := a * ⟨8⟩ + ⟨7⟩
  let sign_bit := ⟨1⟩ <<< test_bit
    if b &&& sign_bit ≠ ⟨0⟩ then
      b ||| (UInt256.size.toUInt256 - sign_bit)
    else b &&& (sign_bit - ⟨1⟩)
  else b

@[expose] def addMod (a b c : UInt256) : UInt256 :=
  -- "All intermediate calculations of this operation are **not** subject to the 2^256 modulo."
  if eq0 c then ⟨0⟩ else
    ofNat <| Nat.mod (a.val + b.val) c.toNat

@[expose] def mulMod (a b c : UInt256) : UInt256 :=
  -- "All intermediate calculations of this operation are **not** subject to the 2^256 modulo."
  if eq0 c then ⟨0⟩ else
    ofNat <| Nat.mod (a.val * b.val) c.toNat

@[expose] def exp (a b : UInt256) : UInt256 := pow a b

@[expose] def lt (a b : UInt256) := fromBool (a < b)

@[expose] def gt (a b : UInt256) := fromBool (a > b)

@[expose] def eq (a b : UInt256) := fromBool (a = b)

@[expose] def isZero (a : UInt256) :=
  fromBool (eq0 a)

@[ext]
theorem ext {a b : UInt256} (h : a.val = b.val) : a = b := by
  cases a
  cases b
  cases h
  rfl

@[simp, reviewed_rfl "word arithmetic API, by definition"]
theorem add_val (a b : UInt256) : (UInt256.add a b).val = a.val + b.val := by
  rfl

@[simp, reviewed_rfl "word arithmetic API, by definition"]
theorem sub_val (a b : UInt256) : (UInt256.sub a b).val = a.val - b.val := by
  rfl

@[simp, reviewed_rfl "word arithmetic API, by definition"]
theorem mul_val (a b : UInt256) : (UInt256.mul a b).val = a.val * b.val := by
  rfl

@[simp]
theorem add_zero (a : UInt256) : UInt256.add a (UInt256.ofNat 0) = a := by
  apply UInt256.ext
  simp only [UInt256.add]
  rw [show (UInt256.ofNat 0).val = (0 : Fin UInt256.size) by rfl]
  exact _root_.add_zero a.val

@[simp]
theorem zero_add (a : UInt256) : UInt256.add (UInt256.ofNat 0) a = a := by
  apply UInt256.ext
  simp only [UInt256.add]
  rw [show (UInt256.ofNat 0).val = (0 : Fin UInt256.size) by rfl]
  exact _root_.zero_add a.val

@[simp]
theorem one_ne_zero : UInt256.ofNat 1 ≠ UInt256.ofNat 0 := by
  decide

@[simp]
theorem mul_zero (a : UInt256) : UInt256.mul a (UInt256.ofNat 0) = UInt256.ofNat 0 := by
  apply UInt256.ext
  simp only [UInt256.mul]
  rw [show (UInt256.ofNat 0).val = (0 : Fin UInt256.size) by rfl]
  simp

@[simp]
theorem zero_mul (a : UInt256) : UInt256.mul (UInt256.ofNat 0) a = UInt256.ofNat 0 := by
  apply UInt256.ext
  simp only [UInt256.mul]
  rw [show (UInt256.ofNat 0).val = (0 : Fin UInt256.size) by rfl]
  simp

theorem eq_ne_zero_iff {a b : UInt256} :
    UInt256.eq a b ≠ UInt256.ofNat 0 ↔ a = b := by
  unfold UInt256.eq fromBool Bool.toUInt256
  by_cases h : a = b
  · simp [h]
  · simp [h]

theorem eq_ne_zero {a b : UInt256} :
    UInt256.eq a b ≠ UInt256.ofNat 0 → a = b := by
  exact eq_ne_zero_iff.mp

end UInt256

-- | Convert from a list of little-endian bytes to a natural number.
@[expose] def fromBytes' : List UInt8 → ℕ
| [] => 0
| b :: bs => b.toFin.val + 2^8 * fromBytes' bs

@[expose] def fromBytesBigEndian : List UInt8 → ℕ := fromBytes' ∘ List.reverse
@[expose] def fromByteArrayBigEndian (b : ByteArray) : ℕ := fromBytesBigEndian b.toList

variable {bs : List UInt8}
         {n : ℕ}

-- | A bound for the natural number value of a list of bytes.
private lemma fromBytes'_le : fromBytes' bs < 2^(8 * bs.length) := by
  induction bs with
  | nil => unfold fromBytes'; simp
  | cons b bs ih =>
    unfold fromBytes'
    have h := b.toFin.isLt
    simp only [List.length_cons, Nat.mul_succ, Nat.add_comm, Nat.pow_add]
    have _ :=
      Nat.add_le_of_le_sub
        (Nat.one_le_pow _ _ (by decide))
        (Nat.le_sub_one_of_lt ih)
    linarith

-- | The natural number value of a length 32 list of bytes is < 2^256.
private lemma fromBytes'_UInt256_le (h : bs.length = 32) : fromBytes' bs < 2^256 := by
    have h' := @fromBytes'_le bs
    rw [h] at h'
    exact h'

-- | Convert a natural number into a list of bytes.
@[expose] def toBytes' : ℕ → List UInt8
  | 0 => []
  | n@(.succ n') =>
    let byte : UInt8 := ⟨Nat.mod n UInt8.size, Nat.mod_lt _ (by linarith)⟩
    have : n / UInt8.size < n' + 1 := by
      rename_i h
      rw [h]
      apply Nat.div_lt_self <;> simp
    byte :: toBytes' (n / UInt8.size)

@[expose] def toBytesBigEndian : ℕ → List UInt8 := List.reverse ∘ toBytes'

-- | If n < 2⁸ᵏ, then (toBytes' n).length ≤ k.
private lemma toBytes'_le {k : ℕ} (h : n < 2 ^ (8 * k)) : (toBytes' n).length ≤ k := by
  induction k generalizing n with
  | zero =>
    simp at h
    rw [h]
    simp [toBytes']
  | succ e ih =>
    match n with
    | .zero => simp [toBytes']
    | .succ n =>
      unfold toBytes'
      simp
      apply ih (Nat.div_lt_of_lt_mul _)
      rw [Nat.mul_succ, Nat.pow_add] at h
      linarith

-- | If n < 2²⁵⁶, then (toBytes' n).length ≤ 32.
private lemma toBytes'_UInt256_le (h : n < UInt256.size) : (toBytes' n).length ≤ 32 := toBytes'_le h

-- | Zero-pad a list of bytes up to some length, adding the zeroes on the right.
@[expose] def zeroPadBytes (n : ℕ) (bs : List UInt8) : List UInt8 :=
  bs ++ (List.replicate (n - bs.length)) 0

-- | The length of a `zeroPadBytes` call is its first argument.
lemma zeroPadBytes_len (h : bs.length ≤ n) : (zeroPadBytes n bs).length = n := by
  unfold zeroPadBytes
  aesop

-- | Appending a bunch of zeroes to a little-endian list of bytes doesn't change its value.
@[simp]
private lemma extend_bytes_zero : fromBytes' (bs ++ List.replicate n 0) = fromBytes' bs := by
  induction bs with
  | nil =>
    simp [fromBytes']
    induction n with
    | zero => simp [List.replicate, fromBytes']
    | succ _ ih => simp [List.replicate, fromBytes']; norm_cast
  | cons _ _ ih => simp [fromBytes', ih]

-- | The ℕ value of a little-endian list of bytes is invariant under right zero-padding up to length 32.
@[simp]
private lemma fromBytes'_zeroPadBytes_32_eq : fromBytes' (zeroPadBytes 32 bs) = fromBytes' bs := extend_bytes_zero

-- | Casting a natural number to a list of bytes and back is the identity.
@[simp]
private lemma fromBytes'_toBytes' {x : ℕ} : fromBytes' (toBytes' x) = x := by
  match x with
  | .zero => simp [toBytes', fromBytes']
  | .succ n =>
    unfold toBytes' fromBytes'
    simp
    have := Nat.div_lt_self (Nat.zero_lt_succ n) (by decide : 1 < UInt8.size)
    rw [fromBytes'_toBytes']
    simp [UInt8.size, add_comm]
    apply Nat.div_add_mod

@[expose] def fromBytes! (bs : List UInt8) : ℕ := fromBytes' (bs.take 32)

private lemma fromBytes_was_good_all_year_long
  (h : bs.length ≤ 32) : fromBytes' bs < 2^256 := by
  have h' := @fromBytes'_le bs
  rw [pow_mul] at h'
  refine lt_of_lt_of_le (b := (2 ^ 8) ^ List.length bs) h' ?lenBs
  case lenBs => rw [←pow_mul]; exact pow_le_pow_right₀ (by decide) (by linarith)

@[simp]
lemma fromBytes_wasnt_naughty : fromBytes! bs < 2^256 := fromBytes_was_good_all_year_long (by simp)

-- Convenience function for spooning into UInt256.
-- Given that I 'accept' UInt8, might as well live with UInt256.
@[expose] def fromBytes_if_you_really_must? (bs : List UInt8) : UInt256 :=
  ⟨fromBytes! bs, fromBytes_wasnt_naughty⟩

@[expose] def toBytes! (n : UInt256) : List UInt8 := zeroPadBytes 32 (toBytes' n.1)

@[expose] def uInt256OfByteArray (arr : ByteArray) : UInt256 :=
  .ofNat <| fromBytes' arr.data.toList.reverse

end EvmYul

section HicSuntDracones

@[expose] def ByteArray.copySlice' (src : ByteArray) (srcOff : Nat) (dest : ByteArray) (destOff len : Nat) (exact : Bool := true) : ByteArray :=
  if false -- srcOff < 2^64 && destOff < 2^64 && len < 2^64
  then src.copySlice srcOff dest destOff len exact -- NB only when `srcOff`, `destOff` and `len` are sufficiently small
  else let srcData := src.data
       let destData := dest.data
       let sourceChunk := srcData.extract srcOff (srcOff + len)
       let destBegin := destData.extract 0 destOff
       let destEnd := destData.extract (destOff + len) destData.size
       ⟨destBegin ++ sourceChunk ++ destEnd⟩

end HicSuntDracones
