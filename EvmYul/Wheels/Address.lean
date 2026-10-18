module

public import EvmYul.Wheels.Bytes
public import EvmYul.ProofTags

public section

/-!
# Account addresses

`AccountAddress` (160-bit words), its lawful order (the comparator of every account map), and the
fixed-width big-endian encodings of words and addresses.
-/

namespace EvmYul

@[expose] def UInt256.toByteArray (val : UInt256) : ByteArray :=
  let b := BE val.toNat
  ByteArray.zeroesUSize ⟨32 - b.size⟩ ++ b

abbrev Literal := UInt256

-- 2^160 https://www.wolframalpha.com/input?i=2%5E160
@[expose] def AccountAddress.size : Nat := 1461501637330902918203684832716283019655932542976

@[expose] instance : NeZero AccountAddress.size where
  out := (by unfold AccountAddress.size; simp)

@[expose] abbrev AccountAddress : Type := Fin AccountAddress.size

@[expose] instance : Ord AccountAddress where
  compare a₁ a₂ := compare a₁.val a₂.val

/-- Addresses are ordered by their numeric value; this is the comparator of every account map. -/
@[reviewed_rfl "the address order is the order on the numeric value, by definition"]
theorem AccountAddress.compare_eq_compareOn :
    (compare : AccountAddress → AccountAddress → Ordering) = compareOn Fin.val := rfl

@[expose] instance : Std.TransOrd AccountAddress := by
  unfold Std.TransOrd; rw [AccountAddress.compare_eq_compareOn]; infer_instance

@[expose] instance : Std.LawfulEqOrd AccountAddress where
  eq_of_compare h := Fin.ext (Std.LawfulEqCmp.eq_of_compare (cmp := (compare : ℕ → ℕ → Ordering)) h)

@[expose] instance : Inhabited AccountAddress := ⟨Fin.ofNat _ 0⟩

namespace AccountAddress

@[expose] def ofNat (n : ℕ) : AccountAddress := Fin.ofNat _ n
@[expose] def ofUInt256 (v : UInt256) : AccountAddress := Fin.ofNat _ (v.val % AccountAddress.size)
@[expose] instance {n : Nat} : OfNat AccountAddress n := ⟨Fin.ofNat _ n⟩

@[expose] def toByteArray (a : AccountAddress) : ByteArray :=
  let b := BE a
  ByteArray.zeroesUSize ⟨20 - b.size⟩ ++ b

end AccountAddress

end EvmYul
