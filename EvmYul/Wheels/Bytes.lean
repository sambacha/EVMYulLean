module

public import EvmYul.UInt256
public import Mathlib.Data.Finmap
public import Mathlib.Data.String.Defs
import all Init.Util
public import EvmYul.ProofTags

public section

/-!
# Byte arrays

Big-endian encoding (`BE`), zero padding, bounded reads and writes of `ByteArray`s, and the
`dbgTrace` equation used by proofs about tracing code. Pure Lean throughout, so the facts about
them are provable and the code runs during `lake build`.
-/

/-- `dbgTrace s f` prints `s` and returns `f ()`. Under the module system the body of `dbgTrace`
is not exposed by `Init`, so proofs about code that traces (the precompiles' failure branches) use
this equation instead of unfolding it. -/
@[reviewed_generic "core `dbgTrace` equation (its body is not exposed to modules)"]
theorem EvmYul.dbgTrace_eq {α : Type} (s : String) (f : Unit → α) : dbgTrace s f = f () := by
  unfold dbgTrace; rfl

-- (195)
def BE : ℕ → ByteArray := List.toByteArray ∘ EvmYul.toBytesBigEndian

/-- `n` zero bytes, in pure Lean (review O-4). Unlike the opaque FFI primitive
`ffi.ByteArray.zeroes` (C `memset_zero`), the kernel and the elaborator can evaluate it, so facts
such as `(zeroesPure n).size = n` are provable and code that uses it runs during `lake build`. -/
@[expose] def ByteArray.zeroesPure (n : ℕ) : ByteArray := ⟨Array.replicate n 0⟩

/-- Drop-in pure replacement for `ffi.ByteArray.zeroes : USize → ByteArray`: the C function
`memset_zero(n)` allocates `n` bytes and zeroes them, so it returns `n.toNat` zero bytes, and so does
this. Taking the `USize` argument keeps every call site's existing wrap-around behaviour unchanged. -/
@[expose] def ByteArray.zeroesUSize (n : USize) : ByteArray := ByteArray.zeroesPure n.toNat

/--
TODO(rework later to a sane version)
-/
@[expose] instance : DecidableEq ByteArray := by
  rintro ⟨a⟩ ⟨b⟩
  rw [ByteArray.mk.injEq]
  apply decEq

@[expose] def ByteArray.get? (self : ByteArray) (n : Nat) : Option UInt8 :=
  if h : n < self.size
  then self.get n h
  else .none


/--
TODO - Well this is ever so slightly unfortunate.
It appears to be the case that some (all?) definitions that have C++ implementations
use 64bit-width integers to hold numeric arguments.

When this assumption is broken, e.g. `n : Nat := 2^64`, the Lean (4.9.0) gives
inernal out of memory error.

This implementation works around the issue at the price of using a slower implementation
in case either of the arguments is too big.
-/
def ByteArray.extract' (a : ByteArray) (b e : Nat) : ByteArray :=
  -- TODO: Shouldn't (`e` - `b`) be < `2^64` instead of `e` since eventually `a.copySlice b empty 0 (e - b)` is called?
  if b < 2^64 && e < 2^64
  then a.extract b e -- NB only when `b` and `e` are sufficiently small
  else ⟨⟨a.toList.drop b |>.take (e - b)⟩⟩

def ByteArray.readBytes (source : ByteArray) (start size : ℕ) : ByteArray :=
  let read :=
    if start < 2^64 && size < 2^64 then
      source.copySlice start empty 0 size
    else
      ⟨⟨source.toList.drop start |>.take size⟩⟩
  read ++ ByteArray.zeroesUSize ⟨size - read.size⟩

@[expose] def ByteArray.readWithoutPadding (source : ByteArray) (addr len : ℕ) : ByteArray :=
  if addr ≥ source.size then .empty else
    let len := min len source.size
    source.extract addr (addr + len)

def inf := 2^66

@[expose] def ByteArray.readWithPadding (source : ByteArray) (addr len : ℕ) : ByteArray :=
  if len ≥ 2^64 then
    panic! s!"ByteArray.readWithPadding: can not handle byte arrays of length {len}"
  else
    let read := source.readWithoutPadding addr len
    read ++ ByteArray.zeroesUSize ⟨len - read.size⟩

def myByteArray : ByteArray := ⟨#[1, 2, 3]⟩

def ByteArray.write
  (source : ByteArray)
  (sourceAddr : ℕ)
  (dest : ByteArray)
  (destAddr len : ℕ)
  : ByteArray
:=
  if len = 0 then dest else
    if sourceAddr ≥ source.size then
      let len := min len (dest.size - destAddr)
      let destAddr := min destAddr dest.size
      (ByteArray.zeroesUSize ⟨len⟩).copySlice 0 dest destAddr len
    else
      let practicalLen := min len (source.size - sourceAddr)
      let endPaddingAddr := min dest.size (destAddr + len)
      let sourcePaddingLength : ℕ := endPaddingAddr - (destAddr + practicalLen)
      let sourcePadding := ByteArray.zeroesUSize ⟨sourcePaddingLength⟩
      let destPaddingLength : ℕ := destAddr - dest.size
      let destPadding := ByteArray.zeroesUSize ⟨destPaddingLength⟩
      (source ++ sourcePadding).copySlice sourceAddr
        (dest ++ destPadding)
        destAddr
        (practicalLen + sourcePaddingLength)

