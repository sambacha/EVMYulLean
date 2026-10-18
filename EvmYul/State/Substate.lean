module

public import EvmYul.FFI.Primitives
public import Std.Data.TreeSet
public import EvmYul.UInt256
public import EvmYul.Wheels
public import EvmYul.State.Account

/-!
# Substate

`Substate` (`A` of the Yellow Paper): self-destruct set, logs, touched accounts, refund counter, and
the accessed accounts and storage keys of EIP-2929, with the order on storage keys.
-/

public section

namespace EvmYul

/--
Not important for reasoning about Substate, this is currently done to get some nice performance properties
of the `Std.TreeSet`.

TODO - to reason about the model, we will be better off with `Finset` or some such -
without the requirement of ordering.

The current goal is to make sure that the model is executable and conformance-testable
before we make it easy to reason about.
-/
def Substate.storageKeysCmp (sk₁ sk₂ : AccountAddress × UInt256) : Ordering :=
  lexOrd.compare sk₁ sk₂

/-- `storageKeysCmp` is the lexicographic combination of the address and slot orders. -/
theorem Substate.storageKeysCmp_eq :
    storageKeysCmp = compareLex (compareOn Prod.fst) (compareOn Prod.snd) := by
  funext x y; simp [storageKeysCmp, lexOrd, compareLex, compareOn]

instance : Std.TransCmp Substate.storageKeysCmp := by
  rw [Substate.storageKeysCmp_eq]; infer_instance

instance : Std.LawfulEqCmp Substate.storageKeysCmp where
  compare_self := by simp [Substate.storageKeysCmp, lexOrd, Std.ReflCmp.compare_self]
  eq_of_compare {a b} h := by
    simp only [Substate.storageKeysCmp, lexOrd, compareLex, compareOn, Ordering.then_eq_eq] at h
    exact Prod.ext (Std.LawfulEqCmp.eq_of_compare h.1) (Std.LawfulEqCmp.eq_of_compare h.2)

@[expose] section

structure LogEntry where
  address : AccountAddress
  topics  : Array UInt256
  data    : ByteArray
deriving BEq, Inhabited, Repr

end

def LogEntry.to𝕋 : LogEntry → 𝕋
  | ⟨address, topics, data⟩ =>
    .𝕃
      [ .𝔹 address.toByteArray
      , .𝕃 <| topics.toList.map (.𝔹 ∘ UInt256.toByteArray)
      , .𝔹 data
      ]

abbrev LogSeries := Array LogEntry

def LogSeries.to𝕋 (logSeries : LogSeries) : 𝕋 :=
  .𝕃 (logSeries.toList.map LogEntry.to𝕋)

@[expose] section

/--
The `Substate` `A`. Section 6.1.
- `selfDestructSet`    `Aₛ`
- `touchedAccounts`    `Aₜ`
- `refundBalance`      `Aᵣ`
- `accessedAccounts`   `Aₐ`
- `accessedStorageKey` `Aₖ`
- `logSeries`          `Aₗ`
-/
structure Substate where
  selfDestructSet     : Std.TreeSet AccountAddress compare
  touchedAccounts     : Std.TreeSet AccountAddress compare
  refundBalance       : UInt256
  accessedAccounts    : Std.TreeSet AccountAddress compare
  accessedStorageKeys : Std.TreeSet (AccountAddress × UInt256) Substate.storageKeysCmp
  logSeries           : LogSeries
  deriving BEq, Inhabited, Repr

end

/--
  (63) `A0 ≡ (∅, (), ∅, 0, π, ∅)`
-/
def A0 : Substate := { (default : Substate) with accessedAccounts := π }

-- See the Bloom filter function M
def bloomFilter (a : Array ByteArray) : ByteArray  :=
  let zeroes : ByteArray := ByteArray.zeroesUSize 256
  a.foldl set3Bits zeroes
 where
  setBit (bytes256 : ByteArray) (bitIndex : ℕ) : ByteArray :=
    let byteIndex := 255 - bitIndex / 8
    let mask : UInt8 := .ofNat <| 1 <<< (bitIndex % 8)
    let newByte := bytes256[byteIndex]! ||| mask
    bytes256.set! byteIndex newByte
  bitIndices (x : ByteArray) : List ℕ :=
    let kec := ffi.KEC x
    let lowOrder11Bits := λ b ↦ b &&& (1<<<11 - 1)
    [ kec.readWithPadding 0 2
    , kec.readWithPadding 2 2
    , kec.readWithPadding 4 2
    ].map (lowOrder11Bits ∘ fromByteArrayBigEndian)
  set3Bits acc b := bitIndices b |>.foldl setBit acc

def Substate.joinLogs (substate : Substate) : Array ByteArray :=
  Array.flatten <|
    substate.logSeries.map
      λ ⟨a, as, _⟩ ↦ (as.map UInt256.toByteArray).push a.toByteArray

end EvmYul
