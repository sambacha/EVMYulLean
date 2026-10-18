module

public import EvmYul.Maps.TreeMap
public meta import EvmYul.Maps.TreeMap
public import EvmYul.Testing.MapModel
public meta import EvmYul.Testing.MapModel
public import EvmYul.Testing.Counted
public meta import EvmYul.Testing.Counted
public import Plausible
public meta import Plausible

@[expose] public meta section

/-!
# Tests for the storage tree map (`EvmYul/Maps/TreeMap.lean`)

Run during `lake build EvmYulGasTests`; any failing check fails the build.

`Storage` is a `Std.TreeMap` ordered by `compare`. These checks execute the storage operations
against the independent reference model of `EvmYul/Testing/MapModel.lean` (an association list
with last-write-wins lookup), so a change of representation, comparator or construction order that
alters behaviour is caught by evaluation. The account maps and the substate's access sets are
tested in `EvmYul/State/AccountMapTests.lean`.

1. **Unit checks**: the reference model itself, `ofList` with duplicate keys, ordered iteration,
   `partition`, and the two counterexamples of `EvmYul/Maps/TreeMap.lean` evaluated.
2. **Property tests** (Plausible, seeded, counted): lookups agree with the reference; keys are
   listed sorted and without duplicates; construction order does not matter; `erase`, `partition`
   and `foldl` behave as specified.
3. **Mutation tests**: a first-write-wins reference, a comparator that identifies distinct keys,
   and an insertion-ordered (unsorted) association list must each be refuted by the same properties.
-/

namespace EvmYul.Maps.TreeMapTests

open Plausible Plausible.Decorations Std EvmYul.Testing.MapModel

/-! ## Storage under test -/

/-- A storage built from the entries, in list order. -/
def mkStorage (l : List (ℕ × ℕ)) : Storage :=
  TreeMap.ofList ((entries l).map fun (k, v) => (UInt256.ofNat k, UInt256.ofNat v)) compare

/-- The storage's lookup, read back as a natural number. -/
def getNat (s : Storage) (k : ℕ) : Option ℕ := (s.get? (UInt256.ofNat k)).map UInt256.toNat

/-- A map under the collapsing comparator (keys with the same parity are identified). -/
def mkCollapsing (l : List (ℕ × ℕ)) : TreeMap ℕ ℕ collapsingCmp :=
  TreeMap.ofList (entries l) collapsingCmp

/-! ## Unit checks -/

/-- Named unit checks; each must evaluate to `true`. -/
def unitChecks : List (String × Bool) :=
  selfChecks ++
  [("ofList with a repeated key keeps the last value",
    getNat (mkStorage [(3, 1), (3, 2)]) 3 == some 2),
   ("keys are listed in increasing order whatever the insertion order",
     (mkStorage [(5, 0), (1, 0), (3, 0)]).keys.map UInt256.toNat == [1, 3, 5]),
   ("partition splits by the predicate",
     let (yes, no) := (mkStorage [(1, 2), (2, 3), (3, 4)]).partition fun _ v => v.toNat % 2 == 0
     yes.keys.map UInt256.toNat == [1, 3] && no.keys.map UInt256.toNat == [2]),
   ("maps built in different orders compare equal",
     mkStorage [(1, 1), (2, 2)] == mkStorage [(2, 2), (1, 1)]),
   ("counterexample: under collapsingCmp, writing key 2 overwrites key 0",
     (((∅ : TreeMap ℕ ℕ collapsingCmp).insert 0 1).insert 2 5).get? 0 == some 5),
   ("counterexample: under alwaysLt, a written key cannot be read back",
     ((∅ : TreeMap ℕ ℕ alwaysLt).insert 0 0).get? 0 == none)]

/-! ## Property tests -/

/-- Seeded configuration (`TESTING.md` E3). -/
def cfg : Configuration := { numInst := 300, maxSize := 40, randomSeed := some 20261010,
                             quiet := true }

/-- Fail the build on a counterexample or on too few valid inputs (counts printed). -/
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
  for (name, ok) in unitChecks do
    unless ok do throw <| IO.userError s!"unit check failed: {name}"
  IO.println s!"storage tree map: {unitChecks.length} unit checks passed"
  expectHolds "storage lookup = last-write-wins reference"
    (∀ (l : List (ℕ × ℕ)) (k : ℕ), getNat (mkStorage l) (keyOf k) = refGet (entries l) (keyOf k))
  expectHolds "storage keys = reference keys (sorted, no duplicates)"
    (∀ l : List (ℕ × ℕ), (mkStorage l).keys.map UInt256.toNat = refKeys (entries l))
  expectHolds "construction order does not matter"
    (∀ ks : List ℕ, (mkStorage (keyed ks)).toList = (mkStorage (keyed ks).reverse).toList)
  expectHolds "erase removes exactly the erased key"
    (∀ (l : List (ℕ × ℕ)) (k j : ℕ),
      getNat ((mkStorage l).erase (UInt256.ofNat (keyOf k))) (keyOf j) =
        if keyOf j = keyOf k then none else refGet (entries l) (keyOf j))
  expectHolds "partition = (filter p, filter (not p))"
    (∀ l : List (ℕ × ℕ),
      let s := mkStorage l
      let p : UInt256 → UInt256 → Bool := fun _ v => v.toNat % 2 == 0
      (s.partition p).1.toList = (s.filter p).toList ∧
        (s.partition p).2.toList = (s.filter fun k v => !p k v).toList)
  expectHolds "foldl visits keys in increasing order"
    (∀ l : List (ℕ × ℕ),
      (mkStorage l).foldl (fun acc k _ => acc ++ [k.toNat]) [] = refKeys (entries l))
  expectRefuted "mutant: first-write-wins reference"
    (∀ (l : List (ℕ × ℕ)) (k : ℕ),
      getNat (mkStorage l) (keyOf k) = refGetFirst (entries l) (keyOf k))
  expectRefuted "mutant: comparator that identifies keys of equal parity"
    (∀ (l : List (ℕ × ℕ)) (k : ℕ), (mkCollapsing l).get? (keyOf k) = refGet (entries l) (keyOf k))
  expectRefuted "mutant: keys listed in insertion order (unsorted association list)"
    (∀ l : List (ℕ × ℕ), insertionKeys (entries l) = refKeys (entries l))

#eval runAll

end EvmYul.Maps.TreeMapTests
