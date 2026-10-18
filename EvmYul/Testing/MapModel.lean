module

public import Std.Data.TreeMap

@[expose] public section

/-!
# Reference model for map tests

An association list with **last-write-wins** lookup. It shares no code with `Std.TreeMap`, so
tests that compare a tree map against it (`EvmYul/Maps/TreeMapTests.lean`,
`EvmYul/State/AccountMapTests.lean`) catch any change of representation, comparator or
construction order that alters behaviour. The two mutant references (`refGetFirst`,
`insertionKeys`) exist so that those tests can show their properties are not vacuous: each mutant
must be refuted.

Keys are reduced to `16` values (`keyOf`) so that random lists contain duplicate keys.
-/

namespace EvmYul.Testing.MapModel

/-- Keys are reduced to `16` values so that random lists contain duplicate keys. -/
def keyOf (k : Nat) : Nat := k % 16

/-- Reference lookup on an association list: the **last** binding of a key wins. -/
def refGet (l : List (Nat × Nat)) (k : Nat) : Option Nat :=
  (l.reverse.find? (·.1 == k)).map (·.2)

/-- Mutant reference: the **first** binding wins. -/
def refGetFirst (l : List (Nat × Nat)) (k : Nat) : Option Nat :=
  (l.find? (·.1 == k)).map (·.2)

/-- Reference key listing: every reduced key that occurs, in increasing order (by enumeration, not
by sorting). -/
def refKeys (l : List (Nat × Nat)) : List Nat :=
  (List.range 16).filter fun k => l.any (·.1 == k)

/-- Mutant listing: keys in order of first insertion (an unsorted association list). -/
def insertionKeys (l : List (Nat × Nat)) : List Nat :=
  (l.map (·.1)).eraseDups

/-- Random entries with reduced keys. -/
def entries (l : List (Nat × Nat)) : List (Nat × Nat) := l.map fun (k, v) => (keyOf k, v)

/-- Entries whose value is a function of the key, so any order describes the same map. -/
def keyed (ks : List Nat) : List (Nat × Nat) := ks.map fun k => (keyOf k, 7 * keyOf k + 1)

/-- Unit checks of the model itself (the reference must be right before it can judge anything). -/
def selfChecks : List (String × Bool) :=
  [("refGet: last binding wins", refGet [(1, 2), (1, 3)] 1 == some 3),
   ("refGet: missing key", refGet [(1, 2)] 0 == none),
   ("refGetFirst: first binding wins", refGetFirst [(1, 2), (1, 3)] 1 == some 2),
   ("refKeys: sorted, no duplicates", refKeys [(5, 0), (1, 0), (5, 1)] == [1, 5]),
   ("insertionKeys: insertion order", insertionKeys [(5, 0), (1, 0), (5, 1)] == [5, 1]),
   ("entries: keys reduced mod 16", entries [(17, 4)] == [(1, 4)])]

end EvmYul.Testing.MapModel
