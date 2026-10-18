module

public import Mathlib.Data.Multiset.Sort

public section

/-!
# Sorted lists of multisets

`computeToList!`: the elements of a finite multiset as a sorted list.
-/

def computeToList! {α}
                   [LE α] [IsTrans α (· ≤ ·)] [Std.Antisymm (α := α) (· ≤ ·)] [Std.Total (α := α) (· ≤ ·)]
                   [DecidableRel (α := α) (· ≤ ·)] (m : Multiset α) : List α :=
  m.sort (· ≤ ·)
