module

public import EvmYul.State.Substate
public import EvmYul.ProofTags
public section

/-!
# Substate interface lemmas (handoff WP-5, PO-9)

The access sets of `Substate` are `Std.TreeSet`s. The tree-set lemmas need the comparison to be
lawful (`Std.TransCmp`); the instances for the comparisons the substate uses (`compare` on
`AccountAddress` and `UInt256`, and the lexicographic `Substate.storageKeysCmp`) live next to those
definitions. This file states a small interface:

* `contains_insert_self` / `contains_insert_of_contains`: inserting makes a key present and keeps
  every key that was present (for both access sets);
* `warmSlot` / `warmAccount`: what the accessing instructions do to the access sets, with the same
  two facts for each.

The gas consequences (the WP-5 warm-access pilot) are in `EvmYul/EVM/Gas/WarmAccess.lean`. The sets
are not replaced by `Finset` (per the handoff).
-/

namespace EvmYul

namespace Substate

variable {α : Type} {cmp : α → α → Ordering} [Std.TransCmp cmp]

/-- Inserting a key makes it present. -/
@[reviewed_generic "tree set fact"]
theorem contains_insert_self (t : Std.TreeSet α cmp) (k : α) :
    (t.insert k).contains k = true :=
  Std.TreeSet.contains_insert_self

/-- Inserting never removes a key. -/
@[reviewed_generic "tree set fact"]
theorem contains_insert_of_contains {t : Std.TreeSet α cmp} {k : α} (k' : α)
    (h : t.contains k = true) : (t.insert k').contains k = true := by
  simp [Std.TreeSet.contains_insert, h]

/-- Warm a storage slot (what `SLOAD`/`SSTORE` do to `A_K`). -/
def warmSlot (A : Substate) (k : AccountAddress × UInt256) : Substate :=
  { A with accessedStorageKeys := A.accessedStorageKeys.insert k }

/-- Warm an account (what account-accessing instructions do to `A_a`). -/
def warmAccount (A : Substate) (a : AccountAddress) : Substate :=
  { A with accessedAccounts := A.accessedAccounts.insert a }

theorem warmSlot_contains (A : Substate) (k : AccountAddress × UInt256) :
    (A.warmSlot k).accessedStorageKeys.contains k = true := contains_insert_self _ _

theorem warmSlot_contains_of_contains {A : Substate} {k : AccountAddress × UInt256} (k')
    (h : A.accessedStorageKeys.contains k = true) :
    (A.warmSlot k').accessedStorageKeys.contains k = true := contains_insert_of_contains _ h

theorem warmAccount_contains (A : Substate) (a : AccountAddress) :
    (A.warmAccount a).accessedAccounts.contains a = true := contains_insert_self _ _

theorem warmAccount_contains_of_contains {A : Substate} {a : AccountAddress} (a')
    (h : A.accessedAccounts.contains a = true) :
    (A.warmAccount a').accessedAccounts.contains a = true := contains_insert_of_contains _ h

end Substate

end EvmYul
