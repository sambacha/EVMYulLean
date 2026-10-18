module

public import EvmYul.Maps.StorageMap
public import EvmYul.ProofTags
/-!
# Reasoning principles for the tree maps

`Storage` and the account maps are `Std.TreeMap`s ordered by `compare`, and the access sets of the
substate are `Std.TreeSet`s. This file states what that representation buys, for any lawful
comparator and for `Storage`:

* **Representation independence.** A lawful tree map is determined by its lookups
  (`treeMap_toList_eq_of_forall_get?_eq`); writes to different keys commute; the frame rule and
  read-after-write hold. Hence the storage trie root depends only on the slots, never on the order
  in which they were written (`computeTrieRoot_insert_comm`).
* **Ordered iteration.** Storage slots are visited in strictly increasing order
  (`Storage.keys_val_strictMono`).
* **The hypotheses are load-bearing.** For a comparator that identifies distinct keys, writing one
  key changes the value read at another (`not_get?_insert_of_ne_collapsing`); for a comparator that
  is not reflexive, a key just written cannot be read back (`not_get?_insert_self_alwaysLt`).

The same facts for the account maps (state root, balance updates) are in
`EvmYul/State/AccountMapLemmas.lean`. Tests: `EvmYul/Maps/TreeMapTests.lean`.
-/

public section

namespace EvmYul

open Std

/-! ## Representation independence -/

section Generic

variable {α β : Type} {cmp : α → α → Ordering} [TransCmp cmp] [LawfulEqCmp cmp]

/-- Tree maps with a lawful comparator that agree on every lookup are equivalent. -/
@[reviewed_generic "tree map extensionality (lawful comparator)"]
theorem treeMap_equiv_of_forall_get?_eq {t₁ t₂ : TreeMap α β cmp}
    (h : ∀ k, t₁.get? k = t₂.get? k) : t₁.Equiv t₂ :=
  TreeMap.Equiv.of_forall_constGet?_eq fun k => by simpa only [TreeMap.get?_eq_getElem?] using h k

/-- A tree map with a lawful comparator is determined by its lookups: maps that agree on every
`get?` list the same entries in the same order. -/
@[reviewed_generic "tree map extensionality (lawful comparator)"]
theorem treeMap_toList_eq_of_forall_get?_eq {t₁ t₂ : TreeMap α β cmp}
    (h : ∀ k, t₁.get? k = t₂.get? k) : t₁.toList = t₂.toList :=
  (treeMap_equiv_of_forall_get?_eq h).toList_eq

/-- Writes to two different keys commute, as seen by every lookup. -/
@[reviewed_generic "tree map write commutation (lawful comparator)"]
theorem treeMap_get?_insert_comm (t : TreeMap α β cmp) {a b : α} (hab : a ≠ b) (x y : β)
    (k : α) :
    ((t.insert a x).insert b y).get? k = ((t.insert b y).insert a x).get? k := by
  simp only [TreeMap.get?_eq_getElem?, TreeMap.getElem?_insert]
  by_cases hb : cmp b k = .eq
  · have hbk := LawfulEqCmp.eq_of_compare hb
    subst hbk
    have : cmp a b ≠ .eq := fun h => hab (LawfulEqCmp.eq_of_compare h)
    simp [this]
  · simp [hb]

/-- Writes to two different keys commute, up to the listed entries. -/
@[reviewed_generic "tree map write commutation (lawful comparator)"]
theorem treeMap_toList_insert_comm (t : TreeMap α β cmp) {a b : α} (hab : a ≠ b) (x y : β) :
    ((t.insert a x).insert b y).toList = ((t.insert b y).insert a x).toList :=
  treeMap_toList_eq_of_forall_get?_eq (treeMap_get?_insert_comm t hab x y)

/-- Lookup after a write to a different key is unchanged (the frame rule). -/
@[reviewed_generic "tree map frame rule (lawful comparator)"]
theorem treeMap_get?_insert_of_ne (t : TreeMap α β cmp) {a k : α} (h : a ≠ k) (v : β) :
    (t.insert a v).get? k = t.get? k := by
  have : cmp a k ≠ .eq := fun h' => h (LawfulEqCmp.eq_of_compare h')
  simp [TreeMap.get?_eq_getElem?, TreeMap.getElem?_insert, this]

/-- Lookup after a write to the same key returns the written value. -/
@[reviewed_generic "tree map read-after-write (lawful comparator)"]
theorem treeMap_get?_insert_self (t : TreeMap α β cmp) (k : α) (v : β) :
    (t.insert k v).get? k = some v := by
  simp [TreeMap.get?_eq_getElem?]

end Generic

/-- **Representation independence of the storage root.** Storages with the same slots have the
same storage trie root. -/
theorem computeTrieRoot_eq_of_forall_get?_eq {s₁ s₂ : Storage}
    (h : ∀ k, s₁.get? k = s₂.get? k) : computeTrieRoot s₁ = computeTrieRoot s₂ := by
  simp only [computeTrieRoot, (treeMap_equiv_of_forall_get?_eq h).toArray_eq]

/-- The storage root does not depend on the order in which two different slots are written. -/
theorem computeTrieRoot_insert_comm (s : Storage) {a b : UInt256} (hab : a ≠ b) (x y : UInt256) :
    computeTrieRoot ((s.insert a x).insert b y) = computeTrieRoot ((s.insert b y).insert a x) :=
  computeTrieRoot_eq_of_forall_get?_eq (treeMap_get?_insert_comm s hab x y)

/-! ## Ordered iteration -/

/-- Storages visit slots in strictly increasing numeric order. -/
theorem Storage.keys_val_strictMono (s : Storage) :
    s.keys.Pairwise (fun a b => a.toNat < b.toNat) :=
  (TreeMap.ordered_keys (t := s)).imp fun {a b} h => by
    rw [UInt256.compare_def] at h
    exact Nat.compare_eq_lt.mp h

/-! ## The lawfulness hypotheses are load-bearing -/

/-- A comparator that identifies keys with the same parity: transitive, but not `LawfulEqCmp`. -/
@[expose] def collapsingCmp (a b : ℕ) : Ordering := compare (a % 2) (b % 2)

/-- A comparator that never reports equality: not reflexive. -/
@[expose] def alwaysLt (_ _ : ℕ) : Ordering := .lt

/-- **Counterexample to the frame rule without `LawfulEqCmp`.** Under `collapsingCmp`, writing key
`2` overwrites the value read at key `0`. -/
theorem not_get?_insert_of_ne_collapsing :
    ¬ ∀ (t : TreeMap ℕ ℕ collapsingCmp) (a k : ℕ), a ≠ k →
      ∀ v, (t.insert a v).get? k = t.get? k := by
  intro h
  have := h ((∅ : TreeMap ℕ ℕ collapsingCmp).insert 0 1) 2 0 (by decide) 5
  revert this
  decide

/-- **Counterexample to read-after-write without reflexivity.** Under `alwaysLt`, a key just
written cannot be read back. -/
theorem not_get?_insert_self_alwaysLt :
    ¬ ∀ (t : TreeMap ℕ ℕ alwaysLt) (k v : ℕ), (t.insert k v).get? k = some v := by
  intro h
  have := h ∅ 0 0
  revert this
  decide

end EvmYul
