module

public import EvmYul.Maps.TreeMap
public import EvmYul.State.AccountMap
/-!
# Reasoning principles for the account maps

The account maps (`AddrMap`, hence `AccountMap` and `PersistentAccountMap`) are lawful tree maps
(`EvmYul/Maps/TreeMap.lean`). Consequences for the world state:

* **Representation independence of the state root.** Account maps with the same accounts have the
  same state trie root, however they were built (`stateTrieRoot_eq_of_forall_get?_eq`,
  `stateTrieRoot_insert_comm`).
* **Ordered iteration.** Addresses are visited in strictly increasing numeric order
  (`AddrMap.keys_val_strictMono`).
* **Balance updates.** `increaseBalance`, `decreaseBalance` and `transferBalance` change only the
  accounts they name, and `decreaseBalance` fails exactly on a missing account or insufficient funds.

Tests: `EvmYul/State/AccountMapTests.lean`.
-/

public section

namespace EvmYul

open Std

/-- The state trie's leaf list `L_S` depends only on the content of the account map. -/
theorem L_S_eq_of_forall_get?_eq {σ₁ σ₂ : PersistentAccountMap .EVM}
    (h : ∀ a, σ₁.get? a = σ₂.get? a) : L_S σ₁ = L_S σ₂ := by
  simp only [L_S, TreeMap.foldl_eq_foldl_toList, treeMap_toList_eq_of_forall_get?_eq h]

/-- **Representation independence of the state root.** Account maps with the same accounts have
the same state trie root, however they were built. -/
theorem stateTrieRoot_eq_of_forall_get?_eq {σ₁ σ₂ : PersistentAccountMap .EVM}
    (h : ∀ a, σ₁.get? a = σ₂.get? a) : stateTrieRoot σ₁ = stateTrieRoot σ₂ := by
  simp only [stateTrieRoot, L_S_eq_of_forall_get?_eq h]

/-- The state root does not depend on the order in which two different accounts are written. -/
theorem stateTrieRoot_insert_comm (σ : PersistentAccountMap .EVM) {a b : AccountAddress}
    (hab : a ≠ b) (x y : PersistentAccountState .EVM) :
    stateTrieRoot ((σ.insert a x).insert b y) = stateTrieRoot ((σ.insert b y).insert a x) := by
  simp only [stateTrieRoot, L_S, TreeMap.foldl_eq_foldl_toList, treeMap_toList_insert_comm σ hab]

/-! ## Ordered iteration -/

/-- Account maps visit addresses in strictly increasing numeric order. -/
theorem AddrMap.keys_val_strictMono {α : Type} [Inhabited α] (σ : AddrMap α) :
    σ.keys.Pairwise (fun a b => a.val < b.val) :=
  (TreeMap.ordered_keys (t := σ)).imp fun h => Nat.compare_eq_lt.mp h

/-! ## Balance updates -/

namespace AccountMap

variable {τ : OperationType} (σ : AccountMap τ)

/-- The credited account ends with its old balance (or none, for a new account) plus the amount. -/
theorem balance_increaseBalance_self (a : AccountAddress) (v : UInt256) :
    ((σ.increaseBalance τ a v).get? a).map (·.balance) =
      some (match σ.get? a with | none => v | some acc => acc.balance + v) := by
  unfold AccountMap.increaseBalance
  cases σ.get? a <;> simp only [treeMap_get?_insert_self, Option.map_some]

/-- Crediting one account leaves every other account unchanged. -/
theorem get?_increaseBalance_of_ne {a b : AccountAddress} (h : a ≠ b) (v : UInt256) :
    (σ.increaseBalance τ a v).get? b = σ.get? b := by
  unfold AccountMap.increaseBalance
  cases σ.get? a <;> exact treeMap_get?_insert_of_ne _ h _

/-- A debit fails exactly when the account is missing or holds less than the amount. -/
theorem decreaseBalance_eq_none_iff (a : AccountAddress) (v : UInt256) :
    σ.decreaseBalance τ a v = none ↔ ∀ acc, σ.get? a = some acc → acc.balance < v := by
  unfold AccountMap.decreaseBalance
  cases σ.get? a with
  | none => simp
  | some acc => by_cases h : acc.balance < v <;> simp [h]

/-- A successful debit leaves every other account unchanged. -/
theorem get?_decreaseBalance_of_ne {a b : AccountAddress} (h : a ≠ b) {v : UInt256}
    {σ' : AccountMap τ} (hσ : σ.decreaseBalance τ a v = some σ') :
    σ'.get? b = σ.get? b := by
  unfold AccountMap.decreaseBalance at hσ
  cases ha : σ.get? a <;> rw [ha] at hσ
  · cases hσ
  · rename_i acc
    by_cases hlt : acc.balance < v
    · simp [hlt] at hσ
    · simp only [hlt, if_false, Option.some.injEq] at hσ
      subst hσ
      exact treeMap_get?_insert_of_ne _ h _

/-- A successful transfer leaves every account other than sender and recipient unchanged. -/
theorem get?_transferBalance_of_ne {f t c : AccountAddress} (hf : f ≠ c) (ht : t ≠ c)
    {v : UInt256} {σ' : AccountMap τ} (hσ : σ.transferBalance τ f t v = some σ') :
    σ'.get? c = σ.get? c := by
  unfold AccountMap.transferBalance at hσ
  cases hd : σ.decreaseBalance τ f v <;> rw [hd] at hσ
  · cases hσ
  · rename_i σ₁
    rw [← get?_decreaseBalance_of_ne σ hf hd, ← get?_increaseBalance_of_ne σ₁ ht v]
    exact congrArg (·.get? c) (Option.some.inj hσ).symm

end AccountMap

end EvmYul
