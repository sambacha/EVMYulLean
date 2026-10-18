module

public import EvmYul.State.AccountMapLemmas
public meta import EvmYul.State.AccountMapLemmas
public import EvmYul.State.Substate
public meta import EvmYul.State.Substate
public import EvmYul.Testing.MapModel
public meta import EvmYul.Testing.MapModel
public import EvmYul.Testing.Counted
public meta import EvmYul.Testing.Counted
public import Plausible
public meta import Plausible

@[expose] public meta section

/-!
# Tests for the account maps and access sets (`EvmYul/State/AccountMapLemmas.lean`)

Run during `lake build EvmYulGasTests`; any failing check fails the build.

The account maps and the substate's access sets are `Std.TreeMap` / `Std.TreeSet`s. These checks
execute the balance updates and set operations against the independent reference model of
`EvmYul/Testing/MapModel.lean`.

1. **Unit checks**: the precompile set `π`, the lexicographic storage-key order of the substate,
   and the balance updates on fixed accounts.
2. **Property tests** (Plausible, seeded, counted): set union, the frame rule for crediting, and
   the exact failure condition of a debit (`decreaseBalance_eq_none_iff`).
3. **Mutation tests**: "a debit fails only on a missing account" (ignores insufficient funds) and
   "crediting changes no balance" must each be refuted, so the properties above are not vacuous.
-/

namespace EvmYul.State.AccountMapTests

open Plausible Plausible.Decorations Std EvmYul.Testing.MapModel

/-! ## Account maps under test -/

/-- An account with the given balance. -/
def acct (b : ℕ) : Account .EVM := { (default : Account .EVM) with balance := UInt256.ofNat b }

/-- An account map built from `(address, balance)` pairs (addresses reduced to `16` values). -/
def mkAccounts (l : List (ℕ × ℕ)) : AccountMap .EVM :=
  TreeMap.ofList ((entries l).map fun (a, b) => (AccountAddress.ofNat a, acct b)) compare

/-- The address with number `n`. -/
def addr (n : ℕ) : AccountAddress := AccountAddress.ofNat n

/-- The balance of an address, as a natural number, if the account exists. -/
def balanceOf (σ : AccountMap .EVM) (a : ℕ) : Option ℕ :=
  (σ.get? (AccountAddress.ofNat a)).map (·.balance.toNat)

/-- A set of addresses (reduced to `16` values). -/
def mkSet (l : List ℕ) : TreeSet AccountAddress compare :=
  TreeSet.ofList (l.map fun a => AccountAddress.ofNat (keyOf a)) compare

/-! ## Unit checks -/

/-- Named unit checks; each must evaluate to `true`. -/
def unitChecks : List (String × Bool) :=
  [("π lists the precompiles 1..10 in order",
     π.toList.map (·.val) == [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]),
   ("0 and 11 are not precompiles, 1 and 10 are",
     !π.contains (AccountAddress.ofNat 0) && !π.contains (AccountAddress.ofNat 11) &&
       π.contains (AccountAddress.ofNat 1) && π.contains (AccountAddress.ofNat 10)),
   ("storage keys are ordered by address, then slot",
     (TreeSet.ofList [(addr 2, UInt256.ofNat 0), (addr 1, UInt256.ofNat 5),
       (AccountAddress.ofNat 1, UInt256.ofNat 3)] Substate.storageKeysCmp).toList.map
       (fun (a, k) => (a.val, k.toNat)) == [(1, 3), (1, 5), (2, 0)]),
   ("accounts are listed by increasing address",
     (mkAccounts [(9, 1), (2, 1), (5, 1)]).keys.map (·.val) == [2, 5, 9]),
   ("crediting a missing account creates it with the amount",
     balanceOf ((∅ : AccountMap .EVM).increaseBalance .EVM (addr 4) (UInt256.ofNat 9)) 4
       == some 9),
   ("crediting an existing account adds the amount",
     balanceOf ((mkAccounts [(4, 5)]).increaseBalance .EVM (addr 4) (UInt256.ofNat 9)) 4
       == some 14),
   ("a debit equal to the balance succeeds and leaves zero",
     (((mkAccounts [(4, 5)]).decreaseBalance .EVM (addr 4) (UInt256.ofNat 5)).map
       fun σ => balanceOf σ 4) == some (some 0)),
   ("a debit larger than the balance fails",
     ((mkAccounts [(4, 5)]).decreaseBalance .EVM (addr 4) (UInt256.ofNat 6)).isNone),
   ("a debit from a missing account fails",
     ((mkAccounts [(4, 5)]).decreaseBalance .EVM (addr 3) (UInt256.ofNat 0)).isNone),
   ("a transfer moves the amount",
     (((mkAccounts [(1, 10), (2, 0)]).transferBalance .EVM (AccountAddress.ofNat 1)
       (AccountAddress.ofNat 2) (UInt256.ofNat 4)).map fun σ => (balanceOf σ 1, balanceOf σ 2))
       == some (some 6, some 4))]

/-! ## Property tests -/

/-- Seeded configuration (`TESTING.md` E3). -/
def cfg : Configuration := { numInst := 300, maxSize := 40, randomSeed := some 20261011,
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
  IO.println s!"account maps: {unitChecks.length} unit checks passed"
  expectHolds "address-set union contains exactly the members of either set"
    (∀ (xs ys : List ℕ) (a : ℕ),
      ((mkSet xs).union (mkSet ys)).contains (AccountAddress.ofNat (keyOf a)) =
        ((xs ++ ys).any fun x => keyOf x == keyOf a))
  expectHolds "account lookup = last-write-wins reference"
    (∀ (l : List (ℕ × ℕ)) (a : ℕ),
      balanceOf (mkAccounts l) (keyOf a) = refGet (entries l) (keyOf a))
  expectHolds "crediting one account leaves the others unchanged"
    (∀ (l : List (ℕ × ℕ)) (a c v : ℕ), keyOf a ≠ keyOf c →
      balanceOf ((mkAccounts l).increaseBalance .EVM (AccountAddress.ofNat (keyOf a))
        (UInt256.ofNat v)) (keyOf c) = balanceOf (mkAccounts l) (keyOf c))
  expectHolds "a debit fails exactly on a missing account or insufficient funds"
    (∀ (l : List (ℕ × ℕ)) (a v : ℕ),
      ((mkAccounts l).decreaseBalance .EVM (addr (keyOf a)) (UInt256.ofNat v)).isNone =
        match refGet (entries l) (keyOf a) with
        | none => true
        | some b => decide (b < v))
  expectRefuted "mutant: a debit fails only on a missing account"
    (∀ (l : List (ℕ × ℕ)) (a v : ℕ),
      ((mkAccounts l).decreaseBalance .EVM (addr (keyOf a)) (UInt256.ofNat v)).isNone =
        (refGet (entries l) (keyOf a)).isNone)
  expectRefuted "mutant: crediting changes no balance"
    (∀ (l : List (ℕ × ℕ)) (a v : ℕ),
      balanceOf ((mkAccounts l).increaseBalance .EVM (addr (keyOf a)) (UInt256.ofNat v))
        (keyOf a) = balanceOf (mkAccounts l) (keyOf a))

#eval runAll

end EvmYul.State.AccountMapTests
