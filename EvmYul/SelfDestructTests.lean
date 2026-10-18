module

public import EvmYul.SelfDestruct
public meta import EvmYul.SelfDestruct
public import EvmYul.Yul.Interpreter
public meta import EvmYul.Yul.Interpreter
public import EvmYul.Testing.EvmFixtures
public meta import EvmYul.Testing.EvmFixtures
@[expose] public meta section

/-!
# Tests of `SELFDESTRUCT` in the EVM and in Yul (EIP-6780)

These run during `lake build EvmYulGasTests`. Each test builds **one** world state, generic in the
machine type, and runs the EVM case and the Yul case of `EvmYul.step` on it. The world state has a
code owner (address 7) with balance `balO`, a beneficiary `r` that may or may not hold an account
(balance `balR`), and the code owner may or may not have been created in this transaction.

1. **Unit checks**, one per EIP-6780 case (created or not, beneficiary itself or another account,
   beneficiary existing or not), and an interpreter check that Yul stops after `selfdestruct`.
2. **Property tests** (Plausible, fixed seed, counted): the EVM and the Yul results both equal
   `specObs`, a rule written from EIP-6780 that shares no code with `State.selfDestruct`; hence
   they also agree with each other.
3. **Mutation tests**: the same properties against a re-implementation of the *old* Yul case
   (always schedule deletion, always burn Ether sent to itself). Plausible must find a
   counterexample, so the properties detect the bug they guard against.
-/

namespace EvmYul.SelfDestructTests

open Plausible EvmYul.Testing.EvmFixtures

/-- An address from a small number. -/
def addr (n : ℕ) : AccountAddress := Fin.ofNat _ n

/-- The code owner of every test state. -/
def owner : AccountAddress := addr 7

/-- An account holding `b` Wei. -/
def acct (τ : OperationType) (b : ℕ) : Account τ := { (default : Account τ) with balance := u b }

/-- The world state of a test, for either machine: the owner holds `balO`; the beneficiary `addr rN`
holds `balR` if `rExists` (and it is not the owner); the owner was created in this transaction iff
`created`. Writes are permitted (`perm`), i.e. this is not a static call. -/
def world (τ : OperationType) (rN balO balR : ℕ) (rExists created : Bool) : State τ :=
  let r := addr rN
  let m : AccountMap τ := (∅ : AccountMap τ).insert owner (acct τ balO)
  let m := if rExists && r != owner then m.insert r (acct τ balR) else m
  { (default : State τ) with
      accountMap := m
      executionEnv := { (default : ExecutionEnv τ) with codeOwner := owner, perm := true }
      createdAccounts := if created then (∅ : Std.TreeSet AccountAddress compare).insert owner
        else ∅ }

/-- What a test observes of a world state: the balances of the owner and of `addr rN` (`none` for
no account), the self-destruct set, and whether `addr rN` is warm. -/
def obs {τ : OperationType} (σ : State τ) (rN : ℕ) : List (Option ℕ) × List ℕ × Bool :=
  ([owner, addr rN].map fun a => (σ.lookupAccount a).map (·.balance.toNat),
   σ.substate.selfDestructSet.toList.map (·.val),
   σ.substate.accessedAccounts.contains (addr rN))

/-- **The rule, written from EIP-6780** (independent of `State.selfDestruct`): the expected
observation after `SELFDESTRUCT` to `addr rN` in `world _ rN balO balR rExists created`. -/
def specObs (rN balO balR : ℕ) (rExists created : Bool) : List (Option ℕ) × List ℕ × Bool :=
  let toSelf := addr rN == owner
  let ownerBal : ℕ := if toSelf then (if created then 0 else balO) else
    (if rExists || balO != 0 then 0 else balO)
  let rBal : Option ℕ :=
    if toSelf then some ownerBal
    else if rExists then some (balR + balO)
    else if balO != 0 then some balO
    else none
  ([some ownerBal, rBal], if created then [owner.val] else [], true)

/-- Run the EVM case of `SELFDESTRUCT` (beneficiary `addr rN` on the stack). -/
def evmRun (rN balO balR : ℕ) (rExists created : Bool) : Option (State .EVM) :=
  let s : EVM.State :=
    { (default : EVM.State) with toState := world .EVM rN balO balR rExists created, stack := [u rN] }
  match EvmYul.step (τ := .EVM) .SELFDESTRUCT none s with
  | .ok s' => some s'.toState
  | .error _ => none

/-- The Yul start state over the same world. -/
def yulStart (rN balO balR : ℕ) (rExists created : Bool) : Yul.State :=
  .Ok { (default : SharedState .Yul) with toState := world .Yul rN balO balR rExists created } ∅

/-- Run the Yul case of `SELFDESTRUCT`; `some` only if it **halts** (`YulHalt`). -/
def yulRun (rN balO balR : ℕ) (rExists created : Bool) : Option (State .Yul) :=
  match EvmYul.step (τ := .Yul) .SELFDESTRUCT none (yulStart rN balO balR rExists created) [u rN] with
  | .error (.YulHalt y _) => some y.toState
  | _ => none

/-- Re-implementation of the **old** Yul case, for the mutation tests: the owner always joins the
self-destruct set, and Ether sent to itself is always burnt (the pre-Cancun rule). -/
def oldYulSelfDestruct {τ : OperationType} (σ : State τ) (r : AccountAddress) : State τ :=
  let Iₐ := σ.executionEnv.codeOwner
  let new := σ.selfDestruct r
  { new with
      substate := { new.substate with selfDestructSet := σ.substate.selfDestructSet.insert Iₐ }
      accountMap :=
        if r == Iₐ then
          (σ.lookupAccount Iₐ).elim σ.accountMap fun a => σ.accountMap.insert Iₐ {a with balance := ⟨0⟩}
        else new.accountMap }

/-- The old Yul case on a test world. -/
def oldYulRun (rN balO balR : ℕ) (rExists created : Bool) : State .Yul :=
  oldYulSelfDestruct (world .Yul rN balO balR rExists created) (addr rN)

/-- Does the EVM result match the rule? -/
def evmOk (rN balO balR : ℕ) (rExists created : Bool) : Bool :=
  (evmRun rN balO balR rExists created).map (obs · rN) == some (specObs rN balO balR rExists created)

/-- Does the Yul result match the rule (and does Yul halt)? -/
def yulOk (rN balO balR : ℕ) (rExists created : Bool) : Bool :=
  (yulRun rN balO balR rExists created).map (obs · rN) == some (specObs rN balO balR rExists created)

/-- Do the EVM and the Yul result agree? -/
def agree (rN balO balR : ℕ) (rExists created : Bool) : Bool :=
  let e := (evmRun rN balO balR rExists created).map (obs · rN)
  e.isSome && e == (yulRun rN balO balR rExists created).map (obs · rN)

/-- `selfdestruct(9)` followed by `sstore(0, 1)`: the store must not run, since Yul halts. -/
def destructThenStore : Yul.Ast.Stmt :=
  .Block [.ExprStmtCall (.Call (.inl (.System .SELFDESTRUCT)) [.Lit (u 9)]),
          .ExprStmtCall (.Call (.inl (.StackMemFlow .SSTORE)) [.Lit (u 0), .Lit (u 1)])]

/-- Run `destructThenStore` in the interpreter. Returns, if execution halted, whether the owner's
storage is still empty and whether the owner is scheduled for deletion. -/
def interpHalt (created : Bool) : Option (Bool × Bool) :=
  match Yul.exec 10 destructThenStore none (yulStart 9 5 0 true created) with
  | .error (.YulHalt y _) =>
    let σ := y.toState
    some ((σ.lookupAccount owner).all (·.storage.isEmpty),
          σ.substate.selfDestructSet.contains owner)
  | _ => none

/-! ## 1. Unit checks -/

/-- Named checks; each must be `true`. -/
def unitChecks : List (String × Bool) :=
  [ ("created, to another existing account: balance moves, owner scheduled (EVM, Yul)",
      evmOk 9 5 3 true true && yulOk 9 5 3 true true &&
      specObs 9 5 3 true true == ([some 0, some 8], [7], true)),
    ("not created, to another existing account: balance moves, owner NOT scheduled (EVM, Yul)",
      evmOk 9 5 3 true false && yulOk 9 5 3 true false &&
      specObs 9 5 3 true false == ([some 0, some 8], [], true)),
    ("not created, to itself: no balance change, not scheduled (EVM, Yul)",
      evmOk 7 5 0 false false && yulOk 7 5 0 false false &&
      specObs 7 5 0 false false == ([some 5, some 5], [], true)),
    ("created, to itself: Ether burnt, scheduled (EVM, Yul)",
      evmOk 7 5 0 false true && yulOk 7 5 0 false true &&
      specObs 7 5 0 false true == ([some 0, some 0], [7], true)),
    ("to a missing account with balance: account created with the balance (EVM, Yul)",
      evmOk 9 5 0 false false && yulOk 9 5 0 false false &&
      specObs 9 5 0 false false == ([some 0, some 5], [], true)),
    ("to a missing account with zero balance: no account created (EVM, Yul)",
      evmOk 9 0 0 false true && yulOk 9 0 0 false true &&
      specObs 9 0 0 false true == ([some 0, none], [7], true)),
    ("Yul SELFDESTRUCT halts instead of returning", (yulRun 9 5 3 true false).isSome),
    ("interpreter: nothing runs after selfdestruct; created owner is scheduled",
      interpHalt true == some (true, true)),
    ("interpreter: nothing runs after selfdestruct; existing owner is not scheduled",
      interpHalt false == some (true, false)),
    ("the old Yul case disagrees on 'not created, to itself' (it burnt the Ether)",
      obs (oldYulRun 7 5 0 false false) 7 != specObs 7 5 0 false false) ]

/-! ## 2. Property and mutation tests -/

/-- Run every check; throws on the first failure. -/
def runAll : IO Unit := do
  for (name, ok) in unitChecks do
    unless ok do throw <| IO.userError s!"unit check failed: {name}"
  IO.println s!"{unitChecks.length} unit checks passed"
  expectHolds "EVM SELFDESTRUCT follows EIP-6780 (specObs)"
    (∀ rN balO balR : ℕ, ∀ rExists created : Bool,
      evmOk (rN % 12) (balO % 4) (balR % 4) rExists created = true)
  expectHolds "Yul SELFDESTRUCT halts and follows EIP-6780 (specObs)"
    (∀ rN balO balR : ℕ, ∀ rExists created : Bool,
      yulOk (rN % 12) (balO % 4) (balR % 4) rExists created = true)
  expectHolds "EVM and Yul SELFDESTRUCT end with the same world state"
    (∀ rN balO balR : ℕ, ∀ rExists created : Bool,
      agree (rN % 12) (balO % 4) (balR % 4) rExists created = true)
  IO.println "3 property suites passed"
  expectRefuted "mutant (old Yul SELFDESTRUCT) follows EIP-6780"
    (∀ rN balO balR : ℕ, ∀ rExists created : Bool,
      (obs (oldYulRun (rN % 12) (balO % 4) (balR % 4) rExists created) (rN % 12) ==
        specObs (rN % 12) (balO % 4) (balR % 4) rExists created) = true)
  expectRefuted "mutant (old Yul SELFDESTRUCT) agrees with the EVM"
    (∀ rN balO balR : ℕ, ∀ rExists created : Bool,
      ((evmRun (rN % 12) (balO % 4) (balR % 4) rExists created).map (obs · (rN % 12)) ==
        some (obs (oldYulRun (rN % 12) (balO % 4) (balR % 4) rExists created) (rN % 12))) = true)

#eval runAll

end EvmYul.SelfDestructTests
