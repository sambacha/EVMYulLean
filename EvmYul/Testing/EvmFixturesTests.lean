module

public import EvmYul.Testing.EvmFixtures
public meta import EvmYul.Testing.EvmFixtures

@[expose] public meta section

/-!
# Self-checks of the shared EVM test fixtures (`EvmYul/Testing/EvmFixtures.lean`)

The fixtures and generators are used by a dozen test files, so a broken fixture would silently
weaken all of them. These checks pin what each fixture does and show that the generators reach the
inputs the property tests rely on:

1. **Unit checks**: each state fixture changes exactly the field it names; the result readers.
2. **Property tests** (seeded, counted): `warmSlot` / `warmAccount` make the slot / account warm;
   `withGas` round-trips; `AnyOp` only produces decoded operations.
3. **Mutation tests** (must be refuted): "the `UInt256` generator never reaches the upper half",
   "it never produces small values" and "`AnyOp` never produces `INVALID`". If a generator lost its
   boundary bias, these would hold and the build would fail.
-/

namespace EvmYul.Testing.EvmFixturesTests

open EvmYul EvmYul.EVM Plausible Plausible.Decorations EvmYul.Testing.EvmFixtures

/-- Named unit checks; each must evaluate to `true`. -/
def unitChecks : List (String × Bool) :=
  [("withStack sets the stack, top first", (withStack [u 1, u 2]).stack == [u 1, u 2]),
   ("withStack leaves the gas at its default",
     (withStack [u 1]).gasAvailable == (default : EVM.State).gasAvailable),
   ("withGas sets the gas", (withGas (withStack []) 77).gasAvailable.toNat == 77),
   ("withGas leaves the stack", (withGas (withStack [u 3]) 77).stack == [u 3]),
   ("the default state has no warm slot",
     !(withStack []).substate.accessedStorageKeys.contains ((default : AccountAddress), u 0)),
   ("withOwnerAccount installs the code owner's account",
     ((withOwnerAccount (withStack [])).accountMap.get?
       (withStack []).executionEnv.codeOwner).isSome),
   ("isOOG: out of gas", isOOG (.error .OutOfGass)),
   ("isOOG: success is not out of gas", !isOOG (.ok (u 0))),
   ("okNat?: success", okNat? (.ok (u 5)) == some 5),
   ("okNat?: failure", okNat? (.error .OutOfGass) == none),
   ("decodedOps contains STOP, ADD and PUSH32",
     decodedOps.contains .STOP && decodedOps.contains .ADD && decodedOps.contains .PUSH32)]

/-- Run every check; throws on the first failure. -/
def runAll : IO Unit := do
  for (name, ok) in unitChecks do
    unless ok do throw <| IO.userError s!"unit check failed: {name}"
  IO.println s!"EVM fixtures: {unitChecks.length} unit checks passed"
  expectHolds "warmSlot makes exactly that slot warm"
    (∀ k j : UInt256,
      (warmSlot (withStack []) k).substate.accessedStorageKeys.contains
        ((withStack []).executionEnv.codeOwner, j) = (j == k))
  expectHolds "warmAccount makes the account warm"
    (∀ n : ℕ, (warmAccount (withStack []) (AccountAddress.ofNat n)).substate.accessedAccounts.contains
        (AccountAddress.ofNat n) = true)
  expectHolds "withGas round-trips"
    (∀ g : ℕ, (withGas (withStack []) g).gasAvailable.toNat = g % UInt256.size)
  expectHolds "AnyOp yields a decoded operation"
    (∀ o : AnyOp, decodedOps.contains o.op = true ∨ o.op = .INVALID)
  expectRefuted "mutant: the UInt256 generator never reaches the upper half"
    (∀ x : UInt256, x.toNat < 2 ^ 255)
  expectRefuted "mutant: the UInt256 generator never produces values below 1000"
    (∀ x : UInt256, 1000 ≤ x.toNat)
  expectRefuted "mutant: AnyOp never produces INVALID"
    (∀ o : AnyOp, o.op ≠ .INVALID)

#eval runAll

end EvmYul.Testing.EvmFixturesTests
