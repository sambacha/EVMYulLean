module

public import EvmYul.EVM.Gas.Classification
public meta import EvmYul.EVM.Gas.Classification
public import EvmYul.Testing.Counted
public meta import EvmYul.Testing.Counted
public import Plausible
public meta import Plausible

@[expose] public meta section

/-!
# Shared fixtures and generators for the EVM tests

Used by the gas, semantics, Yul, Solidity and Vyper test files (previously part of the gas test
file, which nine other test files therefore imported as a library):

* **state fixtures**: a default state with a given stack, gas, warm slots/accounts, an owner
  account; a legacy transaction;
* **result readers**: `isOOG`, `okNat?`;
* **Plausible generators**: `UInt256` biased toward `0` and the `2^256` boundary (where wrap-around
  bugs live), and `AnyOp`, an operation drawn uniformly from the decode table;
* **the seeded harness**: `cfg`, `expectHolds` (fails on a counterexample or on too few valid
  inputs) and `expectRefuted` (mutation tests: fails unless a counterexample is found), both
  printing `total/valid/discarded` counts (`EvmYul/Testing/Counted.lean`).

Self-checks of the fixtures are in `EvmYul/Testing/EvmFixturesTests.lean`.
-/

namespace EvmYul.Testing.EvmFixtures

open EvmYul EvmYul.EVM
open GasConstants GasMeter Plausible Plausible.Decorations

/-! ## Rules written from the specification

Expected values of the gas tests are written as these rules applied to the input (`TESTING.md`
O2). They are transcribed from the Yellow Paper and the EIPs and share no code with the cost
functions under test (`EvmYul/EVM/Gas/Costs.lean`). -/

/-- `⌈n / 32⌉`: the number of 32-byte words covering `n` bytes. -/
def wordsOf (n : ℕ) : ℕ := (n + 31) / 32

/-- EIP-150: all but one 64th of `n`. -/
def allButOne64th (n : ℕ) : ℕ := n - n / 64

/-- YP (328): the memory cost of `a` active words, `G_memory · a + ⌊a² / 512⌋`. -/
def memSpec (a : ℕ) : ℕ := Gmemory * a + a * a / 512

/-- EIP-3529: gas returned after execution, from limit `gl`, remaining `g'` and refund counter `r`:
the remaining gas plus the refund, capped at a fifth of the gas used. -/
def refundRule (gl g' r : ℕ) : ℕ := g' + min r ((gl - g') / 5)

/-! ## State fixtures -/

/-- The default EVM state with the given stack (top of stack first). -/
def withStack (xs : List UInt256) : EVM.State := { (default : EVM.State) with stack := xs }

/-- Mark storage key `k` of the (default) code owner as warm. -/
def warmSlot (s : EVM.State) (k : UInt256) : EVM.State :=
  { s with substate := { s.substate with
      accessedStorageKeys := s.substate.accessedStorageKeys.insert (s.executionEnv.codeOwner, k) } }

/-- Mark account `a` as warm. -/
def warmAccount (s : EVM.State) (a : AccountAddress) : EVM.State :=
  { s with substate := { s.substate with
      accessedAccounts := s.substate.accessedAccounts.insert a } }

/-- Install a (default, empty-storage) account for the code owner so that `SSTORE` can read it. -/
def withOwnerAccount (s : EVM.State) : EVM.State :=
  { s with accountMap := s.accountMap.insert s.executionEnv.codeOwner default }

/-- Set the available gas. -/
def withGas (s : EVM.State) (g : ℕ) : EVM.State :=
  { s with toMachineState := { s.toMachineState with gasAvailable := .ofNat g } }

/-- `UInt256` literal. -/
def u (n : ℕ) : UInt256 := .ofNat n

/-- Did a charge fail with out-of-gas? -/
def isOOG : Except ExecutionException UInt256 → Bool
  | .error .OutOfGass => true
  | _ => false

/-- The remaining gas of a successful charge, as a natural number. -/
def okNat? : Except ExecutionException UInt256 → Option ℕ
  | .ok g => some g.toNat
  | .error _ => none

/-- A legacy transaction to `recipient` (`none`: contract creation) with call data `data`. -/
def legacyTx (recipient : Option AccountAddress) (data : List UInt8) : Transaction :=
  .legacy { nonce := ⟨0⟩, gasLimit := u 1000000, recipient, value := ⟨0⟩, r := .empty,
            s := .empty, data := ⟨data.toArray⟩, gasPrice := ⟨0⟩, w := ⟨0⟩ }

/-- Every operation reachable by decoding a byte. -/
def decodedOps : List (Operation .EVM) :=
  (List.range 256).filterMap fun n => parseInstr (UInt8.ofNat n)

/-! ## Generators and the seeded harness -/

/-- `UInt256` counterexamples are not shrunk (the boundary values are the point). -/
instance : Shrinkable UInt256 := ⟨fun _ => []⟩

/-- `UInt256` generator biased toward small values and the `2^256` boundary. -/
instance : Arbitrary UInt256 where
  arbitrary := do
    let n ← Gen.chooseNat
    let k ← Gen.chooseNat
    match k % 4 with
    | 0 => pure (UInt256.ofNat n)
    | 1 => pure (UInt256.ofNat (UInt256.size - 1 - n))
    | 2 => pure (UInt256.ofNat (2 ^ (n % 256) + k))
    | _ => pure (UInt256.ofNat (n * 1000 + k))

/-- Random EVM operation, drawn uniformly from the decode table. -/
structure AnyOp where
  byte : Fin 256
  deriving Repr

/-- The operation the byte decodes to (`INVALID` for an undefined byte). -/
def AnyOp.op (o : AnyOp) : Operation .EVM := (parseInstr (UInt8.ofNat o.byte.val)).getD .INVALID

/-- Operations are not shrunk. -/
instance : Shrinkable AnyOp := ⟨fun _ => []⟩
instance : Arbitrary AnyOp where
  arbitrary := do
    let n ← Gen.choose Nat 0 255 (by decide)
    pure ⟨⟨n.val, by omega⟩⟩

/-- Seeded configuration (`TESTING.md` E3): 300 samples, fixed seed. -/
def cfg : Configuration := { numInst := 300, maxSize := 1000, randomSeed := some 20261001,
                             quiet := true }

/-- Fail the build on a counterexample, or when fewer than `minValid` inputs (default: half of the
samples) satisfied the property's guards; print `total/valid/discarded` (`CountedTesting`). -/
def expectHolds (name : String) (p : Prop)
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p']
    (minValid : Nat := CountedTesting.defaultMinValid cfg) : IO Unit :=
  discard <| CountedTesting.holdsCore cfg name p' minValid

/-- Mutation test: fail the build unless a counterexample is found (counts printed). -/
def expectRefuted (name : String) (p : Prop)
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] : IO Unit :=
  discard <| CountedTesting.refutedCore cfg name p'

end EvmYul.Testing.EvmFixtures
