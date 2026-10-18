module

public import EvmYul.EVM.Gas.ExpByteLength
public meta import EvmYul.EVM.Gas.ExpByteLength
public import EvmYul.Testing.EvmFixtures
public meta import EvmYul.Testing.EvmFixtures
public import EvmYul.Testing.Counted
public meta import EvmYul.Testing.Counted
public import Plausible
public meta import Plausible

@[expose] public meta section

/-!
# Tests for the `EXP` byte length (`EvmYul.EVM.Gas.ExpByteLength`)

Run during `lake build EvmYulGasTests`; any failing check fails the build.

The proofs in `ExpByteLength` establish K-EXP for all inputs; these checks execute the interpreter's
actual cost functions against an *independent* reference (`bytesRef`, a byte-counting loop that
shares no code with `Nat.log`, `Nat.digits` or `toBytesBigEndian`), so a change to either cost
function, or to the theorem statements' reading of them, is caught by evaluation as well.

1. **Unit checks**: boundary exponents `0, 1, 255, 256, 2^64 − 1, 2^64, 2^255, 2^256 − 1`.
2. **Property tests** (Plausible, seeded): `C'` and `instrCost?` charge
   `G_exp + G_expbyte × bytesRef e` on random exponents of every byte length.
3. **Mutation tests**: each wrong reading of the old TODO (no `+ 1`, ceiling logarithm, no zero test)
   must be refuted by the same property.
-/

namespace EvmYul.EVM.ExpByteLengthTests

open Plausible Plausible.Decorations ExpByteLength EvmYul.Testing.EvmFixtures

/-- Independent reference: count the bytes by repeated division (fuel 64 > 33 bytes of a word). -/
def bytesRef (n : ℕ) : ℕ := go 64 n 0
where
  /-- `acc` plus the number of divisions by 256 until `n` is `0`. -/
  go : ℕ → ℕ → ℕ → ℕ
    | 0, _, acc => acc
    | fuel + 1, n, acc => if n = 0 then acc else go fuel (n / 256) (acc + 1)

/-- A word of roughly `k mod 33` bytes, built from two small random numbers. -/
def word (a k : ℕ) : UInt256 := UInt256.ofNat ((a + 1) * 2 ^ (8 * (k % 33)))

/-- The specification K-EXP, executed: Cancun's charge for exponent `e`. -/
def specCost (e : UInt256) : ℕ := GasConstants.Gexp + GasConstants.Gexpbyte * bytesRef e.toNat

/-- Mutant: the factor without `1 +` (one byte short). -/
def costNoSucc (e : UInt256) : ℕ :=
  if e == ⟨0⟩ then GasConstants.Gexp
  else GasConstants.Gexp + GasConstants.Gexpbyte * Nat.log 256 e.toNat

/-- Mutant: the ceiling logarithm `⌈log₂₅₆ e⌉` as the byte count (agrees except at exact powers of
256, where it is one byte short). -/
def costClog (e : UInt256) : ℕ :=
  if e == ⟨0⟩ then GasConstants.Gexp
  else GasConstants.Gexp + GasConstants.Gexpbyte * Nat.clog 256 e.toNat

/-- Mutant: no zero test. -/
def costNoZeroTest (e : UInt256) : ℕ :=
  GasConstants.Gexp + GasConstants.Gexpbyte * (1 + Nat.log 256 e.toNat)

/-- The interpreter's cost of `EXP` with exponent `e`. -/
def interpCost (e : UInt256) : ℕ := C' (withStack [⟨0⟩, e]) .EXP

/-- Named unit checks; each must evaluate to `true`. -/
def unitChecks : List (String × Bool) :=
  let pts : List ℕ := [0, 1, 255, 256, 2 ^ 64 - 1, 2 ^ 64, 2 ^ 255, 2 ^ 256 - 1]
  let bytes : List ℕ := [0, 1, 1, 2, 8, 9, 32, 32]
  [("reference byte counts at the boundaries", pts.map bytesRef == bytes),
   ("byteLength agrees with the reference at the boundaries",
     pts.map byteLength == bytes),
   ("toBytesBigEndian agrees at the boundaries",
     pts.map (fun n => (EvmYul.toBytesBigEndian n).length) == bytes),
   ("C' at the boundaries is G_exp + G_expbyte × bytes",
     pts.map (fun n => interpCost (UInt256.ofNat n)) ==
       bytes.map (fun b => GasConstants.Gexp + GasConstants.Gexpbyte * b)),
   ("instrCost? (Cancun) agrees with C' at the boundaries",
     pts.all fun n => ForkSchedule.cancun.instrCost? 0 (withStack [⟨0⟩, UInt256.ofNat n]) .EXP ==
       some (interpCost (UInt256.ofNat n))),
   ("the maximum charge is G_exp + 32 G_expbyte = 1610",
     interpCost (UInt256.ofNat (2 ^ 256 - 1)) == 1610),
   ("a missing exponent operand has no price",
     ForkSchedule.cancun.instrCost? 0 (withStack [⟨0⟩]) .EXP == none),
   ("counterexample n = 256: ceiling log undercounts", costClog (UInt256.ofNat 256) != specCost (UInt256.ofNat 256)),
   ("counterexample n = 1: without + 1", costNoSucc (UInt256.ofNat 1) != specCost (UInt256.ofNat 1)),
   ("counterexample n = 0: without the zero test", costNoZeroTest ⟨0⟩ != specCost ⟨0⟩)]

/-- Seeded configuration (`TESTING.md` E3). -/
def cfg : Configuration := { numInst := 300, maxSize := 100, randomSeed := some 20261009,
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
  IO.println s!"EXP byte length: {unitChecks.length} unit checks passed"
  expectHolds "C' EXP = G_exp + G_expbyte × bytes (random exponents of every length)"
    (∀ a k : ℕ, interpCost (word a k) = specCost (word a k))
  expectHolds "instrCost? EXP (Cancun) = G_exp + G_expbyte × bytes"
    (∀ a k : ℕ, ForkSchedule.cancun.instrCost? 0 (withStack [⟨0⟩, word a k]) .EXP =
      some (specCost (word a k)))
  expectHolds "byteLength = reference byte count"
    (∀ a k : ℕ, byteLength (word a k).toNat = bytesRef (word a k).toNat)
  expectRefuted "mutant: factor without + 1"
    (∀ a k : ℕ, costNoSucc (word a k) = specCost (word a k))
  expectRefuted "mutant: ceiling logarithm"
    (∀ k : ℕ, costClog (UInt256.ofNat (2 ^ (8 * (k % 32 + 1)))) =
      specCost (UInt256.ofNat (2 ^ (8 * (k % 32 + 1)))))
  expectRefuted "mutant: no zero test"
    (∀ a k : ℕ, costNoZeroTest (UInt256.ofNat (a * k)) = specCost (UInt256.ofNat (a * k)))

#eval runAll

end EvmYul.EVM.ExpByteLengthTests
