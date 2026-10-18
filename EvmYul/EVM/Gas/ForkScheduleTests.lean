module

public import EvmYul.Testing.EvmFixtures
public meta import EvmYul.Testing.EvmFixtures
public import EvmYul.EVM.Gas.Termination
public meta import EvmYul.EVM.Gas.Termination
public import EvmYul.EVM.Gas.ForkSchedulePins
public meta import EvmYul.EVM.Gas.ForkSchedulePins
@[expose] public meta section

/-!
# Regression tests for the fork-parameterised cost, the accounting transformer and the invariants

Built by `lake build EvmYulGasTests`; any failing check fails the build.

1. **Unit tests** (`#guard`, compiled and run): `ForkSchedule.cost` for concrete states in several
   forks (prices that changed between forks: cold SLOAD, EXP byte, CALL with and without the 63/64
   rule, opcodes that do not exist yet, stack underflow, memory expansion), the accounting
   transformer `chargeOp`, `exceptionalHaltFs` under Frontier, and `settleRefund`.
2. **Property tests** (Plausible, 300 random inputs, fixed seed), mirroring the theorems:
   agreement of `cancun.cost` with `memoryExpansionCost + C'`, the guard, the `chargeOp` normal
   form, positivity in every fork, gas independence outside the CALL family, refund bounds in every
   fork, and the 63/64 boundary in every EIP-150 fork.
3. **Mutation tests**: Plausible must find counterexamples to false variants (SELFDESTRUCT always
   costs gas, gas-independent CALL cost, a Cancun refund with quotient 2, a CALL without the 1/64
   retention), so the property tests above are not vacuous.
-/

namespace EvmYul

namespace EVM

namespace ForkScheduleTests

open GasConstants GasMeter Plausible Plausible.Decorations ForkSchedule
open EvmYul.Testing.EvmFixtures

/-! ## 1. Unit tests -/

/-- The schedule of a fork, as a short name for tests. -/
abbrev F (f : Fork) : ForkSchedule := ofFork f

/-! ### Cold SLOAD across forks (EIP-150, EIP-1884, EIP-2929) -/
#guard (F .frontier).cost (withStack [u 5]) .SLOAD == some 50
#guard (F .tangerineWhistle).cost (withStack [u 5]) .SLOAD == some 200
#guard (F .istanbul).cost (withStack [u 5]) .SLOAD == some 800
#guard (F .berlin).cost (withStack [u 5]) .SLOAD == some 2100
#guard (F .cancun).cost (withStack [u 5]) .SLOAD == some 2100
#guard (F .cancun).cost (warmSlot (withStack [u 5]) (u 5)) .SLOAD == some 100

/-! ### A5 pairing for the `rfl` pins of `GasTests` (TESTING.md A5(b))

The 14 examples `C' s w = k := rfl` in `Gas/CostsTests.lean` hold by unfolding `C'`, so on their own they
only pin the definition. Here the same 14 prices are recomputed by a different route, the
fork-parameterised table `ForkSchedule.cancun` (a separate encoding of YP Appendix G that does not
unfold `C'`), so each pinned value is corroborated independently. `TestSuite` (SA5) keeps the
count of such pins under review. -/
#guard ([(.STOP, 0), (.RETURN, 0), (.ADD, 3), (.PUSH32, 3), (.PUSH0, 2), (.MUL, 5),
    (.SELFBALANCE, 5), (.JUMP, 8), (.JUMPI, 10), (.JUMPDEST, 1), (.BLOCKHASH, 20), (.BLOBHASH, 3),
    (.TLOAD, 100), (.TSTORE, 100)] : List (Operation .EVM × ℕ)).all fun (w, c) =>
  (F .cancun).cost (withStack (List.replicate 8 (u 0))) w == some c

/-! ### EXP byte price (EIP-160): exponent 256 has two bytes -/
#guard (F .frontier).cost (withStack [u 2, u 256]) .EXP == some 30
#guard (F .spuriousDragon).cost (withStack [u 2, u 256]) .EXP == some 110
#guard (F .cancun).cost (withStack [u 2, u 0]) .EXP == some 10

/-! ### BALANCE across forks -/
#guard (F .frontier).cost (withStack [u 7]) .BALANCE == some 20
#guard (F .istanbul).cost (withStack [u 7]) .BALANCE == some 700
#guard (F .cancun).cost (withStack [u 7]) .BALANCE == some 2600

/-! ### Opcode availability and the stack guard: `none` regardless of gas -/
#guard (F .frontier).cost (withStack []) .PUSH0 == none
#guard (F .shanghai).cost (withStack []) .PUSH0 == some 2
#guard (F .london).cost (withStack [u 0]) .TLOAD == none
#guard (F .cancun).cost (withStack [u 0]) .TLOAD == some 100
#guard (F .homestead).cost (withStack [u 1, u 1]) .SHL == none
#guard (F .cancun).cost (withStack [u 1]) .ADD == none
#guard (F .cancun).cost (withStack []) .INVALID == none
#guard (F .cancun).cost (withStack [u 1, u 2]) .ADD == some 3

/-! ### Memory expansion is part of `cost` (MSTORE at offset 0: one word, `3 + 3`) -/
#guard (F .cancun).cost (withStack [u 0, u 0]) .MSTORE == some 6
#guard (F .cancun).costParts (withStack [u 0, u 0]) .MSTORE == some (3, 3)
#guard (F .cancun).cost (withStack [u 0, u 33]) .KECCAK256 == some (42 + 6)

/-! ### CALL: no 63/64 rule before Tangerine Whistle -/
/-- A CALL requesting 1 000 000 gas from address 1, value 0, with 100 000 gas available. -/
def bigCall : EVM.State := withGas (withStack [u 1000000, u 1, u 0, u 0, u 0, u 0, u 0]) 100000

#guard (F .frontier).cost bigCall .CALL == some 1000040
#guard (F .tangerineWhistle).cost bigCall .CALL == some 98449
#guard (F .cancun).cost bigCall .CALL == some 98479
#guard (F .cancun).cost bigCall .CALL == some (C' bigCall .CALL)

/-! ### SSTORE zero → non-zero -/
#guard (F .frontier).cost (withOwnerAccount (withStack [u 5, u 1])) .SSTORE == some 20000
#guard (F .cancun).cost (withOwnerAccount (withStack [u 5, u 1])) .SSTORE == some 22100

/-! ### SELFDESTRUCT: free in Frontier, 5000 + cold surcharge in Cancun -/
#guard (F .frontier).cost (withStack [u 9]) .SELFDESTRUCT == some 0
#guard (F .cancun).cost (withStack [u 9]) .SELFDESTRUCT == some 7600

/-! ### The accounting transformer -/

/-- `chargeOp` summarised: the error, or the remaining gas and the instruction part. -/
def chargeSummary (fs : ForkSchedule) (s : EVM.State) (w : Operation .EVM) :
    Option (ℕ × ℕ) × Option ExecutionException :=
  match fs.chargeOp s w with
  | .ok p => (some (p.1.gasAvailable.toNat, p.2), none)
  | .error e => (none, some e)

#guard chargeSummary (F .cancun) (withGas (withStack [u 0, u 0]) 10) .MSTORE == (some (7, 3), none)
#guard chargeSummary (F .cancun) (withGas (withStack [u 0, u 0]) 6) .MSTORE == (some (3, 3), none)
#guard chargeSummary (F .cancun) (withGas (withStack [u 0, u 0]) 5) .MSTORE ==
  (none, some .OutOfGass)
#guard chargeSummary (F .cancun) (withGas (withStack [u 0]) 100) .MSTORE ==
  (none, some .StackUnderflow)
#guard chargeSummary (F .frontier) (withGas (withStack []) 100) .PUSH0 ==
  (none, some .InvalidInstruction)
#guard (exceptionalHaltFs (F .frontier) #[] .PUSH0 (withGas (withStack []) 100)).toBool == false
#guard (exceptionalHaltFs (F .shanghai) #[] .PUSH0 (withGas (withStack []) 100)).toBool == true

/-! ### Refunds: quotient 2 before London, 5 from London on -/
#guard (F .frontier).settleRefund 100000 50000 100000 == 75000
#guard (F .cancun).settleRefund 100000 50000 100000 == 60000
#guard (F .cancun).settleRefund 100000 50000 3 == 50003
#guard (refundedGas (u 100000) (u 50000) (u 100000)).toNat ==
  (F .cancun).settleRefund 100000 50000 100000

/-! ### Theorem-backed facts (checked by the kernel) -/
example : (F .cancun).PositivePrices := positivePrices_ofFork .cancun
example : (F .frontier).PositivePrices := positivePrices_ofFork .frontier
example (f : Fork) (h : Fork.london ≤ f) (gl gr r : ℕ) :
    (ofFork f).settleRefund gl gr r - gr ≤ (gl - gr) / 5 := settleRefund_refund_le_fifth h gl gr r

/-! ## 2. Property tests (Plausible) -/

/-- A random fork. -/
structure AnyFork where
  idx : Fin 13
  deriving Repr

def AnyFork.fork (f : AnyFork) : Fork := Fork.all.getD f.idx.val .cancun

instance : Shrinkable AnyFork := ⟨fun _ => []⟩
instance : Arbitrary AnyFork where
  arbitrary := do
    let n ← Gen.choose Nat 0 12 (by decide)
    pure ⟨⟨n.val, by omega⟩⟩

/-- A random state: seven operands (enough for every instruction except DUP/SWAP ≥ 8) and gas. -/
def randState (a b c : UInt256) (g : ℕ) : EVM.State :=
  withGas (withOwnerAccount (withStack [a, b, c, a, b, c, a])) g

/-- `costParts_cancun` / `cost_eq_none_iff`: Cancun cost = memory expansion + `C'` evaluated after
the memory charge, and `none` exactly when the guard fails. -/
def cancunAgreementSpec (o : AnyOp) (a b c : UInt256) (g : ℕ) : Bool :=
  let w := o.op
  let s := randState a b c (1000000 * g)
  match cancun.cost s w with
  | none => !cancun.guardOk s w
  | some k =>
    let m := memoryExpansionCost s w
    cancun.guardOk s w &&
      (decide (m ≤ s.gasAvailable.toNat) →
        k == m + C' { s with gasAvailable := s.gasAvailable - .ofNat m } w)

/-- `chargeOp_ok_iff` / `chargeOp_oog_iff`, in every fork. -/
def chargeOpSpec (f : AnyFork) (o : AnyOp) (a b c : UInt256) (g : ℕ) : Bool :=
  let fs := ofFork f.fork
  let w := o.op
  let s := randState a b c (37 * g)
  match fs.chargeOp s w, fs.cost s w with
  | .ok (s', c₂), some k =>
    decide (k ≤ s.gasAvailable.toNat) && decide (c₂ ≤ s'.gasAvailable.toNat) &&
      (deductPrechecked s'.gasAvailable c₂).toNat == s.gasAvailable.toNat - k
  | .error .OutOfGass, some k => decide (s.gasAvailable.toNat < k)
  | .error .InvalidInstruction, none => true
  | .error .StackUnderflow, none => true
  | _, _ => false

/-- `instrCost?_pos`: in every fork, available non-halting instructions cost at least 1 gas. -/
def positivitySpec (f : AnyFork) (o : AnyOp) (a b c : UInt256) (g : ℕ) : Bool :=
  let fs := ofFork f.fork
  let w := o.op
  if fs.available w && !halting w then
    match fs.instrCost? g (randState a b c g) w with
    | some k => decide (0 < k)
    | none => true
  else true

/-- `instrCost?_gas_indep`: outside the CALL family the gas argument is irrelevant. -/
def gasIndepSpec (f : AnyFork) (o : AnyOp) (a b c : UInt256) (n n' : ℕ) : Bool :=
  let fs := ofFork f.fork
  let w := o.op
  let s := randState a b c n
  w == .CALL || w == .CALLCODE || w == .DELEGATECALL || w == .STATICCALL ||
    fs.instrCost? n s w == fs.instrCost? n' s w

/-- `settleRefund_refund_le`, `_le_counter`, `_le_limit` in every fork. -/
def refundForkSpec (f : AnyFork) (gl d r : ℕ) : Bool :=
  let fs := ofFork f.fork
  let left := gl - d
  let back := fs.settleRefund gl left r
  decide (back - left ≤ (gl - left) / fs.refundQuotient) && decide (back - left ≤ r) &&
    decide (back ≤ gl) && decide (left ≤ back)

/-- `callGas_le`, `callCost_retains`, `callGas_le_gas` in every EIP-150 fork. -/
def callForkSpec (f : AnyFork) (k : ℕ) (req val : UInt256) (warm : Bool) : Bool :=
  let fs := ofFork f.fork
  let gas := 997 * k
  let t : AccountAddress := default
  let A : Substate := if warm then { (default : Substate) with
      accessedAccounts := (default : Substate).accessedAccounts.insert t } else default
  let σ : AccountMap .EVM := default
  let e := fs.callExtra t t val σ A
  let cost := fs.callCost gas t t val req σ A
  let callgas := fs.callGas gas t t val req σ A
  fs.callGasRetention != some 64 || !decide (cost ≤ gas) ||
    (decide (callgas ≤ L (gas - e) + fs.Gcallstipend) && decide ((gas - e) / 64 ≤ gas - cost) &&
      decide (callgas ≤ gas))

#eval expectHolds "cancun.cost = memoryExpansionCost + C' (post-memory), none iff guard fails"
  (∀ o : AnyOp, ∀ a b c : UInt256, ∀ g : ℕ, cancunAgreementSpec o a b c g = true)
#eval expectHolds "chargeOp normal form in every fork"
  (∀ f : AnyFork, ∀ o : AnyOp, ∀ a b c : UInt256, ∀ g : ℕ, chargeOpSpec f o a b c g = true)
#eval expectHolds "non-halting instructions cost ≥ 1 gas in every fork"
  (∀ f : AnyFork, ∀ o : AnyOp, ∀ a b c : UInt256, ∀ g : ℕ, positivitySpec f o a b c g = true)
#eval expectHolds "instruction cost independent of gas outside the CALL family"
  (∀ f : AnyFork, ∀ o : AnyOp, ∀ a b c : UInt256, ∀ n n' : ℕ,
    gasIndepSpec f o a b c n n' = true)
#eval expectHolds "refund ≤ used / quotient, ≤ counter, ≤ limit in every fork"
  (∀ f : AnyFork, ∀ gl d r : ℕ, refundForkSpec f gl d r = true)
#eval expectHolds "63/64 call boundary in every EIP-150 fork"
  (∀ f : AnyFork, ∀ k : ℕ, ∀ req val : UInt256, ∀ warm : Bool,
    callForkSpec f k req val warm = true)

/-! ## 3. Mutation tests: Plausible must find counterexamples -/

#eval expectRefuted "conjecture: SELFDESTRUCT costs gas in every fork (free in Frontier)"
  (∀ f : AnyFork, ∀ a : UInt256,
    decide (0 < ((ofFork f.fork).instrCost? 0 (withStack [a]) .SELFDESTRUCT).getD 1) = true)
#eval expectRefuted "conjecture: the CALL cost does not depend on the gas"
  (∀ n n' : ℕ,
    cancun.instrCost? (1000 * n) bigCall .CALL = cancun.instrCost? (1000 * n') bigCall .CALL)
#eval expectRefuted "mutant: a Cancun refund with quotient 2 respects used / 5"
  (∀ gl d r : ℕ,
    decide ((gl - d) + min (d / 2) r - (gl - d) ≤ d / 5) = true)
#eval expectRefuted "mutant: a CALL without the 1/64 retention keeps (gas − extra) / 64"
  (∀ k : ℕ,
    let fs := { cancun with callGasRetention := none }
    let gas := 1000 * k
    let e := fs.callExtra default default ⟨0⟩ default default
    let cost := fs.callCost gas default default ⟨0⟩ (u (gas - e)) default default
    (!decide (cost ≤ gas) || decide ((gas - e) / 64 ≤ gas - cost)) = true)

end ForkScheduleTests

end EVM

end EvmYul
