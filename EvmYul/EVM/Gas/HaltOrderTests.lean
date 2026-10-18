module

public import EvmYul.Testing.EvmFixtures
public meta import EvmYul.Testing.EvmFixtures
public import EvmYul.EVM.Gas.HaltOrder
public meta import EvmYul.EVM.Gas.HaltOrder
public import EvmYul.EVM.Gas.Atomicity
public meta import EvmYul.EVM.Gas.Atomicity

@[expose] public meta section

/-!
# Tests for `exceptionalHalt` (`Gas/HaltOrder.lean`, `Gas/Atomicity.lean`)

Built by `lake build EvmYulGasTests`; every check runs during elaboration, so any failure fails
the build. Fixtures, generators and the seeded `expectHolds` / `expectRefuted` harness:
`EvmYul/Testing/EvmFixtures.lean`.

1. **Unit tests** on concrete states: the check order (operand errors before gas, then OOG before
   every later check), the two-stage memory + instruction charge, `INVALID`.
2. **Property tests**: the two-stage deduction equals one charge of `C_mem + C'` (atomicity); the
   reordered `exceptionalHalt` agrees with the legacy body (differential oracle).
3. **Mutation test**: the deduction without its pre-check wraps around.
-/

namespace EvmYul.EVM.Gas.HaltOrderTests

open GasConstants GasMeter Plausible Plausible.Decorations
open EvmYul.Testing.EvmFixtures

/-! ## Unit tests -/

/-- Outcome of `exceptionalHalt`: remaining gas after the memory charge and `cost₂`, or the error. -/
def haltOutcome (w : Operation .EVM) (s : EVM.State) : Except ExecutionException (ℕ × ℕ) :=
  match exceptionalHalt #[] w s with
  | .ok (s', c) => .ok (s'.gasAvailable.toNat, c)
  | .error e => .error e

def okPair? : Except ExecutionException (ℕ × ℕ) → Option (ℕ × ℕ)
  | .ok p => some p
  | .error _ => none

def isErr (e : ExecutionException) : Except ExecutionException (ℕ × ℕ) → Bool
  | .error e' => e' == e
  | .ok _ => false

-- The expected values are the rules over the fee-schedule constants (pinned against YP Appendix G
-- in `CostsTests`): `ADD` costs `G_verylow`, `JUMP` `G_mid`, `MSTORE` `G_verylow` plus the memory
-- expansion of one word, `G_memory · 1 + ⌊1² / 512⌋ = G_memory`.
-- ADD with enough gas: no memory charge, cost₂ = G_verylow.
#guard okPair? (haltOutcome .ADD (withGas (withStack [u 1, u 2]) 10)) == some (10, Gverylow)
-- ADD with one gas less than its cost: OutOfGass.
#guard isErr .OutOfGass (haltOutcome .ADD (withGas (withStack [u 1, u 2]) (Gverylow - 1)))
-- Stack underflow is checked before any gas is computed (`exceptionalHalt_underflow`), as in
-- EELS. GOLDEN-CHANGE (deliberate, see `Gas/HaltOrder.lean`): the first line used to expect
-- `OutOfGass`; `legacy_tag_differs` proves the old order gave that tag, and
-- `exceptionalHalt_ok_iff_legacy` / `exceptionalHalt_ne_outOfFuel` prove the change is invisible to
-- `X`'s callers. The legacy body is kept as a differential oracle:
#guard isErr .StackUnderflow (haltOutcome .ADD (withGas (withStack []) 2))
#guard isErr .StackUnderflow (haltOutcome .ADD (withGas (withStack []) 3))
#guard (match exceptionalHaltLegacy #[] .ADD (withGas (withStack []) 2) with
  | .error .OutOfGass => true | _ => false)
-- With the operands present, OOG still has priority over every later check
-- (`exceptionalHalt_oog_of_lt`): JUMP to an invalid target with one gas less than its cost is OOG,
-- with exactly its cost it is a bad jump.
#guard isErr .OutOfGass (haltOutcome .JUMP (withGas (withStack [u 5]) (Gmid - 1)))
#guard isErr .BadJumpDestination (haltOutcome .JUMP (withGas (withStack [u 5]) Gmid))
-- MSTORE at 0 with 100 gas: the memory charge `G_memory` is deducted first, cost₂ = G_verylow.
#guard okPair? (haltOutcome .MSTORE (withGas (withStack [u 0, u 5]) 100)) ==
  some (100 - Gmemory, Gverylow)
-- ... and then `deductPrechecked` leaves `100 − (C_mem + C')` (single-charge equivalence).
#guard (match exceptionalHalt #[] .MSTORE (withGas (withStack [u 0, u 5]) 100) with
  | .ok (s', c) => (deductPrechecked s'.gasAvailable c).toNat == 100 - (Gmemory + Gverylow) &&
      okNat? (chargeGas (u 100) (Gmemory + c)) == some (100 - (Gmemory + Gverylow))
  | .error _ => false)
-- MSTORE with exactly C_mem + C' gas succeeds, with one gas less it is OOG.
#guard okPair? (haltOutcome .MSTORE (withGas (withStack [u 0, u 5]) (Gmemory + Gverylow))) ==
  some (Gverylow, Gverylow)
#guard isErr .OutOfGass
  (haltOutcome .MSTORE (withGas (withStack [u 0, u 5]) (Gmemory + Gverylow - 1)))
-- INVALID is rejected before `step` (PO-1: not priced ⇒ not handled).
#guard isErr .InvalidInstruction (haltOutcome .INVALID (withGas (withStack []) 100))
-- `deductPrechecked` without the pre-check wraps (why the check is load-bearing).
example := deductPrechecked_wraps


/-! ## Property tests -/

/-- `exceptionalHalt` atomicity on a random opcode, random stack and random gas. -/
def atomicitySpec (o : AnyOp) (a b c gas : UInt256) : Bool :=
  let s := withOwnerAccount { (withStack [a, b, c, a, b, c, a]) with
    toMachineState := { (default : MachineState) with gasAvailable := gas } }
  let w := o.op
  let m := memoryExpansionCost s w
  match exceptionalHalt #[] w s with
  | .ok (s', k) =>
    decide (m + k ≤ gas.toNat) && (deductPrechecked s'.gasAvailable k).toNat == gas.toNat - (m + k) &&
      k == C' s' w
  | .error e =>
    -- a valid instruction with its operands present whose charge did not fit must be OutOfGass
    -- (`exceptionalHalt_oog_of_lt`); an invalid one / a short stack is reported first
    if δ w = none then e == .InvalidInstruction
    else if s.stack.length < (δ w).getD 0 then e == .StackUnderflow
    else !(decide (gas.toNat < m + C' { s with gasAvailable := s.gasAvailable - .ofNat m } w)) ||
      e == .OutOfGass

/-- Differential oracle (TESTING.md C3/D3): the reordered `exceptionalHalt` and the legacy body
agree on every successful result and on success/failure (`exceptionalHalt_ok_iff_legacy`). The
stack length `n` ranges over short stacks so that the underflow path is exercised. -/
def haltOrderSpec (o : AnyOp) (n : ℕ) (a gas : UInt256) : Bool :=
  let s := withOwnerAccount { (withStack (List.replicate (n % 18) a)) with
    toMachineState := { (default : MachineState) with gasAvailable := gas } }
  let w := o.op
  if δ w = none ∨ s.stack.length < (δ w).getD 0 then
    -- Here the legacy body would evaluate `C'` on missing operands, whose `μₛ[i]!` reads *panic* at
    -- run time (observed when this test first ran it): the defect the reordering removes. The
    -- equivalence on this region is the theorem `exceptionalHalt_ok_iff_legacy`; the test checks
    -- that the new order reports the operand error without computing any cost.
    match exceptionalHalt #[] w s with
    | .error e => if δ w = none then e == .InvalidInstruction else e == .StackUnderflow
    | .ok _ => false
  else
    match exceptionalHalt #[] w s, exceptionalHaltLegacy #[] w s with
    | .ok (s₁, k₁), .ok (s₂, k₂) => s₁.gasAvailable == s₂.gasAvailable && k₁ == k₂
    | .error e₁, .error e₂ => e₁ == e₂
    | _, _ => false

#eval expectHolds "exceptionalHalt: two-stage deduction = one charge of C_mem + C'"
  (∀ o : AnyOp, ∀ a b c gas : UInt256, atomicitySpec o a b c gas = true)
#eval expectHolds "exceptionalHalt atomicity with small stack values (real memory growth)"
  (∀ o : AnyOp, ∀ a b c g : ℕ, atomicitySpec o (u a) (u b) (u c) (u (g * 37)) = true)
#eval expectHolds "exceptionalHalt (checks first) ≡ legacy body (charge first) up to error tag"
  (∀ o : AnyOp, ∀ n : ℕ, ∀ a g : UInt256, haltOrderSpec o n a g = true)
#eval expectHolds "exceptionalHalt ≡ legacy body, small gas (OOG and underflow both reachable)"
  (∀ o : AnyOp, ∀ n a g : ℕ, haltOrderSpec o n (u a) (u g) = true)

/-! ## Mutation tests -/

#eval expectRefuted "mutant: deduction without the pre-check never wraps"
  (∀ g : UInt256, ∀ c : ℕ, (deductPrechecked g c).toNat ≤ g.toNat)

end EvmYul.EVM.Gas.HaltOrderTests
