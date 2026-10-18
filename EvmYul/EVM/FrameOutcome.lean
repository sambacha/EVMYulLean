module

public import EvmYul.State.AccountMap
public import EvmYul.State.Substate
public import EvmYul.ProofTags

public section

/-!
# Named frame results (review O-3)

`Θ` (message call) and `Lambda` (contract creation) used to return unnamed 6- and 7-tuples whose
`Bool` component collapsed three different endings of a frame into `true`/`false`. Both review
findings O-1 and O-2 lived in code that built such tuples by position.

This module gives the results names:

* `FrameOutcome` says **how** a frame ended: normal halt (`success`), `REVERT` (`revert`), or an
  exceptional halt (`exceptionalHalt`: an invalid instruction, stack error, out of gas, a failed
  precompile, a failed code deposit, ...).
* `FrameResult` is the result of `Θ`: the post-frame created-accounts set (EIP-6780), world
  state, remaining gas, substate, outcome and output.
* `CreateResult` is the result of `Lambda`: a `FrameResult` plus the new contract's address.

Running out of *interpreter fuel* is deliberately **not** a `FrameOutcome`: fuel is an artefact of
the executable semantics, not an EVM outcome, so it stays an `Except` error
(`.error .OutOfFuel`) that every frame boundary passes on (review O-2).

The Yellow Paper's success flag `z` is `FrameOutcome.isSuccess`; `Θ` and `Lambda` compute every
other component exactly as before, so the change is a refinement of the old tuples, not a change of
behaviour (see `FrameResult.toTuple` and the theorems in `EvmYul/EVM/SemanticsWitnesses.lean`).
-/

namespace EvmYul

namespace EVM

@[expose] section

/-- How an EVM frame (message call or contract creation) ended. -/
inductive FrameOutcome where
  /-- Normal halt (`STOP`, `RETURN`, end of code, or a successful precompile / code deposit). -/
  | success
  /-- `REVERT`: state changes are rolled back, unused gas is returned. -/
  | revert
  /-- Exceptional halt: state changes are rolled back and all gas given to the frame is consumed. -/
  | exceptionalHalt
  deriving DecidableEq, Repr, Inhabited

end

namespace FrameOutcome

/-- The Yellow Paper's success flag `z`. -/
@[expose] def isSuccess : FrameOutcome → Bool
  | success => true
  | _ => false

@[simp, reviewed_rfl "frame-outcome classification, by definition"] theorem isSuccess_success : success.isSuccess = true := rfl
@[simp, reviewed_rfl "frame-outcome classification, by definition"] theorem isSuccess_revert : revert.isSuccess = false := rfl
@[simp, reviewed_rfl "frame-outcome classification, by definition"] theorem isSuccess_exceptionalHalt : exceptionalHalt.isSuccess = false := rfl

theorem isSuccess_iff (o : FrameOutcome) : o.isSuccess = true ↔ o = success := by
  cases o <;> simp

/-- Outcome of a frame whose only information is the success flag `z` (precompiles, which cannot
`REVERT`: a failed precompile is an exceptional halt). -/
@[expose] def ofSuccessFlag (z : Bool) : FrameOutcome := if z then success else exceptionalHalt

@[simp] theorem isSuccess_ofSuccessFlag (z : Bool) : (ofSuccessFlag z).isSuccess = z := by
  cases z <;> rfl

theorem ofSuccessFlag_ne_revert (z : Bool) : ofSuccessFlag z ≠ revert := by
  cases z <;> simp [ofSuccessFlag]

/-- Attach an outcome to a precompile result `(z, σ, g, A, o)` (the `Ξ_…` functions of
`PrecompiledContracts/Contracts.lean`): precompiles never `REVERT`, so `z = false` is an exceptional halt. -/
@[expose] def ofPrecompile (r : Bool × AccountMap .EVM × UInt256 × Substate × ByteArray) :
    FrameOutcome × AccountMap .EVM × UInt256 × Substate × ByteArray :=
  (ofSuccessFlag r.1, r.2)

end FrameOutcome

/-- The result of a message call `Θ` (Yellow Paper equation (119)). -/
structure FrameResult where
  /-- Accounts created in this transaction after the frame (EIP-6780). -/
  createdAccounts : Std.TreeSet AccountAddress compare
  /-- World state after the frame, `σ'`. -/
  accountMap      : AccountMap .EVM
  /-- Remaining gas, `g'`. -/
  gasLeft         : UInt256
  /-- Accrued substate after the frame, `A'`. -/
  substate        : Substate
  /-- How the frame ended; `z = outcome.isSuccess`. -/
  outcome         : FrameOutcome
  /-- Output data, `o`. -/
  output          : ByteArray

/-- The result of a contract creation `Lambda` (Yellow Paper equation (93)). -/
structure CreateResult extends FrameResult where
  /-- Address of the (attempted) new contract. -/
  address : AccountAddress

namespace FrameResult

/-- The Yellow Paper's success flag `z`. -/
abbrev z (r : FrameResult) : Bool := r.outcome.isSuccess

/-- The old positional 6-tuple returned by `Θ` before `FrameResult` existed. -/
@[expose] def toTuple (r : FrameResult) :
    Std.TreeSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate × Bool × ByteArray :=
  (r.createdAccounts, r.accountMap, r.gasLeft, r.substate, r.z, r.output)

end FrameResult

end EVM

end EvmYul
