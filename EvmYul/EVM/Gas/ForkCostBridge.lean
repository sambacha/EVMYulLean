module

public import EvmYul.EVM.Semantics
public import EvmYul.EVM.Gas.ForkCostLemmas
public import EvmYul.EVM.Gas.Lemmas
public section

/-!
# The split cost/accounting `Z` is the previous `Z`

`exceptionalHalt` (executed by `X`) is now `ForkSchedule.chargeOp cancun` (the pure cost
`ForkSchedule.cost` plus the accounting transformer) followed by `haltChecks`. This file keeps the
previous definition (`chargeAndCheck`, `exceptionalHaltPrev`, moved here verbatim from
`EvmYul/EVM/Semantics.lean`) and proves:

* `exceptionalHalt_eq_prev`: the two are **equal for every input** (same results, same exception
  tags). The interpreter, and therefore every conformance run, behaves exactly as before.
* `costParts_cancun`: on a valid instruction with its operands on the stack, the Cancun cost
  parts are `memoryExpansionCost` and `C'` evaluated after the memory charge (the interleaving of
  the Yellow Paper, made explicit).
* `costParts_eq_none_iff`, `cost_eq_none_iff`: the pure cost is `none` exactly when the stack guard
  fails, for every schedule.
* Order-sensitivity (proved in `GasCallBoundary`): `instrCost?_gas_indep` (only the CALL family
  reads the gas) and
  `call_cost_order_sensitive` (for CALL, evaluating the cost before or after the memory charge
  gives different results, so the charge order is semantically relevant).
-/

namespace EvmYul

namespace EVM

open GasMeter ForkSchedule UInt256

/--
The gas-dependent part of exceptional halting `Z` (158), run by `exceptionalHaltPrev` once the
instruction is known to be valid and to have all of its operands on the stack. It deducts the
memory-expansion cost with `GasMeter.chargeGas`, evaluates `cost₂ = C'` on the resulting state,
raises `OutOfGass` if `cost₂` does not fit, and then checks the remaining (operand-dependent)
exceptional-halting conditions. On success it returns the post-memory state and `cost₂`.
-/
@[expose] def chargeAndCheck (validJumps : Array UInt256) (w : Operation .EVM) (evmState : State) :
    Except EVM.ExecutionException (State × ℕ) := do
  let cost₁ := memoryExpansionCost evmState w
  -- Guarded deduction: `OutOfGass` iff `gasAvailable < cost₁`, otherwise subtraction
  -- without wrap-around (see `GasMeter.chargeGas`, `chargeGas_bind_eq_guarded`).
  let gasAvailable ← GasMeter.chargeGas evmState.gasAvailable cost₁
  let evmState := { evmState with gasAvailable := gasAvailable}
  let cost₂ := C' evmState w

  if evmState.gasAvailable.toNat < cost₂ then
    .error .OutOfGass

  let invalidJump := jumpTargetNotIn evmState.stack[0]? validJumps

  if w = .JUMP ∧ invalidJump then
    .error .BadJumpDestination

  if w = .JUMPI ∧ (evmState.stack[1]? ≠ some ⟨0⟩) ∧ invalidJump then
    .error .BadJumpDestination

  if w = .RETURNDATACOPY ∧
      (evmState.stack.getD 1 ⟨0⟩).toNat + (evmState.stack.getD 2 ⟨0⟩).toNat >
        evmState.returnData.size then
    .error .InvalidMemoryAccess

  if evmState.stack.length - (δ w).getD 0 + (α w).getD 0 > 1024 then
    .error .StackOverflow

  if (¬ evmState.executionEnv.perm) ∧ modifiesState w evmState.stack then
    .error .StaticModeViolation

  if (w = .SSTORE) ∧ evmState.gasAvailable.toNat ≤ GasConstants.Gcallstipend then
    .error .OutOfGass

  if
    w.isCreate ∧ evmState.stack.getD 2 ⟨0⟩ > ⟨49152⟩
  then
    .error .OutOfGass

  pure (evmState, cost₂)

/--
The previous definition of exceptional halting `Z` (158), as executed by `X` before the
cost/accounting split: the `InvalidInstruction` and `StackUnderflow` checks, then
`chargeAndCheck`, which evaluates `memoryExpansionCost` and `C'` (with `!` operand reads). Kept as
the reference for `exceptionalHalt_eq_prev`.
-/
@[expose] def exceptionalHaltPrev (validJumps : Array UInt256) (w : Operation .EVM) (evmState : State) :
    Except EVM.ExecutionException (State × ℕ) :=
  if δ w = none then
    .error .InvalidInstruction
  else if evmState.stack.length < (δ w).getD 0 then
    .error .StackUnderflow
  else
    chargeAndCheck validJumps w evmState

/-! ## The guard -/

theorem guardOk_iff (fs : ForkSchedule) (s : State) (w : Operation .EVM) :
    fs.guardOk s w = true ↔
      fs.available w = true ∧ δ w ≠ none ∧ (δ w).getD 0 ≤ s.stack.length := by
  unfold guardOk
  cases h : δ w <;> simp

theorem checkGuard_eq_ok_iff (fs : ForkSchedule) (s : State) (w : Operation .EVM) :
    fs.checkGuard s w = .ok () ↔ fs.guardOk s w = true := by
  rw [guardOk_iff]; unfold checkGuard
  cases h : δ w <;> cases fs.available w <;> simp

/-- **`none` iff the guard fails**, for every schedule: the cost computation itself never
produces `none`. -/
theorem costParts_eq_none_iff (fs : ForkSchedule) (s : State) (w : Operation .EVM) :
    fs.costParts s w = none ↔ fs.guardOk s w = false := by
  unfold costParts
  cases hg : fs.guardOk s w
  · simp
  · simp only [if_true, reduceCtorEq, iff_false]
    obtain ⟨-, hδ, hst⟩ := (guardOk_iff fs s w).1 hg
    obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.1 hδ
    rw [hk] at hst
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.1 (memoryCost?_isSome fs s w hk hst)
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1
      (instrCost?_isSome fs (s.gasAvailable.toNat - m) s w hk hst)
    simp [hm, hc]

theorem cost_eq_none_iff (fs : ForkSchedule) (s : State) (w : Operation .EVM) :
    fs.cost s w = none ↔ fs.guardOk s w = false := by
  rw [← costParts_eq_none_iff]; unfold cost; simp

/-- Under the guard, the cost parts are the memory cost and the instruction cost at the gas left
after the memory cost. -/
theorem costParts_eq_some {fs : ForkSchedule} {s : State} {w : Operation .EVM} {p : ℕ × ℕ}
    (h : fs.costParts s w = some p) :
    fs.guardOk s w = true ∧ fs.memoryCost? s w = some p.1 ∧
      fs.instrCost? (s.gasAvailable.toNat - p.1) s w = some p.2 := by
  unfold costParts at h
  split at h
  · rename_i hg
    simp only [Option.bind_eq_bind, Option.pure_def] at h
    cases hm : fs.memoryCost? s w with
    | none => simp [hm] at h
    | some m =>
      cases hc : fs.instrCost? (s.gasAvailable.toNat - m) s w with
      | none => simp [hm, hc] at h
      | some c =>
        simp [hm, hc] at h
        subst h
        exact ⟨hg, rfl, hc⟩
  · cases h

/-- **The Cancun cost parts are the interpreter's.** On a valid instruction with its operands on
the stack, whose memory cost fits, the parts are `memoryExpansionCost` and `C'` evaluated on the
state after the memory charge. -/
theorem costParts_cancun {s : State} {w : Operation .EVM} (hδ : δ w ≠ none)
    (hst : (δ w).getD 0 ≤ s.stack.length) (hm : memoryExpansionCost s w ≤ s.gasAvailable.toNat) :
    cancun.costParts s w = some (memoryExpansionCost s w,
      C' { s with gasAvailable := s.gasAvailable - .ofNat (memoryExpansionCost s w) } w) := by
  obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.1 hδ
  rw [hk] at hst
  have hg : cancun.guardOk s w = true :=
    (guardOk_iff _ _ _).2 ⟨available_cancun w, hδ, by rw [hk]; exact hst⟩
  have h1 := toNat_sub_ofNat_of_le hm
  have hc := instrCost?_cancun
    { s with gasAvailable := s.gasAvailable - .ofNat (memoryExpansionCost s w) } w hk hst
  rw [instrCost?_gasAvailable] at hc
  simp only at hc
  rw [h1] at hc
  unfold costParts
  simp [hg, memoryCost?_cancun s w hk hst, hc]

/-! ## The split `Z` equals the previous `Z` -/

theorem exceptionalHalt_eq_prev (vj : Array UInt256) (w : Operation .EVM) (s : State) :
    exceptionalHalt vj w s = exceptionalHaltPrev vj w s := by
  unfold exceptionalHalt exceptionalHaltFs exceptionalHaltPrev
  by_cases hδ : δ w = none
  · simp [chargeOp, ForkSchedule.checkGuard, hδ, available_cancun, bind, Except.bind]
  by_cases hst : s.stack.length < (δ w).getD 0
  · simp [chargeOp, ForkSchedule.checkGuard, hδ, hst, available_cancun, bind, Except.bind]
  rw [if_neg hδ, if_neg hst]
  have hguard : cancun.checkGuard s w = .ok () := by
    rw [checkGuard_eq_ok_iff, guardOk_iff]; exact ⟨available_cancun w, hδ, by omega⟩
  by_cases hm : memoryExpansionCost s w ≤ s.gasAvailable.toNat
  · rw [chargeOp, hguard, costParts_cancun hδ (by omega) hm]
    unfold chargeAndCheck
    have hcg : chargeGas s.gasAvailable (memoryExpansionCost s w) =
        .ok (s.gasAvailable - .ofNat (memoryExpansionCost s w)) := by
      unfold chargeGas; rw [if_neg (by omega)]
    have e1 : (UInt256.ofNat 49152) = (⟨49152⟩ : UInt256) := rfl
    simp only [hcg, bind, Except.bind, pure, Except.pure, haltChecks, true_and, e1,
      GasConstants.Gcallstipend]
    by_cases h1 : (s.gasAvailable - UInt256.ofNat (memoryExpansionCost s w)).toNat <
        C' { s with gasAvailable := s.gasAvailable - UInt256.ofNat (memoryExpansionCost s w) } w
    · simp only [h1, if_true]
    · simp only [h1, if_false]
      split_ifs <;> rfl
  · have hcg : chargeGas s.gasAvailable (memoryExpansionCost s w) = .error .OutOfGass := by
      unfold chargeGas; rw [if_pos (by omega)]
    obtain ⟨k, hk⟩ := Option.ne_none_iff_exists'.1 hδ
    have hst' : k ≤ s.stack.length := by rw [hk] at hst; simpa using hst
    obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1
      (instrCost?_isSome cancun (s.gasAvailable.toNat - memoryExpansionCost s w) s w hk hst')
    have hp : cancun.costParts s w = some (memoryExpansionCost s w, c) := by
      unfold costParts
      rw [if_pos ((guardOk_iff _ _ _).2 ⟨available_cancun w, hδ, by omega⟩)]
      simp [memoryCost?_cancun s w hk hst', hc]
    rw [chargeOp, hguard, hp]
    unfold chargeAndCheck
    simp [hcg, bind, Except.bind]

/-- `exceptionalHalt` and the previous definition are the same function. -/
theorem exceptionalHalt_eq_prev_fun : exceptionalHalt = exceptionalHaltPrev := by
  funext vj w s; exact exceptionalHalt_eq_prev vj w s

end EVM

end EvmYul
