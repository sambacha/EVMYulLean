module

public import EvmYul.EVM.Gas.HaltOrder
public import EvmYul.EVM.Gas.Positivity
public import EvmYul.ProofTags
public section

/-!
# Core gas invariants of the split cost / accounting model

All statements are about the definitions the interpreter executes (`ForkSchedule.cost`,
`ForkSchedule.chargeOp`, `exceptionalHaltFs`, and `exceptionalHalt = exceptionalHaltFs cancun`),
and most are proved for **every** fork schedule.

* **Normal form of the accounting transformer** (`chargeOp_of_costParts`, `chargeOp_of_none`):
  `chargeOp` fails with `OutOfGass` iff the total cost exceeds the gas, and otherwise deducts the
  memory part exactly.
* **`Z` never fires spuriously** (`exceptionalHaltFs_error_cases`): every exception raised by
  `exceptionalHaltFs` is justified by its condition. `OutOfGass` in particular is raised only if
  the pure cost exceeds the available gas, or by the two EIP sentries (SSTORE stipend, initcode
  size). Conversely (`exceptionalHaltFs_ok_of`), if the cost fits and the remaining conditions
  hold, `Z` does not fire.
* **Gas strictly decreases on every non-halting step** (`exceptionalHaltFs_charge_lt`,
  `exceptionalHalt_charge_lt`): the charge of an instruction other than STOP, RETURN, REVERT,
  SELFDESTRUCT and INVALID is at least 1 gas in every named fork (`instrCost?_pos`, with the
  decidable side condition `PositivePrices` checked for all 13 forks by `decide`).
* **Refunds** (`settleRefund_refund_le`): the refund is at most `⌊used / refundQuotient⌋`, so at
  most `⌊used / 5⌋` from London on, and the Cancun instance is the interpreter's `refundedGas`.
* **The 63/64 rule at every call boundary** (`call_boundary`, `create_boundary`, proved in
  `GasCallBoundary`): when `Z`
  accepts a CALL-family instruction, the gas that `call` forwards is at most
  `L(μ_g − C_EXTRA)` plus the stipend, the caller keeps at least `⌊(μ_g − C_EXTRA)/64⌋`, and the
  `UInt256` conversion of the forwarded gas does not wrap; for CREATE/CREATE2 the callee gets
  exactly `L(μ_g)` and the caller keeps exactly `⌊μ_g/64⌋`.
-/

namespace EvmYul

namespace EVM

open GasMeter ForkSchedule UInt256 GasConstants

/-! ## Normal form of the accounting transformer -/

section ChargeOp

variable {fs : ForkSchedule} {s : State} {w : Operation .EVM}

/-- With cost parts `(m, c)`, `chargeOp` is a single guarded charge of `m + c` that leaves the
state with the memory part deducted (the instruction part is deducted later by `step`). -/
theorem chargeOp_of_costParts {m c : ℕ} (h : fs.costParts s w = some (m, c)) :
    fs.chargeOp s w =
      if s.gasAvailable.toNat < m + c then .error .OutOfGass
      else .ok ({ s with gasAvailable := s.gasAvailable - .ofNat m }, c) := by
  have hg : fs.checkGuard s w = .ok () :=
    (checkGuard_eq_ok_iff _ _ _).2 (costParts_eq_some h).1
  unfold chargeOp
  rw [hg, h]
  simp only [bind, Except.bind]
  unfold chargeGas
  by_cases hm : s.gasAvailable.toNat < m
  · rw [if_pos hm, if_pos (by omega)]
  · rw [if_neg hm]
    simp only
    rw [toNat_sub_ofNat_of_le (by omega)]
    by_cases hc : s.gasAvailable.toNat - m < c
    · rw [if_pos hc, if_pos (by omega)]
    · rw [if_neg hc, if_neg (by omega)]; rfl

/-- Without cost parts (the guard fails), `chargeOp` raises `InvalidInstruction` or
`StackUnderflow`, and nothing else. -/
theorem chargeOp_of_none (h : fs.costParts s w = none) :
    fs.chargeOp s w = .error .InvalidInstruction ∨ fs.chargeOp s w = .error .StackUnderflow := by
  unfold chargeOp
  cases hg : fs.checkGuard s w with
  | error e =>
    unfold checkGuard at hg
    split_ifs at hg <;> cases hg <;> simp [bind, Except.bind]
  | ok u => simp [bind, Except.bind, h]

theorem chargeOp_ok_iff {s' : State} {c : ℕ} :
    fs.chargeOp s w = .ok (s', c) ↔
      ∃ m, fs.costParts s w = some (m, c) ∧ m + c ≤ s.gasAvailable.toNat ∧
        s' = { s with gasAvailable := s.gasAvailable - .ofNat m } := by
  constructor
  · intro h
    cases hp : fs.costParts s w with
    | none => rcases chargeOp_of_none hp with h' | h' <;> rw [h'] at h <;> cases h
    | some p =>
      obtain ⟨m, c'⟩ := p
      rw [chargeOp_of_costParts hp] at h
      split_ifs at h with hlt
      cases h
      exact ⟨m, rfl, by omega, rfl⟩
  · rintro ⟨m, hp, hle, rfl⟩
    rw [chargeOp_of_costParts hp, if_neg (by omega)]

/-- `chargeOp` raises `OutOfGass` iff the pure cost exists and exceeds the available gas. -/
theorem chargeOp_oog_iff :
    fs.chargeOp s w = .error .OutOfGass ↔
      ∃ c, fs.cost s w = some c ∧ s.gasAvailable.toNat < c := by
  unfold cost
  cases hp : fs.costParts s w with
  | none => rcases chargeOp_of_none hp with h' | h' <;> simp [h']
  | some p =>
    obtain ⟨m, c⟩ := p
    rw [chargeOp_of_costParts hp]
    split_ifs with hlt <;> simp [hlt]

/-- After a successful charge, the gas left once `step` has deducted the instruction part is the
initial gas minus the pure cost, with no wrap-around. -/
theorem chargeOp_ok_deduct {s' : State} {c : ℕ} (h : fs.chargeOp s w = .ok (s', c)) :
    ∃ k, fs.cost s w = some k ∧ k ≤ s.gasAvailable.toNat ∧
      (deductPrechecked s'.gasAvailable c).toNat = s.gasAvailable.toNat - k := by
  obtain ⟨m, hp, hle, rfl⟩ := chargeOp_ok_iff.1 h
  refine ⟨m + c, by simp [cost, hp], hle, ?_⟩
  have h1 : ({ s with gasAvailable := s.gasAvailable - .ofNat m } : State).gasAvailable.toNat =
      s.gasAvailable.toNat - m := toNat_sub_ofNat_of_le (by omega)
  rw [deductPrechecked_toNat (by rw [h1]; omega), h1]
  omega

end ChargeOp

/-! ## `Z` never fires spuriously -/

section Halt

variable {fs : ForkSchedule} {vj : Array UInt256} {w : Operation .EVM} {s : State}

/-- The three outcomes of the stack guard. -/
theorem checkGuard_cases (fs : ForkSchedule) (s : State) (w : Operation .EVM) :
    fs.checkGuard s w = .ok () ∨
    (fs.checkGuard s w = .error .InvalidInstruction ∧ (fs.available w = false ∨ δ w = none)) ∨
    (fs.checkGuard s w = .error .StackUnderflow ∧ fs.available w = true ∧ δ w ≠ none ∧
      s.stack.length < (δ w).getD 0) := by
  unfold checkGuard
  by_cases ha : fs.available w = true
  · by_cases hd : δ w = none
    · right; left; simp [ha, hd]
    · by_cases hk : s.stack.length < (δ w).getD 0
      · right; right; simp [ha, hd, hk]
      · left; simp [ha, hd, hk]
  · right; left; simp [ha]

theorem chargeOp_of_checkGuard_error {e : ExecutionException}
    (h : fs.checkGuard s w = .error e) : fs.chargeOp s w = .error e := by
  unfold chargeOp; rw [h]; rfl

/-- The post-memory state `Z` hands to `haltChecks` and to `step`. -/
abbrev afterMemory (s : State) (m : ℕ) : State :=
  { s with gasAvailable := s.gasAvailable - .ofNat m }

/--
**Soundness of `Z`.** Every exception raised by `exceptionalHaltFs` is justified:

* `InvalidInstruction` only for an instruction unknown in the fork or with `δ = none`;
* `StackUnderflow` only when the operands are not on the stack;
* `OutOfGass` from the accounting transformer only when the pure cost exceeds the gas;
* anything else only when the cost fits and `haltChecks` raises it.
-/
theorem exceptionalHaltFs_error_cases {e : ExecutionException}
    (h : exceptionalHaltFs fs vj w s = .error e) :
    (e = .InvalidInstruction ∧ (fs.available w = false ∨ δ w = none)) ∨
    (e = .StackUnderflow ∧ fs.available w = true ∧ δ w ≠ none ∧
      s.stack.length < (δ w).getD 0) ∨
    (e = .OutOfGass ∧ ∃ c, fs.cost s w = some c ∧ s.gasAvailable.toNat < c) ∨
    (∃ m c, fs.costParts s w = some (m, c) ∧ m + c ≤ s.gasAvailable.toNat ∧
      haltChecks fs vj w (afterMemory s m) = .error e) := by
  unfold exceptionalHaltFs at h
  rcases checkGuard_cases fs s w with hg | ⟨hg, hc⟩ | ⟨hg, hc⟩
  · have hok : fs.guardOk s w = true := (checkGuard_eq_ok_iff _ _ _).1 hg
    cases hp : fs.costParts s w with
    | none => rw [(costParts_eq_none_iff _ _ _).1 hp] at hok; cases hok
    | some p =>
      obtain ⟨m, c⟩ := p
      rw [chargeOp_of_costParts hp] at h
      split_ifs at h with hlt
      · cases h
        right; right; left
        exact ⟨rfl, m + c, by simp [cost, hp], hlt⟩
      · right; right; right
        refine ⟨m, c, rfl, by omega, ?_⟩
        simp only [bind, Except.bind] at h
        cases hh : haltChecks fs vj w (afterMemory s m) with
        | error e' => rw [hh] at h; cases h; rfl
        | ok u => rw [hh] at h; cases h
  · rw [chargeOp_of_checkGuard_error hg] at h; cases h
    exact .inl ⟨rfl, hc⟩
  · rw [chargeOp_of_checkGuard_error hg] at h; cases h
    exact .inr (.inl ⟨rfl, hc⟩)

/-- A `do`-block guard that raises `e` either fired (its condition holds) or was passed. -/
@[reviewed_generic "Except plumbing"]
theorem except_jp_cases' {ε α : Type} {b : Prop} [Decidable b] {e e' : ε}
    {K : PUnit → Except ε α}
    (h : (if b then (do let y ← Except.error e'; K y) else (do let y ← pure PUnit.unit; K y)) =
      .error e) : (e = e' ∧ b) ∨ K PUnit.unit = .error e := by
  by_cases hb : b
  · rw [if_pos hb] at h; cases h; exact .inl ⟨rfl, hb⟩
  · rw [if_neg hb] at h; exact .inr h

/-- `haltChecks` raises `OutOfGass` only through its two EIP sentries. -/
theorem haltChecks_oog {s' : State} (h : haltChecks fs vj w s' = .error .OutOfGass) :
    (fs.sstoreRule = .netMetered ∧ w = .SSTORE ∧ s'.gasAvailable.toNat ≤ fs.Gcallstipend) ∨
    (w.isCreate = true ∧ ∃ lim, fs.maxInitcodeSize = some lim ∧
      s'.stack.getD 2 ⟨0⟩ > .ofNat lim) := by
  unfold haltChecks at h
  iterate 5 (rcases except_jp_cases h with he | h; · cases he)
  rcases except_jp_cases' h with ⟨-, hb⟩ | h
  · exact .inl hb
  · right
    split at h
    · rename_i lim hlim
      by_cases hb : w.isCreate = true ∧ s'.stack.getD 2 ⟨0⟩ > .ofNat lim
      · exact ⟨hb.1, lim, hlim, hb.2⟩
      · rw [if_neg hb] at h; cases h
    · cases h

/-- **`OutOfGass` is never spurious.** If `Z` raises `OutOfGass`, then either the pure cost really
exceeds the available gas, or the cost fits and one of the two EIP sentries holds: an SSTORE with at
most the call stipend left after the memory charge (EIP-2200), or a CREATE/CREATE2 whose initcode
size operand exceeds the limit (EIP-3860). -/
theorem exceptionalHaltFs_oog_sound (h : exceptionalHaltFs fs vj w s = .error .OutOfGass) :
    ∃ c, fs.cost s w = some c ∧
      (s.gasAvailable.toNat < c ∨
        (c ≤ s.gasAvailable.toNat ∧
          ((fs.sstoreRule = .netMetered ∧ w = .SSTORE ∧
              s.gasAvailable.toNat - (c - (fs.costParts s w).elim 0 (·.2)) ≤ fs.Gcallstipend) ∨
           (w.isCreate = true ∧ ∃ lim, fs.maxInitcodeSize = some lim ∧
              s.stack.getD 2 ⟨0⟩ > .ofNat lim)))) := by
  rcases exceptionalHaltFs_error_cases h with ⟨he, -⟩ | ⟨he, -⟩ | ⟨-, c, hc, hlt⟩ |
      ⟨m, c, hp, hle, hh⟩
  · cases he
  · cases he
  · exact ⟨c, hc, .inl hlt⟩
  · refine ⟨m + c, by simp [cost, hp], .inr ⟨hle, ?_⟩⟩
    have hgas : (afterMemory s m).gasAvailable.toNat = s.gasAvailable.toNat - m :=
      toNat_sub_ofNat_of_le (by omega)
    rcases haltChecks_oog hh with ⟨h1, h2, h3⟩ | ⟨h1, lim, h2, h3⟩
    · left; refine ⟨h1, h2, ?_⟩
      rw [hgas] at h3; simp only [hp, Option.elim]; omega
    · right; exact ⟨h1, lim, h2, h3⟩

/-- **Completeness of `Z`.** If the pure cost fits and none of the remaining halting conditions
holds, `Z` does not fire: it returns the post-memory state and the instruction cost. -/
theorem exceptionalHaltFs_ok_of {m c : ℕ} (hp : fs.costParts s w = some (m, c))
    (hle : m + c ≤ s.gasAvailable.toNat) (hh : haltChecks fs vj w (afterMemory s m) = .ok ()) :
    exceptionalHaltFs fs vj w s = .ok (afterMemory s m, c) := by
  unfold exceptionalHaltFs
  rw [chargeOp_of_costParts hp, if_neg (by omega)]
  simp only [bind, Except.bind]
  rw [hh]; rfl

/-- On success, `Z` charged exactly the pure cost, which fit. -/
theorem exceptionalHaltFs_ok_cost {s' : State} {c₂ : ℕ}
    (h : exceptionalHaltFs fs vj w s = .ok (s', c₂)) :
    ∃ k, fs.cost s w = some k ∧ k ≤ s.gasAvailable.toNat ∧
      (deductPrechecked s'.gasAvailable c₂).toNat = s.gasAvailable.toNat - k := by
  unfold exceptionalHaltFs at h
  obtain ⟨p, hp, h⟩ := except_bind_ok h
  obtain ⟨u, -, h⟩ := except_bind_ok h
  cases h
  exact chargeOp_ok_deduct hp

end Halt

/-! ## Gas strictly decreases on every non-halting step -/

section Decrease

variable {fs : ForkSchedule} {s : State} {w : Operation .EVM}

/-- The pure cost of an available non-halting instruction is positive (`PositivePrices`). -/
theorem cost_pos (hP : fs.PositivePrices) (hw : ForkSchedule.halting w = false) {k : ℕ}
    (h : fs.cost s w = some k) : 0 < k := by
  unfold cost at h
  obtain ⟨⟨m, c⟩, hp, rfl⟩ := Option.map_eq_some_iff.1 h
  obtain ⟨hg, -, hc⟩ := costParts_eq_some hp
  have := instrCost?_pos hP ((guardOk_iff _ _ _).1 hg).1 hw hc
  simp only; omega

/-- **Strict decrease** (every schedule with positive prices): if `Z` accepts a non-halting
instruction, the gas after the full charge (memory part by `chargeOp`, instruction part by
`deductPrechecked` in `step`) is strictly smaller than before. -/
theorem exceptionalHaltFs_charge_lt (hP : fs.PositivePrices) (hw : ForkSchedule.halting w = false)
    {vj : Array UInt256} {s' : State} {c₂ : ℕ} (h : exceptionalHaltFs fs vj w s = .ok (s', c₂)) :
    (deductPrechecked s'.gasAvailable c₂).toNat < s.gasAvailable.toNat := by
  obtain ⟨k, hk, hle, heq⟩ := exceptionalHaltFs_ok_cost h
  have := cost_pos hP hw hk
  omega

/-- **Strict decrease for the interpreter** (`exceptionalHalt = exceptionalHaltFs cancun`). -/
theorem exceptionalHalt_charge_lt (hw : ForkSchedule.halting w = false)
    {vj : Array UInt256} {s' : State} {c₂ : ℕ} (h : exceptionalHalt vj w s = .ok (s', c₂)) :
    (deductPrechecked s'.gasAvailable c₂).toNat < s.gasAvailable.toNat :=
  exceptionalHaltFs_charge_lt (positivePrices_ofFork .cancun) hw h

end Decrease

/-! ## Refunds -/

section Refund

/-- **Refund bound** (every schedule): the refund granted by `settleRefund` is at most
`⌊used / refundQuotient⌋`, where `used = gasLimit − gasLeft`. -/
theorem settleRefund_refund_le (fs : ForkSchedule) (gasLimit gasLeft r : ℕ) :
    fs.settleRefund gasLimit gasLeft r - gasLeft ≤ (gasLimit - gasLeft) / fs.refundQuotient := by
  simp only [settleRefund, Nat.add_sub_cancel_left]; exact Nat.min_le_left _ _

/-- The refund is also at most the accrued refund counter. -/
theorem settleRefund_refund_le_counter (fs : ForkSchedule) (gasLimit gasLeft r : ℕ) :
    fs.settleRefund gasLimit gasLeft r - gasLeft ≤ r := by
  simp only [settleRefund, Nat.add_sub_cancel_left]; exact Nat.min_le_right _ _

/-- The sender never gets back more than the gas limit. -/
theorem settleRefund_le_limit (fs : ForkSchedule) {gasLimit gasLeft : ℕ} (r : ℕ)
    (h : gasLeft ≤ gasLimit) : fs.settleRefund gasLimit gasLeft r ≤ gasLimit := by
  unfold settleRefund
  have := Nat.div_le_self (gasLimit - gasLeft) fs.refundQuotient
  have := Nat.min_le_left ((gasLimit - gasLeft) / fs.refundQuotient) r
  omega

/-- From London on the refund quotient is 5 (EIP-3529); before London it is 2. -/
theorem refundQuotient_ofFork (f : Fork) :
    (ofFork f).refundQuotient = if Fork.london ≤ f then 5 else 2 := by
  cases f <;> decide

/-- **`refund ≤ ⌊used / 5⌋`** for every fork from London on. -/
theorem settleRefund_refund_le_fifth {f : Fork} (hf : Fork.london ≤ f) (gasLimit gasLeft r : ℕ) :
    (ofFork f).settleRefund gasLimit gasLeft r - gasLeft ≤ (gasLimit - gasLeft) / 5 := by
  have := settleRefund_refund_le (ofFork f) gasLimit gasLeft r
  rwa [refundQuotient_ofFork, if_pos hf] at this

/-- **The interpreter's refund is the Cancun `settleRefund`**: `GasMeter.refundedGas`, used by the
transaction-level execution, computes `cancun.settleRefund` on the natural-number values (no
`UInt256` wrap-around). -/
theorem refundedGas_toNat_eq_settleRefund {gl g' r : UInt256} (h : g'.toNat ≤ gl.toNat) :
    (refundedGas gl g' r).toNat = cancun.settleRefund gl.toNat g'.toNat r.toNat := by
  rw [refundedGas_toNat h]; rfl

end Refund

end EVM

end EvmYul
