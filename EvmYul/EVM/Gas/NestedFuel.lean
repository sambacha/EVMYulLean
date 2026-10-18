module

public import EvmYul.EVM.Gas.Nested
public section

/-!
# Nested frames: fuel adequacy at every frame (K8, K1)

The second half of the nested-frame analysis, split from `EvmYul/EVM/Gas/Nested.lean` (which proves
the gas bounds `allGasBounds` used here). With fuel above the gas by a fixed margin (`X`: 2, `Ξ`: 3,
`Θ`/`Λ`: 4, `call`: 5 above `C_CALLGAS`, `step`: 1), no frame raises `OutOfFuel`
(`allFuelAdequate`, a simultaneous induction on the fuel). Conclusions: `nestedFuelAdequateZ`,
`X_ne_outOfFuel_unconditional` (**K8**), `Θ_ne_outOfFuel`, `Lambda_ne_outOfFuel`,
`Υ_ne_outOfFuel` / `Υ_transactionFuel_ne_outOfFuel` (**K1**). Negations show the margins are needed:
`not_X_ne_outOfFuel_of_gas_lt_fuel`, `not_Θ_ne_outOfFuel_margin_two`, `not_Θ_gasLeft_lt`.
-/

namespace EvmYul

namespace EVM

open GasMeter UInt256 ForkSchedule

attribute [local irreducible] Ξ_ECREC Ξ_SHA256 Ξ_RIP160 Ξ_ID Ξ_EXPMOD Ξ_BN_ADD Ξ_BN_MUL Ξ_SNARKV
  Ξ_BLAKE2_F Ξ_PointEval

/-! ## Fuel adequacy at every frame -/

/-- At fuel `n` above the gas plus 2, `X` never runs out of fuel. -/
@[expose] def XFuel (n : ℕ) : Prop :=
  ∀ (vj : Array UInt256) (s : State), s.gasAvailable.toNat + 2 < n → X n vj s ≠ .error .OutOfFuel

/-- At fuel `n` above the gas `g` plus 3, `Ξ` never runs out of fuel. -/
@[expose] def ΞFuel (n : ℕ) : Prop :=
  ∀ cA gbh bl σ σ₀ (g : UInt256) A I, g.toNat + 3 < n →
    Ξ n cA gbh bl σ σ₀ g A I ≠ .error .OutOfFuel

/-- At fuel `n` above the gas `g` plus 4, the message call `Θ` never runs out of fuel. -/
@[expose] def ΘFuel (n : ℕ) : Prop :=
  ∀ bvh cA gbh bl σ σ₀ A s o r c (g : UInt256) p v v' d e H w, g.toNat + 4 < n →
    Θ n bvh cA gbh bl σ σ₀ A s o r c g p v v' d e H w ≠ .error .OutOfFuel

/-- At fuel `n` above the gas `g` plus 4, the contract creation `Lambda` never runs out of fuel. -/
@[expose] def ΛFuel (n : ℕ) : Prop :=
  ∀ bvh cA gbh bl σ σ₀ A s o (g : UInt256) p v i e ζ H w, g.toNat + 4 < n →
    Lambda n bvh cA gbh bl σ σ₀ A s o g p v i e ζ H w ≠ .error .OutOfFuel

/-- At fuel `n` above the callee's allowance `Ccallgas` plus 5, a `CALL`-family instruction never
runs out of fuel. -/
@[expose] def CallFuel (n : ℕ) : Prop :=
  ∀ gasCost bvh (gas source recipient t value value' inO inS outO outS : UInt256) perm
    (st : State),
    Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient) value gas
        st.accountMap st.toMachineState st.substate + 5 < n →
      call n gasCost bvh gas source recipient t value value' inO inS outO outS perm st ≠
        .error .OutOfFuel

/-- At fuel `n` above the gas after the exceptional-halt checks plus 1, a step never runs out of
fuel. -/
@[expose] def StepFuel (n : ℕ) : Prop :=
  ∀ (vj : Array UInt256) (w : Operation .EVM) (arg : Option (UInt256 × Nat)) (s s₁ : State) (c : ℕ),
    exceptionalHalt vj w s = .ok (s₁, c) → s₁.gasAvailable.toNat + 1 < n →
      step n c (some (w, arg)) s₁ ≠ .error .OutOfFuel

theorem eq_outOfFuel_of_beq {e : ExecutionException} (h : (e == .OutOfFuel) = true) :
    e = .OutOfFuel := by
  cases e <;> first | rfl | exact absurd h (by decide)

theorem ξFuel_succ {n : ℕ} (h : XFuel n) : ΞFuel (n + 1) := by
  intro cA gbh bl σ σ₀ g A I hg hr
  simp only [Ξ, bind, Except.bind] at hr
  split at hr
  · rename_i e he
    cases hr
    exact h _ _ (by exact (show g.toNat + 2 < n by omega)) he
  · split at hr <;> cases hr

theorem θFuel_succ {n : ℕ} (h : ΞFuel n) : ΘFuel (n + 1) := by
  intro bvh cA gbh bl σ σ₀ A s o r c g p v v' d e H w hg hr
  cases c with
  | Precompiled p => simp only [Θ, bind, Except.bind] at hr; cases hr
  | Code code =>
    simp only [Θ, bind, Except.bind] at hr
    split at hr
    · rename_i e he
      split at hr
      · rename_i hoof
        have := eq_outOfFuel_of_beq hoof
        subst this
        exact h _ _ _ _ _ _ _ _ (by omega) he
      · cases hr
    · cases hr
    · cases hr

theorem lambdaFuel_succ {n : ℕ} (h : ΞFuel n) : ΛFuel (n + 1) := by
  intro bvh cA gbh bl σ σ₀ A s o g p v i e ζ H w hg hr
  simp only [Lambda, bind, Except.bind] at hr
  split at hr
  · rename_i err heq
    cases hr
    generalize Lambda.L_A _ _ _ _ = x at heq
    cases x <;> simp [liftM, monadLift, MonadLift.monadLift,
      instMonadLiftOptionExceptExecutionException, Option.option] at heq
  split at hr
  · rename_i e he
    split at hr
    · rename_i hoof
      have := eq_outOfFuel_of_beq hoof
      subst this
      exact h _ _ _ _ _ _ _ _ (by omega) he
    · cases hr
  · cases hr
  · cases hr

theorem callFuel_succ {n : ℕ} (h : ΘFuel n) : CallFuel (n + 1) := by
  intro gasCost bvh gas source recipient t value value' inO inS outO outS perm st hg hr
  simp only [call, bind, Except.bind, pure, Except.pure] at hr
  split at hr
  · split at hr
    · rename_i e he
      cases hr
      exact h _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (lt_of_le_of_lt (Nat.add_le_add_right (toNat_ofNat_le _) 4) (by omega)) he
    · cases hr
  · cases hr

theorem create_charge_ge {vj : Array UInt256} {s s₁ : State} {c : ℕ}
    (hZ : exceptionalHalt vj .CREATE s = .ok (s₁, c)) : 5 ≤ c := by
  obtain ⟨-, -, h⟩ := exceptionalHalt_ok_parts hZ
  simp only [instrCost?, bind, Option.bind, pure] at h
  split at h
  · cases h
  · cases h; simp only [cancun]; omega

theorem create2_charge_ge {vj : Array UInt256} {s s₁ : State} {c : ℕ}
    (hZ : exceptionalHalt vj .CREATE2 s = .ok (s₁, c)) : 5 ≤ c := by
  obtain ⟨-, -, h⟩ := exceptionalHalt_ok_parts hZ
  simp only [instrCost?, bind, Option.bind, pure] at h
  split at h
  · cases h
  · cases h; simp only [cancun]; omega

theorem call_fuel_contra {n c : ℕ} (hC : CallFuel n) {bvh : List ByteArray}
    {gas source recipient t value value' inO inS outO outS : UInt256} {perm : Bool} {st : State}
    (hcall : call n c bvh gas source recipient t value value' inO inS outO outS perm st =
      .error .OutOfFuel)
    (hcov : Ccallgas (AccountAddress.ofUInt256 t) (AccountAddress.ofUInt256 recipient) value gas
      st.accountMap st.toMachineState st.substate + 100 ≤ c)
    (hle : c ≤ st.gasAvailable.toNat) (hg : st.gasAvailable.toNat < n) : False :=
  hC _ _ _ _ _ _ _ _ _ _ _ _ _ st (by omega) hcall

theorem step_CALL_fuel {n : ℕ} (hC : CallFuel n) {vj : Array UInt256}
    {arg : Option (UInt256 × Nat)} {s s₁ : State} {c : ℕ}
    (hZ : exceptionalHalt vj .CALL s = .ok (s₁, c)) (hg : s₁.gasAvailable.toNat < n) :
    step (n + 1) c (some (.CALL, arg)) s₁ ≠ .error .OutOfFuel := by
  intro hs
  simp only [step, bind, Except.bind, pure, Except.pure] at hs
  obtain ⟨hs', -, -⟩ := exceptionalHalt_ok_parts hZ
  have hstk : s₁.stack = s.stack := by rw [hs']
  have hI : s₁.executionEnv = s.executionEnv := by rw [hs']
  rcases h7 : s.stack.pop7 with _ | ⟨tl, a0, a1, a2, a3, a4, a5, a6⟩
  · rw [hstk, h7] at hs
    simp [liftM, monadLift, MonadLift.monadLift, instMonadLiftOptionExceptExecutionException,
      Option.option] at hs
  · have hst := pop7_eq_some h7
    rw [hstk, hst] at hs
    simp only [Stack.pop7, liftM, monadLift, MonadLift.monadLift,
      instMonadLiftOptionExceptExecutionException, Option.option] at hs
    split at hs
    · rename_i e hcall
      cases hs
      have hc : cancun.instrCost? s₁.gasAvailable.toNat s .CALL =
          some (cancun.callCost s₁.gasAvailable.toNat (.ofUInt256 a1) (.ofUInt256 a1) a2 a0
            s.accountMap s.substate) := by
        simp [instrCost?, hst]
      obtain ⟨hcov, hle⟩ := charge_covers_of_instrCost hZ hc
      exact call_fuel_contra hC hcall (by simpa only [hI, ofUInt256_ofNat_address] using hcov)
        (by exact hle) (by exact hg)
    · cases hs

theorem step_CALLCODE_fuel {n : ℕ} (hC : CallFuel n) {vj : Array UInt256}
    {arg : Option (UInt256 × Nat)} {s s₁ : State} {c : ℕ}
    (hZ : exceptionalHalt vj .CALLCODE s = .ok (s₁, c)) (hg : s₁.gasAvailable.toNat < n) :
    step (n + 1) c (some (.CALLCODE, arg)) s₁ ≠ .error .OutOfFuel := by
  intro hs
  simp only [step, bind, Except.bind, pure, Except.pure] at hs
  obtain ⟨hs', -, -⟩ := exceptionalHalt_ok_parts hZ
  have hstk : s₁.stack = s.stack := by rw [hs']
  have hI : s₁.executionEnv = s.executionEnv := by rw [hs']
  rcases h7 : s.stack.pop7 with _ | ⟨tl, a0, a1, a2, a3, a4, a5, a6⟩
  · rw [hstk, h7] at hs
    simp [liftM, monadLift, MonadLift.monadLift, instMonadLiftOptionExceptExecutionException,
      Option.option] at hs
  · have hst := pop7_eq_some h7
    rw [hstk, hst] at hs
    simp only [Stack.pop7, liftM, monadLift, MonadLift.monadLift,
      instMonadLiftOptionExceptExecutionException, Option.option] at hs
    split at hs
    · rename_i e hcall
      cases hs
      have hc : cancun.instrCost? s₁.gasAvailable.toNat s .CALLCODE =
          some (cancun.callCost s₁.gasAvailable.toNat (.ofUInt256 a1) s.executionEnv.codeOwner a2 a0
            s.accountMap s.substate) := by
        simp [instrCost?, hst]
      obtain ⟨hcov, hle⟩ := charge_covers_of_instrCost hZ hc
      exact call_fuel_contra hC hcall (by simpa only [hI, ofUInt256_ofNat_address] using hcov)
        (by exact hle) (by exact hg)
    · cases hs

theorem step_DELEGATECALL_fuel {n : ℕ} (hC : CallFuel n) {vj : Array UInt256}
    {arg : Option (UInt256 × Nat)} {s s₁ : State} {c : ℕ}
    (hZ : exceptionalHalt vj .DELEGATECALL s = .ok (s₁, c)) (hg : s₁.gasAvailable.toNat < n) :
    step (n + 1) c (some (.DELEGATECALL, arg)) s₁ ≠ .error .OutOfFuel := by
  intro hs
  simp only [step, bind, Except.bind, pure, Except.pure] at hs
  obtain ⟨hs', -, -⟩ := exceptionalHalt_ok_parts hZ
  have hstk : s₁.stack = s.stack := by rw [hs']
  have hI : s₁.executionEnv = s.executionEnv := by rw [hs']
  rcases h7 : s.stack.pop6 with _ | ⟨tl, a0, a1, a3, a4, a5, a6⟩
  · rw [hstk, h7] at hs
    simp [liftM, monadLift, MonadLift.monadLift, instMonadLiftOptionExceptExecutionException,
      Option.option] at hs
  · have hst := pop6_eq_some h7
    rw [hstk, hst] at hs
    simp only [Stack.pop6, liftM, monadLift, MonadLift.monadLift,
      instMonadLiftOptionExceptExecutionException, Option.option] at hs
    split at hs
    · rename_i e hcall
      cases hs
      have hc : cancun.instrCost? s₁.gasAvailable.toNat s .DELEGATECALL =
          some (cancun.callCost s₁.gasAvailable.toNat (.ofUInt256 a1) s.executionEnv.codeOwner ⟨0⟩ a0
            s.accountMap s.substate) := by
        simp [instrCost?, hst]
      obtain ⟨hcov, hle⟩ := charge_covers_of_instrCost hZ hc
      exact call_fuel_contra hC hcall (by simpa only [hI, ofUInt256_ofNat_address] using hcov)
        (by exact hle) (by exact hg)
    · cases hs

theorem step_STATICCALL_fuel {n : ℕ} (hC : CallFuel n) {vj : Array UInt256}
    {arg : Option (UInt256 × Nat)} {s s₁ : State} {c : ℕ}
    (hZ : exceptionalHalt vj .STATICCALL s = .ok (s₁, c)) (hg : s₁.gasAvailable.toNat < n) :
    step (n + 1) c (some (.STATICCALL, arg)) s₁ ≠ .error .OutOfFuel := by
  intro hs
  simp only [step, bind, Except.bind, pure, Except.pure] at hs
  obtain ⟨hs', -, -⟩ := exceptionalHalt_ok_parts hZ
  have hstk : s₁.stack = s.stack := by rw [hs']
  have hI : s₁.executionEnv = s.executionEnv := by rw [hs']
  rcases h7 : s.stack.pop6 with _ | ⟨tl, a0, a1, a3, a4, a5, a6⟩
  · rw [hstk, h7] at hs
    simp [liftM, monadLift, MonadLift.monadLift, instMonadLiftOptionExceptExecutionException,
      Option.option] at hs
  · have hst := pop6_eq_some h7
    rw [hstk, hst] at hs
    simp only [Stack.pop6, liftM, monadLift, MonadLift.monadLift,
      instMonadLiftOptionExceptExecutionException, Option.option] at hs
    split at hs
    · rename_i e hcall
      cases hs
      have hc : cancun.instrCost? s₁.gasAvailable.toNat s .STATICCALL =
          some (cancun.callCost s₁.gasAvailable.toNat (.ofUInt256 a1) (.ofUInt256 a1) ⟨0⟩ a0
            s.accountMap s.substate) := by
        simp [instrCost?, hst]
      obtain ⟨hcov, hle⟩ := charge_covers_of_instrCost hZ hc
      exact call_fuel_contra hC hcall (by simpa only [hI, ofUInt256_ofNat_address] using hcov)
        (by exact hle) (by exact hg)
    · cases hs

theorem step_CREATE_fuel {n : ℕ} (hL : ΛFuel n) {arg : Option (UInt256 × Nat)}
    {s₁ : State} {c : ℕ} (hc5 : 5 ≤ c) (hc : c ≤ s₁.gasAvailable.toNat)
    (hg : s₁.gasAvailable.toNat < n) :
    step (n + 1) c (some (.CREATE, arg)) s₁ ≠ .error .OutOfFuel := by
  intro hs
  have hD : (ofNat (L (deductPrechecked s₁.gasAvailable c).toNat) : UInt256).toNat + 4 < n := by
    have h1 := toNat_ofNat_le (L (deductPrechecked s₁.gasAvailable c).toNat)
    have h2 : L (deductPrechecked s₁.gasAvailable c).toNat ≤
        (deductPrechecked s₁.gasAvailable c).toNat := Nat.sub_le _ _
    have h3 := deductPrechecked_toNat hc
    omega
  simp only [step, bind, Except.bind, pure, Except.pure] at hs
  split at hs
  · split at hs
    · rename_i e heq
      cases hs
      split at heq
      · cases heq
      split at heq
      · split at heq
        · cases heq
        · rename_i hΛ
          exact hL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hD hΛ
        · cases heq
      · cases heq
    · split at hs <;> cases hs
  · cases hs

theorem step_CREATE2_fuel {n : ℕ} (hL : ΛFuel n) {arg : Option (UInt256 × Nat)}
    {s₁ : State} {c : ℕ} (hc5 : 5 ≤ c) (hc : c ≤ s₁.gasAvailable.toNat)
    (hg : s₁.gasAvailable.toNat < n) :
    step (n + 1) c (some (.CREATE2, arg)) s₁ ≠ .error .OutOfFuel := by
  intro hs
  have hD : (ofNat (L (deductPrechecked s₁.gasAvailable c).toNat) : UInt256).toNat + 4 < n := by
    have h1 := toNat_ofNat_le (L (deductPrechecked s₁.gasAvailable c).toNat)
    have h2 : L (deductPrechecked s₁.gasAvailable c).toNat ≤
        (deductPrechecked s₁.gasAvailable c).toNat := Nat.sub_le _ _
    have h3 := deductPrechecked_toNat hc
    omega
  simp only [step, bind, Except.bind, pure, Except.pure] at hs
  split at hs
  · split at hs
    · rename_i e heq
      cases hs
      split at heq
      · cases heq
      split at heq
      · split at heq
        · cases heq
        · rename_i hΛ
          exact hL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hD hΛ
        · cases heq
      · cases heq
    · split at hs <;> cases hs
  · cases hs

theorem stepFuel_succ {n : ℕ} (hC : CallFuel n) (hL : ΛFuel n) : StepFuel (n + 1) := by
  intro vj w arg s s₁ c hZ hg
  have hg' : s₁.gasAvailable.toNat < n := by omega
  obtain ⟨-, hc, -⟩ := exceptionalHalt_ok_parts hZ
  by_cases hw : w ∈ spawnOps
  · simp only [spawnOps, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
    · exact step_CREATE_fuel hL (create_charge_ge hZ) hc hg'
    · exact step_CREATE2_fuel hL (create2_charge_ge hZ) hc hg'
    · exact step_CALL_fuel hC hZ hg'
    · exact step_CALLCODE_fuel hC hZ hg'
    · exact step_DELEGATECALL_fuel hC hZ hg'
    · exact step_STATICCALL_fuel hC hZ hg'
  · intro he
    have := step_some_gasSafe (f := n) (c := c) (arg := arg) s₁ hw
    rw [he] at this
    exact this.error_ne rfl

theorem xFuel_succ {n : ℕ} (hN : StepFuel n) (hX : XFuel n) : XFuel (n + 1) := by
  intro vj s hs
  unfold X
  simp only [traceInstructions, Bool.false_eq_true, ↓reduceIte]
  generalize (decode s.executionEnv.code s.pc).getD (Operation.STOP, none) = instr
  obtain ⟨w, arg⟩ := instr
  simp only
  rcases hZ : exceptionalHalt vj w s with e | ⟨s₁, c⟩
  · simp only; intro he; cases he; exact exceptionalHalt_ne_outOfFuel hZ
  · obtain ⟨hs₁, hc, -⟩ := exceptionalHalt_ok_parts hZ
    have hg₁ : s₁.gasAvailable.toNat ≤ s.gasAvailable.toNat := by
      have := exceptionalHalt_ok_gas hZ
      omega
    simp only [bind, Except.bind]
    rcases hstep : step n c (some (w, arg)) s₁ with e | s₂
    · simp only; intro he; cases he; exact hN vj w arg s s₁ c hZ (by omega) hstep
    · simp only
      split
      · rename_i hH
        split at hH
        · cases hH
        · rename_i h1
          split at hH
          · cases hH
          · rename_i h2
            have hw : halting w = false := halting_eq_false_of h1 h2 (by
              rintro rfl; exact exceptionalHalt_INVALID_ne_ok vj s s₁ c hZ)
            have hlt : s₂.gasAvailable.toNat < s.gasAvailable.toNat := by
              rcases stepGasSoundZ n vj w arg s s₁ c s₂ hZ hstep with h | h
              · have := exceptionalHalt_charge_lt hw hZ
                omega
              · omega
            exact hX vj s₂ (by omega)
      · split <;> simp

theorem allFuelAdequate (n : ℕ) :
    XFuel n ∧ ΞFuel n ∧ ΘFuel n ∧ ΛFuel n ∧ CallFuel n ∧ StepFuel n := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro _ _ h; omega
    · intro _ _ _ _ _ _ _ _ h; omega
    · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h; omega
    · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h; omega
    · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h; omega
    · intro _ _ _ _ _ _ _ h; omega
  | succ n ih =>
    obtain ⟨hX, hΞ, hΘ, hΛ, hC, hS⟩ := ih
    exact ⟨xFuel_succ hS hX, ξFuel_succ hX, θFuel_succ hΞ, lambdaFuel_succ hΞ,
      callFuel_succ hΘ, stepFuel_succ hC hΛ⟩

/-! ## Conclusions -/

/-- `NestedFuelAdequateZ`, now unconditional (all instructions, including the six spawning ones). -/
theorem nestedFuelAdequateZ : NestedFuelAdequateZ := fun f => (allFuelAdequate f).2.2.2.2.2

theorem spawnStepGasSoundZ : SpawnStepGasSoundZ :=
  fun f vj w arg s s₁ c s₂ _ => stepGasSoundZ f vj w arg s s₁ c s₂

theorem spawnNestedFuelAdequateZ : SpawnNestedFuelAdequateZ :=
  fun f vj w arg s s₁ c _ => nestedFuelAdequateZ f vj w arg s s₁ c

/-- **K8**: `X`'s fuel counter is never exhausted once the fuel exceeds the gas by 2 — with no
hypotheses (all instructions, including CREATE/CREATE2/CALL/CALLCODE/DELEGATECALL/STATICCALL). -/
theorem X_ne_outOfFuel_unconditional (f : ℕ) (vj : Array UInt256) (s : State)
    (h : s.gasAvailable.toNat + 2 < f) : X f vj s ≠ .error .OutOfFuel :=
  X_ne_outOfFuel stepGasSoundZ nestedFuelAdequateZ f vj s h

/-- A message call (`Θ`) given more than `g + 4` fuel never runs out of fuel. -/
theorem Θ_ne_outOfFuel {f : ℕ} {bvh cA gbh bl σ σ₀ A s o r c} {g : UInt256} {p v v' d e H w}
    (h : g.toNat + 4 < f) :
    Θ f bvh cA gbh bl σ σ₀ A s o r c g p v v' d e H w ≠ .error .OutOfFuel :=
  (allFuelAdequate f).2.2.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h

/-- A contract creation (`Λ`) given more than `g + 4` fuel never runs out of fuel. -/
theorem Lambda_ne_outOfFuel {f : ℕ} {bvh cA gbh bl σ σ₀ A s o} {g : UInt256} {p v i e ζ H w}
    (h : g.toNat + 4 < f) :
    Lambda f bvh cA gbh bl σ σ₀ A s o g p v i e ζ H w ≠ .error .OutOfFuel :=
  (allFuelAdequate f).2.2.2.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h

/-- **K1**: a transaction run with more fuel than `gasLimit + 4` never fails with `OutOfFuel`. -/
theorem Υ_ne_outOfFuel {fuel : ℕ} (σ : AccountMap .EVM) (H_f : ℕ) (H genesis : BlockHeader)
    (blocks : ProcessedBlocks) (T : Transaction) (S_T : AccountAddress)
    (hf : T.base.gasLimit.toNat + 4 < fuel) :
    Υ fuel σ H_f H genesis blocks T S_T ≠ .error (.ExecutionException .OutOfFuel) := by
  intro h
  unfold Υ at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  have hg : (UInt256.ofNat (T.base.gasLimit.toNat - intrinsicGas T)).toNat + 4 < fuel :=
    lt_of_le_of_lt (Nat.add_le_add_right (le_trans (toNat_ofNat_le _) (Nat.sub_le _ _)) 4) hf
  split at h
  · split at h
    · cases h
    · rename_i e' he'
      cases h
      exact Lambda_ne_outOfFuel hg he'
  · split at h
    · cases h
    · rename_i e' he'
      cases h
      exact Θ_ne_outOfFuel hg he'

/-- **K1 for the fuel the conformance runner uses**: `Υ (transactionFuel T b)` never fails with
`OutOfFuel`, whatever the sender balance `b`. -/
theorem Υ_transactionFuel_ne_outOfFuel (b : UInt256) (σ : AccountMap .EVM) (H_f : ℕ)
    (H genesis : BlockHeader) (blocks : ProcessedBlocks) (T : Transaction) (S_T : AccountAddress) :
    Υ (transactionFuel T b) σ H_f H genesis blocks T S_T ≠
      .error (.ExecutionException .OutOfFuel) :=
  Υ_ne_outOfFuel σ H_f H genesis blocks T S_T
    (lt_of_lt_of_le (by unfold fuelOverhead; omega) (le_max_right _ _))

/-! ## Negations: the hypotheses cannot be dropped -/

/-- The fuel margin of `X_ne_outOfFuel_unconditional` cannot be reduced to "more fuel than gas":
with gas 0 and fuel 1, `X` runs out of fuel (the STOP it decodes still needs a step). -/
theorem not_X_ne_outOfFuel_of_gas_lt_fuel :
    ¬ ∀ (f : ℕ) (vj : Array UInt256) (s : State), s.gasAvailable.toNat < f →
      X f vj s ≠ .error .OutOfFuel :=
  fun h => h 1 #[] default Nat.one_pos rfl

/-- `Θ` needs a fuel margin above its gas: a margin of 2 is not enough (gas 0, fuel 3, empty
code). `Θ_ne_outOfFuel` uses `g + 4 < f`. -/
theorem not_Θ_ne_outOfFuel_margin_two :
    ¬ ∀ (f : ℕ) (g : UInt256), g.toNat + 2 < f →
      Θ f [] .empty default ∅ ∅ ∅ default default default default (.Code .empty) g ⟨0⟩ ⟨0⟩ ⟨0⟩
        .empty 0 default true ≠ .error .OutOfFuel :=
  fun h => h 3 ⟨0⟩ (by decide) rfl

/-- `Θ_gasLeft_le` is tight: it cannot be strengthened to a strict inequality, since a callee
with empty code (an immediate STOP) hands back all 7 units of gas it was given. -/
theorem not_Θ_gasLeft_lt :
    ¬ ∀ (f : ℕ) (g : UInt256) (res : FrameResult),
      Θ f [] .empty default ∅ ∅ ∅ default default default default (.Code .empty) g ⟨0⟩ ⟨0⟩ ⟨0⟩
        .empty 0 default true = .ok res → res.gasLeft.toNat < g.toNat := by
  intro h
  have hm : (Θ 5 [] .empty default ∅ ∅ ∅ default default default default (.Code .empty) ⟨7⟩ ⟨0⟩
      ⟨0⟩ ⟨0⟩ .empty 0 default true).map (·.gasLeft) = .ok ⟨7⟩ := rfl
  cases hr : Θ 5 [] .empty default ∅ ∅ ∅ default default default default (.Code .empty) ⟨7⟩ ⟨0⟩
      ⟨0⟩ ⟨0⟩ .empty 0 default true with
  | error e => rw [hr] at hm; cases hm
  | ok res =>
    rw [hr] at hm
    have hg : res.gasLeft = ⟨7⟩ := by injection hm
    have := h 5 ⟨7⟩ res hr
    rw [hg] at this
    exact absurd this (by decide)

end EVM

end EvmYul
