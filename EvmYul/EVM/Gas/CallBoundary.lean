module

public import EvmYul.EVM.Gas.Invariants
public section

/-!
# The 63/64 rule at every call boundary, and order sensitivity of the cost

## Fork-generic statements (pure cost model)

For every schedule, if the CALL charge `callCost gas …` fits into `gas` (the gas left after the
memory-expansion charge), then `callExtra ≤ gas` (`callExtra_le_of_callCost_le`), and the gas the
callee receives fits into a `UInt256` (`callGas_lt_size`, side condition `Gcallstipend ≤
Gcallvalue`, true in every fork). With EIP-150 (`callGasRetention = some 64`, Tangerine Whistle on):

* the cap is at most `L(gas − C_EXTRA)` (`callGasCap_le_L`), so the callee receives at most
  `L(gas − C_EXTRA)` plus the stipend (`callGas_le`);
* the caller keeps at least `⌊(gas − C_EXTRA)/64⌋` after paying (`callCost_retains`).

## The interpreter

`call_boundary_of_instrCost` turns the facts above into statements about the interpreter: when
`exceptionalHalt` accepts an instruction whose instruction part is a Cancun `callCost`, the value
`Ccallgas` that `call` passes to `Θ` (via `UInt256.ofNat`) is bounded by `L(μ_g − C_EXTRA)` plus
the stipend and does not wrap, and the caller retains `⌊(μ_g − C_EXTRA)/64⌋` after `step` deducts
the charge. `call_boundary` is the CALL instance (stack `g :: t :: v :: _`), `staticcall_boundary`
the STATICCALL instance. For CREATE/CREATE2 (`create_boundary`) the callee gets exactly
`L(μ_g)`, the caller keeps exactly `⌊μ_g/64⌋`, and the conversion does not wrap.

## Order sensitivity

The cost is not a function of the instruction and the pre-state alone *in the YP order*: the
CALL family reads the gas after the memory charge. `instrCost?_gas_indep` shows that every other
instruction's cost is independent of the gas argument, and `call_cost_order_sensitive` exhibits a
CALL whose cost differs when evaluated on pre-memory gas versus post-memory gas.
-/

namespace EvmYul

namespace EVM

open GasMeter ForkSchedule UInt256 GasConstants

namespace ForkSchedule

/-- `x != 0` for a nonzero `UInt256` (its derived `BEq` is not registered as lawful). -/
theorem bne_zero_of_ne {x : UInt256} (hx : x ≠ ⟨0⟩) : (x != ⟨0⟩) = true := by
  rcases x with ⟨v⟩
  have : v ≠ 0 := fun h => hx (by subst h; rfl)
  change (!(v == 0)) = true
  simpa using this

section Generic

variable {fs : ForkSchedule} {gas : ℕ} {t r : AccountAddress} {val g : UInt256}
  {σ : AccountMap .EVM} {A : Substate}

theorem allBut_of_64 (h64 : fs.callGasRetention = some 64) (n : ℕ) : fs.allBut n = L n := by
  unfold allBut L; rw [h64]

/-- If the CALL charge fits, so does `C_EXTRA` (every schedule). -/
theorem callExtra_le_of_callCost_le (hc : fs.callCost gas t r val g σ A ≤ gas) :
    fs.callExtra t r val σ A ≤ gas := by
  unfold callCost at hc; omega

/-- The cap never exceeds what is left after `C_EXTRA` once the charge fits (every schedule). -/
theorem callGasCap_le_sub (hc : fs.callCost gas t r val g σ A ≤ gas) :
    fs.callGasCap gas t r val g σ A ≤ gas - fs.callExtra t r val σ A := by
  unfold callCost at hc; omega

/-- EIP-150: the cap is at most `L(gas − C_EXTRA)`. -/
theorem callGasCap_le_L (h64 : fs.callGasRetention = some 64)
    (hx : fs.callExtra t r val σ A ≤ gas) :
    fs.callGasCap gas t r val g σ A ≤ L (gas - fs.callExtra t r val σ A) := by
  unfold callGasCap; rw [h64]; simp only
  rw [if_pos hx, ← allBut_of_64 h64]; exact Nat.min_le_left _ _

/-- EIP-150: the callee receives at most `L(gas − C_EXTRA)` plus the stipend. -/
theorem callGas_le (h64 : fs.callGasRetention = some 64)
    (hc : fs.callCost gas t r val g σ A ≤ gas) :
    fs.callGas gas t r val g σ A ≤ L (gas - fs.callExtra t r val σ A) + fs.Gcallstipend := by
  have := callGasCap_le_L (g := g) h64 (callExtra_le_of_callCost_le hc)
  unfold callGas; split <;> omega

/-- **EIP-150 retention**: after paying a fitting CALL charge, the caller keeps at least
`⌊(gas − C_EXTRA)/64⌋`. -/
theorem callCost_retains (h64 : fs.callGasRetention = some 64)
    (hc : fs.callCost gas t r val g σ A ≤ gas) :
    (gas - fs.callExtra t r val σ A) / 64 ≤ gas - fs.callCost gas t r val g σ A := by
  have hx := callExtra_le_of_callCost_le hc
  have := callGasCap_le_L (g := g) h64 hx
  have := L_add_div (gas - fs.callExtra t r val σ A)
  unfold callCost at *; omega

/-- The value-transfer surcharge is at least the stipend, so the callee's gas is at most `gas`. -/
theorem callGas_le_gas (hst : fs.Gcallstipend ≤ fs.Gcallvalue)
    (hc : fs.callCost gas t r val g σ A ≤ gas) : fs.callGas gas t r val g σ A ≤ gas := by
  have := callGasCap_le_sub hc
  have := callExtra_le_of_callCost_le hc
  unfold callGas
  split
  · omega
  · rename_i hv
    have : fs.Gcallvalue ≤ fs.callExtra t r val σ A := by
      unfold callExtra
      have hne : (val != ⟨0⟩) = true := bne_zero_of_ne hv
      rw [if_pos hne]; omega
    omega

/-- **No wrap-around** of the forwarded gas (every schedule with `Gcallstipend ≤ Gcallvalue`). -/
theorem callGas_lt_size (hst : fs.Gcallstipend ≤ fs.Gcallvalue)
    (hc : fs.callCost gas t r val g σ A ≤ gas) (hg : gas < UInt256.size) :
    fs.callGas gas t r val g σ A < UInt256.size :=
  lt_of_le_of_lt (callGas_le_gas hst hc) hg

end Generic

/-- EIP-150 is active exactly from Tangerine Whistle on. -/
theorem callGasRetention_ofFork (f : Fork) :
    (ofFork f).callGasRetention = if Fork.tangerineWhistle ≤ f then some 64 else none := by
  cases f <;> decide

/-- The side condition of `callGas_lt_size` holds in every named fork. -/
theorem stipend_le_callvalue_ofFork (f : Fork) :
    (ofFork f).Gcallstipend ≤ (ofFork f).Gcallvalue := by
  cases f <;> decide

/-! ## Cancun agrees with the interpreter's `C_EXTRA`, `C_CALL`, `C_CALLGAS` -/

theorem callExtra_cancun (t r : AccountAddress) (val : UInt256) (σ : AccountMap .EVM)
    (A : Substate) : cancun.callExtra t r val σ A = Cextra t r val σ A := by
  simp only [callExtra, Cextra, accessCost, Caccess, Cxfer, Cnew]; rfl

theorem callGasCap_cancun (t r : AccountAddress) (val g : UInt256) (σ : AccountMap .EVM)
    (μ : MachineState) (A : Substate) :
    cancun.callGasCap μ.gasAvailable.toNat t r val g σ A = Cgascap t r val g σ μ A := by
  unfold callGasCap Cgascap
  simp only [callExtra_cancun, allBut_of_64 (fs := cancun) rfl]

theorem callCost_cancun (t r : AccountAddress) (val g : UInt256) (σ : AccountMap .EVM)
    (μ : MachineState) (A : Substate) :
    cancun.callCost μ.gasAvailable.toNat t r val g σ A = Ccall t r val g σ μ A := by
  unfold callCost; rw [callGasCap_cancun, callExtra_cancun]; rfl

theorem callGas_cancun (t r : AccountAddress) (val g : UInt256) (σ : AccountMap .EVM)
    (μ : MachineState) (A : Substate) :
    cancun.callGas μ.gasAvailable.toNat t r val g σ A = Ccallgas t r val g σ μ A := by
  unfold callGas
  rw [callGasCap_cancun]
  split
  · rename_i hv; subst hv; rfl
  · rename_i hv; rw [Ccallgas_of_ne_zero hv]; rfl

end ForkSchedule

/-! ## The interpreter's call boundary -/

section Interpreter

variable {vj : Array UInt256} {w : Operation .EVM} {s s' : State} {c₂ : ℕ}

/-- What a successful `exceptionalHalt` leaves: only the gas changes, the instruction part `c₂` is
the Cancun instruction cost on the new gas, and it fits. -/
theorem exceptionalHalt_ok_parts (h : exceptionalHalt vj w s = .ok (s', c₂)) :
    s' = { s with gasAvailable := s'.gasAvailable } ∧ c₂ ≤ s'.gasAvailable.toNat ∧
      cancun.instrCost? s'.gasAvailable.toNat s w = some c₂ := by
  unfold exceptionalHalt exceptionalHaltFs at h
  obtain ⟨⟨s₁, c₁⟩, hp, h⟩ := except_bind_ok h
  obtain ⟨u, -, h⟩ := except_bind_ok h
  cases h
  obtain ⟨m, hcp, hle, rfl⟩ := chargeOp_ok_iff.1 hp
  obtain ⟨-, -, hc⟩ := costParts_eq_some hcp
  have hg : (s.gasAvailable - .ofNat m).toNat = s.gasAvailable.toNat - m :=
    toNat_sub_ofNat_of_le (by omega)
  refine ⟨rfl, ?_, ?_⟩
  · simp only [hg]; omega
  · simp only [hg]; exact hc

/-- **63/64 at the call boundary** (generic over the CALL family): if `exceptionalHalt` accepts
an instruction whose Cancun instruction cost is `callCost … t r v g …`, then the gas `call` hands
to `Θ` (`Ccallgas`, on the state `exceptionalHalt` returns) satisfies the 63/64 bound, its
`UInt256` conversion is exact, and after `step` deducts the charge the caller still holds
`⌊(μ_g − C_EXTRA)/64⌋`. -/
theorem call_boundary_of_instrCost {t r : AccountAddress} {v g : UInt256}
    (h : exceptionalHalt vj w s = .ok (s', c₂))
    (hc : ∀ n, cancun.instrCost? n s w = some (cancun.callCost n t r v g s.accountMap s.substate)) :
    let extra := Cextra t r v s'.accountMap s'.substate
    let callgas := Ccallgas t r v g s'.accountMap s'.toMachineState s'.substate
    extra ≤ s'.gasAvailable.toNat ∧
      callgas ≤ L (s'.gasAvailable.toNat - extra) + GasConstants.Gcallstipend ∧
      (UInt256.ofNat callgas).toNat = callgas ∧
      (s'.gasAvailable.toNat - extra) / 64 ≤ (deductPrechecked s'.gasAvailable c₂).toNat := by
  obtain ⟨hs', hle, hcost⟩ := exceptionalHalt_ok_parts h
  rw [hc] at hcost
  cases hcost
  have hσ : s'.accountMap = s.accountMap := by rw [hs']
  have hA : s'.substate = s.substate := by rw [hs']
  simp only [hσ, hA] at *
  have hfit : cancun.callCost s'.gasAvailable.toNat t r v g s.accountMap s.substate ≤
      s'.gasAvailable.toNat := hle
  have hx := callExtra_le_of_callCost_le hfit
  have hlt := s'.gasAvailable.toNat_lt_size
  rw [callExtra_cancun] at hx
  refine ⟨hx, ?_, ?_, ?_⟩
  · have := callGas_le (fs := cancun) rfl hfit
    rw [callGas_cancun, callExtra_cancun] at this; exact this
  · apply toNat_ofNat_of_lt
    have := callGas_lt_size (fs := cancun) (by decide) hfit hlt
    rwa [callGas_cancun] at this
  · have := callCost_retains (fs := cancun) rfl hfit
    rw [deductPrechecked_toNat hle]
    rwa [callExtra_cancun] at this

/-- **63/64 at a CALL** (`μ_s = g :: t :: v :: _`). -/
theorem call_boundary {g t v : UInt256} {rest : List UInt256} (hs : s.stack = g :: t :: v :: rest)
    (h : exceptionalHalt vj .CALL s = .ok (s', c₂)) :
    let T := AccountAddress.ofUInt256 t
    let extra := Cextra T T v s'.accountMap s'.substate
    let callgas := Ccallgas T T v g s'.accountMap s'.toMachineState s'.substate
    extra ≤ s'.gasAvailable.toNat ∧
      callgas ≤ L (s'.gasAvailable.toNat - extra) + GasConstants.Gcallstipend ∧
      (UInt256.ofNat callgas).toNat = callgas ∧
      (s'.gasAvailable.toNat - extra) / 64 ≤ (deductPrechecked s'.gasAvailable c₂).toNat :=
  call_boundary_of_instrCost h fun n => by simp [instrCost?, hs]

/-- **63/64 at a STATICCALL** (`μ_s = g :: t :: _`, no value). -/
theorem staticcall_boundary {g t : UInt256} {rest : List UInt256} (hs : s.stack = g :: t :: rest)
    (h : exceptionalHalt vj .STATICCALL s = .ok (s', c₂)) :
    let T := AccountAddress.ofUInt256 t
    let extra := Cextra T T ⟨0⟩ s'.accountMap s'.substate
    let callgas := Ccallgas T T ⟨0⟩ g s'.accountMap s'.toMachineState s'.substate
    extra ≤ s'.gasAvailable.toNat ∧
      callgas ≤ L (s'.gasAvailable.toNat - extra) + GasConstants.Gcallstipend ∧
      (UInt256.ofNat callgas).toNat = callgas ∧
      (s'.gasAvailable.toNat - extra) / 64 ≤ (deductPrechecked s'.gasAvailable c₂).toNat :=
  call_boundary_of_instrCost h fun n => by simp [instrCost?, hs]

/-- **63/64 at CREATE/CREATE2**: the callee receives exactly `L(μ_g)` (the `UInt256.ofNat`
conversion is exact) and the caller keeps exactly `⌊μ_g/64⌋`. -/
theorem create_boundary (g : UInt256) :
    (UInt256.ofNat (L g.toNat)).toNat = L g.toNat ∧ L g.toNat + g.toNat / 64 = g.toNat ∧
      g.toNat - L g.toNat = g.toNat / 64 := by
  have h1 := L_add_div g.toNat
  refine ⟨toNat_ofNat_of_lt (lt_of_le_of_lt (L_le _) g.toNat_lt_size), h1, by omega⟩

end Interpreter

/-! ## Order sensitivity -/

namespace ForkSchedule

/-- Every instruction outside the CALL family has a cost independent of the gas argument. -/
theorem instrCost?_gas_indep (fs : ForkSchedule) (s : State) (w : Operation .EVM)
    (hw : w ≠ .CALL ∧ w ≠ .CALLCODE ∧ w ≠ .DELEGATECALL ∧ w ≠ .STATICCALL) (n n' : ℕ) :
    fs.instrCost? n s w = fs.instrCost? n' s w := by
  obtain ⟨h1, h2, h3, h4⟩ := hw
  unfold instrCost?
  split <;> first | rfl | (exfalso; contradiction)


/-- **Order sensitivity of the CALL cost** (every EIP-150 schedule): with `C_EXTRA + 6400` gas
before a memory charge of 640 and a request of at least 6300, the CALL instruction cost is
`6300 + C_EXTRA` on the pre-memory gas but `5670 + C_EXTRA` on the post-memory gas (the YP and
the interpreter use the latter). So the cost cannot be computed from the pre-state alone in the
YP order, and the `gas` argument of `instrCost?` is essential. -/
theorem call_cost_order_sensitive (fs : ForkSchedule) (h64 : fs.callGasRetention = some 64)
    (s : State) {g t v : UInt256} {rest : List UInt256} (hs : s.stack = g :: t :: v :: rest)
    (hg : 6300 ≤ g.toNat) :
    let T := AccountAddress.ofUInt256 t
    let extra := fs.callExtra T T v s.accountMap s.substate
    fs.instrCost? (extra + 6400) s .CALL = some (6300 + extra) ∧
      fs.instrCost? (extra + 6400 - 640) s .CALL = some (5670 + extra) := by
  intro T extra
  simp only [T, extra, instrCost?, hs, List.getElem?_cons_zero, List.getElem?_cons_succ,
    Option.bind_eq_bind, Option.bind_some, Option.pure_def, callCost, callGasCap, h64,
    Option.some.injEq]
  generalize fs.callExtra (.ofUInt256 t) (.ofUInt256 t) v s.accountMap s.substate = e
  rw [if_pos (by omega), if_pos (by omega), allBut_of_64 h64, allBut_of_64 h64]
  have h1 : e + 6400 - e = 6400 := by omega
  have h2 : e + 6400 - 640 - e = 5760 := by omega
  rw [h1, h2]
  simp only [L]
  omega

end ForkSchedule

end EVM

end EvmYul
