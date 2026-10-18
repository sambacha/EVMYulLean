module

public import EvmYul.Testing.EvmFixtures
public meta import EvmYul.Testing.EvmFixtures
@[expose] public meta section

/-!
# Gas regression tests: unit tests, property tests, mutation tests

Tests of the fee schedule and cost functions (`EvmYul/EVM/Gas/Costs.lean`, `Classification`,
`Meter`, `Lemmas`). Build with `lake build EvmYulGasTests`. Every check runs while the file is
elaborated, so a failing check fails the build. Fixtures and generators:
`EvmYul/Testing/EvmFixtures.lean`.

1. **Unit tests** pin the fee-schedule constants once against YP Appendix G / the EIPs, and check
   every dynamic cost against the specification's formula applied to the input (never against a
   bare number copied from a run). They use `rfl`/`decide` when the fact is a theorem for *all*
   states, and `#guard` (compiled evaluation) when the fact needs a concrete state.
2. **Property tests** (Plausible) run each property on 300 random inputs with a fixed seed. The
   `UInt256` generator is biased toward the `0` and `2^256` boundaries, where wrap-around bugs live.
   A counterexample throws, so the build fails and the witness is printed.
3. **Mutation tests** run Plausible on properties that are *known to be false*: the refuted
   conjectures and deliberately broken variants of the model. The test fails unless Plausible
   finds a counterexample. This shows the property suites can actually fail, so they are not
   vacuous. Plausible's `failure` result carries a proof of `¬ p`, so a reported counterexample
   is sound.
-/

namespace EvmYul

namespace EVM

namespace GasTests

open GasConstants GasMeter Plausible Plausible.Decorations EvmYul.Testing.EvmFixtures

/-! ## 1. Unit tests

The unit tests keep **the table** and **the rules** apart. The table is the list of fee-schedule
constants, pinned once against the literal values printed in YP Appendix G and the EIPs. Every other
expected value is written as the rule applied to the input — the YP / EIP formula, over those
constants and over `wordsOf` / `allButOne64th` / `memSpec` / `refundRule` below, which are written
from the specification and share no code with the cost functions under test. A test therefore says
*which* rule it checks, and a wrong constant is caught by the table, not silently absorbed by every
expected value. -/

/-! ### The table: fee-schedule constants (YP Appendix G, EIP-2929, EIP-2200, EIP-3529, EIP-3860) -/
example : Gzero = 0 ∧ Gbase = 2 ∧ Gverylow = 3 ∧ Glow = 5 ∧ Gmid = 8 ∧ Ghigh = 10 ∧
    Gjumpdest = 1 ∧ Gexp = 10 ∧ Gexpbyte = 50 ∧ Gkeccak256 = 30 ∧ Gkeccak256word = 6 ∧
    Gcopy = 3 ∧ Glog = 375 ∧ Glogdata = 8 ∧ Glogtopic = 375 ∧ Gmemory = 3 ∧ Gblockhash = 20 :=
  by decide
example : Gtransaction = 21000 ∧ Gtxcreate = 32000 ∧ Gtxdatazero = 4 ∧ Gtxdatanonzero = 16 ∧
    Gcreate = 32000 ∧ Gcallstipend = 2300 ∧ Gcoldsload = 2100 ∧ Gcoldaccountaccess = 2600 ∧
    Gwarmaccess = 100 ∧ Gsset = 20000 ∧ Gsreset = 2900 ∧ Rsclear = 4800 ∧ Ginitcodeword = 2 :=
  by decide

/-! The rules written from the specification (`wordsOf`, `allButOne64th`, `memSpec`,
`refundRule`) are shared fixtures in `EvmYul/Testing/EvmFixtures.lean`; they share no code with
`Costs.lean`. -/

/-! ### Static costs hold in every state (theorems, not just tests) -/
example (s : EVM.State) : C' s .STOP = 0 := rfl
example (s : EVM.State) : C' s .RETURN = 0 := rfl
example (s : EVM.State) : C' s .ADD = 3 := rfl
example (s : EVM.State) : C' s .PUSH32 = 3 := rfl
example (s : EVM.State) : C' s .PUSH0 = 2 := rfl
example (s : EVM.State) : C' s .MUL = 5 := rfl
example (s : EVM.State) : C' s .SELFBALANCE = 5 := rfl
example (s : EVM.State) : C' s .JUMP = 8 := rfl
example (s : EVM.State) : C' s .JUMPI = 10 := rfl
example (s : EVM.State) : C' s .JUMPDEST = 1 := rfl
example (s : EVM.State) : C' s .BLOCKHASH = 20 := rfl
example (s : EVM.State) : C' s .BLOBHASH = 3 := rfl
example (s : EVM.State) : C' s .TLOAD = 100 := rfl
example (s : EVM.State) : C' s .TSTORE = 100 := rfl

/-! ### The classification covers the whole decode table -/

-- Exactly STOP, RETURN and REVERT are free among valid decoded opcodes (static + dynamic).
#guard ((decodedOps.filter fun w =>
    δ w ≠ none ∧ C' (withOwnerAccount (withStack (List.replicate 8 (u 0)))) w = 0
  ).eraseDups == [.STOP, .RETURN, .REVERT])
-- Undefined bytes decode to INVALID, the only operation in the `invalid` group.
#guard decodedOps.all fun w => (feeGroup w == .invalid) == (w == .INVALID)

/-! ### Dynamic costs on concrete states: the rule applied to the input -/
-- EXP (YP, the EXP case of `C`): `G_exp + G_expbyte · (bytes of the exponent)`;
-- 0 has 0 bytes, 255 one, 256 two.
#guard C' (withStack [u 2, u 0]) .EXP == Gexp + Gexpbyte * 0
#guard C' (withStack [u 2, u 255]) .EXP == Gexp + Gexpbyte * 1
#guard C' (withStack [u 2, u 256]) .EXP == Gexp + Gexpbyte * 2
-- KECCAK256 over `n` bytes: `G_keccak256 + G_keccak256word · ⌈n / 32⌉`.
#guard C' (withStack [u 0, u 33]) .KECCAK256 == Gkeccak256 + Gkeccak256word * wordsOf 33
-- CALLDATACOPY of `n` bytes: `G_verylow + G_copy · ⌈n / 32⌉`.
#guard C' (withStack [u 0, u 0, u 33]) .CALLDATACOPY == Gverylow + Gcopy * wordsOf 33
-- LOG2 with `n` data bytes: `G_log + G_logdata · n + 2 · G_logtopic`.
#guard C' (withStack [u 0, u 10]) .LOG2 == Glog + Glogdata * 10 + 2 * Glogtopic
-- SLOAD (EIP-2929): cold `G_coldsload`, warm `G_warmaccess`.
#guard C' (withStack [u 5]) .SLOAD == Gcoldsload
#guard C' (warmSlot (withStack [u 5]) (u 5)) .SLOAD == Gwarmaccess
-- BALANCE (EIP-2929): cold `G_coldaccountaccess`, warm `G_warmaccess`.
#guard C' (withStack [u 7]) .BALANCE == Gcoldaccountaccess
#guard C' (warmAccount (withStack [u 7]) (AccountAddress.ofUInt256 (u 7))) .BALANCE == Gwarmaccess
-- SSTORE (EIP-2200 + EIP-2929) on a clean slot of value 0: setting it costs `G_sset`, a no-op write
-- `G_warmaccess`, each plus `G_coldsload` when the slot is cold.
#guard C' (withOwnerAccount (withStack [u 5, u 1])) .SSTORE == Gcoldsload + Gsset
#guard C' (withOwnerAccount (withStack [u 5, u 0])) .SSTORE == Gcoldsload + Gwarmaccess
#guard C' (warmSlot (withOwnerAccount (withStack [u 5, u 1])) (u 5)) .SSTORE == Gsset
-- CREATE with `n` bytes of initcode (EIP-3860): `G_create + G_initcodeword · ⌈n / 32⌉`.
#guard C' (withStack [u 0, u 0, u 33]) .CREATE == Gcreate + Ginitcodeword * wordsOf 33
-- CALL to a cold account, no value, gas `g`, request `q` (EIP-150, EIP-2929): the callee gets
-- `min q (allButOne64th (g − G_coldaccountaccess))`, and the caller pays that plus the access cost.
#guard C' (withGas (withStack [u 1000000, u 1, u 0, u 0, u 0, u 0, u 0]) 100000) .CALL ==
  min 1000000 (allButOne64th (100000 - Gcoldaccountaccess)) + Gcoldaccountaccess
#guard C' (withGas (withStack [u 500, u 1, u 0, u 0, u 0, u 0, u 0]) 100000) .CALL ==
  min 500 (allButOne64th (100000 - Gcoldaccountaccess)) + Gcoldaccountaccess

/-! ### Memory expansion (YP (328)) -/
#guard [0, 1, 32, 1024].all fun a => Cₘ (u a) == memSpec a
-- MSTORE at offset `o` from empty memory touches `⌈(o + 32) / 32⌉` words.
#guard memoryExpansionCost (withStack [u 0, u 0]) .MSTORE == memSpec (wordsOf (0 + 32))
#guard memoryExpansionCost (withStack [u 1000, u 0]) .MSTORE == memSpec (wordsOf (1000 + 32))

/-! ### 1/64 rule -/
#guard [0, 63, 64, 6400, 97400].all fun n => L n == allButOne64th n

/-! ### Guarded charge: OOG exactly when the cost exceeds the gas, else `gas − cost` -/
#guard isOOG (chargeGas (u 10) 11)
#guard okNat? (chargeGas (u 10) 10) == some (10 - 10)
#guard okNat? (chargeGas (u 10) 3) == some (10 - 3)
#guard isOOG (chargeGas (u 0) 1)

/-! ### EIP-3529 refund: the cap binds, does not bind, and nothing was used -/
#guard (refundedGas (u 100000) (u 40000) (u 50000)).toNat == refundRule 100000 40000 50000
#guard (refundedGas (u 100000) (u 40000) (u 5000)).toNat == refundRule 100000 40000 5000
#guard (refundedGas (u 100000) (u 100000) (u 5000)).toNat == refundRule 100000 100000 5000
-- The three points exercise different branches of the rule (cap binding / not binding / zero used).
#guard refundRule 100000 40000 50000 < 40000 + 50000 ∧ refundRule 100000 40000 5000 = 40000 + 5000 ∧
  refundRule 100000 100000 5000 = 100000

/-! ### Intrinsic gas (YP (64), EIP-2028, EIP-3860) -/
#guard intrinsicGas (legacyTx (some default) []) == Gtransaction
#guard intrinsicGas (legacyTx (some default) [0, 1]) == Gtransaction + Gtxdatazero + Gtxdatanonzero
-- Creation with 33 non-zero bytes: the creation surcharge plus the initcode words.
#guard intrinsicGas (legacyTx none (List.replicate 33 1)) ==
  Gtransaction + Gtxcreate + Gtxdatanonzero * 33 + Ginitcodeword * wordsOf 33

/-! ## 2. Property tests (Plausible) -/

/-! ### Specifications as executable checkers (mirroring the theorems in `GasLemmas`) -/

/-- `a + d`, saturated at `2^256 − 1` (always `≥ a`). -/
def bump (a : UInt256) (d : ℕ) : UInt256 :=
  if a.toNat + d < UInt256.size then .ofNat (a.toNat + d) else .ofNat (UInt256.size - 1)

/-- `chargeGas_ok_iff` / `chargeGas_error_iff`. -/
def chargeSpec (g : UInt256) (c : ℕ) : Bool :=
  match chargeGas g c with
  | .ok g' => c ≤ g.toNat && g'.toNat == g.toNat - c
  | .error e => g.toNat < c && e == .OutOfGass

/-- `chargeGas_bind_ok_iff`: the two-phase charge fails iff `gas < c₁ + c₂`. -/
def twoPhaseSpec (g : UInt256) (c₁ c₂ : ℕ) : Bool :=
  match chargeGas g c₁ >>= fun g₁ => chargeGas g₁ c₂ with
  | .ok g' => c₁ + c₂ ≤ g.toNat && g'.toNat == g.toNat - (c₁ + c₂)
  | .error _ => g.toNat < c₁ + c₂

/--
Refund lemmas: cap, bounds and the 4/5 lower bound on the final gas used. The remaining gas
`g' = gl − d` is built from the inputs, so `g' ≤ gl` holds without a discarding guard.
-/
def refundSpec (gl : UInt256) (d : ℕ) (r : UInt256) : Bool :=
  let g' := UInt256.ofNat (gl.toNat - d)
  let gs := refundedGas gl g' r
  let used := gl.toNat - g'.toNat
  g'.toNat ≤ gs.toNat && gs.toNat ≤ gl.toNat && gs.toNat - g'.toNat ≤ used / 5 &&
    gs.toNat - g'.toNat ≤ r.toNat && 4 * used ≤ 5 * (gl - gs).toNat

/-- CALL lemmas on a cold/warm callee with arbitrary gas, value and request. -/
def callSpec (gas req val : UInt256) (warm : Bool) : Bool :=
  let t : AccountAddress := default
  let A : Substate := if warm then { (default : Substate) with
      accessedAccounts := (default : Substate).accessedAccounts.insert t } else default
  let σ : AccountMap .EVM := default
  let μ : MachineState := { (default : MachineState) with gasAvailable := gas }
  let e := Cextra t t val σ A
  let cap := Cgascap t t val req σ μ A
  let callgas := Ccallgas t t val req σ μ A
  cap ≤ req.toNat &&
  (decide (e ≤ gas.toNat) → cap ≤ L (gas.toNat - e)) &&
  callgas == cap + (if val = ⟨0⟩ then 0 else Gcallstipend) &&
  (decide (Ccall t t val req σ μ A ≤ gas.toNat) →
      (gas.toNat - e) / 64 ≤ gas.toNat - Ccall t t val req σ μ A)

/-- S4: post-memory-charge cap never exceeds the instruction-start cap (when not OOG). -/
def s4Spec (gas req : UInt256) (m : ℕ) : Bool :=
  let t : AccountAddress := default
  let μ : MachineState := { (default : MachineState) with gasAvailable := gas }
  let e := Cextra t t ⟨0⟩ default default
  decide (m ≤ gas.toNat) → decide (e ≤ gas.toNat - m) →
    Cgascap t t ⟨0⟩ req default (afterMemoryCharge μ m) default ≤ Cgascap t t ⟨0⟩ req default μ default

/-- Fee classification vs `C'` on random opcodes and random stacks. -/
def classificationSpec (o : AnyOp) (a b c : UInt256) : Bool :=
  let w := o.op
  let s := withOwnerAccount (withStack [a, b, c, a, b, c, a])
  match (feeGroup w).staticCost? with
  | some k => C' s w == k
  | none => feeGroup w == .invalid || decide (0 < C' s w)

#eval expectHolds "chargeGas: OOG iff gas < cost, no wrap-around"
  (∀ g : UInt256, ∀ c : ℕ, chargeSpec g c = true)
#eval expectHolds "chargeGas: OOG iff gas < cost (cost near the gas value)"
  (∀ g : UInt256, ∀ d : ℕ, chargeSpec g (g.toNat + d - 500) = true)
#eval expectHolds "two-phase charge: OOG iff gas < C_mem + C'"
  (∀ g : UInt256, ∀ c₁ c₂ : ℕ, twoPhaseSpec g c₁ c₂ = true)
#eval expectHolds "Cₘ monotone"
  (∀ a : UInt256, ∀ d : ℕ, Cₘ a ≤ Cₘ (bump a d))
#eval expectHolds "L bounds"
  (∀ n : ℕ, L n ≤ n ∧ 63 * n ≤ 64 * L n ∧ L n + n / 64 = n)
#eval expectHolds "EIP-3529 refund cap"
  (∀ gl : UInt256, ∀ d : ℕ, ∀ r : UInt256, refundSpec gl d r = true)
#eval expectHolds "CALL cap / stipend / 1/64 retention"
  (∀ gas req val : UInt256, ∀ warm : Bool, callSpec gas req val warm = true)
#eval expectHolds "S4: post-memory cap ≤ instruction-start cap"
  (∀ gas req : UInt256, ∀ m : ℕ, s4Spec gas req m = true)
#eval expectHolds "fee classification agrees with C' (static) / C' > 0 (dynamic)"
  (∀ o : AnyOp, ∀ a b c : UInt256, classificationSpec o a b c = true)

/-! ## 3. Mutation tests: Plausible must find counterexamples -/

#eval expectRefuted "conjecture: Cgascap monotone in available gas"
  (∀ gas₁ gas₂ : UInt256, gas₁.toNat ≤ gas₂.toNat →
    Cgascap default default ⟨0⟩ (u (2 ^ 200)) default
        { (default : MachineState) with gasAvailable := gas₁ } default ≤
    Cgascap default default ⟨0⟩ (u (2 ^ 200)) default
        { (default : MachineState) with gasAvailable := gas₂ } default)
#eval expectRefuted "conjecture: L n < n for n > 0"
  (∀ n : ℕ, 0 < n → L n < n)
#eval expectRefuted "mutant: unguarded raw subtraction never increases gas"
  (∀ g : UInt256, ∀ c : ℕ, (g - UInt256.ofNat c).toNat ≤ g.toNat)
#eval expectRefuted "mutant: refund without the 1/5 cap stays within the cap"
  (∀ gl g' r : UInt256, g'.toNat ≤ gl.toNat → (g' + r).toNat - g'.toNat ≤ (gl.toNat - g'.toNat) / 5)
#eval expectRefuted "conjecture: every opcode costs gas (STOP/RETURN/REVERT are free)"
  (∀ o : AnyOp, ∀ a : UInt256, feeGroup o.op ≠ .invalid → 0 < C' (withOwnerAccount (withStack [a, a, a, a, a, a, a])) o.op)
#eval expectRefuted "conjecture: post-memory cap = instruction-start cap"
  (∀ gas : UInt256, ∀ m : ℕ, m ≤ gas.toNat →
    Cgascap default default ⟨0⟩ (u (2 ^ 200)) default
        (afterMemoryCharge { (default : MachineState) with gasAvailable := gas } m) default =
      Cgascap default default ⟨0⟩ (u (2 ^ 200)) default { (default : MachineState) with gasAvailable := gas } default)
#eval expectRefuted "mutant: C_mem without the quadratic term is Cₘ"
  (∀ a : UInt256, Gmemory * a.toNat = Cₘ a)

/-! ## Proof-backed counterexamples referenced by the mutation tests -/
example := not_Cgascap_mono_in_gas
example := not_forall_L_lt
example := not_forall_unguarded_sub_le

end GasTests

end EVM

end EvmYul
