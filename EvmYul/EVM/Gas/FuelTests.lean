module

public import EvmYul.Testing.EvmFixtures
public meta import EvmYul.Testing.EvmFixtures
public import EvmYul.EVM.Gas.Fuel
public meta import EvmYul.EVM.Gas.Fuel

@[expose] public meta section

/-!
# Tests for the interpreter fuel (`Gas/Fuel.lean`)

Built by `lake build EvmYulGasTests`; every check runs during elaboration, so any failure fails
the build. Fixtures, generators and the seeded `expectHolds` / `expectRefuted` harness:
`EvmYul/Testing/EvmFixtures.lean`.

1. **Unit tests**: balance-as-fuel is zero on an empty balance (CE-9); the transaction fuel exceeds
   the gas limit and is at least the balance (the requirement, not the value of `fuelOverhead`);
   `chargeAll` on fixed cost lists.
2. **Property tests**: `chargeAll` succeeds iff the costs fit; positive costs bound the number of
   steps by the gas (PO-10); the transaction fuel dominates the old fuel and the gas limit.
3. **Mutation tests**: PO-10 without the cost-at-least-one hypothesis, and "balance-as-fuel is
   always positive", must be refuted.
-/

namespace EvmYul.EVM.Gas.FuelTests

open GasConstants GasMeter Plausible Plausible.Decorations
open EvmYul.Testing.EvmFixtures

/-! ## Unit tests -/

#guard balanceFuel ⟨0⟩ == 0
-- The requirement (CE-9), not the chosen overhead: a zero-balance sender still gets more fuel than
-- the transaction's gas limit (`legacyTx` has gas limit 10^6), and a sender never gets less fuel
-- than the old balance-as-fuel choice.
#guard transactionFuel (legacyTx (some default) []) ⟨0⟩ > 1000000
#guard transactionFuel (legacyTx (some default) []) (u (10 ^ 30)) ≥ 10 ^ 30
example := Υ_zero_fuel
#guard okNat? (chargeAll (u 10) [1, 2, 3]) == some (10 - [1, 2, 3].sum)
#guard isOOG (chargeAll (u 5) [1, 2, 3])
#guard okNat? (chargeAll (u 0) [0, 0, 0]) == some 0


/-! ## Property tests -/

/-- `chargeAll_ok_iff` as a checker. -/
def chargeAllSpec (g : ℕ) (cs : List ℕ) : Bool :=
  match chargeAll (u g) cs with
  | .ok g' => decide (cs.sum ≤ g) && g'.toNat == g - cs.sum
  | .error _ => decide (g < cs.sum)

/-- `chargeAll_length_le` as a checker (costs `c + 1 ≥ 1`). -/
def fuelBoundSpec (g : ℕ) (cs : List ℕ) : Bool :=
  match chargeAll (u g) (cs.map (· + 1)) with
  | .ok _ => decide (cs.length ≤ g)
  | .error _ => true

/-- The same bound with zero-cost steps allowed (false: mutation test). -/
def fuelBoundNoMinSpec (g : ℕ) (cs : List ℕ) : Bool :=
  match chargeAll (u g) cs with
  | .ok _ => decide (cs.length ≤ g)
  | .error _ => true

#eval expectHolds "chargeAll: succeeds iff Σ ≤ g, leaves g − Σ"
  (∀ g : ℕ, ∀ cs : List ℕ, chargeAllSpec g cs = true)
#eval expectHolds "PO-10: positive costs ⇒ #steps ≤ gas"
  (∀ g : ℕ, ∀ cs : List ℕ, fuelBoundSpec g cs = true)
/-- A legacy transaction with the given gas limit. -/
def txWithGasLimit (gl : ℕ) : Transaction :=
  .legacy { nonce := ⟨0⟩, gasLimit := u gl, recipient := none, value := ⟨0⟩, r := .empty,
            s := .empty, data := .empty, gasPrice := ⟨0⟩, w := ⟨0⟩ }

/-- `balanceFuel_le_transactionFuel` and `gasLimit_lt_transactionFuel` as a checker. -/
def fuelSpec (b : UInt256) (gl : ℕ) : Bool :=
  decide (balanceFuel b ≤ transactionFuel (txWithGasLimit gl) b) &&
    decide ((u gl).toNat < transactionFuel (txWithGasLimit gl) b)

#eval expectHolds "transactionFuel ≥ old fuel and > gasLimit"
  (∀ b : UInt256, ∀ gl : ℕ, fuelSpec b gl = true)

/-! ## Mutation tests -/

#eval expectRefuted "PO-10 without the ≥1 cost hypothesis (zero-cost steps)"
  (∀ g n : ℕ, fuelBoundNoMinSpec g (List.replicate n 0) = true)
#eval expectRefuted "CE-9: balance-as-fuel is always positive"
  (∀ b : UInt256, 0 < balanceFuel b)

/-! ## Proof-backed counterparts of the refuted claims -/
example := not_chargeAll_length_le_without_min_cost
example := balanceFuel_zero_fails

end EvmYul.EVM.Gas.FuelTests
