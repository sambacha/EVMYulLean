module

public import EvmYul.Testing.EvmFixtures
public meta import EvmYul.Testing.EvmFixtures
public import EvmYul.EVM.Gas.CallReadings
public meta import EvmYul.EVM.Gas.CallReadings

@[expose] public meta section

/-!
# Tests for the CALL-cap readings (`Gas/CallReadings.lean`)

Built by `lake build EvmYulGasTests`; every check runs during elaboration, so any failure fails
the build. Fixtures, generators and the seeded `expectHolds` / `expectRefuted` harness:
`EvmYul/Testing/EvmFixtures.lean`.

1. **Unit tests**: the CE-4 instance, the D-1 witness (model = EELS, the YP-literal reading
   halts), agreement without memory expansion, and the pure model against the real `C'`.
2. **Exhaustive margin model check** over a small band of `(g, m, e, q)`, including the CE-4 shape
   `g − m < e ≤ g`.
3. **Property tests**: model = EELS; YP-literal success implies model success; the CE-4 band halts.
4. **Mutation tests**: the refuted handoff claims (D-1 default, CE-4 as stated) and EELS without the
   memory cost in the 63/64 base must be refuted.
-/

namespace EvmYul.EVM.Gas.CallReadingsTests

open GasConstants GasMeter Plausible Plausible.Decorations
open EvmYul.Testing.EvmFixtures

open CallReadings

/-! ## Unit tests -/

-- CE-4 instance: both readings (and EELS) halt; nothing is forwarded.
#guard modelCallCharge 2650 100 2600 10000 == none
#guard ypCallCharge 2650 100 2600 10000 == none
#guard eelsCallCharge 2650 100 2600 10000 == none
example := ce4_instance
-- D-1 witness: model = EELS forward 5670; the YP-literal reading halts.
#guard modelCallCharge 9000 640 2600 1000000 == some 5670
#guard eelsCallCharge 9000 640 2600 1000000 == some 5670
#guard ypCallCharge 9000 640 2600 1000000 == none
example := yp_ne_model_witness
-- Without memory expansion all readings agree (cold CALL, 100000 gas, request 10^6).
#guard modelCallCharge 100000 0 2600 1000000 == some 95879
#guard ypCallCharge 100000 0 2600 1000000 == some 95879
-- The pure model agrees with the real `C'`/`Cgascap` for the CALL unit test of `GasTests`:
-- C_CALL = 98479 = 95879 + 2600.
#guard C' (withGas (withStack [u 1000000, u 1, u 0, u 0, u 0, u 0, u 0]) 100000) .CALL ==
  (modelCallCharge 100000 0 2600 1000000).getD 0 + 2600


/-! ## Exhaustive margin model check over a small band -/

/-- All `(g, m, e, q)` in the checked band. -/
def band : List (ℕ × ℕ × ℕ × ℕ) := Id.run do
  let mut out := []
  for g in [0:121] do
    for m in [0:13] do
      for e in [0:21] do
        for q in [0, 7, 1000000] do
          out := (g, m, e, q) :: out
  return out

/-- The universally quantified theorems, checked pointwise on the band. -/
def bandOk : (ℕ × ℕ × ℕ × ℕ) → Bool
  | (g, m, e, q) =>
    modelCallCharge g m e q == eelsCallCharge g m e q &&
    (match ypCallCharge g m e q, modelCallCharge g m e q with
     | some f, some f' => f' ≤ f
     | some _, none => false
     | _, _ => true) &&
    (!(decide (g < m + e)) || (modelCallCharge g m e q == none && ypCallCharge g m e q == none))

#guard band.length == 121 * 13 * 21 * 3
#guard band.all bandOk
-- The checker sees the CE-4 shape (`g − m < e ≤ g`, `m > 0`) ...
#guard band.any fun (g, m, e, _) => 0 < m && g < m + e && e ≤ g
-- ... and sees genuine divergences between the YP-literal reading and the model.
#guard (band.filter fun (g, m, e, q) => ypCallCharge g m e q != modelCallCharge g m e q).length > 0


/-! ## Property tests -/

#eval expectHolds "D-1: model = EELS (small values)"
  (∀ g m e q : ℕ, modelCallCharge g m e q = eelsCallCharge g m e q)
#eval expectHolds "D-1: model = EELS (256-bit values)"
  (∀ g m e q : UInt256, modelCallCharge g.toNat m.toNat e.toNat q.toNat =
    eelsCallCharge g.toNat m.toNat e.toNat q.toNat)
/-- `ypCallCharge_some_imp_model` as a checker. -/
def ypImpModelSpec (g m e q : ℕ) : Bool :=
  match ypCallCharge g m e q, modelCallCharge g m e q with
  | some f, some f' => decide (f' ≤ f)
  | some _, none => false
  | _, _ => true

#eval expectHolds "YP-literal success ⇒ model success, forwarding no more"
  (∀ g m e q : ℕ, ypImpModelSpec g m e q = true)
/-- A point of the CE-4 band `g < m + e`, built from unconstrained inputs (no discarding). -/
def ce4BandSpec (m e d q : ℕ) : Bool :=
  let g := m + (e + 1) - 1 - d
  modelCallCharge g m (e + 1) q == none && ypCallCharge g m (e + 1) q == none

#eval expectHolds "CE-4 band: both readings halt"
  (∀ m e d q : ℕ, ce4BandSpec m e d q = true)

/-! ## Mutation tests -/

#eval expectRefuted "handoff D-1 default: YP-literal reading = current model (behaviour-preserving switch)"
  (∀ g m e q : ℕ, ypCallCharge g m e q = modelCallCharge g m e q)
#eval expectRefuted "handoff CE-4 as stated: in the band the model forwards the full request"
  (∀ g m e q : ℕ, g < m + e → modelCallCharge g m e q = some q)
#eval expectRefuted "mutant: EELS without the memory cost in the 63/64 base"
  (∀ g m e q : ℕ, modelCallCharge g m e q =
    (let cap := if g < e then q else min q (L (g - e)); if g < cap + e + m then none else some cap))

/-! ## Proof-backed counterpart of the refuted claim -/
example := not_forall_yp_eq_model

end EvmYul.EVM.Gas.CallReadingsTests
