module

public import EvmYul.Testing.EvmFixtures
public meta import EvmYul.Testing.EvmFixtures
public import EvmYul.EVM.Gas.WarmAccess
public meta import EvmYul.EVM.Gas.WarmAccess

@[expose] public meta section

/-!
# Tests for warm / cold access pricing (`Gas/WarmAccess.lean`)

Built by `lake build EvmYulGasTests`; every check runs during elaboration, so any failure fails
the build. Fixtures, generators and the seeded `expectHolds` / `expectRefuted` harness:
`EvmYul/Testing/EvmFixtures.lean`.

1. **Unit tests**: `SLOAD` of a warm slot costs `G_warmaccess`, of a cold slot `G_coldsload`;
   account access `G_warmaccess` / `G_coldaccountaccess` (EIP-2929; the constants themselves are
   pinned against the EIP in `CostsTests`).
2. **Property test**: warming slot `k` makes `SLOAD k` warm and leaves every other slot cold.
3. **Mutation test**: "warming a slot has no effect on `SLOAD`" must be refuted.
-/

namespace EvmYul.EVM.Gas.WarmAccessTests

open GasConstants GasMeter Plausible Plausible.Decorations
open EvmYul.Testing.EvmFixtures

/-! ## Unit tests -/

#guard Csload [u 5] (Substate.warmSlot default ((default : ExecutionEnv .EVM).codeOwner, u 5))
  default == Gwarmaccess
#guard Csload [u 5] default (default : ExecutionEnv .EVM) == Gcoldsload
#guard Caccess default (Substate.warmAccount default default) == Gwarmaccess
#guard Caccess (AccountAddress.ofNat 7) (Substate.warmAccount default default) == Gcoldaccountaccess


/-! ## Property tests -/

/-- Warming slot `k` makes `SLOAD k` warm and leaves every other slot cold. -/
def warmSpec (k k' : UInt256) : Bool :=
  let A := Substate.warmSlot default ((default : ExecutionEnv .EVM).codeOwner, k)
  Csload [k] A default == Gwarmaccess && (k == k' || Csload [k'] A default == Gcoldsload)

#eval expectHolds "warm slot ⇒ SLOAD costs G_warmaccess; other slots unaffected"
  (∀ k k' : UInt256, warmSpec k k' = true)


/-! ## Mutation tests -/

#eval expectRefuted "mutant: warming a slot has no effect on SLOAD"
  (∀ k : UInt256, Csload [k] (Substate.warmSlot default ((default : ExecutionEnv .EVM).codeOwner, k))
      default = Gcoldsload)

end EvmYul.EVM.Gas.WarmAccessTests
