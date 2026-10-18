module

public import EvmYul.Testing.EvmFixtures
public meta import EvmYul.Testing.EvmFixtures
public import EvmYul.EVM.Gas.FeeSchedule
public meta import EvmYul.EVM.Gas.FeeSchedule

@[expose] public meta section

/-!
# Tests for the fee schedule record (`Gas/FeeSchedule.lean`)

Built by `lake build EvmYulGasTests`; every check runs during elaboration, so any failure fails
the build. Fixtures, generators and the seeded `expectHolds` / `expectRefuted` harness:
`EvmYul/Testing/EvmFixtures.lean`.

The Cancun schedule is the hard fork's schedule; on every decoded opcode with a static fee group
`C'` equals the schedule's price; and the record is not trivial (changing a field changes it).
-/

namespace EvmYul.EVM.Gas.FeeScheduleTests

open GasConstants GasMeter Plausible Plausible.Decorations
open EvmYul.Testing.EvmFixtures

example : Hardfork.cancun.schedule = FeeSchedule.cancun := rfl
example := FeeSchedule.cancun_values
#guard Hardfork.all.length == 1
-- On every decoded opcode with a static fee group, `C'` equals the schedule's price.
#guard decodedOps.all fun w =>
  match Hardfork.cancun.schedule.staticCost (feeGroup w) with
  | some c => C' (withOwnerAccount (withStack (List.replicate 8 (u 0)))) w == c
  | none => true
-- The schedule is a real record: changing a field changes it (decidable equality is not trivial).
#guard FeeSchedule.cancun != { FeeSchedule.cancun with Gverylow := 4 }

end EvmYul.EVM.Gas.FeeScheduleTests
