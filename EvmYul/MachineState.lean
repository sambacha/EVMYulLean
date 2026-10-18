module

public import Batteries

public import EvmYul.Maps.ByteMap
public import EvmYul.UInt256
public import Batteries.Data.HashMap

/-!
# Machine state shared by the EVM and Yul

`MachineState` (`μ` of the Yellow Paper, without stack and program counter): the gas available,
the active word count, the memory and the return data.
-/

public section

namespace EvmYul

open Batteries

@[expose] instance : DecidableEq ByteArray
  | a, b => match decEq a.data b.data with
    | isTrue  h₁ => isTrue <| congrArg ByteArray.mk h₁
    | isFalse h₂ => isFalse <| λ h ↦ by cases h; exact (h₂ rfl)

@[expose] section

/--
The partial shared `MachineState` `μ`. Section 9.4.1.
- `gasAvailable` `g`
- `memory`       `m`
- `activeWords`  `i` - # active words.
- `returnData`   `o` - Data from the previous call from the current environment.
-/
structure MachineState where
  gasAvailable        : UInt256
  activeWords         : UInt256
  memory              : ByteArray
  returnData          : ByteArray
  H_return            : ByteArray
  deriving Inhabited

end

-- inductive WordSize := | Standard | Single

-- def WordSize.toNat (this : WordSize) : ℕ :=
--   match this with
--     | WordSize.Standard => 32
--     | WordSize.Single   => 1

-- instance : Coe WordSize Nat := ⟨WordSize.toNat⟩

end EvmYul
