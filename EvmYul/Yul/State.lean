module

public import Mathlib.Data.Finmap

public import EvmYul.Wheels
public import EvmYul.Yul.VarStore
public import EvmYul.SharedState

/-!
# Yul state

`Yul.State`: an ok state (shared state and variable store), the out-of-fuel state, or a checkpoint
reached by `continue`, `break` or `leave`.
-/

public section

namespace EvmYul

namespace Yul

/--
A jump in control flow containing a checkpoint of the state at jump-time.
- `Continue`: yul `continue` was encountered
- `Break`   : yul `break` was encountered
- `Leave`   : evm `return` was encountered
-/
inductive Jump where
  | Continue : EvmYul.SharedState .Yul → VarStore → Jump
  | Break    : EvmYul.SharedState .Yul → VarStore → Jump
  | Leave    : EvmYul.SharedState .Yul → VarStore → Jump

/--
The Yul `State`.
- `Ok state varstore` : The underlying `EvmYul.State` `state` along with `varstore`.
- `OutOfFuel`         : No state.
- `Checkpoint`        : Restore a previous state due to control flow.

The definition is ever so slightly off due to historical reasons.
-/
inductive State where
  | Ok         : EvmYul.SharedState .Yul → VarStore → State
  | OutOfFuel  : State
  | Checkpoint : Jump → State

@[expose] instance : Inhabited State where
  default := .Ok default default

namespace State

@[expose] def sharedState : State → EvmYul.SharedState .Yul
  | Ok sharedState _ => sharedState
  | _ => default

end State

end Yul

end EvmYul
