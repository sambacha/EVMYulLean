module

public import EvmYul.State.Basic
public import EvmYul.MachineState

/-!
# State shared by the EVM and Yul

`SharedState τ`: the world state together with the machine state, the part of the state that both
interpreters update in the same way.
-/

public section

namespace EvmYul

@[expose] section

structure SharedState (τ : OperationType) extends EvmYul.State τ, EvmYul.MachineState
  deriving Inhabited

end

end EvmYul
