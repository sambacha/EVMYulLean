module

public import EvmYul.MachineState
public import EvmYul.Yul.VarStore

/-!
# Yul machine state

The machine state of the Yul interpreter: the machine state shared with the EVM plus the variable
store.
-/
public section

namespace EvmYul

namespace Yul

@[expose] section

/--
The partial Yul `MachineState` `μ`.
-/
structure MachineState extends EvmYul.MachineState where
  varStore : VarStore
deriving Inhabited

end

end Yul

end EvmYul
