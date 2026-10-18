module

public import EvmYul.UInt256

public section

/-!
# Chain parameters

The chain id and the name of the fork schedule the model targets.
-/

namespace EvmYul

@[expose] def chainId : ℕ := 1

end EvmYul

def TargetSchedule := "Cancun"
