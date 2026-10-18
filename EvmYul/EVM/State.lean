module

public import EvmYul.Stack
public import EvmYul.State.Basic
public import EvmYul.SharedState

/-!
# EVM machine state

`EVM.State`: the shared state plus the program counter, the stack and the number of steps executed,
and `ExecutionResult`, the success-or-revert result of an EVM execution.
-/

public section

namespace EvmYul

namespace EVM

@[expose] section

/--
The EVM `State` (extends EvmYul.SharedState).
- `pc`         `pc`
- `stack`      `s`
- `execLength` - Length of execution.
-/
structure State extends EvmYul.SharedState .EVM where
  pc    : UInt256
  stack : Stack UInt256
  execLength : ℕ
  deriving Inhabited

end

inductive ExecutionResult (S : Type) where
  | success (state : S) (o : ByteArray)
  | revert (g : UInt256) (o : ByteArray)

end EVM

end EvmYul
