module

public import EvmYul.Yul.Interpreter
public import EvmYul.Yul.StateOps

/-!
# Tests of the Yul interpreter

Checks of `Yul.Interpreter` on fixed programs (a `break` stops the rest of its block).
-/

@[expose] public section

namespace EvmYul
namespace Yul

open Ast

/--
Yul shape:

```yul
{
  break
  let x := 1
}
```
-/
def breakThenLetBlock : Stmt :=
  .Block [
    .Break,
    .Let ["x"] (some (.Lit (UInt256.ofNat 1)))
  ]

theorem exec_block_stops_after_break
    (sharedState : EvmYul.SharedState .Yul) (store : VarStore) :
    exec 3 breakThenLetBlock none (.Ok sharedState store) =
        .ok (.Checkpoint (.Break sharedState store)) := by
  simp [breakThenLetBlock, exec, State.setBreak]

end Yul
end EvmYul
