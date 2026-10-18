module

public import EvmYul.Yul.State

/-!
# Yul exceptions

The ways a Yul execution stops abnormally: invalid arguments or instructions, out of fuel, a
static-mode violation, a missing contract or function, `revert`, and the halt that carries the
final state and value (`YulHalt`).
-/

public section

namespace EvmYul

namespace Yul

inductive Exception where
  | InvalidArguments                              : Exception
  | NotEncodableRLP                               : Exception
  | InvalidInstruction                            : Exception
  | OutOfFuel                                     : Exception
  | StaticModeViolation                           : Exception
  | MissingContract (s : String)                  : Exception
  | MissingContractFunction (s : String)          : Exception
  | InvalidExpression                             : Exception
  | YulEXTCODESIZENotImplemented                  : Exception
  | Revert                                        : Exception
  | YulHalt (state : Yul.State) (value : UInt256) : Exception
  -- | StopInvoked        : Exception

@[expose] instance : Repr Exception where
  reprPrec s _ :=
    match s with
      | .InvalidArguments => "InvalidArguments"
      | .NotEncodableRLP => "NotEncodableRLP"
      | .InvalidInstruction => "InvalidInstruction"
      | .OutOfFuel => "OutOfFuel"
      | .StaticModeViolation => "StaticModeViolation"
      | .MissingContract s => "MissingContract: " ++ s
      | .MissingContractFunction f => "MissingContractFunction: " ++ f
      | .InvalidExpression => "InvalidExpression"
      | .YulEXTCODESIZENotImplemented => "YulEXTCODESIZENotImplemented"
      | .Revert => "Revert"
      | .YulHalt _ _ => "YulHalt: (holds a state and a value)"


end Yul

end EvmYul
