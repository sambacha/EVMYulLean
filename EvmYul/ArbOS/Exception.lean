/-!
# ArbOS execution exceptions

RFC §26: an unsupported ArbOS/Robinhood behaviour must fail explicitly.  Returning a
default value (typically `0`) for a system call that the model does not implement would
let a proof succeed against behaviour that never exists on chain, which is the most
dangerous class of error for this project.
-/

namespace EvmYul

namespace ArbOS

/-- Failures that are specific to the ArbOS layer, i.e. not EVM execution failures. -/
inductive ExecutionException where
  /-- The system contract exists, but this selector is not modelled. -/
  | unsupportedMethod (address : Nat) (selector : UInt32)
  /-- Calldata is too short or otherwise not decodable for the selected method. -/
  | invalidCalldata
  /-- The address is a known ArbOS system contract that this model does not implement. -/
  | unavailableFeature (address : Nat) (name : String)
  /-- A cross-chain message is malformed (e.g. an inconsistent origin). -/
  | invalidMessage (reason : String)
  /-- An EIP-7702 authorization failed validation. -/
  | invalidAuthorization (reason : String)
  /-- The execution profile requires ArbOS state that is not present. -/
  | missingArbOSState
  deriving DecidableEq, Repr, BEq, Inhabited

instance : ToString ExecutionException where
  toString
    | .unsupportedMethod a s => s!"ArbOS: unsupported method {s} at address {a}"
    | .invalidCalldata => "ArbOS: invalid calldata"
    | .unavailableFeature a n => s!"ArbOS: unavailable feature {n} at address {a}"
    | .invalidMessage r => s!"ArbOS: invalid message ({r})"
    | .invalidAuthorization r => s!"ArbOS: invalid authorization ({r})"
    | .missingArbOSState => "ArbOS: missing ArbOS state"

end ArbOS

end EvmYul
