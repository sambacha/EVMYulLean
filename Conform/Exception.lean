module

public import EvmYul

/-!
# Conformance-runner exceptions

The errors of the conformance runner itself, as opposed to EVM exceptions: a test whose JSON is
malformed (`CannotParse`), and a test file whose structure is not the expected one
(`InvalidTestStructure`).
-/
public section

namespace EvmYul

namespace Conform

/--
`Exception` represents the class of conformance testing errors.
- `CannotParse`          - The `Json` of a test is malformed. `why` is the reason. 
- `InvalidTestStructure` - The structure of tests has been violated. `why` is the reason. 
-/
inductive Exception where
  | CannotParse (why : String)
  | InvalidTestStructure (why : String)
  deriving Repr

end Conform

end EvmYul
