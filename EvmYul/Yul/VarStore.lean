module

public import Mathlib.Data.Finmap

public import EvmYul.Wheels

/-!
# Yul variable store

`VarStore`, the finite map from identifiers to literals.
-/

public section

namespace EvmYul

namespace Yul

abbrev VarStore := Finmap (λ _ : Identifier ↦ Literal)

end Yul

end EvmYul
