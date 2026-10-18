module

public import EvmYul.UInt256

public section

/-!
# `Option` helpers

Case analysis with a default (`Option.option`) and conversion to `Except` with a given error.
-/

@[expose] def Option.option {α β : Type} (dflt : β) (f : α -> β) : Option α → β
  | .none => dflt
  | .some x => f x

def Option.toExceptWith {α β : Type} (dflt : β) (x : Option α) : Except β α :=
  x.option (.error dflt) Except.ok
