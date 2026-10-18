module

public import EvmYul.Operations

public import EvmYul.Wheels

/-!
# Pretty printers

Human-readable renderings of operations and finite maps, for debugging and reports. The printer of a
type is always `<Datatype>.pretty (self : Datatype) : String`, up to parametricity.
-/

public section

namespace EvmYul

/--
Strip the existing `repr` a'la:
- EvmYul.Operation.Push (EvmYul.Operation.POp.PUSH1) → PUSH1

This breaks the moment that `Repr` changes its behaviour; it is fine for the time being.
-/
def Operation.pretty {τ} (self : Operation τ) : String :=
  let reprStr := ToString.toString <| repr self
  let lastComponent := reprStr.splitOn "." |>.getLast!
  (lastComponent.take lastComponent.length.pred).toString

/--
`Finmap`s are not very computation-friendly and so the API is ever so slightly meh;
do feel encouraged to sorry out the order properties and just point it to an instance of `LE`.

TODO(not critical) - Unify all the maps used throught the formalisation one day.
-/
def Finmap.pretty {α β : Type} [ToString α] [ToString β]
                               [LE ((_ : α) × β)]
                               [IsTrans ((_ : α) × β) fun x x_1 => x ≤ x_1]
                               [Std.Antisymm (α := (_ : α) × β) fun x x_1 => x ≤ x_1]
                               [Std.Total (α := (_ : α) × β) fun x x_1 => x ≤ x_1]
                               [DecidableRel fun (x : ((_ : α) × β)) x_1 => x ≤ x_1]
                  (self : Finmap (λ _ : α ↦ β)) : String := Id.run do
  let mut result : String := ""
  for ⟨k, v⟩ in computeToList! self.entries do
    result := result.append s!"{k} → {v}\n"
  return result

end EvmYul
