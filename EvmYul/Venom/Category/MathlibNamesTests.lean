module

public import Mathlib.CategoryTheory.PathCategory.Basic
public import Mathlib.CategoryTheory.Category.KleisliCat
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Retract
public import Mathlib.CategoryTheory.Category.RelCat
public import Mathlib.CategoryTheory.Adjunction.Reflective
public import Mathlib.CategoryTheory.Idempotents.Karoubi
public import Mathlib.CategoryTheory.Grothendieck
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Category.Quiv
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.CategoryTheory.Quotient
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

@[expose] public meta section

/-!
# Audit of the Mathlib names used by the categorical specification (task T0)

Every row of the identifier map of the handoff (section 5.3) is resolved here against the
pinned Mathlib (`lake-manifest.json`, the revision paired with Lean 4.28.0); the build fails if a
name disappears or moves. Findings (drifts from the handoff's from-memory table):

* `Paths`, `Paths.of`, `Paths.lift`, `Paths.lift_unique` live in
  `Mathlib.CategoryTheory.PathCategory.Basic`, as expected.
* `Equivalence` and `Quotient` are ambiguous with core names: use `CategoryTheory.Equivalence`
  and `CategoryTheory.Quotient`.
* The Karoubi envelope is `CategoryTheory.Idempotents.Karoubi`.
* The full subcategory is `ObjectProperty.FullSubcategory` (the older `FullSubcategory` is gone).
* `Functor.IsEquivalence` is a `Prop`-valued class built from `Full`, `Faithful` and `EssSurj`
  instances; there is no constructor named `of_fullyFaithfully_essSurj`.
* `Grothendieck` needs its own import, `Mathlib.CategoryTheory.Grothendieck`.
* Not in Mathlib (defined in this folder or left out): dominators (`Flow.lean`), lax natural
  transformations into a poset-enriched Kleisli category (`Simulation.lean`), graded monads,
  Elgot iteration, Lawvere theories, premonoidal categories.

The single rule applied is `TESTING.md`'s regression rule for interfaces this folder relies on.
-/

namespace EvmYul.Venom.Category.MathlibNamesTests

open CategoryTheory

#check @Quiver.Path
#check @Prefunctor
#check @Paths
#check @Paths.of
#check @Paths.lift
#check @Paths.lift_unique
#check @CategoryTheory.Equivalence
#check @Functor.FullyFaithful
#check @Functor.Full
#check @Functor.Faithful
#check @Functor.EssSurj
#check @Functor.IsEquivalence
#check @Adjunction
#check @Reflective
#check @KleisliCat
#check @Preorder.smallCategory
#check @RelCat
#check @Retract
#check @Idempotents.Karoubi
#check @Discrete
#check @Over
#check @Under
#check @Comma
#check @Grothendieck
#check @yoneda
#check @ObjectProperty.FullSubcategory
#check @Quiv
#check @Cat
#check @Skeleton
#check @CategoryTheory.Quotient
#check @NatTrans
#check @Functor.id

end EvmYul.Venom.Category.MathlibNamesTests
