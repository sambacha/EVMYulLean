module

public import Mathlib.CategoryTheory.Retract
public import Mathlib.CategoryTheory.Category.KleisliCat
public import EvmYul.Venom.Text

public section

/-!
# Printing and parsing as a retract in the category of partial maps (D2.1, P2.1)

Partial maps are the Kleisli category of `Option` (Mathlib's `KleisliCat Option`). A printer
`pr : AST → Text` and a parser `pa : Text → Option AST` with `pa (pr a) = some a` form a
**retract** `print ≫ parse = 𝟙` there (`printParseRetract`, Mathlib's `Retract`).

* **P2 (AST fidelity)** is the retract equation (`printParse_retract`).
* **P3 (normal form).** `N = parse ≫ print` is idempotent for every retract (`normalizer_idem`),
  and two retracts of the same text object that induce the same idempotent are canonically
  isomorphic (`retractIsoOfSameIdempotent`): a differential test that compares the two
  normalizers checks that two implementations have isomorphic ASTs.
* **Instance (proved).** The opcode table of `Text.lean` is a retract of the strings
  (`opRetract`, from `opOfName?_opName`). The round trip of whole functions is not proved; it is
  tested in `RetractTests.lean` (and `TextTests.lean`) on random functions and on recorded Vyper
  output, where `N` is also checked to be idempotent on text.
-/

namespace EvmYul.Venom.Category

open CategoryTheory

/-- The object of partial maps for a type. -/
@[expose] abbrev PartialObj (X : Type) : KleisliCat Option := KleisliCat.mk Option X

/-- **D2.1.** A printer and a parser that reads back every printed AST form a retract in the
category of partial maps. -/
@[expose] def printParseRetract {AST Text : Type} (pr : AST → Text) (pa : Text → Option AST)
    (h : ∀ a, pa (pr a) = some a) : Retract (PartialObj AST) (PartialObj Text) where
  i := fun a => some (pr a)
  r := pa
  retract := by
    funext a
    show (some (pr a) >>= pa) = some a
    simp [h]

/-- **P2.** The retract equation, pointwise: printing then parsing gives back the AST. -/
theorem printParse_retract {AST Text : Type} (pr : AST → Text) (pa : Text → Option AST)
    (h : ∀ a, pa (pr a) = some a) (a : AST) :
    ((printParseRetract pr pa h).i ≫ (printParseRetract pr pa h).r) a = some a := by
  rw [(printParseRetract pr pa h).retract]
  rfl

/-- The normalizer `N = parse ≫ print` of a retract. -/
@[expose] def normalizer {C : Type*} [Category C] {X Y : C} (r : Retract X Y) : Y ⟶ Y := r.r ≫ r.i

/-- **P3.** The normalizer is idempotent. -/
theorem normalizer_idem {C : Type*} [Category C] {X Y : C} (r : Retract X Y) :
    normalizer r ≫ normalizer r = normalizer r := by
  rw [normalizer, Category.assoc, ← Category.assoc r.i, r.retract, Category.id_comp]

/-- **P3.** Two retracts of the same object with the same normalizer are canonically isomorphic. -/
@[expose] def retractIsoOfSameIdempotent {C : Type*} [Category C] {X₁ X₂ Y : C}
    (r₁ : Retract X₁ Y) (r₂ : Retract X₂ Y) (h : normalizer r₁ = normalizer r₂) : X₁ ≅ X₂ where
  hom := r₁.i ≫ r₂.r
  inv := r₂.i ≫ r₁.r
  hom_inv_id := by
    have : r₂.r ≫ r₂.i = r₁.r ≫ r₁.i := h.symm
    rw [Category.assoc, ← Category.assoc r₂.r, this, ← Category.assoc, ← Category.assoc,
      r₁.retract, Category.id_comp, r₁.retract]
  inv_hom_id := by
    have : r₁.r ≫ r₁.i = r₂.r ≫ r₂.i := h
    rw [Category.assoc, ← Category.assoc r₁.r, this, ← Category.assoc, ← Category.assoc,
      r₂.retract, Category.id_comp, r₂.retract]

/-- **Instance (proved).** The opcode names of `Text.lean` are a retract of the strings. -/
@[expose] def opRetract : Retract (PartialObj Cfg.Op) (PartialObj String) :=
  printParseRetract Text.opName Text.opOfName? Text.opOfName?_opName

end EvmYul.Venom.Category
