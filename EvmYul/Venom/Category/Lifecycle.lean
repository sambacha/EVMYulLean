module

public import Mathlib.CategoryTheory.Adjunction.Reflective
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Thin
public import EvmYul.Venom.Category.Refinement

public section

/-!
# The SSA lifecycle as an equivalence of categories (D4.6), conditional on MakeSSA

Let `P` be any preorder of programs (the refinement category `Prog`, or refinement for one fixed
machine) and `S` a predicate (strict SSA). The SSA programs form the full subcategory
`ObjectProperty.FullSubcategory S`, with inclusion `ι = ObjectProperty.ι S`.

**Hypothesis (`SSAConstruction`).** A map `make` (MakeSSA) whose results satisfy `S` and that is
semantics-preserving *in both directions* (`x ≤ make x` and `make x ≤ x`). This is a hypothesis, not a
theorem: whether the real MakeSSA satisfies it is the open obligation. Under the compiled
`Cfg.Refines` it is not expected to hold for any renaming pass, because `Refines` quantifies over
every machine interface, including ones where `assign` is not a copy (`CfgTests.lean`, falsified
claim 1); this is why the statements here are generic in the preorder and can be instantiated with
refinement for one fixed machine.

**Proved under the hypothesis.**
* `inclusion_isEquivalence`: `ι` is full, faithful and essentially surjective, hence an equivalence
  (`ssaEquivalence : FullSubcategory S ≌ P`);
* `ssaReflective`: the inclusion is reflective (`MakeSSA ⊣ ι`), the reflector being the inverse of
  the equivalence; `reflector_obj_iso` identifies it with `make` on objects;
* `quasiInverse_iso_inclusion`: any second quasi-inverse back to `P` (PhiElimination), i.e. any
  object map out of `S` that is semantics-preserving in both directions, is naturally isomorphic to
  `ι`. In the semantic category, PhiElimination *is* the inclusion.
-/

namespace EvmYul.Venom.Category

open CategoryTheory

variable {P : Type} [Preorder P] (S : ObjectProperty P)

/-- **The MakeSSA hypothesis**: a map into `S` that is equivalent to the identity in the
preorder. -/
structure SSAConstruction where
  /-- The construction (MakeSSA). -/
  make : P → P
  /-- Its results are in `S`. -/
  mk_mem : ∀ x, S (make x)
  /-- It refines its input. -/
  le_mk : ∀ x, x ≤ make x
  /-- Its input refines it. -/
  mk_le : ∀ x, make x ≤ x

variable {S}

/-- The output of the construction as an object of the full subcategory. -/
@[expose] def SSAConstruction.obj (c : SSAConstruction S) (x : P) : S.FullSubcategory :=
  ⟨c.make x, c.mk_mem x⟩

/-- The inclusion is essentially surjective under the hypothesis. -/
theorem inclusion_essSurj (c : SSAConstruction S) : (ObjectProperty.ι S).EssSurj where
  mem_essImage x := ⟨c.obj x, ⟨iso_of_both_ways (homOfLE (c.mk_le x)) (homOfLE (c.le_mk x))⟩⟩

/-- **D4.6.** The inclusion of the SSA programs is an equivalence of categories. -/
theorem inclusion_isEquivalence (c : SSAConstruction S) : (ObjectProperty.ι S).IsEquivalence :=
  { essSurj := inclusion_essSurj c }

/-- The equivalence `FullSubcategory S ≌ P`. -/
@[expose] noncomputable def ssaEquivalence (c : SSAConstruction S) : S.FullSubcategory ≌ P :=
  have := inclusion_isEquivalence c
  (ObjectProperty.ι S).asEquivalence

/-- **D4.6.** The inclusion is reflective; the reflector is the inverse of the equivalence. -/
@[expose] noncomputable def ssaReflective (c : SSAConstruction S) : Reflective (ObjectProperty.ι S) where
  L := (ssaEquivalence c).inverse
  adj := by exact (ssaEquivalence c).symm.toAdjunction

/-- The reflector is MakeSSA on objects, up to isomorphism. -/
theorem reflector_obj_iso (c : SSAConstruction S) (x : P) :
    Nonempty ((ssaEquivalence c).inverse.obj x ≅ c.obj x) := by
  refine ⟨(ObjectProperty.ι S).preimageIso (iso_of_both_ways (homOfLE ?_) (homOfLE ?_))⟩
  exacts [(leOfHom ((ssaEquivalence c).counitIso.hom.app x)).trans (c.le_mk x),
    (c.mk_le x).trans (leOfHom ((ssaEquivalence c).counitIso.inv.app x))]

/-- A map out of the SSA programs that is semantics-preserving in both directions
(PhiElimination). -/
structure SSAElimination (S : ObjectProperty P) where
  /-- The map. -/
  elim : S.FullSubcategory → P
  /-- It refines its input. -/
  le_elim : ∀ x, x.obj ≤ elim x
  /-- Its input refines it. -/
  elim_le : ∀ x, elim x ≤ x.obj

/-- The map is monotone, hence a functor of thin categories. -/
@[expose] def SSAElimination.functor (d : SSAElimination S) : S.FullSubcategory ⥤ P where
  obj := d.elim
  map {x y} h := homOfLE (le_trans (d.elim_le x)
    (le_trans (leOfHom ((ObjectProperty.ι S).map h)) (d.le_elim y)))

/-- **D4.6.** Any such elimination is naturally isomorphic to the inclusion. -/
@[expose] def quasiInverse_iso_inclusion (d : SSAElimination S) :
    d.functor ≅ ObjectProperty.ι S :=
  NatIso.ofComponents (fun x => iso_of_both_ways
    (show d.elim x ⟶ x.obj from homOfLE (d.elim_le x))
    (show x.obj ⟶ d.elim x from homOfLE (d.le_elim x)))

end EvmYul.Venom.Category
