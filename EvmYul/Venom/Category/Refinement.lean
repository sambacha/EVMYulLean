module

public import Mathlib.CategoryTheory.PathCategory.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import EvmYul.Venom.Cfg

public section

/-!
# The refinement category, pass relations, pipelines and validator lifts (D4.1–D4.3, D4.5)

* **D4.1.** `Prog` is the type of Venom functions ordered by the compiled refinement `Cfg.Refines`;
  Mathlib's `Preorder.smallCategory` makes it a thin category (`prog_hom_iff`): identities are
  `Refines.refl`, composition is `Refines.trans`.
* **D4.2.** A phase is a predicate on functions (`Phase`); a correct pass between phases is a
  left-total relation contained in refinement (`PassRel`). Phases and pass relations form a
  category (`Phase.category`, the wide subcategory `Rel_⊑` of the category of relations): closure
  under composition is transitivity of `Refines` (P4.1).
* **D4.3.** A pipeline is a path in a quiver of phases whose arrows are passes; assigning a pass
  relation to each arrow (a prefunctor) gives the pipeline functor `pipeline` by `Paths.lift`, so
  **pipeline correctness is functoriality** (`pipeline_sound`: every input has an output, and every
  output refines its input, for every path at once).
* **D4.5.** A `Validator` (a decidable check with a soundness proof) is a prefunctor from the quiver
  of checked pairs into `Prog` (`checkedPrefunctor`); its `Paths.lift` sends every accepted trace to
  a refinement. `chain_sound_lift` re-derives the compiled `Validator.chain_sound` as an instance of
  this lift (`chainPath` turns an accepted trace into a path of checked pairs).
-/

namespace EvmYul.Venom.Category

open CategoryTheory EvmYul.Venom.Cfg

/-! ## D4.1 The refinement category -/

/-- Venom functions as objects of the refinement category. -/
@[expose] def Prog : Type := Func

/-- A function as an object of `Prog`. -/
@[expose] def Prog.of (f : Func) : Prog := f

/-- The function of an object of `Prog`. -/
@[expose] def Prog.func (p : Prog) : Func := p

/-- **D4.1.** Refinement preorders the functions. -/
@[expose] instance Prog.preorder : Preorder Prog where
  le a b := Refines a.func b.func
  le_refl a := Refines.refl a.func
  le_trans _ _ _ h₁ h₂ := Refines.trans h₁ h₂

/-- The thin category `Prog`: there is a morphism `a ⟶ b` iff `a` refines to `b`. -/
theorem prog_hom_iff (a b : Func) : Nonempty (Prog.of a ⟶ Prog.of b) ↔ Refines a b :=
  ⟨fun ⟨h⟩ => leOfHom h, fun h => ⟨homOfLE h⟩⟩

/-! ## D4.2 Phases and pass relations -/

/-- A phase: a predicate on functions (SSA, after `FmpLowering`, normalized, …). -/
structure Phase where
  /-- The functions in the phase. -/
  holds : Func → Prop

/-- The functions of a phase. -/
@[expose] abbrev Phase.Obj (P : Phase) : Type := {f : Func // P.holds f}

/-- **D4.2.** A correct pass from phase `P` to phase `Q`: a left-total relation whose pairs refine. -/
@[ext]
structure PassRel (P Q : Phase) where
  /-- Which outputs the pass may produce for which inputs. -/
  rel : P.Obj → Q.Obj → Prop
  /-- Every input has an output. -/
  total : ∀ x, ∃ y, rel x y
  /-- Every output refines its input. -/
  sound : ∀ x y, rel x y → Refines x.1 y.1

/-- The identity pass. -/
@[expose] def PassRel.id (P : Phase) : PassRel P P where
  rel x y := x = y
  total x := ⟨x, rfl⟩
  sound x _ h := h ▸ Refines.refl x.1

/-- Running one pass after another (relational composition). -/
@[expose] def PassRel.comp {P Q R : Phase} (F : PassRel P Q) (G : PassRel Q R) : PassRel P R where
  rel x z := ∃ y, F.rel x y ∧ G.rel y z
  total x := by
    obtain ⟨y, hy⟩ := F.total x
    obtain ⟨z, hz⟩ := G.total y
    exact ⟨z, y, hy, hz⟩
  sound x z := by
    rintro ⟨y, hy, hz⟩
    exact Refines.trans (F.sound x y hy) (G.sound y z hz)

/-- **P4.1.** Phases and correct passes form a category (`Rel_⊑`). -/
@[expose] instance Phase.category : Category Phase where
  Hom P Q := PassRel P Q
  id P := PassRel.id P
  comp F G := PassRel.comp F G
  id_comp F := by
    ext x z
    exact ⟨fun ⟨_, h, hz⟩ => h ▸ hz, fun h => ⟨x, rfl, h⟩⟩
  comp_id F := by
    ext x z
    exact ⟨fun ⟨_, hz, h⟩ => h ▸ hz, fun h => ⟨z, h, rfl⟩⟩
  assoc F G H := by
    ext x w
    exact ⟨fun ⟨z, ⟨y, h₁, h₂⟩, h₃⟩ => ⟨y, h₁, z, h₂, h₃⟩,
      fun ⟨y, h₁, z, h₂, h₃⟩ => ⟨z, ⟨y, h₁, h₂⟩, h₃⟩⟩

/-! ## D4.3 Pipelines -/

/-- **D4.3.** The pipeline functor of an assignment of pass relations to the arrows of a phase
quiver. -/
@[expose] def pipeline {V : Type} [Quiver V] (F : V ⥤q Phase) : Paths V ⥤ Phase := Paths.lift F

/-- The composite pass relation of a path of passes. -/
@[expose] def pipelineRel {V : Type} [Quiver V] (F : V ⥤q Phase) {a b : V} (p : Quiver.Path a b) :
    PassRel (F.obj a) (F.obj b) :=
  (pipeline F).map (X := Paths.of V |>.obj a) (Y := Paths.of V |>.obj b) p

/-- **Pipeline correctness is functoriality.** For every path of passes, every input has an
output, and every output refines its input. -/
theorem pipeline_sound {V : Type} [Quiver V] (F : V ⥤q Phase) {a b : V} (p : Quiver.Path a b)
    (x : (F.obj a).Obj) : ∃ y, (pipelineRel F p).rel x y ∧ Refines x.1 y.1 :=
  let ⟨y, hy⟩ := (pipelineRel F p).total x; ⟨y, hy, (pipelineRel F p).sound x y hy⟩

/-- The pipeline of a composite path is the composite of the pipelines. -/
theorem pipelineRel_comp {V : Type} [Quiver V] (F : V ⥤q Phase) {a b c : V}
    (p : Quiver.Path a b) (q : Quiver.Path b c) :
    pipelineRel F (p.comp q) = PassRel.comp (pipelineRel F p) (pipelineRel F q) :=
  (pipeline F).map_comp (X := Paths.of V |>.obj a) (Y := Paths.of V |>.obj b)
    (Z := Paths.of V |>.obj c) p q

/-! ## D4.5 Validators as lifts from the quiver of checked pairs -/

/-- The functions as vertices of the quiver of pairs a validator accepts. -/
structure Checked (v : Validator) where
  /-- The function. -/
  func : Func

/-- An arrow `a ⟶ b` is a proof that the validator accepts `(a, b)`. -/
@[expose] instance Checked.quiver (v : Validator) : Quiver (Checked v) where
  Hom a b := PLift (v.check a.func b.func = true)

/-- **D4.5.** Soundness makes the quiver of checked pairs a prefunctor into `Prog`. -/
@[expose] def checkedPrefunctor (v : Validator) : Checked v ⥤q Prog where
  obj a := Prog.of a.func
  map {a b} h := homOfLE (v.sound a.func b.func h.down)

/-- Its extension to paths: every path of checked pairs is a refinement. -/
@[expose] def checkedLift (v : Validator) : Paths (Checked v) ⥤ Prog := Paths.lift (checkedPrefunctor v)

/-- The last function of a nonempty trace. -/
@[expose] def traceLast : Func → List Func → Func
  | a, [] => a
  | _, b :: rest => traceLast b rest

/-- An accepted trace `a, b, …` as a path of checked pairs from `a` to its last function. -/
@[expose] def chainPath (v : Validator) :
    ∀ (a : Func) (rest : List Func), v.chain (a :: rest) = true →
      Quiver.Path (Checked.mk (v := v) a) (Checked.mk (traceLast a rest))
  | _, [], _ => .nil
  | a, b :: rest, h => by
    rw [Validator.chain, Bool.and_eq_true] at h
    exact (Quiver.Hom.toPath (V := Checked v) (PLift.up h.1)).comp (chainPath v b rest h.2)

theorem traceLast_eq (a : Func) (l : List Func) :
    traceLast a l = (a :: l).getLast (List.cons_ne_nil _ _) := by
  induction l generalizing a <;> simp [traceLast, *]

theorem traceLast_eq_getLast (a b : Func) (rest : List Func) :
    traceLast a (b :: rest) = (b :: rest).getLast (List.cons_ne_nil _ _) := by
  rw [traceLast_eq, List.getLast_cons (List.cons_ne_nil _ _)]

/-- **`Validator.chain_sound` as an instance of `Paths.lift`.** -/
theorem chain_sound_lift (v : Validator) (a b : Func) (rest : List Func)
    (h : v.chain (a :: b :: rest) = true) :
    Refines a ((b :: rest).getLast (List.cons_ne_nil _ _)) :=
  traceLast_eq_getLast a b rest ▸ leOfHom ((checkedLift v).map (X := Paths.of (Checked v) |>.obj ⟨a⟩)
    (Y := Paths.of (Checked v) |>.obj ⟨traceLast a (b :: rest)⟩) (chainPath v a (b :: rest) h))

end EvmYul.Venom.Category
