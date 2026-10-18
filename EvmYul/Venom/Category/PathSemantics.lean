module

public import Mathlib.CategoryTheory.PathCategory.Basic
public import EvmYul.Venom.Category.Machine

public section

/-!
# Semantics as the free functor out of the path category (D3.4–D3.7)

A **decoration** of a quiver `V` (D3.4) assigns to every vertex an object of the Kleisli category
`MachCat σ` and to every arrow a Kleisli morphism: a prefunctor `V ⥤q MachCat σ`
(`Decor.prefunctor`). By the universal property of the free category, Mathlib's `Paths.lift`
extends it to a functor `Decor.sem : Paths V ⥤ MachCat σ` (D3.5), so functoriality holds by
construction (`sem_comp`, `sem_cons`, `sem_nil`, `sem_toPath`) and is unique (`sem_unique`).

A decoration also has an **exit morphism** at every vertex (`Decor.exit`, ε of D3.6), whose
codomain is the empty type: an exit never returns normally; it throws `halt`, `revert` or `fault`,
or is undefined (the block does not leave the function).

* `Decor.Outcome D a x s r` (D3.6): some path `π` from `a` and the exit at its end send input
  `(x, s)` to the exit `r`: the whole-function semantics as a union over paths.
* `Decor.OutcomeWithin D n` (D3.7): the same over paths of length `≤ n`, the fuel filtration
  (`OutcomeWithin.mono`, `outcome_iff_exists_within`).
* `Decor.Deterministic D` (P3.2): all outcomes agree, i.e. the join of D3.6 exists. It is a
  property of a decoration, proved for Venom functions in `Bridge.lean` (`funcDecor_deterministic`).
-/

namespace EvmYul.Venom.Category

open CategoryTheory

/-- **D3.4 (decoration).** Objects over the vertices, Kleisli morphisms over the arrows, and an
exit morphism at every vertex. -/
structure Decor (V : Type) [Quiver V] (σ : Type) where
  /-- The object at a vertex (the environment type at block entry). -/
  obj : V → Type
  /-- The morphism of an arrow (body, guard of the slot, φ-copy into the target). -/
  step : ∀ {a b : V}, (a ⟶ b) → (MachCat.of σ (obj a) ⟶ MachCat.of σ (obj b))
  /-- The exit morphism of a vertex (body and a halting terminator). -/
  exit : ∀ b : V, MachCat.of σ (obj b) ⟶ MachCat.of σ Empty

namespace Decor

variable {V : Type} [Quiver V] {σ : Type}

/-- The decoration as a prefunctor into the Kleisli category. -/
@[expose] def prefunctor (D : Decor V σ) : V ⥤q MachCat σ where
  obj b := MachCat.of σ (D.obj b)
  map e := D.step e

/-- **D3.5 (semantics = free functor).** `Paths.lift` of the decoration. -/
@[expose] def sem (D : Decor V σ) : Paths V ⥤ MachCat σ := Paths.lift D.prefunctor

/-- The semantics of a path (a morphism of `Paths V`). -/
@[expose] def semPath (D : Decor V σ) {a b : V} (p : Quiver.Path a b) :
    MachCat.of σ (D.obj a) ⟶ MachCat.of σ (D.obj b) :=
  D.sem.map (X := Paths.of V |>.obj a) (Y := Paths.of V |>.obj b) p

theorem semPath_nil (D : Decor V σ) (a : V) :
    D.semPath (Quiver.Path.nil : Quiver.Path a a) = 𝟙 (MachCat.of σ (D.obj a)) :=
  Paths.lift_nil D.prefunctor a

theorem semPath_cons (D : Decor V σ) {a b c : V} (p : Quiver.Path a b) (e : b ⟶ c) :
    D.semPath (p.cons e) = D.semPath p ≫ D.step e :=
  Paths.lift_cons D.prefunctor p e

/-- **Functoriality**: the semantics of a composite path is the composite of the semantics. -/
theorem semPath_comp (D : Decor V σ) {a b c : V} (p : Quiver.Path a b) (q : Quiver.Path b c) :
    D.semPath (p.comp q) = D.semPath p ≫ D.semPath q :=
  D.sem.map_comp (X := Paths.of V |>.obj a) (Y := Paths.of V |>.obj b)
    (Z := Paths.of V |>.obj c) p q

/-- A single arrow means its decoration. -/
theorem semPath_toPath (D : Decor V σ) {a b : V} (e : a ⟶ b) : D.semPath e.toPath = D.step e :=
  Paths.lift_toPath D.prefunctor e

/-- **Uniqueness**: a functor out of `Paths V` that agrees with the decoration on arrows is the
semantics. -/
theorem sem_unique (D : Decor V σ) (Φ : Paths V ⥤ MachCat σ)
    (h : Paths.of V ⋙q Φ.toPrefunctor = D.prefunctor) : Φ = D.sem :=
  Paths.lift_unique D.prefunctor Φ h

/-! ## Outcomes as a union over paths (D3.6, D3.7, P3.2) -/

/-- **D3.6.** `r` is an outcome from vertex `a` on input `(x, s)`: some path `π : a ⟶ b` followed by
the exit of `b` throws `r`. -/
@[expose] def Outcome (D : Decor V σ) (a : V) (x : D.obj a) (s : σ) (r : Exit σ) : Prop :=
  ∃ (b : V) (p : Quiver.Path a b), ((D.semPath p ≫ D.exit b) x).run s = some (.error r)

/-- **D3.7 (fuel filtration).** The same, over paths of length at most `n`. -/
@[expose] def OutcomeWithin (D : Decor V σ) (n : Nat) (a : V) (x : D.obj a) (s : σ) (r : Exit σ) :
    Prop :=
  ∃ (b : V) (p : Quiver.Path a b), p.length ≤ n ∧
    ((D.semPath p ≫ D.exit b) x).run s = some (.error r)

theorem OutcomeWithin.mono {D : Decor V σ} {n m : Nat} (h : n ≤ m) {a : V} {x : D.obj a} {s : σ}
    {r : Exit σ} (ho : D.OutcomeWithin n a x s r) : D.OutcomeWithin m a x s r :=
  let ⟨b, p, hp, he⟩ := ho; ⟨b, p, hp.trans h, he⟩

/-- The whole semantics is the union of its fuel filtration. -/
theorem outcome_iff_exists_within (D : Decor V σ) (a : V) (x : D.obj a) (s : σ) (r : Exit σ) :
    D.Outcome a x s r ↔ ∃ n, D.OutcomeWithin n a x s r :=
  ⟨fun ⟨b, p, h⟩ => ⟨p.length, b, p, le_rfl, h⟩, fun ⟨_, b, p, _, h⟩ => ⟨b, p, h⟩⟩

/-- **P3.2 (determinism).** All outcomes from the same input agree, so the union of D3.6 is a join
of compatible partial maps. -/
@[expose] def Deterministic (D : Decor V σ) : Prop :=
  ∀ (a : V) (x : D.obj a) (s : σ) (r r' : Exit σ), D.Outcome a x s r → D.Outcome a x s r' → r = r'

end Decor

end EvmYul.Venom.Category
