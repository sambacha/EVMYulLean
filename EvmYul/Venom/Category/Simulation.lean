module

public import EvmYul.Venom.Category.PathSemantics

public section

/-!
# Simulations as lax natural transformations (D4.4)

A witness that a decorated flow `D` (on a quiver `V`) is refined by `D'` (on `W`) is a `LaxSim`:

* a prefunctor `h : V ⥤q Paths W`, given by its object map `hobj` and its arrow map `hmap` into
  paths of `W` (an arrow may go to a path of any length, the empty path included, which models
  stuttering), extended to paths (`LaxSim.mapPath`, a functor by `mapPath_comp`);
* a family `α b : D(b) ⟶ D'(h b)` of Kleisli morphisms;
* for every arrow `e : a ⟶ b` the square `D(e) ≫ α b ⊑ α a ≫ D'(h e)` commutes up to the order
  "defined implies equal" of `Machine.lean` (`HomLE`), and the exits are respected:
  `ε b ⊑ α b ≫ ε'(h b)`.

**Proved.**
* `LaxSim.square_path`: lax naturality extends from arrows to all paths (induction on the path;
  composition is monotone on both sides, `HomLE.comp_left`/`comp_right`). This is the statement
  that `α : Sem_D ⟹ h̃ ⋙ Sem_D'` is a lax natural transformation.
* `LaxSim.outcome`: every outcome of `D` from `(a, x, s)` is an outcome of `D'` from `h a` on the
  input that `α a` produces: the refinement of whole-function semantics (D3.6) that the witness
  certifies.
* `LaxSim.refl`, `LaxSim.ofStrict`: the identity simulation, and simulations whose squares commute
  strictly (CFG-preserving passes with `h̃ = 𝟭`, and the subdivision of `Normalization.lean`).
-/

namespace EvmYul.Venom.Category

open CategoryTheory

variable {V W : Type} [Quiver V] [Quiver W] {σ : Type}

/-- **D4.4.** A lax simulation of `D` by `D'`. -/
structure LaxSim (D : Decor V σ) (D' : Decor W σ) where
  /-- Where vertices go. -/
  hobj : V → W
  /-- Where arrows go: to paths (possibly empty). -/
  hmap : ∀ {a b : V}, (a ⟶ b) → Quiver.Path (hobj a) (hobj b)
  /-- The components. -/
  α : ∀ b : V, MachCat.of σ (D.obj b) ⟶ MachCat.of σ (D'.obj (hobj b))
  /-- The lax naturality square of an arrow. -/
  square : ∀ {a b : V} (e : a ⟶ b), HomLE (D.step e ≫ α b) (α a ≫ D'.semPath (hmap e))
  /-- Exits are respected. -/
  exit_le : ∀ b : V, HomLE (D.exit b) (α b ≫ D'.exit (hobj b))

namespace LaxSim

variable {D : Decor V σ} {D' : Decor W σ}

/-- The image of a path: `h̃`, the functor `Paths V ⥤ Paths W` that `h` induces. -/
@[expose] def mapPath (S : LaxSim D D') {a : V} : {b : V} → Quiver.Path a b →
    Quiver.Path (S.hobj a) (S.hobj b)
  | _, .nil => .nil
  | _, .cons p e => (S.mapPath p).comp (S.hmap e)

theorem mapPath_nil (S : LaxSim D D') (a : V) :
    S.mapPath (Quiver.Path.nil : Quiver.Path a a) = Quiver.Path.nil := by
  simp [mapPath]

theorem mapPath_cons (S : LaxSim D D') {a b c : V} (p : Quiver.Path a b) (e : b ⟶ c) :
    S.mapPath (p.cons e) = (S.mapPath p).comp (S.hmap e) := by
  simp [mapPath]

/-- `h̃` is a functor: it preserves composition of paths. -/
theorem mapPath_comp (S : LaxSim D D') {a b : V} (p : Quiver.Path a b) :
    ∀ {c : V} (q : Quiver.Path b c), S.mapPath (p.comp q) = (S.mapPath p).comp (S.mapPath q)
  | _, .nil => by simp [mapPath]
  | _, .cons q e => by
    rw [Quiver.Path.comp_cons, mapPath_cons, mapPath_cons, mapPath_comp S p q,
      Quiver.Path.comp_assoc]

/-- **Lax naturality on paths.** -/
theorem square_path (S : LaxSim D D') {a : V} :
    ∀ {b : V} (p : Quiver.Path a b),
      HomLE (D.semPath p ≫ S.α b) (S.α a ≫ D'.semPath (S.mapPath p))
  | _, .nil => by
    rw [Decor.semPath_nil, mapPath_nil, Decor.semPath_nil, Category.id_comp, Category.comp_id]
    exact HomLE.refl _
  | _, .cons p e => by
    rw [Decor.semPath_cons, mapPath_cons, Decor.semPath_comp, Category.assoc]
    refine HomLE.trans (HomLE.comp_left _ (S.square e)) ?_
    rw [← Category.assoc, ← Category.assoc]
    exact HomLE.comp_right (square_path S p) _

/-- **Refinement of outcomes.** -/
theorem outcome (S : LaxSim D D') {a : V} {x : D.obj a} {s : σ} {x' : D'.obj (S.hobj a)} {s' : σ}
    (hα : ((S.α a) x).run s = some (.ok (x', s'))) {r : Exit σ} (ho : D.Outcome a x s r) :
    D'.Outcome (S.hobj a) x' s' r := by
  obtain ⟨b, p, he⟩ := ho
  have h₁ := HomLE.comp_left (D.semPath p) (S.exit_le b)
  rw [← Category.assoc] at h₁
  have h := (h₁.trans (HomLE.comp_right (S.square_path p) _)) x s (by simp [he])
  rw [he, Category.assoc, MachCat.comp_run, hα] at h
  exact ⟨S.hobj b, S.mapPath p, h.symm⟩

end LaxSim

/-- The identity simulation. -/
@[expose] def LaxSim.refl (D : Decor V σ) : LaxSim D D where
  hobj := id
  hmap e := e.toPath
  α _ := 𝟙 _
  square e := by
    rw [Category.comp_id, Category.id_comp]
    show HomLE (D.step e) (D.semPath e.toPath)
    rw [Decor.semPath_toPath]
    exact HomLE.refl _
  exit_le b := by
    rw [Category.id_comp]
    exact HomLE.refl _

/-- A simulation whose squares commute strictly and whose exits agree. -/
@[expose] def LaxSim.ofStrict {D : Decor V σ} {D' : Decor W σ} (hobj : V → W)
    (hmap : ∀ {a b : V}, (a ⟶ b) → Quiver.Path (hobj a) (hobj b))
    (α : ∀ b : V, MachCat.of σ (D.obj b) ⟶ MachCat.of σ (D'.obj (hobj b)))
    (square : ∀ {a b : V} (e : a ⟶ b), D.step e ≫ α b = α a ≫ D'.semPath (hmap e))
    (exit_eq : ∀ b : V, D.exit b = α b ≫ D'.exit (hobj b)) : LaxSim D D' where
  hobj := hobj
  hmap := hmap
  α := α
  square e := by rw [square e]; exact HomLE.refl _
  exit_le b := by rw [exit_eq b]; exact HomLE.refl _

end EvmYul.Venom.Category
