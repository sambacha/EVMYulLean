module

public import Mathlib.CategoryTheory.Category.KleisliCat
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Control.Lawful
public import Mathlib.Data.Finset.Basic
public import EvmYul.Venom.Cfg

public section

/-!
# The machine monad, its Kleisli category, environments as a presheaf (D3.1–D3.3, P3.1)

* **D3.1.** `Exit σ` (halt, revert, fault) and the machine monad
  `Mach σ = StateT σ (ExceptT (Exit σ) Option)`, so `Mach σ X ≅ σ → Option (Exit σ ⊕ X × σ)`
  (`Mach.run`, `Mach.mk`). `none` is ⊥: undefined (a branch not taken, fuel exhausted). Its Kleisli
  category is Mathlib's `KleisliCat (Mach σ)` (`MachCat σ`). The hom-sets carry the order
  "defined implies equal" (`HomLE`), a preorder (`HomLE.refl`, `HomLE.trans`) for which
  composition is monotone on both sides (`HomLE.comp_left`, `HomLE.comp_right`): the
  poset-enrichment that lax naturality (`Simulation.lean`) needs.
* **D3.2.** Environments of a context `Γ` are `Γ → Word`, contravariant in `Γ` by precomposition
  (`Env.pull`). On types this is literally the representable presheaf `yoneda.obj Word`
  (`envPresheaf_obj`, `envPresheaf_map`); on finite variable sets ordered by inclusion it is the
  restriction presheaf `ctxEnv : (Finset Var)ᵒᵖ ⥤ Type` (D1.5's contexts).
* **D3.3.** A machine model is the existing class `EvmInterface σ` of `Cfg.lean`; each primitive is
  a Kleisli morphism `prim op : List Word ⟶ List Word` (a missing result is a fault).
* **P3.1 (parallel copy).** The φs of an edge are **one** morphism, precomposition with
  `⟨incl, σₑ⟩ : Γ_dom ⊕ Phi → Γ_out` (`phiCopy`); every φ reads the predecessor's environment
  (`phiCopy_inr`), so a swap swaps (`phiCopy_swap`). The sequential reading (one copy after the
  other) is a different map, and it loses a value on the swap (`seqCopy_swap_loses`): that is the
  counterexample that rules it out.
-/

namespace EvmYul.Venom.Category

open CategoryTheory EvmYul.Venom.Cfg

/-! ## D3.1 The machine monad -/

@[expose] section

/-- How a run leaves the function: halt or revert with a final state, or fault. -/
inductive Exit (σ : Type) where
  /-- Normal halt (`stop`, `return`, `ret`). -/
  | halt (s : σ)
  /-- Revert. -/
  | revert (s : σ)
  /-- A fault: an instruction with no meaning, a missing block, a malformed φ. -/
  | fault
  deriving DecidableEq

end

/-- **D3.1.** The machine monad: state, an exit exception, and ⊥ (`none`). -/
@[expose] abbrev Mach (σ : Type) : Type → Type := StateT σ (ExceptT (Exit σ) Option)

/-- The Kleisli category of the machine monad. -/
@[expose] abbrev MachCat (σ : Type) : Type 1 := KleisliCat (Mach σ)

/-- The object of `MachCat σ` for a type. -/
@[expose] abbrev MachCat.of (σ : Type) (X : Type) : MachCat σ := KleisliCat.mk (Mach σ) X

/-- A computation as a plain function `σ → Option (Except (Exit σ) (X × σ))`. -/
@[expose] def Mach.run {σ X : Type} (m : Mach σ X) (s : σ) : Option (Except (Exit σ) (X × σ)) :=
  (m s).run

/-- A computation from a plain function. -/
@[expose] def Mach.mk {σ X : Type} (f : σ → Option (Except (Exit σ) (X × σ))) : Mach σ X :=
  fun s => ExceptT.mk (f s)

theorem Mach.run_mk {σ X : Type} (f : σ → Option (Except (Exit σ) (X × σ))) (s : σ) :
    (Mach.mk f).run s = f s := by
  simp [Mach.run, Mach.mk, ExceptT.run, ExceptT.mk]

theorem Mach.ext {σ X : Type} {m n : Mach σ X} (h : ∀ s, m.run s = n.run s) : m = n :=
  funext h

theorem Mach.run_pure {σ X : Type} (x : X) (s : σ) :
    (pure x : Mach σ X).run s = some (.ok (x, s)) := by
  simp [Mach.run, pure, StateT.pure, ExceptT.pure, ExceptT.run, ExceptT.mk]

/-- Bind in plain terms: ⊥ and exits propagate, a value continues. -/
theorem Mach.run_bind {σ X Y : Type} (m : Mach σ X) (k : X → Mach σ Y) (s : σ) :
    (m >>= k).run s = match m.run s with
      | none => none
      | some (.error e) => some (.error e)
      | some (.ok (x, s')) => (k x).run s' := by
  simp only [Mach.run, bind, StateT.bind, ExceptT.bind, ExceptT.run, ExceptT.mk]
  rcases m s with _ | _ | ⟨x, s'⟩ <;> simp [Option.bind] <;> rfl

/-- Kleisli composition in plain terms. -/
theorem MachCat.comp_run {σ : Type} {X Y Z : MachCat σ} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) (s : σ) :
    Mach.run ((f ≫ g) x) s = match (f x).run s with
      | none => none
      | some (.error e) => some (.error e)
      | some (.ok (y, s')) => (g y).run s' :=
  Mach.run_bind (f x) g s

/-- Identities in plain terms. -/
theorem MachCat.id_run {σ : Type} {X : MachCat σ} (x : X) (s : σ) :
    ((𝟙 X : X ⟶ X) x).run s = some (.ok (x, s)) :=
  Mach.run_pure (σ := σ) (X := X) x s

/-! ## The order on hom-sets: defined implies equal -/

/-- `f ⊑ g`: wherever `f` is defined, `g` gives the same answer. -/
@[expose] def HomLE {σ : Type} {X Y : MachCat σ} (f g : X ⟶ Y) : Prop :=
  ∀ x s, (f x).run s ≠ none → (f x).run s = (g x).run s

@[reviewed_rfl "reflexivity of the pointwise order: each defined value equals itself"]
theorem HomLE.refl {σ : Type} {X Y : MachCat σ} (f : X ⟶ Y) : HomLE f f := fun _ _ _ => rfl

theorem HomLE.trans {σ : Type} {X Y : MachCat σ} {f g h : X ⟶ Y} (h₁ : HomLE f g)
    (h₂ : HomLE g h) : HomLE f h :=
  fun x s hx => (h₁ x s hx).trans (h₂ x s (h₁ x s hx ▸ hx))

/-- Composition is monotone in its first argument. -/
theorem HomLE.comp_right {σ : Type} {X Y Z : MachCat σ} {f g : X ⟶ Y} (h : HomLE f g)
    (k : Y ⟶ Z) : HomLE (f ≫ k) (g ≫ k) := fun x s hx => by
  simp only [MachCat.comp_run] at hx ⊢
  rw [← h x s fun h0 => hx (by rw [h0])]

/-- Composition is monotone in its second argument. -/
theorem HomLE.comp_left {σ : Type} {X Y Z : MachCat σ} (k : X ⟶ Y) {f g : Y ⟶ Z}
    (h : HomLE f g) : HomLE (k ≫ f) (k ≫ g) := fun x s hx => by
  simp only [MachCat.comp_run] at hx ⊢
  rcases hk : (k x).run s with _ | _ | ⟨y, s'⟩ <;> [rfl; rfl; exact h y s' (by rwa [hk] at hx)]

/-! ## D3.2 Environments as a presheaf -/

/-- Environments of a context. -/
@[expose] abbrev Env (Γ : Type) : Type := Γ → Word

/-- **D3.2.** Restriction along a context morphism `f : Γ' → Γ`: `Env(f) = (−) ∘ f`. -/
@[expose] def Env.pull {Γ Γ' : Type} (f : Γ' → Γ) (e : Env Γ) : Env Γ' := e ∘ f

theorem Env.pull_id {Γ : Type} (e : Env Γ) : Env.pull id e = e := by
  funext x; simp [Env.pull]

theorem Env.pull_comp {Γ Γ' Γ'' : Type} (f : Γ' → Γ) (g : Γ'' → Γ') (e : Env Γ) :
    Env.pull (f ∘ g) e = Env.pull g (Env.pull f e) := by
  funext x; simp [Env.pull]

/-- The representable presheaf `yoneda.obj Word : Typeᵒᵖ ⥤ Type`. -/
@[expose] abbrev envPresheaf : Typeᵒᵖ ⥤ Type := yoneda.obj Word

/-- Its value at `Γ` is `Env Γ`. -/
@[reviewed_rfl "API: the representable presheaf at Γ is the type of environments of Γ"]
theorem envPresheaf_obj (Γ : Type) : envPresheaf.obj (Opposite.op Γ) = Env Γ := rfl

/-- Its action on a context morphism is `Env.pull`. -/
theorem envPresheaf_map {Γ Γ' : Type} (f : Γ' → Γ) (e : Env Γ) :
    envPresheaf.map (Quiver.Hom.op (X := Γ') (Y := Γ) f) e = Env.pull f e := by
  funext x; simp [Env.pull]

/-- Restriction of an environment of `Γ` to a smaller context `Γ' ⊆ Γ`. -/
@[expose] def ctxRestrict {Γ' Γ : Finset Var} (h : Γ' ⊆ Γ) (e : Env {x // x ∈ Γ}) :
    Env {x // x ∈ Γ'} :=
  Env.pull (fun x => ⟨x.1, h x.2⟩) e

/-- **D3.2 on finite contexts.** `Γ ↦ Env Γ` with restriction along inclusions, a functor
`(Finset Var)ᵒᵖ ⥤ Type`. -/
@[expose] def ctxEnv : (Finset Var)ᵒᵖ ⥤ Type where
  obj Γ := Env {x // x ∈ Γ.unop}
  map {Γ Γ'} h := ctxRestrict (leOfHom h.unop)
  map_id _ := by funext e x; simp [ctxRestrict, Env.pull]
  map_comp _ _ := by funext e x; simp [ctxRestrict, Env.pull]

/-! ## D3.3 Models -/

/-- **D3.3.** A primitive of a machine model as a Kleisli morphism; no result is a fault. -/
@[expose] def prim {σ : Type} [EvmInterface σ] (op : Op) :
    MachCat.of σ (List Word) ⟶ MachCat.of σ (List Word) :=
  fun ws => Mach.mk fun s => match EvmInterface.exec op ws s with
    | none => some (.error .fault)
    | some (rs, s') => some (.ok (rs, s'))

/-! ## P3.1 Parallel copy -/

/-- **The φ-copy of an edge** into a block with dominating context `Γdom` and φ-targets `Phi`: one
precomposition with `⟨incl, σₑ⟩`, where `σₑ` names the source of each φ in the predecessor's
output context `Γout`. -/
@[expose] def phiCopy {Γdom Phi Γout : Type} (incl : Γdom → Γout) (σe : Phi → Γout) :
    Env Γout → Env (Γdom ⊕ Phi) :=
  Env.pull (Sum.elim incl σe)

/-- Every φ target reads the predecessor's environment, whatever the other φs do. -/
theorem phiCopy_inr {Γdom Phi Γout : Type} (incl : Γdom → Γout) (σe : Phi → Γout) (e : Env Γout)
    (x : Phi) : phiCopy incl σe e (.inr x) = e (σe x) := by
  simp [phiCopy, Env.pull]

/-- Variables of the dominating context pass through unchanged. -/
theorem phiCopy_inl {Γdom Phi Γout : Type} (incl : Γdom → Γout) (σe : Phi → Γout) (e : Env Γout)
    (x : Γdom) : phiCopy incl σe e (.inl x) = e (incl x) := by
  simp [phiCopy, Env.pull]

/-- The φ-copy as a pure Kleisli morphism (`ρₑ = η ∘ Env(⟨incl, σₑ⟩)` of D3.4). -/
@[expose] def phiCopyHom (σ : Type) {Γdom Phi Γout : Type} (incl : Γdom → Γout) (σe : Phi → Γout) :
    MachCat.of σ (Env Γout) ⟶ MachCat.of σ (Env (Γdom ⊕ Phi)) :=
  fun e => pure (phiCopy incl σe e)

/-- **The swap.** `x, y := y, x` as φs on a loop's back edge (`x = phi …, y` and `y = phi …, x`)
swaps the two values. -/
theorem phiCopy_swap (e : Env Bool) :
    phiCopy (Γdom := Empty) Empty.elim (fun b : Bool => !b) e (.inr true) = e false ∧
    phiCopy (Γdom := Empty) Empty.elim (fun b : Bool => !b) e (.inr false) = e true := by
  simp [phiCopy, Env.pull]

/-- The **sequential** reading of a list of copies `xᵢ := srcᵢ`, each reading the environment
updated by the previous ones. -/
@[expose] def seqCopy {Γ : Type} [DecidableEq Γ] : List (Γ × Γ) → Env Γ → Env Γ
  | [], e => e
  | (x, src) :: rest, e => seqCopy rest (Function.update e x (e src))

/-- **Counterexample to the sequential reading.** On the swap `x := y; y := x` with `x ≠ y`
values, the sequential copy gives both variables `y`'s old value: the old value of `x` is lost,
whereas `phiCopy_swap` keeps it. -/
theorem seqCopy_swap_loses (e : Env Bool) (h : e true ≠ e false) :
    seqCopy [(true, false), (false, true)] e false ≠ e true := by
  simpa [seqCopy] using h.symm

end EvmYul.Venom.Category
