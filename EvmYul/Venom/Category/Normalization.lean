module

public import EvmYul.Venom.Category.Simulation

public section

/-!
# CFG normalization: critical edges, edge subdivision and its simulation witness (D1.3)

**The normal form, corrected.** The specification's D1.3 (tagged as taken from docs, unverified)
calls a flow normalized iff no *vertex* has both more than one predecessor and more than one
successor. Vyper's pass (`vyper/venom/passes/cfg_normalization.py` at `15e442d`) says instead:

> This pass splits basic blocks when there are multiple conditional predecessors.
> The code generator expect a normalized CFG, that has the property that
> each basic block has at most one conditional predecessor.

and splits an edge `p → b` exactly when `len(self.cfg.cfg_in(bb)) > 1` and
`len(self.cfg.cfg_out(pred_bb)) > 1`, i.e. it removes **critical edges** (`NoCriticalArrow`), on
successor and predecessor *sets* (parallel slots count once). The two notions differ:
`vertexNormal_ne_noCritical` is a five-block flow `p₁, p₂ → b → s₁, s₂` with no critical edge in
which `b` has two predecessors and two successors. Edge subdivision cannot change any original
block's degrees, so D1.3 as written is not the postcondition of the pass.

**Subdivision.** `Subdiv V` inserts a vertex on every arrow. `subdiv_noCritical`: it has no critical
arrow (every arrow has an endpoint of in- and out-degree one). `subdivRestrict D'` reads a
decoration of `Subdiv V` back on `V` (an arrow means the composite of its two halves), and
`subdivRestrict_semPath`: its semantics is that of `D'` along the subdivided path (the canonical
prefunctor `Q ⥤q P(Sd Q)` of D1.3 commutes strictly with the semantics). `subdivSim` packages this
as the simulation witness of D4.4 (identity components), so every outcome is preserved
(`subdiv_outcome`). Vyper's pass splits only the critical edges and forwards φ operands through an
`assign` in the split block; that per-function refinement is not proved here.
-/

namespace EvmYul.Venom.Category

open CategoryTheory

/-! ## Critical edges -/

section
variable {V : Type} [Quiver V]

/-- `a` has at least two different successors (successor *set*, as Vyper's `cfg_out`). -/
@[expose] def MultiSucc (a : V) : Prop :=
  ∃ c₁ c₂ : V, c₁ ≠ c₂ ∧ Nonempty (a ⟶ c₁) ∧ Nonempty (a ⟶ c₂)

/-- `b` has at least two different predecessors (predecessor *set*, as Vyper's `cfg_in`). -/
@[expose] def MultiPred (b : V) : Prop :=
  ∃ c₁ c₂ : V, c₁ ≠ c₂ ∧ Nonempty (c₁ ⟶ b) ∧ Nonempty (c₂ ⟶ b)

/-- **The postcondition of CFGNormalization**: no arrow from a block with several successors to a
block with several predecessors. -/
@[expose] def NoCriticalArrow (V : Type) [Quiver V] : Prop :=
  ∀ (a b : V), Nonempty (a ⟶ b) → ¬ (MultiSucc a ∧ MultiPred b)

/-- **D1.3 as written**: no vertex with several predecessors and several successors. -/
@[expose] def VertexNormal (V : Type) [Quiver V] : Prop :=
  ∀ b : V, ¬ (MultiPred b ∧ MultiSucc b)

end

/-! ## The counterexample to D1.3 -/

@[expose] section

/-- The five blocks of the counterexample. -/
inductive Five where
  | p₁ | p₂ | b | s₁ | s₂
  deriving DecidableEq

end

/-- The arrows `p₁ → b`, `p₂ → b`, `b → s₁`, `b → s₂`. -/
@[expose] def Five.adj : Five → Five → Bool
  | .p₁, .b | .p₂, .b | .b, .s₁ | .b, .s₂ => true
  | _, _ => false

/-- The quiver of the counterexample. -/
@[expose] instance Five.quiver : Quiver Five where
  Hom x y := PLift (Five.adj x y = true)

/-- **Counterexample.** The flow `p₁, p₂ → b → s₁, s₂` has no critical arrow, but `b` has two
predecessors and two successors, so it is not normalized in the sense of D1.3. -/
theorem vertexNormal_ne_noCritical : NoCriticalArrow Five ∧ ¬ VertexNormal Five := by
  constructor
  · rintro x y ⟨⟨hxy⟩⟩ ⟨⟨c₁, c₂, hne, ⟨⟨h₁⟩⟩, ⟨⟨h₂⟩⟩⟩, ⟨d₁, d₂, hne', ⟨⟨k₁⟩⟩, ⟨⟨k₂⟩⟩⟩⟩
    cases x <;> cases y <;> simp [Five.adj] at hxy <;>
      cases c₁ <;> cases c₂ <;> simp [Five.adj] at h₁ h₂ hne <;>
      cases d₁ <;> cases d₂ <;> simp [Five.adj] at k₁ k₂ hne'
  · intro h
    exact h .b ⟨⟨.p₁, .p₂, by decide, ⟨⟨rfl⟩⟩, ⟨⟨rfl⟩⟩⟩, ⟨.s₁, .s₂, by decide, ⟨⟨rfl⟩⟩, ⟨⟨rfl⟩⟩⟩⟩

/-! ## Subdivision -/

section
variable {V : Type} [Quiver.{0} V]

/-- An arrow of `V` with its endpoints. -/
@[expose] abbrev Arrow (V : Type) [Quiver.{0} V] : Type := Σ (a : V) (b : V), a ⟶ b

@[expose] section

/-- **Edge subdivision**: the vertices of `V` and one new vertex per arrow. -/
inductive Subdiv (V : Type) [Quiver.{0} V] : Type where
  /-- A vertex of `V`. -/
  | vert (a : V)
  /-- The new vertex in the middle of an arrow. -/
  | mid (e : Arrow V)

end

/-- The arrows of the subdivision: `a ⟶ e` and `e ⟶ b` for every arrow `e : a ⟶ b`. -/
@[expose] instance Subdiv.quiver : Quiver (Subdiv V) where
  Hom
    | .vert a, .mid e => PLift (a = e.1)
    | .mid e, .vert b => PLift (e.2.1 = b)
    | _, _ => PEmpty

/-- The first half of a subdivided arrow. -/
@[expose] def Subdiv.first {a b : V} (e : a ⟶ b) :
    (Subdiv.vert a : Subdiv V) ⟶ (Subdiv.mid ⟨a, b, e⟩ : Subdiv V) :=
  PLift.up rfl

/-- The second half of a subdivided arrow. -/
@[expose] def Subdiv.second {a b : V} (e : a ⟶ b) :
    (Subdiv.mid ⟨a, b, e⟩ : Subdiv V) ⟶ (Subdiv.vert b : Subdiv V) :=
  PLift.up rfl

/-- The canonical map of an arrow to its subdivided path of length two. -/
@[expose] def Subdiv.path {a b : V} (e : a ⟶ b) :
    Quiver.Path (Subdiv.vert a : Subdiv V) (Subdiv.vert b) :=
  ((Quiver.Path.nil).cons (Subdiv.first e)).cons (Subdiv.second e)

/-- The only predecessor of a subdivision vertex is its arrow's source. -/
private theorem subdiv_pred_unique {e : Arrow V} {c : Subdiv V}
    (h : Nonempty (c ⟶ (Subdiv.mid e : Subdiv V))) : c = Subdiv.vert e.1 := by
  obtain ⟨h⟩ := h
  cases c <;> [exact congrArg Subdiv.vert h.down; exact h.elim]

/-- The only successor of a subdivision vertex is its arrow's target. -/
private theorem subdiv_succ_unique {e : Arrow V} {c : Subdiv V}
    (h : Nonempty ((Subdiv.mid e : Subdiv V) ⟶ c)) : c = Subdiv.vert e.2.1 := by
  obtain ⟨h⟩ := h
  cases c <;> [exact congrArg Subdiv.vert h.down.symm; exact h.elim]

/-- **The subdivision has no critical arrow.** -/
theorem subdiv_noCritical : NoCriticalArrow (Subdiv V) := by
  rintro x y ⟨h⟩ ⟨⟨c₁, c₂, hne, h₁, h₂⟩, ⟨d₁, d₂, hne', k₁, k₂⟩⟩
  cases x with
  | vert a =>
    cases y with
    | vert _ => exact h.elim
    | mid e => exact hne' ((subdiv_pred_unique k₁).trans (subdiv_pred_unique k₂).symm)
  | mid e => exact hne ((subdiv_succ_unique h₁).trans (subdiv_succ_unique h₂).symm)

/-- A decoration of the subdivision read back on `V`: an arrow means its two halves. -/
@[expose] def subdivRestrict {σ : Type} (D' : Decor (Subdiv V) σ) : Decor V σ where
  obj a := D'.obj (Subdiv.vert a)
  step e := D'.semPath (Subdiv.path e)
  exit a := D'.exit (Subdiv.vert a)

/-- The image of a path of `V` in the subdivision. -/
@[expose] def Subdiv.mapPath {a : V} : {b : V} → Quiver.Path a b →
    Quiver.Path (Subdiv.vert a : Subdiv V) (Subdiv.vert b)
  | _, .nil => .nil
  | _, .cons p e => (Subdiv.mapPath p).comp (Subdiv.path e)

/-- **The subdivision commutes with the semantics.** -/
theorem subdivRestrict_semPath {σ : Type} (D' : Decor (Subdiv V) σ) {a : V} :
    ∀ {b : V} (p : Quiver.Path a b),
      (subdivRestrict D').semPath p = D'.semPath (Subdiv.mapPath p)
  | _, .nil => by simp only [Subdiv.mapPath, Decor.semPath_nil]; rfl
  | _, .cons p e => by
    simp only [Subdiv.mapPath, Decor.semPath_cons, Decor.semPath_comp, subdivRestrict_semPath D' p]
    rfl

/-- **The simulation witness of subdivision (D4.4)**, with identity components. -/
@[expose] def subdivSim {σ : Type} (D' : Decor (Subdiv V) σ) : LaxSim (subdivRestrict D') D' :=
  LaxSim.ofStrict (fun a => Subdiv.vert a) (fun e => Subdiv.path e) (fun _ => 𝟙 _)
    (fun e => by rw [Category.comp_id, Category.id_comp]; rfl)
    (fun b => by rw [Category.id_comp]; rfl)

/-- Every outcome on `V` is an outcome of the subdivision. -/
theorem subdiv_outcome {σ : Type} (D' : Decor (Subdiv V) σ) {a : V}
    {x : D'.obj (Subdiv.vert a)} {s : σ} {r : Exit σ} (h : (subdivRestrict D').Outcome a x s r) :
    D'.Outcome (Subdiv.vert a) x s r :=
  (subdivSim D').outcome (x' := x) (s' := s) (MachCat.id_run (σ := σ) x s) h

end

end EvmYul.Venom.Category
