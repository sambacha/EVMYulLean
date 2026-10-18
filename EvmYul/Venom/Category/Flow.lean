module

public import Mathlib.Combinatorics.Quiver.Path
public import Mathlib.Order.Basic
public import EvmYul.ProofTags

public section

/-!
# Flow quivers, reachability and dominance (specification D1.1, D1.4, P1.1)

A Venom function's control flow is a **quiver** (a directed multigraph): blocks are vertices and
every label operand of a terminator is its own arrow (`Flow`), so `jnz c, @a, @a` gives two
parallel arrows and self-loops are allowed. Paths are Mathlib's `Quiver.Path` (the morphisms of
the free category `Paths`).

Dominance is stated on paths, as in the specification (D1.4): `d` dominates `b` iff every path
from the entry to `b` passes through `d` (`Dom`), and *passes through* is literally a factorization
`p = p₁ ≫ p₂` with `p₁ : entry ⟶ d` (`visits_iff_factor`). Everything here is proved for an
arbitrary quiver with a root, so it applies to `Flow` and to every other graph built later
(`FuncFlow.lean` turns a Venom `Func` into one).

**P1.1 (proved).**
* `Dom.refl`, `Dom.trans`, `entry_dom`: a preorder with the entry least;
* `Dom.antisymm`: antisymmetric on reachable vertices (infinite descent on path length);
* `Dom.chain`: the dominators of a reachable vertex are totally ordered;
* `idom_unique`: hence a vertex has at most one immediate dominator, so the Hasse diagram of
  dominance is a forest whose only root is the entry (the dominator tree);
* `domPartialOrder`: the partial order on the reachable vertices, the thin category in which the
  scope functor of `Scope.lean` lives.
-/

namespace EvmYul.Venom.Category

/-! ## Flow quivers -/

/-- **D1.1 (flow quiver).** Blocks `B`, terminator successor slots `E` (one arrow per label operand,
so parallel arrows and self-loops are allowed), their source and target, and the entry block. -/
structure Flow where
  /-- Basic blocks (vertices). -/
  B : Type
  /-- Terminator successor slots (arrows). -/
  E : Type
  /-- The block whose terminator holds the slot. -/
  src : E → B
  /-- The block the slot names. -/
  tgt : E → B
  /-- The entry block. -/
  entry : B

/-- The quiver of a flow: an arrow `a ⟶ b` is a slot from `a` to `b`. -/
@[expose] instance Flow.quiver (G : Flow) : Quiver G.B where
  Hom a b := {e : G.E // G.src e = a ∧ G.tgt e = b}

/-! ## Passing through a vertex -/

section
variable {V : Type} [Quiver V]

/-- `strictVisits p d`: `d` occurs on `p` after its first vertex. -/
@[expose] def strictVisits {a : V} : {b : V} → Quiver.Path a b → V → Prop
  | _, .nil, _ => False
  | c, .cons p _, d => strictVisits p d ∨ d = c

/-- `visits p d`: `d` occurs on `p` (as its first vertex or later). -/
@[expose] def visits {a b : V} (p : Quiver.Path a b) (d : V) : Prop := d = a ∨ strictVisits p d

theorem strictVisits_nil {a d : V} : ¬ strictVisits (Quiver.Path.nil : Quiver.Path a a) d :=
  fun h => h

theorem strictVisits_cons {a b c d : V} (p : Quiver.Path a b) (e : b ⟶ c) :
    strictVisits (p.cons e) d ↔ strictVisits p d ∨ d = c := Iff.rfl

/-- A path visits its last vertex. -/
theorem visits_target {a b : V} : (p : Quiver.Path a b) → visits p b
  | .nil => .inl rfl
  | .cons _ _ => .inr (.inr rfl)

/-- A path visits its first vertex. -/
theorem visits_source {a b : V} (p : Quiver.Path a b) : visits p a := Or.inl rfl

/-- The vertices strictly visited by a composite. -/
theorem strictVisits_comp {a b : V} (p : Quiver.Path a b) :
    ∀ {c : V} (q : Quiver.Path b c) (d : V),
      strictVisits (p.comp q) d ↔ strictVisits p d ∨ strictVisits q d
  | _, .nil, d => by simp [strictVisits]
  | _, .cons q e, d => by
    rw [Quiver.Path.comp_cons, strictVisits_cons, strictVisits_cons, strictVisits_comp p q d]
    tauto

/-- The vertices visited by a composite: those of the first part, and those of the second after
its first vertex (which is the last vertex of the first part). -/
theorem visits_comp {a b c : V} (p : Quiver.Path a b) (q : Quiver.Path b c) (d : V) :
    visits (p.comp q) d ↔ visits p d ∨ strictVisits q d := by
  rw [visits, visits, strictVisits_comp, or_assoc]

/-- **Passing through is factoring (D1.4).** `p` visits `d` iff `p = p₁ ≫ p₂` with
`p₁ : a ⟶ d`. -/
theorem visits_iff_factor {a b : V} (p : Quiver.Path a b) (d : V) :
    visits p d ↔ ∃ (p₁ : Quiver.Path a d) (p₂ : Quiver.Path d b), p = p₁.comp p₂ := by
  refine ⟨fun h => ?_, fun ⟨p₁, p₂, h⟩ => h ▸ (visits_comp p₁ p₂ d).2 (.inl (visits_target p₁))⟩
  induction p with
  | nil => obtain rfl := h.resolve_right strictVisits_nil; exact ⟨.nil, .nil, rfl⟩
  | cons p e ih =>
    rcases or_assoc.2 h with h | rfl
    · obtain ⟨p₁, p₂, rfl⟩ := ih h; exact ⟨p₁, p₂.cons e, rfl⟩
    · exact ⟨p.cons e, .nil, rfl⟩

/-- **The last visit.** If `p` visits `d`, it factors as `p₁ ≫ r` where `r` starts at `d` and never
returns to it. -/
theorem visits_last {a b : V} (p : Quiver.Path a b) (d : V) (h : visits p d) :
    ∃ (p₁ : Quiver.Path a d) (r : Quiver.Path d b), p = p₁.comp r ∧ ¬ strictVisits r d := by
  induction p with
  | nil => obtain rfl := h.resolve_right strictVisits_nil; exact ⟨.nil, .nil, rfl, id⟩
  | @cons _ c p e ih =>
    by_cases hdc : d = c
    · subst hdc; exact ⟨p.cons e, .nil, rfl, id⟩
    · obtain ⟨p₁, r, rfl, hn⟩ := ih ((or_assoc.2 h).resolve_right hdc)
      exact ⟨p₁, r.cons e, rfl, fun h => h.elim hn hdc⟩

/-! ## Reachability and dominance -/

/-- **Reachability (D1.4).** `b` is reachable from `r` iff there is a path `r ⟶ b`. -/
@[expose] def Reach (r b : V) : Prop := Nonempty (Quiver.Path r b)

/-- **Dominance (D1.4).** With root `r`: `d` dominates `b` iff every path from `r` to `b` visits
`d`. -/
@[expose] def Dom (r d b : V) : Prop := ∀ p : Quiver.Path r b, visits p d

/-- Dominance exactly as the specification writes it: every path factors through `d`. -/
theorem dom_iff_factor (r d b : V) :
    Dom r d b ↔ ∀ p : Quiver.Path r b,
      ∃ (p₁ : Quiver.Path r d) (p₂ : Quiver.Path d b), p = p₁.comp p₂ :=
  forall_congr' fun p => visits_iff_factor p d

/-- Every vertex dominates itself. -/
theorem Dom.refl (r b : V) : Dom r b b := fun p => visits_target p

/-- The root dominates every vertex. -/
theorem entry_dom (r b : V) : Dom r r b := fun p => visits_source p

/-- Dominance is transitive. -/
theorem Dom.trans {r a b c : V} (hab : Dom r a b) (hbc : Dom r b c) : Dom r a c := fun p => by
  obtain ⟨p₁, p₂, rfl⟩ := (visits_iff_factor p b).1 (hbc p)
  exact (visits_comp p₁ p₂ a).2 (.inl (hab p₁))

/-- A dominator of a reachable vertex is reachable. -/
theorem Dom.reach {r d b : V} (h : Dom r d b) (hb : Reach r b) : Reach r d :=
  let ⟨p⟩ := hb; let ⟨p₁, _⟩ := (visits_iff_factor p d).1 (h p); ⟨p₁⟩

/-- **Antisymmetry on reachable vertices** (infinite descent on the length of a path to `a`). -/
theorem Dom.antisymm {r a b : V} (hab : Dom r a b) (hba : Dom r b a) (hb : Reach r b) :
    a = b := by
  obtain ⟨pa⟩ := hab.reach hb
  by_contra hne
  induction h : pa.length using Nat.strongRecOn generalizing pa with
  | _ n ih =>
    obtain ⟨q, t, rfl⟩ := (visits_iff_factor pa b).1 (hba pa)
    obtain ⟨q₁, q₂, rfl⟩ := (visits_iff_factor q a).1 (hab q)
    have ht : t.length ≠ 0 := fun h0 => hne (t.eq_of_length_zero h0).symm
    exact ih _ (by simp only [Quiver.Path.length_comp] at h; omega) q₁ rfl

/-- **The dominators of a reachable vertex form a chain.** -/
theorem Dom.chain {r d₁ d₂ b : V} (h₁ : Dom r d₁ b) (h₂ : Dom r d₂ b) (hb : Reach r b) :
    Dom r d₁ d₂ ∨ Dom r d₂ d₁ := by
  obtain ⟨p⟩ := hb
  obtain ⟨p₁, r₁, -, hr₁⟩ := visits_last p d₁ (h₁ p)
  by_cases hs : strictVisits r₁ d₂
  · -- `d₂` occurs on the suffix after the last visit of `d₁`: `d₁` dominates `d₂`.
    obtain ⟨s, t, rfl⟩ := (visits_iff_factor r₁ d₂).1 (.inr hs)
    exact .inl fun q => ((visits_comp q t d₁).1 (h₁ (q.comp t))).resolve_right
      fun h => hr₁ ((strictVisits_comp s t d₁).2 (.inr h))
  · -- `d₂` does not occur on that suffix: `d₂` dominates `d₁`.
    exact .inr fun q => ((visits_comp q r₁ d₂).1 (h₂ (q.comp r₁))).resolve_right hs

/-- Strict dominance. -/
@[expose] def SDom (r d b : V) : Prop := Dom r d b ∧ d ≠ b

/-- `i` is an immediate dominator of `b`: a strict dominator dominated by every strict
dominator. -/
@[expose] def IDom (r i b : V) : Prop := SDom r i b ∧ ∀ d, SDom r d b → Dom r d i

/-- **The dominator tree (P1.1).** A reachable vertex has at most one immediate dominator. -/
theorem idom_unique {r i j b : V} (hi : IDom r i b) (hj : IDom r j b) (hb : Reach r b) : i = j :=
  Dom.antisymm (hj.2 i hi.1) (hi.2 j hj.1) (hj.1.1.reach hb)

/-- The strict dominators of a reachable vertex are totally ordered by dominance. -/
theorem SDom.chain {r d₁ d₂ b : V} (h₁ : SDom r d₁ b) (h₂ : SDom r d₂ b) (hb : Reach r b) :
    Dom r d₁ d₂ ∨ Dom r d₂ d₁ :=
  Dom.chain h₁.1 h₂.1 hb

/-- The reachable vertices of a quiver with root `r`. -/
@[expose] def Reachable (r : V) : Type := {b : V // Reach r b}

/-- **P1.1: dominance is a partial order on the reachable vertices**, `d ≤ b` iff `d` dominates
`b`, with the root least (`root_le`). -/
@[expose] instance domPartialOrder (r : V) : PartialOrder (Reachable r) where
  le d b := Dom r d.1 b.1
  le_refl b := Dom.refl r b.1
  le_trans _ _ _ h₁ h₂ := Dom.trans h₁ h₂
  le_antisymm a b h₁ h₂ := Subtype.ext (Dom.antisymm h₁ h₂ b.2)

/-- The root as a reachable vertex. -/
@[expose] def Reachable.root (r : V) : Reachable r := ⟨r, ⟨.nil⟩⟩

/-- The root is the least element of the dominance order. -/
theorem root_le (r : V) (b : Reachable r) : Reachable.root r ≤ b := entry_dom r b.1

end

end EvmYul.Venom.Category
