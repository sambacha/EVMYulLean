module

public import EvmYul.Venom.Category.Flow
public import EvmYul.Venom.Dominance

public section

/-!
# The flow quiver of a Venom function, and the checked dominator tree on it

`flowOf f` is the flow quiver (D1.1) of a function of the control-flow-graph layer
(`EvmYul.Venom.Cfg`): vertices are labels, and an arrow out of `u` is a slot `(u, k)` of the
successor list of the block labelled `u` (the label operands of its terminator, `Block.succs`), so
`jnz c, @a, @a` has two parallel arrows `u ⟶ a`. The list is kept as Vyper prints it (`OUT=[…]`
is computed from the same operands); Python's `out_bbs` may collapse parallel edges, which only
changes the multiplicity of arrows, never reachability or dominance.

**The bridge (proved).** `Dominance.lean` defines dominance by an inductive predicate
`ReachAvoid` (a path from the entry that never meets `a`) and checks untrusted dominator trees
against it (`checkTree_sound`). Here that definition is shown to be the path definition of the
specification (D1.4) on this quiver:

* `reachAvoid_iff`: `ReachAvoid f a v` iff some `Quiver.Path` from the entry to `v` never visits
  `a`;
* `dominates_iff_dom`: `Dominance.Dominates f a v ↔ Dom f.entry a v`;
* `checkTree_dom`: hence an accepted certificate gives dominance in the sense of D1.4, and the
  executable query `dominatesB` is sound for it (`dominatesB_dom`). Together with the untrusted
  `computeDomTree`, this is the verified executable dominator computation of task T2.
-/

namespace EvmYul.Venom.Category

open EvmYul.Venom.Cfg EvmYul.Venom.Dominance

/-- The successor slots of a function: `(u, k)` with `k` an index into the successor list of the
block labelled `u`. -/
@[expose] def Slot (f : Func) : Type :=
  {p : Label × Nat // ∃ b, f.find? p.1 = some b ∧ p.2 < b.succs.length}

/-- The label a slot names. -/
@[expose] def slotTarget (f : Func) (e : Slot f) : Label :=
  ((f.find? e.1.1).map fun b => b.succs.getD e.1.2 "").getD ""

/-- **The flow quiver of a function (D1.1).** -/
@[expose] def flowOf (f : Func) : Flow where
  B := Label
  E := Slot f
  src e := e.1.1
  tgt e := slotTarget f e
  entry := f.entry

/-- An edge of `Dominance.lean` is exactly a nonempty set of arrows of the flow quiver. -/
theorem edge_iff_arrow (f : Func) (u v : Label) :
    Edge f u v ↔ Nonempty (@Quiver.Hom (flowOf f).B _ u v) := by
  constructor
  · rintro ⟨b, hb, hv⟩
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hv
    exact ⟨⟨⟨(u, k), b, hb, hk⟩, rfl, by simp [flowOf, slotTarget, hb, hk]⟩⟩
  · rintro ⟨⟨⟨⟨u', k⟩, b, hb, hk⟩, rfl, rfl⟩⟩
    exact ⟨b, hb, by simp [flowOf, slotTarget, hb, hk]⟩

/-- A path of the flow quiver from the entry that avoids `a` gives `ReachAvoid`. -/
private theorem reachAvoid_of_path (f : Func) (a : Label) :
    ∀ {v : Label} (p : @Quiver.Path (flowOf f).B _ f.entry v), ¬ visits p a → ReachAvoid f a v
  | _, .nil, h => .entry fun he => h (.inl he.symm)
  | _, .cons p e, h => .step (reachAvoid_of_path f a p fun hv => h (or_assoc.1 (.inl hv)))
      ((edge_iff_arrow f _ _).2 ⟨e⟩) fun hva => h (.inr (.inr hva.symm))

/-- `ReachAvoid` gives a path of the flow quiver from the entry that avoids `a`. -/
private theorem path_of_reachAvoid (f : Func) (a : Label) {v : Label} (h : ReachAvoid f a v) :
    ∃ p : @Quiver.Path (flowOf f).B _ f.entry v, ¬ visits p a := by
  induction h with
  | entry hne => exact ⟨.nil, fun hv => hv.elim (hne ·.symm) strictVisits_nil⟩
  | step _ he hva ih =>
    obtain ⟨p, hp⟩ := ih
    obtain ⟨e⟩ := (edge_iff_arrow f _ _).1 he
    exact ⟨p.cons e, fun hv => (or_assoc.2 hv).elim hp (hva ·.symm)⟩

/-- `ReachAvoid` is "some path from the entry avoids `a`". -/
theorem reachAvoid_iff (f : Func) (a v : Label) :
    ReachAvoid f a v ↔ ∃ p : @Quiver.Path (flowOf f).B _ f.entry v, ¬ visits p a :=
  ⟨path_of_reachAvoid f a, fun ⟨p, hp⟩ => reachAvoid_of_path f a p hp⟩

/-- **`Dominance.Dominates` is the dominance of the specification (D1.4)** on the flow quiver. -/
theorem dominates_iff_dom (f : Func) (a v : Label) :
    Dominates f a v ↔ @Dom (flowOf f).B _ f.entry a v := by
  rw [Dominates, reachAvoid_iff, not_exists_not, Dom]

/-- **Soundness of the checked dominator tree for D1.4.** Every tree ancestor-or-self of `v` in an
accepted certificate dominates `v` in the flow quiver. -/
theorem checkTree_dom {f : Func} {t : DomTree} (h : checkTree f t = true) {a v : Label}
    (hav : TreeAnc t.parent a v) : @Dom (flowOf f).B _ f.entry a v :=
  (dominates_iff_dom f a v).1 (checkTree_sound h hav)

/-- The executable query `dominatesB` is sound for D1.4 under an accepted certificate. -/
theorem dominatesB_dom {f : Func} {t : DomTree} (h : checkTree f t = true) {a v : Label}
    (hq : dominatesB t a v = true) : @Dom (flowOf f).B _ f.entry a v :=
  (dominates_iff_dom f a v).1 (dominatesB_sound h hq)

end EvmYul.Venom.Category
