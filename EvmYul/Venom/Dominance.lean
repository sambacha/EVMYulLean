module

public import EvmYul.Venom.Cfg

public section

/-!
# Dominance in Venom control-flow graphs: a checked dominator tree and a strict-SSA check

A block `a` **dominates** a block `v` when every path from the entry to `v` passes through `a`
(`Dominates`, defined from the paths themselves: there is no path from the entry to `v` that avoids
`a`, `ReachAvoid`). Venom's passes rely on dominance: a variable may be used only where its
definition dominates the use (strict SSA), and φ sources must be defined on the incoming edge.

**Design: compute untrusted, check proved.** `computeDomTree` computes immediate dominators with the
classic iterative data-flow equations (`Dom(v) = {v} ∪ ⋂ Dom(p)` over the predecessors). It is not
trusted. `checkTree` checks the result as a **certificate** in one pass over the edges:

1. the entry has no parent;
2. for every edge `u → v` out of a tree node `u` (the entry, or a block with a parent), `v` is the
   entry or has a parent `p`, and `p` is an ancestor-or-self of `u` in the tree.

**Theorem** (`checkTree_sound`). If `checkTree` accepts, every tree ancestor of a block dominates it.
The proof is an induction on the paths that avoid the ancestor: such a path stays inside the tree and
never reaches a block below the ancestor, because each edge lands below the parent of its target,
which is above its source. `dominatesB` is the executable query (`dominatesB_sound`).

**Strict SSA** (`checkSSA`, `checkSSA_sound`). Every variable has one definition; every use in an
ordinary instruction is defined earlier in the same block or in a block that dominates it; every φ
source for a predecessor `p` is defined in a block that dominates `p`. With an accepted tree, the
theorem gives the dominance facts for every use.
-/

namespace EvmYul.Venom.Dominance

open EvmYul.Venom.Cfg

/-! ## Paths and dominance -/

/-- An edge `u → v`: `v` is a successor of the block labelled `u` (the block `run` executes). -/
@[expose] def Edge (f : Func) (u v : Label) : Prop := ∃ b, f.find? u = some b ∧ v ∈ b.succs

@[expose] section

/-- `ReachAvoid f a v`: there is a path from the entry to `v` on which `a` never occurs. -/
inductive ReachAvoid (f : Func) (a : Label) : Label → Prop where
  /-- The entry, if it is not `a`. -/
  | entry : f.entry ≠ a → ReachAvoid f a f.entry
  /-- Extend a path by an edge to a block other than `a`. -/
  | step {u v : Label} : ReachAvoid f a u → Edge f u v → v ≠ a → ReachAvoid f a v

end

/-- **Dominance**: every path from the entry to `v` passes through `a`. -/
@[expose] def Dominates (f : Func) (a v : Label) : Prop := ¬ ReachAvoid f a v

theorem ReachAvoid.entry_ne {f : Func} {a w : Label} (h : ReachAvoid f a w) : f.entry ≠ a := by
  induction h <;> assumption

/-- The entry dominates every block (every path starts at the entry). -/
theorem entry_dominates (f : Func) (v : Label) : Dominates f f.entry v :=
  fun h => h.entry_ne rfl

/-- Every block dominates itself. -/
theorem dominates_refl (f : Func) (v : Label) : Dominates f v v := by
  intro h; cases h <;> simp_all

/-! ## Dominator trees -/

@[expose] section

/-- `TreeAnc parent a v`: `a` is `v` or an ancestor of `v` in the tree given by `parent`. -/
inductive TreeAnc (parent : Label → Option Label) (a : Label) : Label → Prop where
  /-- Every node is its own ancestor-or-self. -/
  | refl : TreeAnc parent a a
  /-- An ancestor of the parent is an ancestor. -/
  | up {v p : Label} : parent v = some p → TreeAnc parent a p → TreeAnc parent a v

end

theorem TreeAnc.trans {parent : Label → Option Label} {a b c : Label}
    (h₁ : TreeAnc parent a b) (h₂ : TreeAnc parent b c) : TreeAnc parent a c := by
  induction h₂ with
  | refl => exact h₁
  | up hp _ ih => exact .up hp ih

@[expose] section

/-- A dominator tree as a certificate: the parent (immediate dominator) of every non-entry node. -/
structure DomTree where
  /-- `(v, idom v)` pairs. -/
  idom : List (Label × Label)
  deriving Repr, DecidableEq

end

/-- The parent of a node. -/
@[expose] def DomTree.parent (t : DomTree) (v : Label) : Option Label := t.idom.lookup v

/-- `v` and its ancestors, following at most `n` parent links. -/
@[expose] def ancestors (parent : Label → Option Label) : Nat → Label → List Label
  | 0, v => [v]
  | n + 1, v => v :: match parent v with
    | some p => ancestors parent n p
    | none => []

theorem mem_ancestors {parent : Label → Option Label} {a : Label} :
    ∀ (n : Nat) (v : Label), a ∈ ancestors parent n v → TreeAnc parent a v
  | 0, v, h => by simp only [ancestors, List.mem_singleton] at h; exact h ▸ .refl
  | n + 1, v, h => by
    simp only [ancestors, List.mem_cons] at h
    rcases h with rfl | h
    · exact .refl
    split at h
    · exact .up ‹_› (mem_ancestors n _ h)
    · simp at h

/-- The number of parent links followed by the checks (the tree has `|idom| + 1` nodes). -/
@[expose] def DomTree.depth (t : DomTree) : Nat := t.idom.length + 1

/-- **The certificate check.** The entry has no parent; every edge `u → v` out of a tree node lands
on the entry or on a node whose parent is an ancestor-or-self of `u`. -/
@[expose] def checkTree (f : Func) (t : DomTree) : Bool :=
  (t.parent f.entry).isNone &&
  (f.entry :: t.idom.map Prod.fst).all fun u =>
    match f.find? u with
    | none => true
    | some b => b.succs.all fun v =>
        decide (v = f.entry) ||
          match t.parent v with
          | some p => decide (p ∈ ancestors t.parent t.depth u)
          | none => false

/-- The executable dominance query: is `a` an ancestor-or-self of `v` in the tree? -/
@[expose] def dominatesB (t : DomTree) (a v : Label) : Bool :=
  decide (a ∈ ancestors t.parent t.depth v)

private theorem lookup_some_mem {l : List (Label × Label)} {v p : Label}
    (h : l.lookup v = some p) : v ∈ l.map Prod.fst := by
  induction l with
  | nil => simp [List.lookup] at h
  | cons kv rest ih =>
    by_cases hk : v = kv.1
    · simp [hk]
    · rw [List.lookup, beq_false_of_ne hk] at h; exact .tail _ (ih h)

/-- **Soundness of the certificate check**: if `checkTree` accepts, every tree ancestor-or-self of a
block dominates it. -/
theorem checkTree_sound {f : Func} {t : DomTree} (h : checkTree f t = true) {a v : Label}
    (hav : TreeAnc t.parent a v) : Dominates f a v := by
  simp only [checkTree, Bool.and_eq_true, Option.isNone_iff_eq_none, List.all_eq_true] at h
  obtain ⟨hroot, hedges⟩ := h
  -- an ancestor of the entry is the entry
  have anc_entry : ∀ w, TreeAnc t.parent a w → w = f.entry → a = f.entry := by
    rintro w (_ | ⟨hp, _⟩) rfl
    · rfl
    · simp [hroot] at hp
  -- a path avoiding `a` stays in the tree and never reaches a node below `a`
  have key : ∀ w, ReachAvoid f a w →
      (w = f.entry ∨ (t.parent w).isSome) ∧ ¬ TreeAnc t.parent a w := by
    intro w hw
    induction hw with
    | entry hne => exact ⟨.inl rfl, fun hc => hne (anc_entry _ hc rfl).symm⟩
    | @step u v' hu he hva ih =>
      obtain ⟨hin, hnot⟩ := ih
      obtain ⟨b, hb, hv⟩ := he
      have hudom : u ∈ f.entry :: t.idom.map Prod.fst := by
        rcases hin with rfl | hs
        · exact List.mem_cons_self
        · obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 hs
          exact .tail _ (lookup_some_mem hp)
      have hv' := hedges u hudom
      rw [hb, List.all_eq_true] at hv'
      replace hv' := hv' v' hv
      by_cases hve : v' = f.entry
      · subst hve
        exact ⟨.inl rfl, fun hc => hu.entry_ne (anc_entry _ hc rfl).symm⟩
      simp only [hve, decide_false, Bool.false_or] at hv'
      rcases hp : t.parent v' with _ | p <;> simp only [hp] at hv'
      · simp at hv'
      refine ⟨.inr (by simp), fun hc => ?_⟩
      rcases hc with _ | ⟨hp', hap⟩
      · exact hva rfl
      · rw [hp] at hp'; cases hp'
        exact hnot (hap.trans (mem_ancestors _ _ (of_decide_eq_true hv')))
  exact fun hr => (key v hr).2 hav

/-- **Soundness of the dominance query** under an accepted certificate. -/
theorem dominatesB_sound {f : Func} {t : DomTree} (h : checkTree f t = true) {a v : Label}
    (hq : dominatesB t a v = true) : Dominates f a v :=
  checkTree_sound h (mem_ancestors _ _ (of_decide_eq_true hq))

/-! ## Strict SSA -/

/-- The definition site of a variable: the label of the first block defining it and the index of the
instruction there. -/
@[expose] def defSite (f : Func) (x : Var) : Option (Label × Nat) :=
  f.blocks.findSome? fun b =>
    (b.insts.zipIdx.find? fun (i, _) => decide (x ∈ i.outs)).map fun (_, k) => (b.label, k)

/-- The variables among a list of operands. -/
@[expose] def varsOf (args : List Operand) : List Var :=
  args.filterMap fun | .var x => some x | _ => none

/-- The `(predecessor, variable)` source pairs of a φ's operands `@p₁, a₁, @p₂, a₂, …`. -/
@[expose] def phiVarSources : List Operand → List (Label × Var)
  | .lbl p :: .var x :: rest => (p, x) :: phiVarSources rest
  | _ :: _ :: rest => phiVarSources rest
  | _ => []

/-- A use of `x` at instruction `k` of block `l` is covered: `x` is defined earlier in `l`, or in
another block that is a tree ancestor of `l`. (A definition later in the same block is not
covered, even though every block dominates itself.) -/
@[expose] def useOk (f : Func) (t : DomTree) (l : Label) (k : Nat) (x : Var) : Bool :=
  match defSite f x with
  | some (d, j) => if d = l then decide (j < k) else dominatesB t d l
  | none => false

/-- **The strict-SSA check**: one definition per variable; ordinary uses covered by `useOk` (defined earlier in the block, or in another block that is a tree
ancestor); every φ
variable source for predecessor `p` defined in a tree ancestor-or-self of `p`. -/
@[expose] def checkSSA (f : Func) (t : DomTree) : Bool :=
  decide ((f.blocks.flatMap fun b => b.insts.flatMap (·.outs)).Nodup) &&
  f.blocks.all fun b => b.insts.zipIdx.all fun (i, k) =>
    if i.op = .phi then
      (phiVarSources i.args).all fun (p, x) =>
        match defSite f x with
        | some (d, _) => dominatesB t d p
        | none => false
    else (varsOf i.args).all (useOk f t b.label k)

/-- **Soundness of the strict-SSA check.** With an accepted dominator tree, every variable used by an
ordinary instruction (at index `k` of block `b`) has a definition site `(d, j)` that is earlier in the
same block or in another block that dominates `b`; every φ source for predecessor `p` is defined in a block
that dominates `p`. -/
theorem checkSSA_sound {f : Func} {t : DomTree} (ht : checkTree f t = true)
    (hs : checkSSA f t = true) {b : Block} (hb : b ∈ f.blocks) {i : Inst} {k : Nat}
    (hik : (i, k) ∈ b.insts.zipIdx) :
    (i.op ≠ .phi → ∀ x ∈ varsOf i.args, ∃ d j, defSite f x = some (d, j) ∧
        ((d = b.label ∧ j < k) ∨ (d ≠ b.label ∧ Dominates f d b.label))) ∧
    (i.op = .phi → ∀ p x, (p, x) ∈ phiVarSources i.args →
        ∃ d j, defSite f x = some (d, j) ∧ Dominates f d p) := by
  simp only [checkSSA, Bool.and_eq_true, List.all_eq_true] at hs
  have hi := hs.2 b hb (i, k) hik
  refine ⟨fun hop x hx => ?_, fun hop p x hpx => ?_⟩
  · simp only [hop, if_false, List.all_eq_true] at hi
    have hu := hi x hx
    simp only [useOk] at hu
    split at hu
    · refine ⟨_, _, ‹_›, ?_⟩
      split at hu
      · exact .inl ⟨‹_›, of_decide_eq_true hu⟩
      · exact .inr ⟨‹_›, dominatesB_sound ht hu⟩
    · simp at hu
  · simp only [hop, if_true, List.all_eq_true] at hi
    have hu := hi (p, x) hpx
    split at hu
    · exact ⟨_, _, ‹_›, dominatesB_sound ht hu⟩
    · simp at hu

/-! ## Computing the tree (untrusted) -/

/-- The successors of block `u` (none if there is no such block). -/
@[expose] def succsOf (f : Func) (u : Label) : List Label := ((f.find? u).map Block.succs).getD []

/-- The blocks reachable from the entry (breadth first, at most `|blocks| + 1` rounds). -/
@[expose] def reachable (f : Func) : List Label :=
  let step (seen : List Label) : List Label :=
    seen ++ ((seen.flatMap (succsOf f)).filter (· ∉ seen)).eraseDups
  (List.range (f.blocks.length + 1)).foldl (fun s _ => step s) [f.entry]

/-- The reachable predecessors of `v`. -/
@[expose] def predsOf (f : Func) (reach : List Label) (v : Label) : List Label :=
  reach.filter fun u => v ∈ succsOf f u

/-- The dominator sets by the iterative equations, from the full sets (at most `|reach| + 1`
rounds). -/
@[expose] def domSets (f : Func) : List (Label × List Label) :=
  let reach := reachable f
  let init := reach.map fun v => (v, if v = f.entry then [f.entry] else reach)
  let round (d : List (Label × List Label)) : List (Label × List Label) :=
    reach.map fun v =>
      if v = f.entry then (v, [f.entry]) else
      let ps := (predsOf f reach v).map fun p => (d.lookup p).getD reach
      let meet := match ps with
        | [] => []
        | s :: ss => s.filter fun x => ss.all (x ∈ ·)
      (v, if v ∈ meet then meet else v :: meet)
  (List.range (reach.length + 1)).foldl (fun d _ => round d) init

/-- **The immediate dominators (untrusted).** For each reachable `v` other than the entry, the
strict dominator with the most dominators of its own (the closest one). Check with `checkTree`. -/
@[expose] def computeDomTree (f : Func) : DomTree :=
  let ds := domSets f
  let size (x : Label) := ((ds.lookup x).getD []).length
  ⟨ds.filterMap fun (v, dv) =>
    if v = f.entry then none else
    (dv.filter (· ≠ v)).foldl (fun best x => match best with
      | some y => if size y < size x then some x else some y
      | none => some x) none |>.map (v, ·)⟩

/-- The dominator tree of a function, computed and then checked: `some t` only if `checkTree`
accepts `t`, so `checkTree_sound` applies to it. -/
@[expose] def domTree? (f : Func) : Option DomTree :=
  let t := computeDomTree f
  if checkTree f t then some t else none

end EvmYul.Venom.Dominance
