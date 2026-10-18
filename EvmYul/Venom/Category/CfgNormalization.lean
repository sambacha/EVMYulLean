module

public import EvmYul.Venom.Dominance

public section

/-!
# Critical-edge splitting on Venom functions (an executable CFGNormalization)

An executable counterpart of Vyper's `CFGNormalization` pass (`vyper/venom/passes/
cfg_normalization.py` at `15e442d`) on the CFG layer:

* `criticalEdges f`: the edges `p → b` with more than one successor *label* at `p` and more than
  one predecessor *label* at `b` (Vyper's `cfg_out` / `cfg_in` are sets, so the parallel slots of
  `jnz c, @a, @a` count once);
* `normalize f`: for each critical edge, a new block `p_split_b` holding `jmp @b`; `p`'s terminator
  names it instead of `b`, and `b`'s φs read their operand for `p` from it (Vyper also forwards
  φ-defined variables through an `assign` in the split block; in this layer environments are
  global and the split block changes none, so no copy is needed).

Abstractly this is the edge subdivision of `Normalization.lean`, restricted to the critical edges.
`CfgNormalizationTests.lean` checks on random functions that `normalize` leaves no critical edge
and does not change `run`'s results (with twice the fuel), and on recorded Vyper output.
-/

namespace EvmYul.Venom.Category

open EvmYul.Venom.Cfg EvmYul.Venom.Dominance

/-- The successor labels of block `u`, without repetition (Vyper's `cfg_out`). -/
@[expose] def succSet (f : Func) (u : Label) : List Label := (succsOf f u).eraseDups

/-- The predecessor labels of block `v`, without repetition (Vyper's `cfg_in`). -/
@[expose] def predSet (f : Func) (v : Label) : List Label :=
  ((f.blocks.filter fun b => v ∈ b.succs).map (·.label)).eraseDups

/-- The critical edges `p → b` (as label pairs). -/
@[expose] def criticalEdges (f : Func) : List (Label × Label) :=
  f.blocks.flatMap fun b =>
    ((succSet f b.label).filter fun v =>
      decide ((succSet f b.label).length > 1) && decide ((predSet f v).length > 1)).map
      (b.label, ·)

/-- D1.3 as written, decided: no block with more than one predecessor and more than one
successor. -/
@[expose] def vertexNormalB (f : Func) : Bool :=
  f.blocks.all fun b => !(decide ((predSet f b.label).length > 1) &&
    decide ((succSet f b.label).length > 1))

/-- The label of the block that splits `p → b` (Vyper's naming). -/
@[expose] def splitLabel (p b : Label) : Label := p ++ "_split_" ++ b

/-- Replace the label `old` by `new` among the operands of an instruction. -/
@[expose] def relabel (old new : Label) (i : Inst) : Inst :=
  { i with args := i.args.map fun o => match o with
    | .lbl l => if l = old then .lbl new else .lbl l
    | o => o }

/-- Split the edge `p → b`. -/
@[expose] def splitEdge (f : Func) (pb : Label × Label) : Func :=
  let (p, b) := pb
  let s := splitLabel p b
  let blocks := f.blocks.map fun blk =>
    let blk := if blk.label = p then
      { blk with insts := match blk.insts.reverse with
        | [] => []
        | t :: rest => (relabel b s t :: rest).reverse }
      else blk
    if blk.label = b then
      { blk with insts := blk.insts.map fun i => if i.op = .phi then relabel p s i else i }
    else blk
  { f with blocks := blocks ++ [⟨s, [⟨.jmp, [.lbl b], []⟩]⟩] }

/-- **CFG normalization**: split every critical edge. -/
@[expose] def normalize (f : Func) : Func := (criticalEdges f).foldl splitEdge f

end EvmYul.Venom.Category
