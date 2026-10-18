module

public import EvmYul.ProofTags

public section

/-!
# Venom control-flow graphs: blocks, φ as a parallel copy, fuel semantics and refinement

The straight-line fragment (`Syntax.lean`, `Semantics.lean`) covers one basic block. This module
covers the graph: functions made of labelled blocks, with `jmp`/`jnz` between them and φ
instructions at block entry. It is the root-level sketch `Venom.lean` turned into a library
module, with the corrections that its review found (`docs/VENOM_LOWERING_PLAN.md`):

* **Kept as written.** The raw substrate (`Inst`, `Block`, `Func`), the abstract machine interface
  `EvmInterface`, φ as a parallel copy read from the environment at block entry (`applyPhis`), the
  fuel-indexed semantics `run`, the refinement relation `Refines` with `Refines.trans`, and the
  translation-validation interface `Validator` with `Validator.chain_sound`.
* **Proved here (induction).** More fuel never changes a result that is not `fuelOut`
  (`run_stable`), so two fuels that both finish agree (`run_det`). This is what makes the
  existential fuel in `Refines` meaningful: the target's answer does not depend on the fuel chosen.
* **Falsified in `CfgTests.lean`** (each with a proved counterexample):
  1. `Refines` quantifies over **every** `EvmInterface`, including ones where `add` is not addition
     and `assign` is not a copy. So it rejects constant folding and φ elimination, and no checker for
     those passes can be a `Validator`.
  2. `Refines` is silent on runs that never finish, so a loop that runs forever "refines" to `stop`.
  3. `Func.check` accepts blocks that `run` can never execute (`djmp`, wrong `jnz` arity, a
     terminator in the middle of a block, φ after an ordinary instruction). Such a function faults,
     and a faulting source is refined by **every** target, so a validator that relies on
     `Func.check` accepts any output for it.
* **Corrections.** `RefinesIn` fixes the machine interface, so passes that rely on what `add` or
  `assign` mean can be correct. `RefinesTotal` also requires that a run that never finishes stays
  that way. `Func.wf` is a stricter checker whose blocks have exactly the shape that `runBlock`
  executes (`Block.wf_body`).

**Additions for real Vyper output.** `Op` has the instructions of the recorded Vyper 0.4.3 output
that the sketch lacked (`xor`, `shr`, `calldataload`, `codecopy`, …), `assert` (a non-terminator
that reverts on zero, executed by `runPlain`, not by the machine) and the EVM `return`
(`evmReturn`, a halting terminator).

**`djmp` (§7).** With label addresses (`LabelAddr`, the code offsets of the blocks) a label used
as a value denotes its address and `djmp c, @l₁, …, @lₙ` goes to the listed label whose address is
the value of `c` (`runL`, `execTermL_djmp_iff`). Without addresses `runL` is `run` (`runL_noAddr`).

The interface `EvmInterface` stays abstract here; `EvmMachine.lean` instantiates it with the
project's EVM (`evmInterface`, through `exceptionalHalt` and `EVM.step`), and its tests run CFG
functions with loops, φs and `assert` on it.
-/

namespace EvmYul.Venom.Cfg

/-! ## 1. Raw substrate -/

/-- A Venom value: a 256-bit word. -/
@[expose] abbrev Word := BitVec 256
/-- A variable name (`%x` in Venom text, without the `%`). -/
@[expose] abbrev Var := String
/-- A block label (`@l` in Venom text, without the `@`). -/
@[expose] abbrev Label := String

@[expose] section

/-- An instruction operand: a literal word, a variable, or a label (jump targets and φ sources). -/
inductive Operand where
  /-- A literal word. -/
  | lit (w : Word)
  /-- A variable. -/
  | var (v : Var)
  /-- A label. -/
  | lbl (l : Label)
  deriving Repr, DecidableEq

end

@[expose] section

/-- The opcodes: the copy `assign`, φ, machine operations, `assert`, and the terminators. The first
19 are the sketch's; the rest are the instructions of the real Vyper 0.4.3 output
(`docs/research/venom/store_bb_runtime_0.4.3.txt`) and of the straight-line fragment that the
sketch lacked, so that real output can be parsed (`Text.lean`) and run on the EVM
(`EvmMachine.lean`). `evmReturn` is the EVM `return ofs, len`; `ret` is Venom's internal return. -/
inductive Op where
  | assign | phi | add | sub | mul | lt | iszero
  | mload | mstore | sload | sstore
  | jmp | jnz | djmp | ret | stop | revert | invoke | alloca
  | div | mod | and | or | xor | shl | shr | gt | eq
  | calldataload | calldatasize | callvalue | codecopy
  | assert | evmReturn
  deriving Repr, DecidableEq

end

@[expose] section

/-- An instruction: opcode, operands and the variables it defines. -/
structure Inst where
  /-- The opcode. -/
  op : Op
  /-- The operands, in Venom text order. -/
  args : List Operand
  /-- The variables defined (none, one, or several for multi-output instructions). -/
  outs : List Var
  deriving Repr

end

@[expose] section

/-- A basic block: φs first, the terminator last. -/
structure Block where
  /-- The block's label. -/
  label : Label
  /-- The instructions. -/
  insts : List Inst
  deriving Repr

end

@[expose] section

/-- A function: its entry label and its blocks. -/
structure Func where
  /-- The function's name. -/
  name : String
  /-- The label of the entry block. -/
  entry : Label
  /-- The blocks. -/
  blocks : List Block
  deriving Repr

end

/-- Terminator opcodes. -/
@[expose] def Op.isTerm : Op → Bool
  | .jmp | .jnz | .djmp | .ret | .stop | .revert | .evmReturn => true
  | _ => false

/-- The block's terminator: its last instruction, if that is a terminator. -/
@[expose] def Block.term? (b : Block) : Option Inst :=
  match b.insts.getLast? with
  | some i => if i.op.isTerm then some i else none
  | none => none

/-- The labels among an instruction's operands. -/
@[expose] def Inst.targets (i : Inst) : List Label :=
  i.args.filterMap fun | .lbl l => some l | _ => none

/-- The successor labels of a block (the labels of its terminator). -/
@[expose] def Block.succs (b : Block) : List Label := (b.term?.map Inst.targets).getD []

/-- The leading φ instructions of a block. -/
@[expose] def Block.phis (b : Block) : List Inst := b.insts.takeWhile (·.op == .phi)

/-- The instructions between the leading φs and the terminator: what `runBlock` executes as
ordinary instructions. -/
@[expose] def Block.body (b : Block) : List Inst := (b.insts.drop b.phis.length).dropLast

/-- The block with label `l`. -/
@[expose] def Func.find? (f : Func) (l : Label) : Option Block := f.blocks.find? (·.label == l)

/-- The structural check of the sketch: the entry block exists, and every block ends in a terminator
whose labels exist. (Falsified as a guard for `run` in `CfgTests.lean`; see `Func.wf`.) -/
@[expose] def Func.check (f : Func) : Bool :=
  (f.find? f.entry).isSome &&
  f.blocks.all fun b => b.term?.isSome && b.succs.all fun l => (f.find? l).isSome

/-! ## 2. The machine interface -/

/-- The machine operations, abstractly: the only point where an EVM model enters. `exec op args s`
is the result values and new state, or `none` for a fault. -/
class EvmInterface (σ : Type) where
  /-- Semantics of a non-control-flow opcode over the machine state. -/
  exec : Op → List Word → σ → Option (List Word × σ)

/-- Variable environment. -/
@[expose] abbrev Env := Var → Option Word
/-- The empty environment. -/
@[expose] def Env.empty : Env := fun _ => none
/-- `e` with `v := w`. -/
@[expose] def Env.set (e : Env) (v : Var) (w : Word) : Env := fun x => if x = v then some w else e x

/-- The value of an operand; a label has none. -/
@[expose] def evalOp (e : Env) : Operand → Option Word
  | .lit w => some w
  | .var v => e v
  | .lbl _ => none

/-- The φ source for predecessor `prev`, from Venom's φ syntax `%x = phi @p1, %a, @p2, %b`. -/
@[expose] def phiPick (prev : Label) : List Operand → Option Operand
  | .lbl l :: v :: rest => if l = prev then some v else phiPick prev rest
  | _ => none

/-! ## 3. Fuel-indexed semantics -/

@[expose] section

/-- Where a block goes next. -/
inductive Next where
  | goto (l : Label) | halt | revert

end

@[expose] section

/-- The result of a run. -/
inductive Result (σ : Type) where
  | halted (s : σ) | reverted (s : σ) | fault | fuelOut

end

/-- A run finished normally (`halted` or `reverted`). -/
@[expose] def Result.IsTerminal {σ : Type} : Result σ → Prop
  | .halted _ | .reverted _ => True
  | _ => False

section
variable {σ : Type} [EvmInterface σ]

/-- The φs of a block as a **parallel** copy: every source is read from `old`, the environment at
block entry, never from the copies already made. -/
@[expose] def applyPhis (prev : Label) (old : Env) (phis : List Inst) : Option Env :=
  phis.foldlM (init := old) fun acc i => do
    let src ← phiPick prev i.args
    let w ← evalOp old src
    match i.outs with
    | [x] => pure (acc.set x w)
    | _ => none

/-- One ordinary instruction through the machine interface. -/
@[expose] def execPlain (env : Env) (s : σ) (i : Inst) : Option (Env × σ) := do
  let ws ← i.args.mapM (evalOp env)
  let (outs, s') ← EvmInterface.exec i.op ws s
  if outs.length = i.outs.length then
    pure ((i.outs.zip outs).foldl (fun e (x, w) => e.set x w) env, s')
  else none

/-- A terminator; `djmp`, `invoke` and malformed operand lists have no semantics here (`none`);
§7 gives `djmp` its meaning with label addresses (`execTermL`). -/
@[expose] def execTerm (env : Env) (i : Inst) : Option Next :=
  match i.op, i.args with
  | .jmp, [.lbl l] => some (.goto l)
  | .jnz, [c, .lbl t, .lbl e] => do
      let w ← evalOp env c
      some (.goto (if w = 0 then e else t))
  | .stop, _ => some .halt
  | .ret, _ => some .halt
  | .evmReturn, _ => some .halt
  | .revert, _ => some .revert
  | _, _ => none

end

@[expose] section

/-- How the ordinary instructions of a block end: normally, or at a failed `assert`. -/
inductive BodyEnd (σ : Type) where
  /-- All instructions ran. -/
  | cont (env : Env) (s : σ)
  /-- An `assert` saw zero: the run reverts in state `s`. -/
  | abort (s : σ)

end

section
variable {σ : Type} [EvmInterface σ]

/-- The ordinary instructions of a block. `assert a` is not sent to the machine interface: it ends
the block with a revert when `a` is zero (Venom's `assert`, which reverts without being a
terminator), and does nothing otherwise. Every other instruction goes through `execPlain`. -/
@[expose] def runPlain (env : Env) (s : σ) : List Inst → Option (BodyEnd σ)
  | [] => some (.cont env s)
  | i :: is =>
    if i.op = .assert then
      match i.args with
      | [a] => do
        let c ← evalOp env a
        if c = 0 then some (.abort s) else runPlain env s is
      | _ => none
    else do
      let (env', s') ← execPlain env s i
      runPlain env' s' is

/-- One block entered from `prev`: the φs, then the body, then the terminator. -/
@[expose] def runBlock (b : Block) (prev : Label) (env : Env) (s : σ) : Option (Next × Env × σ) := do
  let env ← applyPhis prev env b.phis
  let term ← b.term?
  match ← runPlain env s b.body with
  | .abort s' => pure (.revert, env, s')
  | .cont env s =>
    let n ← execTerm env term
    pure (n, env, s)

/-- Run a function for at most `fuel` blocks. -/
@[expose] def run (f : Func) : Nat → Label → Label → Env → σ → Result σ
  | 0, _, _, _, _ => .fuelOut
  | n + 1, prev, cur, env, s =>
    match f.find? cur with
    | none => .fault
    | some b =>
      match runBlock b prev env s with
      | none => .fault
      | some (.goto l, env', s') => run f n cur l env' s'
      | some (.halt, _, s') => .halted s'
      | some (.revert, _, s') => .reverted s'

/-- **Fuel monotonicity** (induction on the fuel): a result other than `fuelOut` does not change
when more fuel is given. -/
theorem run_stable (f : Func) :
    ∀ (n k : Nat) (prev cur : Label) (env : Env) (s : σ),
      run f n prev cur env s ≠ .fuelOut → run f (n + k) prev cur env s = run f n prev cur env s
  | 0, _, _, _, _, _, h => absurd rfl h
  | n + 1, k, prev, cur, env, s, h => by
    rw [show n + 1 + k = (n + k) + 1 by omega]
    simp only [run] at h ⊢
    split <;> try rfl
    split <;> try rfl
    rename_i hf _ l env' s' hb
    simp only [hf, hb] at h
    exact run_stable f n k cur l env' s' h

/-- **Determinism across fuels**: two runs that both finish (or both fault) agree. -/
theorem run_det (f : Func) {n m : Nat} {prev cur : Label} {env : Env} {s : σ}
    (hn : run f n prev cur env s ≠ .fuelOut) (hm : run f m prev cur env s ≠ .fuelOut) :
    run f n prev cur env s = run f m prev cur env s := by
  rcases Nat.le_total n m with h | h <;> obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  · exact (run_stable f n k prev cur env s hn).symm
  · exact run_stable f m k prev cur env s hm
end

/-! ## 4. Refinement -/

/-- The sketch's refinement: for **every** machine interface, every finished run of `src` is a
finished run of `tgt`. (Too strong for most passes; falsified in `CfgTests.lean`.) -/
@[expose] def Refines (src tgt : Func) : Prop :=
  ∀ (σ : Type) [EvmInterface σ] (fuel : Nat) (s : σ) (r : Result σ),
    run src fuel "" src.entry Env.empty s = r → r.IsTerminal →
    ∃ fuel', run tgt fuel' "" tgt.entry Env.empty s = r

theorem Refines.refl (f : Func) : Refines f f :=
  fun _ _ fuel _ _ h _ => ⟨fuel, h⟩

/-- Refinement composes. -/
theorem Refines.trans {a b c : Func} (h₁ : Refines a b) (h₂ : Refines b c) : Refines a c :=
  fun σ _ fuel s r hr ht => let ⟨f₁, hb⟩ := h₁ σ fuel s r hr ht; h₂ σ f₁ s r hb ht

/-- A translation validator: an executable check of a pass's input and output, proved sound for
`Refines`. -/
structure Validator where
  /-- The check. -/
  check : Func → Func → Bool
  /-- Soundness. -/
  sound : ∀ a b, check a b = true → Refines a b

/-- A pipeline trace `f₀ → f₁ → … → fₙ` is accepted iff every adjacent pair is. -/
@[expose] def Validator.chain (v : Validator) : List Func → Bool
  | a :: b :: rest => v.check a b && v.chain (b :: rest)
  | _ => true

/-- An accepted pipeline trace refines from its first to its last function (induction on the
trace). -/
theorem Validator.chain_sound (v : Validator) :
    ∀ (a b : Func) (rest : List Func), v.chain (a :: b :: rest) = true →
      Refines a ((b :: rest).getLast (List.cons_ne_nil _ _)) := by
  intro a b rest h
  induction rest generalizing a b with
  | nil => exact v.sound a b (by simpa [Validator.chain] using h)
  | cons c rest ih =>
    rw [Validator.chain, Bool.and_eq_true] at h
    simpa using (v.sound a b h.1).trans (ih b c h.2)

/-! ## 5. Corrected refinement: a fixed machine, and divergence kept -/

section
variable {σ : Type} [EvmInterface σ]

/-- The run of `f` from its entry, empty environment, state `s`. -/
@[expose] def runEntry (f : Func) (fuel : Nat) (s : σ) : Result σ :=
  run f fuel "" f.entry Env.empty s

/-- Refinement for **one** machine interface (the instance in scope): every finished run of `src`
is a finished run of `tgt`. -/
@[expose] def RefinesIn (src tgt : Func) : Prop :=
  ∀ (fuel : Nat) (s : σ) (r : Result σ), runEntry src fuel s = r → r.IsTerminal →
    ∃ fuel', runEntry tgt fuel' s = r

/-- `f` never finishes from state `s`: every fuel runs out. -/
@[expose] def Diverges (f : Func) (s : σ) : Prop := ∀ fuel, runEntry f fuel s = .fuelOut

/-- `RefinesIn`, and a source that never finishes gives a target that never finishes. -/
@[expose] def RefinesTotal (src tgt : Func) : Prop :=
  RefinesIn (σ := σ) src tgt ∧ ∀ s : σ, Diverges src s → Diverges tgt s

theorem RefinesIn.trans {a b c : Func} (h₁ : RefinesIn (σ := σ) a b)
    (h₂ : RefinesIn (σ := σ) b c) : RefinesIn (σ := σ) a c :=
  fun fuel s r hr ht => let ⟨f₁, hb⟩ := h₁ fuel s r hr ht; h₂ f₁ s r hb ht

theorem RefinesTotal.trans {a b c : Func} (h₁ : RefinesTotal (σ := σ) a b)
    (h₂ : RefinesTotal (σ := σ) b c) : RefinesTotal (σ := σ) a c :=
  ⟨h₁.1.trans h₂.1, fun s hs => h₂.2 s (h₁.2 s hs)⟩

/-- The sketch's `Refines` implies `RefinesIn` for every machine interface. -/
theorem Refines.toRefinesIn {src tgt : Func} (h : Refines src tgt) :
    RefinesIn (σ := σ) src tgt :=
  fun fuel s r hr ht => h σ fuel s r hr ht

end

/-! ## 6. A checker with the shape `runBlock` executes -/

/-- A φ instruction that `applyPhis` can execute for some predecessor: one output, and operands
in `@label, value` pairs. -/
@[expose] def Inst.phiShapeOk (i : Inst) : Bool :=
  i.op == .phi && i.outs.length == 1 && i.args.length % 2 == 0 &&
    (i.args.zipIdx.all fun (a, k) => match a with
      | .lbl _ => k % 2 == 0
      | _ => k % 2 == 1)

/-- A terminator that `execTerm` executes: `jmp @l`, `jnz c, @t, @e`, `stop`, `ret`, `revert`.
(`djmp` is not executed by `run`, so it is rejected rather than accepted and left to fault.) -/
@[expose] def Inst.termShapeOk (i : Inst) : Bool :=
  match i.op, i.args with
  | .jmp, [.lbl _] => true
  | .jnz, [.lbl _, .lbl _, .lbl _] => false
  | .jnz, [_, .lbl _, .lbl _] => true
  | .stop, _ | .ret, _ | .revert, _ | .evmReturn, _ => true
  | _, _ => false

/-- The shape of a block: a terminator last, the φs exactly the leading instructions with
pairwise different outputs, and a body with no φ and no terminator. -/
@[expose] def Block.wf (b : Block) : Bool :=
  (match b.term? with | some t => t.termShapeOk | none => false) &&
  b.phis.all Inst.phiShapeOk &&
  ((b.phis.map Inst.outs).flatten).Nodup &&
  b.body.all fun i => !i.op.isTerm && i.op != .phi && (i.op != .assert || i.args.length == 1)

/-- The stricter checker: `Func.check`, labels unique, and every block well shaped. -/
@[expose] def Func.wf (f : Func) : Bool :=
  f.check && (f.blocks.map (·.label)).Nodup && f.blocks.all Block.wf

/-- **Specification of `Block.wf` (body).** In a well-shaped block, the instructions that `runBlock`
passes to the machine interface contain no φ and no terminator. -/
theorem Block.wf_body {b : Block} (h : b.wf = true) :
    ∀ i ∈ b.body, i.op.isTerm = false ∧ i.op ≠ .phi ∧ (i.op = .assert → i.args.length = 1) := by
  simp only [Block.wf, Bool.and_eq_true, List.all_eq_true] at h
  intro i hi
  have := h.2 i hi
  simp only [Bool.not_eq_true', bne_iff_ne, ne_eq, Bool.or_eq_true, beq_iff_eq] at this
  exact ⟨this.1.1, this.1.2, fun ha => this.2.resolve_left (· ha)⟩

/-- **Specification of `Block.wf` (terminator).** A well-shaped block has a terminator, and
`execTerm` gives it a meaning in every environment where its condition is defined. -/
theorem Block.wf_term {b : Block} (h : b.wf = true) :
    ∃ t, b.term? = some t ∧ t.termShapeOk = true := by
  simp only [Block.wf, Bool.and_eq_true] at h
  obtain ⟨⟨⟨ht, _⟩, _⟩, _⟩ := h
  split at ht <;> first | exact ⟨_, ‹_›, ht⟩ | simp at ht

/-- `Func.wf` is stronger than the sketch's `Func.check`. -/
theorem Func.wf_check {f : Func} (h : f.wf = true) : f.check = true := by
  simp_all [Func.wf]

/-! ## 7. Label addresses and `djmp`

Real Vyper output dispatches on the function selector with `djmp %7, @selector_bucket_0,
@selector_bucket_1`, where `%7` is read from a jump table (`db @selector_bucket_0`) in the data
section. Sections 1–6 give `djmp` no meaning (`execTerm` faults) and evaluate a label operand to
nothing. This section adds **label addresses** (`LabelAddr`): a label used as a value denotes its
address, and `djmp c, @l₁, …, @lₙ` goes to the listed label whose address is the value of `c`.

* `runL_noAddr`: with no addresses the new semantics is `run` (a conservative extension).
* `execTermL_djmp_iff`: on labels with pairwise different addresses, `djmp` goes to `l` exactly
  when `l` is listed and its address is the value; `Func.addrOk` checks that hypothesis for a whole
  function (`Func.addrOk_djmp`).
* `runBlockL_goto_mem_succs`: a block only jumps to a label that it declares (`Block.succs`, the
  `OUT=[…]` list that Vyper prints), for every terminator, `djmp` included.
* `runL_stable`: fuel monotonicity, as `run_stable`.
* `Func.wfD`: `Func.wf` with `djmp` accepted; it accepts everything `Func.wf` accepts (`Func.wf_wfD`).
-/

/-- Label addresses: the word a label denotes when it is used as a value (`add @selector_buckets,
…`, a `db @l` entry of a data section, the value a `djmp` jumps to). On the EVM it is the code
offset of the block's `JUMPDEST`; here it is a parameter, so every result holds for every layout.
`none`: the label has no address. -/
@[expose] abbrev LabelAddr := Label → Option Word

/-- No label has an address: then the semantics with label addresses is `run` (`runL_noAddr`). -/
@[expose] def noAddr : LabelAddr := fun _ => none

/-- The value of an operand; a label denotes its address. -/
@[expose] def evalOpL (addr : LabelAddr) (e : Env) : Operand → Option Word
  | .lit w => some w
  | .var v => e v
  | .lbl l => addr l

/-- The target of `djmp w, @l₁, …, @lₙ`: the first listed label whose address is `w`; `none` if
there is none or a non-label operand comes first. -/
@[expose] def djmpPick (addr : LabelAddr) (w : Word) : List Operand → Option Label
  | [] => none
  | .lbl l :: rest => if addr l = some w then some l else djmpPick addr w rest
  | _ :: _ => none

section
variable {σ : Type} [EvmInterface σ]

/-- `applyPhis` with label addresses (a φ source may be a label). -/
@[expose] def applyPhisL (addr : LabelAddr) (prev : Label) (old : Env) (phis : List Inst) :
    Option Env :=
  phis.foldlM (init := old) fun acc i => do
    let src ← phiPick prev i.args
    let w ← evalOpL addr old src
    match i.outs with
    | [x] => pure (acc.set x w)
    | _ => none

/-- `execPlain` with label addresses (an operand may be a label). -/
@[expose] def execPlainL (addr : LabelAddr) (env : Env) (s : σ) (i : Inst) : Option (Env × σ) := do
  let ws ← i.args.mapM (evalOpL addr env)
  let (outs, s') ← EvmInterface.exec i.op ws s
  if outs.length = i.outs.length then
    pure ((i.outs.zip outs).foldl (fun e (x, w) => e.set x w) env, s')
  else none

/-- A terminator with label addresses: `djmp c, @l₁, …, @lₙ` goes to the listed label whose address
is the value of `c` (`djmpPick`), and faults if there is none; the other terminators are
`execTerm`'s (so a `jnz` condition is never a label). -/
@[expose] def execTermL (addr : LabelAddr) (env : Env) (i : Inst) : Option Next :=
  if i.op = .djmp then
    match i.args with
    | c :: ts => do
      let w ← evalOpL addr env c
      let l ← djmpPick addr w ts
      some (.goto l)
    | [] => none
  else execTerm env i

/-- `runPlain` with label addresses. -/
@[expose] def runPlainL (addr : LabelAddr) (env : Env) (s : σ) : List Inst → Option (BodyEnd σ)
  | [] => some (.cont env s)
  | i :: is =>
    if i.op = .assert then
      match i.args with
      | [a] => do
        let c ← evalOpL addr env a
        if c = 0 then some (.abort s) else runPlainL addr env s is
      | _ => none
    else do
      let (env', s') ← execPlainL addr env s i
      runPlainL addr env' s' is

/-- `runBlock` with label addresses. -/
@[expose] def runBlockL (addr : LabelAddr) (b : Block) (prev : Label) (env : Env) (s : σ) :
    Option (Next × Env × σ) := do
  let env ← applyPhisL addr prev env b.phis
  let term ← b.term?
  match ← runPlainL addr env s b.body with
  | .abort s' => pure (.revert, env, s')
  | .cont env s =>
    let n ← execTermL addr env term
    pure (n, env, s)

/-- **The semantics with `djmp`**: `run` with label addresses. Run `f` for at most `fuel` blocks. -/
@[expose] def runL (addr : LabelAddr) (f : Func) : Nat → Label → Label → Env → σ → Result σ
  | 0, _, _, _, _ => .fuelOut
  | n + 1, prev, cur, env, s =>
    match f.find? cur with
    | none => .fault
    | some b =>
      match runBlockL addr b prev env s with
      | none => .fault
      | some (.goto l, env', s') => runL addr f n cur l env' s'
      | some (.halt, _, s') => .halted s'
      | some (.revert, _, s') => .reverted s'

theorem evalOpL_noAddr : evalOpL noAddr = evalOp := by
  funext e o; cases o <;> rfl

theorem applyPhisL_noAddr : applyPhisL noAddr = applyPhis := by
  funext prev old phis; simp only [applyPhisL, applyPhis, evalOpL_noAddr]

theorem execPlainL_noAddr : execPlainL (σ := σ) noAddr = execPlain := by
  funext env s i; simp only [execPlainL, execPlain, evalOpL_noAddr]

theorem djmpPick_noAddr (w : Word) : ∀ ts, djmpPick noAddr w ts = none
  | [] => rfl
  | .lbl _ :: rest => by simp [djmpPick, noAddr, djmpPick_noAddr w rest]
  | .lit _ :: _ => rfl
  | .var _ :: _ => rfl

theorem execTermL_noAddr : execTermL noAddr = execTerm := by
  funext env ⟨op, args, outs⟩
  simp only [execTermL]
  split <;> try rfl
  subst_vars
  cases args with
  | nil => rfl
  | cons c ts => cases evalOpL noAddr env c <;> simp [djmpPick_noAddr, execTerm]

theorem runPlainL_noAddr : runPlainL (σ := σ) noAddr = runPlain := by
  funext env s is
  induction is generalizing env s <;>
    simp only [runPlainL, runPlain, evalOpL_noAddr, execPlainL_noAddr, *]

theorem runBlockL_noAddr : runBlockL (σ := σ) noAddr = runBlock := by
  funext b prev env s
  simp only [runBlockL, runBlock, applyPhisL_noAddr, runPlainL_noAddr, execTermL_noAddr]

/-- **Conservativity** (induction on the fuel): with no label addresses, the semantics with `djmp`
is `run`. Every result about `run` is a result about `runL noAddr`. -/
theorem runL_noAddr (f : Func) :
    ∀ (n : Nat) (prev cur : Label) (env : Env) (s : σ),
      runL noAddr f n prev cur env s = run f n prev cur env s
  | 0, _, _, _, _ => rfl
  | n + 1, prev, cur, env, s => by
    unfold runL run
    rw [runBlockL_noAddr]
    rcases f.find? cur with _ | b; · rfl
    dsimp only
    rcases runBlock b prev env s with _ | ⟨_ | _ | _, env', s'⟩ <;> try rfl
    exact runL_noAddr f n _ _ _ _

/-- **`djmp` lands on a listed label whose address is the value** (soundness of `djmpPick`). -/
theorem djmpPick_sound (addr : LabelAddr) (w : Word) :
    ∀ {ts : List Operand} {l : Label}, djmpPick addr w ts = some l → .lbl l ∈ ts ∧ addr l = some w
  | [], _, h => by simp [djmpPick] at h
  | .lbl l' :: rest, l, h => by
    simp only [djmpPick] at h
    split at h
    · cases h; exact ⟨by simp, ‹_›⟩
    · exact (djmpPick_sound addr w h).imp_left (List.mem_cons_of_mem _)
  | .lit _ :: _, _, h => by simp [djmpPick] at h
  | .var _ :: _, _, h => by simp [djmpPick] at h

/-- **Completeness of `djmpPick`**: on labels whose addresses are pairwise different, every listed
label is reached through its own address. -/
theorem djmpPick_complete (addr : LabelAddr) :
    ∀ {ls : List Label} {l : Label} {w : Word},
      (∀ a ∈ ls, ∀ b ∈ ls, addr a = some w → addr b = some w → a = b) →
      l ∈ ls → addr l = some w → djmpPick addr w (ls.map .lbl) = some l
  | [], _, _, _, h, _ => by simp at h
  | a :: rest, l, w, hinj, hl, hw => by
    simp only [List.map_cons, djmpPick]
    split
    · exact congrArg some (hinj a (by simp) l hl ‹_› hw)
    · rename_i ha
      exact djmpPick_complete addr (fun x hx y hy => hinj x (.tail _ hx) y (.tail _ hy))
        ((List.mem_cons.mp hl).resolve_left fun h => ha (h ▸ hw)) hw

/-- A terminator of `execTerm` only goes to its own labels. -/
theorem execTerm_goto_mem {env : Env} {i : Inst} {l : Label}
    (h : execTerm env i = some (.goto l)) : l ∈ i.targets := by
  rcases i with ⟨op, args, outs⟩
  simp only [execTerm] at h
  split at h
  · cases h; simp [Inst.targets]
  · rename_i c t e
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨w, _, hw⟩ := h
    split at hw <;> cases hw <;> cases c <;> simp [Inst.targets]
  all_goals simp at h

/-- **A terminator only goes to its own labels** (`djmp` included): the successors that a block
declares (`Block.succs`, Vyper's `OUT=[…]`) contain every block it can jump to. -/
theorem execTermL_goto_mem (addr : LabelAddr) {env : Env} {i : Inst} {l : Label}
    (h : execTermL addr env i = some (.goto l)) : l ∈ i.targets := by
  simp only [execTermL] at h
  split at h
  · split at h
    · rename_i c ts hargs
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
        Next.goto.injEq] at h
      obtain ⟨w, _, l', hl', rfl⟩ := h
      simp only [Inst.targets, hargs, List.mem_filterMap]
      exact ⟨.lbl l', .tail _ (djmpPick_sound addr w hl').1, rfl⟩
    · simp at h
  · exact execTerm_goto_mem h

/-- **Dynamic successors are static successors**: a block run with label addresses that goes to
`l` declares `l` among its successors. -/
theorem runBlockL_goto_mem_succs (addr : LabelAddr) {b : Block} {prev : Label} {env env' : Env}
    {s s' : σ} {l : Label} (h : runBlockL addr b prev env s = some (.goto l, env', s')) :
    l ∈ b.succs := by
  simp only [runBlockL, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨env₁, _, t, ht, r, _, hr⟩ := h
  cases r <;> simp [Option.bind_eq_some_iff] at hr
  obtain ⟨_, hn, rfl, -⟩ := hr
  simpa [Block.succs, ht] using execTermL_goto_mem addr hn

/-- **The meaning of `djmp`.** For `djmp c, @l₁, …, @lₙ` whose listed labels have pairwise
different addresses, and a condition with value `w`, the block goes to `l` exactly when `l` is
listed and its address is `w`. -/
theorem execTermL_djmp_iff (addr : LabelAddr) {env : Env} {i : Inst} {c : Operand}
    {ls : List Label} {w : Word} (hop : i.op = .djmp) (hargs : i.args = c :: ls.map .lbl)
    (hc : evalOpL addr env c = some w)
    (hinj : ∀ a ∈ ls, ∀ b ∈ ls, addr a = some w → addr b = some w → a = b) (l : Label) :
    execTermL addr env i = some (.goto l) ↔ l ∈ ls ∧ addr l = some w := by
  simp only [execTermL, hop, if_true, hargs, hc, Option.bind_eq_bind, Option.bind_some]
  constructor
  · intro h
    simp only [Option.bind_eq_some_iff, Option.some.injEq, Next.goto.injEq] at h
    obtain ⟨l', hl', rfl⟩ := h
    simpa using djmpPick_sound addr w hl'
  · rintro ⟨hl, ha⟩
    simp [djmpPick_complete addr hinj hl ha]

/-- A terminator that `execTermL` executes: the shapes of `termShapeOk`, and
`djmp c, @l₁, …, @lₙ` with a non-label condition and at least one label, all different. -/
@[expose] def Inst.termShapeOkD (i : Inst) : Bool :=
  match i.op, i.args with
  | .djmp, c :: ts =>
    (match c with | .lbl _ => false | _ => true) && !ts.isEmpty &&
      ts.all (fun | .lbl _ => true | _ => false) && ts.Nodup
  | _, _ => i.termShapeOk

/-- `Block.wf` with `djmp` allowed as a terminator (`termShapeOkD`). -/
@[expose] def Block.wfD (b : Block) : Bool :=
  (match b.term? with | some t => t.termShapeOkD | none => false) &&
  b.phis.all Inst.phiShapeOk &&
  ((b.phis.map Inst.outs).flatten).Nodup &&
  b.body.all fun i => !i.op.isTerm && i.op != .phi && (i.op != .assert || i.args.length == 1)

/-- `Func.wf` with `djmp` allowed (`Block.wfD`). -/
@[expose] def Func.wfD (f : Func) : Bool :=
  f.check && (f.blocks.map (·.label)).Nodup && f.blocks.all Block.wfD

/-- Every label listed by a `djmp` of `f` has an address, and they are pairwise different. -/
@[expose] def Func.addrOk (addr : LabelAddr) (f : Func) : Bool :=
  f.blocks.all fun b => match b.term? with
    | some t =>
      if t.op = .djmp then
        let ls := t.targets
        ls.all (fun l => (addr l).isSome) && (ls.map addr).Nodup
      else true
    | none => true

/-- `termShapeOkD` accepts every terminator that `termShapeOk` accepts. -/
theorem Inst.termShapeOk_termShapeOkD {i : Inst} (h : i.termShapeOk = true) :
    i.termShapeOkD = true := by
  unfold Inst.termShapeOkD
  split <;> first | exact h | simp_all [Inst.termShapeOk]

/-- `Func.wfD` is weaker than `Func.wf`: every function accepted before is still accepted. -/
theorem Func.wf_wfD {f : Func} (h : f.wf = true) : f.wfD = true := by
  simp only [Func.wf, Func.wfD, Bool.and_eq_true, List.all_eq_true] at h ⊢
  refine ⟨h.1, fun b hb => ?_⟩
  have hb := h.2 b hb
  simp only [Block.wf, Block.wfD, Bool.and_eq_true] at hb ⊢
  refine ⟨⟨⟨?_, hb.1.1.2⟩, hb.1.2⟩, hb.2⟩
  have := hb.1.1.1
  split at this <;> first | exact Inst.termShapeOk_termShapeOkD this | cases this

/-- **Fuel monotonicity of `runL`** (induction on the fuel). -/
theorem runL_stable (addr : LabelAddr) (f : Func) :
    ∀ (n k : Nat) (prev cur : Label) (env : Env) (s : σ),
      runL addr f n prev cur env s ≠ .fuelOut →
        runL addr f (n + k) prev cur env s = runL addr f n prev cur env s
  | 0, _, _, _, _, _, h => absurd rfl h
  | n + 1, k, prev, cur, env, s, h => by
    rw [show n + 1 + k = (n + k) + 1 by omega]
    simp only [runL] at h ⊢
    split <;> try rfl
    split <;> try rfl
    rename_i hf _ l env' s' hb
    simp only [hf, hb] at h
    exact runL_stable addr f n k cur l env' s' h

end

private theorem inj_of_nodup_map {α β : Type} {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y
  | [], _, x, hx, _, _, _ => by simp at hx
  | a :: l, h, x, hx, y, hy, hxy => by
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.mp hx with rfl | hx' <;> rcases List.mem_cons.mp hy with rfl | hy'
    · rfl
    · exact absurd (hxy ▸ List.mem_map_of_mem hy') h.1
    · exact absurd (hxy.symm ▸ List.mem_map_of_mem hx') h.1
    · exact inj_of_nodup_map h.2 x hx' y hy' hxy

/-- What `Func.addrOk` gives: on the labels of a `djmp` of `f`, the addresses are pairwise
different, which is the hypothesis of `execTermL_djmp_iff`. -/
theorem Func.addrOk_djmp {addr : LabelAddr} {f : Func} (h : f.addrOk addr = true) {b : Block}
    (hb : b ∈ f.blocks) {t : Inst} (ht : b.term? = some t) (hop : t.op = .djmp) :
    ∀ x ∈ t.targets, ∀ y ∈ t.targets, ∀ w, addr x = some w → addr y = some w → x = y := by
  simp only [Func.addrOk, List.all_eq_true] at h
  have := h b hb
  simp only [ht, hop, if_true, Bool.and_eq_true, decide_eq_true_eq] at this
  exact fun x hx y hy w hxw hyw => inj_of_nodup_map this.2 x hx y hy (hxw.trans hyw.symm)
end EvmYul.Venom.Cfg
