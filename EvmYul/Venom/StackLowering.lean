module

public import EvmYul.Venom.Cfg

public section

/-!
# Lowering whole Venom functions to stack code: the full control-flow-graph language

`BlockLowering.lean` checks stack code for functions whose blocks are made of the straight-line
fragment (`Syntax.lean`: numbered variables, pure operations, seven effects, `assert`). This module
checks stack code for functions of the control-flow-graph language itself (`Cfg.lean`), as the
parser reads them from real Vyper output (`Text.lean`):

* string labels and variables, φs as instructions (`%x = phi @p₁, a₁, @p₂, a₂`);
* **every** machine opcode, through the machine interface `EvmInterface` (the copy `assign`,
  `codecopy`, `calldataload`, …), with any number of results;
* labels used as values (`add @selector_buckets, %5`), through label addresses `LabelAddr`;
* `assert`, and the terminators `jmp`, `jnz`, **`djmp`** and the halts.

The Venom side is the semantics with label addresses `runL` (`Cfg.lean` §7); the stack side is
`runS` below. Both call the same machine interface, so the theorem holds for every machine,
including the project's EVM (`evmInterface`).

**Stack code** (`SOp`): `push w`, `pushL l` (the address of `l`, a `PUSH2 @l`), `dup k`, `swap k`,
`pop`, `exec o n m` (pop `n` operands, top first, run opcode `o` through the machine interface, push
its `m` results, first result on top) and `assert`. A block ends in `jump l`, `jumpi t e fix`
(pop the condition; to `t` if non-zero, otherwise run the shuffle code `fix` and go to `e`: the
fall-through path of `PUSH t; JUMPI` may adjust the stack, the taken path cannot), `djump` (pop an
address; go to the block with that address, like the EVM `JUMP`), `halt` or `revert`.

**The checker** (`checkFunc`) runs the stack code symbolically from each block's entry layout,
as `BlockLowering.lean` does, with the same freshness condition, now for every result of a
multi-result instruction. At an edge `p → l` the stack must be `layout l` with the φ outputs of
`l` replaced by their sources for `p` (`edgeOk`). For `djmp c, @l₁, …, @lₙ` the condition must be
on top, the rest must fit every `lᵢ`, and no other block of the stack function may share an address
with an `lᵢ`.

**Theorem** (`checkFunc_sound`). If the checker accepts, then for every fuel, every machine state,
every machine interface and every label-address map, either the Venom function faults, or the
stack function ends exactly as the Venom function does (same result and final machine state, or
both out of fuel). The only fault of the Venom side that the stack side need not reproduce is a
`djmp` to a value that is the address of none of its labels: Venom gives it no meaning, while the
EVM `JUMP` goes wherever the value points. `checkFunc_refines` restates the theorem for finished
runs. The proof is an induction on the fuel whose invariant is the edge relation (`EntryRel`);
inside a block it is `checkCode_sound`, an induction on the stack code.

**Not modelled here.** The gas of the stack instructions themselves (`PUSH`, `DUP`, `SWAP`, `POP`,
`JUMPDEST`, `JUMP`): the machine state only sees the instructions sent to the interface. The byte
layout (that `addr l` is the offset of `l`'s `JUMPDEST`) is a parameter, not constructed.
-/

namespace EvmYul.Venom.StackLowering

open EvmYul.Venom.Cfg

/-! ## Stack code -/

@[expose] section

/-- A stack instruction. -/
inductive SOp where
  /-- Push a literal word. -/
  | push (w : Word)
  /-- Push the address of a label (`PUSH2 @l`). -/
  | pushL (l : Label)
  /-- `DUPk`: copy the `k`-th item (`1 ≤ k ≤ 16`). -/
  | dup (k : Nat)
  /-- `SWAPk`: exchange the top with the item `k` below it (`1 ≤ k ≤ 16`). -/
  | swap (k : Nat)
  /-- `POP`. -/
  | pop
  /-- Pop `n` operands (top first), run opcode `o` through the machine interface, push its `m`
  results (first result on top). -/
  | exec (o : Op) (n m : Nat)
  /-- Pop a word; revert if it is zero (Venom's `assert`). -/
  | assert
  deriving Repr, DecidableEq

end

@[expose] section

/-- How a block of stack code ends. -/
inductive STerm where
  /-- `PUSH2 l; JUMP`. -/
  | jump (l : Label)
  /-- `PUSH2 t; JUMPI; fix; PUSH2 e; JUMP`: pop the condition; to `t` if it is non-zero,
  otherwise run the shuffle code `fix` and go to `e`. -/
  | jumpi (t e : Label) (fix : List SOp)
  /-- `JUMP`: pop an address and go to the block with that address. -/
  | djump
  /-- Halt (`STOP`, `RETURN`). -/
  | halt
  /-- `REVERT`. -/
  | revert
  deriving Repr

end

@[expose] section

/-- A block of stack code. -/
structure SBlock where
  /-- The label. -/
  label : Label
  /-- The code. -/
  code : List SOp
  /-- How it ends. -/
  term : STerm
  deriving Repr

end

@[expose] section

/-- A function in stack code. -/
structure SFunc where
  /-- The entry label. -/
  entry : Label
  /-- The blocks. -/
  blocks : List SBlock
  deriving Repr

end

/-- The block with label `l`. -/
@[expose] def SFunc.find? (sf : SFunc) (l : Label) : Option SBlock :=
  sf.blocks.find? (·.label == l)

/-- Exchange the top of a list with its `k`-th item below the top (`SWAPk`). -/
@[expose] def swapAt {α : Type} (k : Nat) : List α → List α
  | [] => []
  | x :: xs => xs.getD (k - 1) x :: xs.set (k - 1) x

@[expose] section

/-- How a run of stack code ends: it falls through, or an `assert` reverted. -/
inductive SEnd (σ : Type) where
  /-- The code ran to its end with stack `stk`. -/
  | cont (stk : List Word) (s : σ)
  /-- An `assert` popped zero. -/
  | abort (s : σ)

end

section
variable {σ : Type} [EvmInterface σ]

/-- Run stack code. `none` is a fault (stack underflow, a `DUP`/`SWAP` out of range, a label
without an address, the machine interface failing, a wrong number of results). -/
@[expose] def runCode (addr : LabelAddr) : List SOp → List Word → σ → Option (SEnd σ)
  | [], stk, s => some (.cont stk s)
  | .push w :: c, stk, s => runCode addr c (w :: stk) s
  | .pushL l :: c, stk, s =>
    match addr l with
    | some w => runCode addr c (w :: stk) s
    | none => none
  | .dup k :: c, stk, s =>
    if 1 ≤ k ∧ k ≤ 16 ∧ k ≤ stk.length then runCode addr c (stk.getD (k - 1) 0 :: stk) s
    else none
  | .swap k :: c, stk, s =>
    if 1 ≤ k ∧ k ≤ 16 ∧ k < stk.length then runCode addr c (swapAt k stk) s else none
  | .pop :: c, stk, s =>
    match stk with
    | [] => none
    | _ :: stk' => runCode addr c stk' s
  | .exec o n m :: c, stk, s =>
    if n ≤ stk.length then
      match EvmInterface.exec o (stk.take n) s with
      | some (outs, s') => if outs.length = m then runCode addr c (outs ++ stk.drop n) s' else none
      | none => none
    else none
  | .assert :: c, stk, s =>
    match stk with
    | [] => none
    | x :: stk' => if x = 0 then some (.abort s) else runCode addr c stk' s

/-- Run a stack function for at most `fuel` blocks from block `cur` with stack `stk`. -/
@[expose] def runS (addr : LabelAddr) (sf : SFunc) : Nat → Label → List Word → σ → Result σ
  | 0, _, _, _ => .fuelOut
  | n + 1, cur, stk, s =>
    match sf.find? cur with
    | none => .fault
    | some b =>
      match runCode addr b.code stk s with
      | none => .fault
      | some (.abort s') => .reverted s'
      | some (.cont stk₂ s₂) =>
        match b.term with
        | .jump l => runS addr sf n l stk₂ s₂
        | .jumpi t e fix =>
          match stk₂ with
          | [] => .fault
          | x :: stk₃ =>
            if x = 0 then
              match runCode addr fix stk₃ s₂ with
              | some (.cont stk₄ s₄) => runS addr sf n e stk₄ s₄
              | some (.abort s₄) => .reverted s₄
              | none => .fault
            else runS addr sf n t stk₃ s₂
        | .djump =>
          match stk₂ with
          | [] => .fault
          | x :: stk₃ =>
            match sf.blocks.find? (fun b' => addr b'.label == some x) with
            | some b' => runS addr sf n b'.label stk₃ s₂
            | none => .fault
        | .halt => .halted s₂
        | .revert => .reverted s₂

end

/-! ## The checker -/

/-- `x` does not occur in the symbolic stack `S`. -/
@[expose] def freshC (x : Var) (S : List Operand) : Bool := S.all (· != .var x)

/-- Check stack code `c` against the ordinary instructions `is` of a block, from symbolic stack
`S` (top first). The result is the symbolic stack at the end. An instruction `%y₁, …, %yₘ = o a₁,
…, aₙ` must be matched by `exec o n m` with `a₁ … aₙ` on top; its results must be distinct and
fresh in the rest of the stack. `assert a` must be matched by `assert` with `a` on top. -/
@[expose] def checkCode (addr : LabelAddr) : List Inst → List SOp → List Operand →
    Option (List Operand)
  | is, .push w :: c, S => checkCode addr is c (.lit w :: S)
  | is, .pushL l :: c, S => if (addr l).isSome then checkCode addr is c (.lbl l :: S) else none
  | is, .dup k :: c, S =>
    if 1 ≤ k ∧ k ≤ 16 ∧ k ≤ S.length then checkCode addr is c (S.getD (k - 1) (.lit 0) :: S)
    else none
  | is, .swap k :: c, S =>
    if 1 ≤ k ∧ k ≤ 16 ∧ k < S.length then checkCode addr is c (swapAt k S) else none
  | is, .pop :: c, S =>
    match S with
    | [] => none
    | _ :: S' => checkCode addr is c S'
  | [], [], S => some S
  | i :: is, .exec o n m :: c, S =>
    if i.op = o ∧ i.op ≠ .assert ∧ i.args.length = n ∧ i.outs.length = m ∧ S.take n = i.args ∧
        i.outs.Nodup ∧ i.outs.all (fun x => freshC x (S.drop n)) = true then
      checkCode addr is c (i.outs.map .var ++ S.drop n)
    else none
  | i :: is, .assert :: c, a :: S =>
    if i.op = .assert ∧ i.args = [a] then checkCode addr is c S else none
  | _, _, _ => none

/-- The φs of a block as `(output, operands)`. -/
@[expose] def phiDefs (phis : List Inst) : List (Var × List Operand) :=
  phis.filterMap fun i => match i.outs with
    | [x] => some (x, i.args)
    | _ => none

/-- An operand of a layout at an edge from `pred` into a block with φs `phis`: a φ output becomes
its source for `pred` (`none` if it has none); anything else stays. -/
@[expose] def substPhi (phis : List Inst) (pred : Label) : Operand → Option Operand
  | .var x =>
    match (phiDefs phis).lookup x with
    | some args => phiPick pred args
    | none => some (.var x)
  | o => some o

/-- A φ source that can be read at an edge with exit stack `S`: a literal, a label with an address,
or an operand on `S`. -/
@[expose] def srcOk (addr : LabelAddr) (S : List Operand) : Operand → Bool
  | .lit _ => true
  | .lbl l => (addr l).isSome
  | o => decide (o ∈ S)

/-- The edge `pred → l` leaves symbolic stack `S`: block `l` exists, each of its φs has one output,
the outputs are distinct, every φ has a readable source for `pred`, and `S` is `layout l` with the
φ outputs replaced by their sources. -/
@[expose] def edgeOk (addr : LabelAddr) (f : Func) (layout : Label → List Operand) (pred l : Label)
    (S : List Operand) : Bool :=
  match f.find? l with
  | none => false
  | some b =>
    b.phis.all (fun i => i.outs.length == 1 && match phiPick pred i.args with
      | some o => srcOk addr S o
      | none => false) &&
    decide (((phiDefs b.phis).map Prod.fst).Nodup) &&
    decide ((layout l).mapM (substPhi b.phis pred) = some S)

/-- The labels of a list of operands, if they are all labels. -/
@[expose] def asLabels : List Operand → Option (List Label)
  | [] => some []
  | .lbl l :: rest => (asLabels rest).map (l :: ·)
  | _ :: _ => none

/-- Is the operand a label? -/
@[expose] def isLbl : Operand → Bool
  | .lbl _ => true
  | _ => false

/-- Check a block's terminator `t` against the stack terminator `st`, from exit stack `S`. -/
@[expose] def checkTerm (addr : LabelAddr) (f : Func) (sf : SFunc) (layout : Label → List Operand)
    (lbl : Label) (t : Inst) (st : STerm) (S : List Operand) : Bool :=
  match t.op, t.args, st with
  | .jmp, [.lbl l], .jump l' => l == l' && edgeOk addr f layout lbl l S
  | .jnz, [c, .lbl tl, .lbl el], .jumpi tl' el' fix =>
    tl == tl' && el == el' && !isLbl c &&
      match S with
      | c' :: S' =>
        c == c' && edgeOk addr f layout lbl tl S' &&
          match checkCode addr [] fix S' with
          | some S'' => edgeOk addr f layout lbl el S''
          | none => false
      | [] => false
  | .djmp, c :: ts, .djump =>
    match S, asLabels ts with
    | c' :: S', some ls =>
      c == c' && ls.all (fun l => edgeOk addr f layout lbl l S') &&
        sf.blocks.all (fun sb => ls.all fun l => addr sb.label != addr l || sb.label == l)
    | _, _ => false
  | .stop, _, .halt | .ret, _, .halt | .evmReturn, _, .halt => true
  | .revert, _, .revert => true
  | _, _, _ => false

/-- Check one Venom block: its stack block exists, its body is checked from its layout, and its
terminator is checked from the resulting stack. -/
@[expose] def checkBlock (addr : LabelAddr) (f : Func) (sf : SFunc) (layout : Label → List Operand)
    (b : Block) : Bool :=
  match sf.find? b.label, b.term? with
  | some sb, some t =>
    match checkCode addr b.body sb.code (layout b.label) with
    | some S => checkTerm addr f sf layout b.label t sb.term S
    | none => false
  | _, _ => false

/-- **The function checker.** Same entry; the entry block exists, has no φs and an empty layout;
every Venom block passes `checkBlock`. -/
@[expose] def checkFunc (addr : LabelAddr) (f : Func) (sf : SFunc) (layout : Label → List Operand) :
    Bool :=
  f.entry == sf.entry && (layout f.entry).isEmpty &&
    (match f.find? f.entry with
     | some b => b.phis.isEmpty
     | none => false) &&
    f.blocks.all (checkBlock addr f sf layout)

/-! ## Soundness of the code checker -/

/-- The symbolic stack `S` holds, in environment `env`, exactly the words of the stack `stk`. -/
@[expose] def StackRel (addr : LabelAddr) (S : List Operand) (env : Env) (stk : List Word) : Prop :=
  S.map (evalOpL addr env) = stk.map some

section
variable {σ : Type} [EvmInterface σ]

/-- How the Venom body and the stack code correspond: both fall through with the same machine
state and the checker's stack holding the concrete one, both revert in the same state, or both
fault. -/
@[expose] def CodeMatch (addr : LabelAddr) (S : List Operand) :
    Option (BodyEnd σ) → Option (SEnd σ) → Prop
  | some (.cont env s), some (.cont stk s') => s = s' ∧ StackRel addr S env stk
  | some (.abort s), some (.abort s') => s = s'
  | none, none => True
  | _, _ => False

end

private theorem length_of_stackRel {addr : LabelAddr} {S : List Operand} {env : Env}
    {stk : List Word} (h : StackRel addr S env stk) : S.length = stk.length := by
  simpa using congrArg List.length h

private theorem stackRel_take {addr : LabelAddr} {S : List Operand} {env : Env} {stk : List Word}
    (h : StackRel addr S env stk) (n : Nat) : StackRel addr (S.take n) env (stk.take n) := by
  unfold StackRel at *; rw [List.map_take, h, List.map_take]

private theorem stackRel_drop {addr : LabelAddr} {S : List Operand} {env : Env} {stk : List Word}
    (h : StackRel addr S env stk) (n : Nat) : StackRel addr (S.drop n) env (stk.drop n) := by
  unfold StackRel at *; rw [List.map_drop, h, List.map_drop]

private theorem stackRel_cons {addr : LabelAddr} {S : List Operand} {env : Env} {stk : List Word}
    {o : Operand} {x : Word} (ho : evalOpL addr env o = some x) (h : StackRel addr S env stk) :
    StackRel addr (o :: S) env (x :: stk) := by
  unfold StackRel at *; simp [ho, h]

private theorem stackRel_append {addr : LabelAddr} {S T : List Operand} {env : Env}
    {stk stk' : List Word} (h : StackRel addr S env stk) (h' : StackRel addr T env stk') :
    StackRel addr (S ++ T) env (stk ++ stk') := by
  unfold StackRel at *; simp [h, h']

private theorem mapM_of_stackRel {addr : LabelAddr} {env : Env} :
    ∀ {S : List Operand} {stk : List Word}, StackRel addr S env stk →
      S.mapM (evalOpL addr env) = some stk
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [StackRel] at h
  | _ :: _, [], h => by simp [StackRel] at h
  | x :: xs, y :: ys, h => by
    simp only [StackRel, List.map_cons, List.cons.injEq] at h
    have := mapM_of_stackRel (S := xs) (stk := ys) h.2
    simp [List.mapM_cons, h.1, this]

private theorem map_swapAt {α β : Type} (f : α → β) (k : Nat) :
    ∀ l : List α, (swapAt k l).map f = swapAt k (l.map f)
  | [] => rfl
  | x :: xs => by simp [swapAt, List.map_set]

private theorem stackRel_getD {addr : LabelAddr} {S : List Operand} {env : Env} {stk : List Word}
    {i : Nat} (h : StackRel addr S env stk) (hi : i < S.length) (d₁ : Operand) (d₂ : Word) :
    evalOpL addr env (S.getD i d₁) = some (stk.getD i d₂) := by
  have hi' : i < stk.length := length_of_stackRel h ▸ hi
  simpa [List.getD_eq_getElem?_getD, hi, hi'] using congrArg (·[i]?) h

/-- Setting the results of an instruction: the environment `execPlainL` builds. -/
private theorem setAll_spec :
    ∀ (xs : List Var) (ws : List Word) (env : Env), xs.Nodup → xs.length = ws.length →
      (∀ y, y ∉ xs → ((xs.zip ws).foldl (fun e (p : Var × Word) => e.set p.1 p.2) env) y = env y) ∧
      xs.map (fun x => ((xs.zip ws).foldl (fun e (p : Var × Word) => e.set p.1 p.2) env) x) =
        ws.map some
  | [], [], _, _, _ => ⟨fun _ _ => rfl, rfl⟩
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | x :: xs, w :: ws, env, hnd, hlen => by
    rw [List.nodup_cons] at hnd
    have ih := setAll_spec xs ws (env.set x w) hnd.2 (by simpa using hlen)
    simp only [List.zip_cons_cons, List.foldl_cons, List.map_cons, List.cons.injEq]
    refine ⟨fun y hy => ?_, ?_, ih.2⟩
    · rw [ih.1 y (fun h => hy (List.mem_cons_of_mem _ h))]
      have : y ≠ x := fun h => hy (h ▸ List.mem_cons_self)
      simp [Env.set, this]
    · rw [ih.1 x hnd.1]; simp [Env.set]

/-- Changing the environment outside the variables of `S` leaves `S`'s values unchanged. -/
private theorem stackRel_frame {addr : LabelAddr} {S : List Operand} {env env' : Env}
    {stk : List Word} {xs : List Var} (h : StackRel addr S env stk)
    (hfresh : xs.all (fun x => freshC x S) = true) (hframe : ∀ y, y ∉ xs → env' y = env y) :
    StackRel addr S env' stk := by
  unfold StackRel at *
  rw [← h]
  refine List.map_congr_left fun o ho => ?_
  simp only [List.all_eq_true, freshC, bne_iff_ne, ne_eq] at hfresh
  cases o with
  | var v => simp [evalOpL, hframe v fun hv => hfresh v hv (.var v) ho rfl]
  | _ => rfl

/-- **Soundness of the code checker** (induction on the stack code). If `checkCode` accepts code
`c` for the instructions `is` from symbolic stack `S` with result `S'`, and `S` holds the concrete
stack, then the Venom body and the stack code correspond (`CodeMatch`). -/
theorem checkCode_sound {σ : Type} [EvmInterface σ] (addr : LabelAddr) :
    ∀ (c : List SOp) (is : List Inst) (S S' : List Operand) (env : Env) (stk : List Word) (s : σ),
      checkCode addr is c S = some S' → StackRel addr S env stk →
      CodeMatch addr S' (runPlainL addr env s is) (runCode addr c stk s) := by
  intro c
  induction c with
  | nil =>
    intro is S S' env stk s hc hrel
    cases is with
    | nil =>
      simp only [checkCode, Option.some.injEq] at hc; subst hc
      exact ⟨rfl, hrel⟩
    | cons i is => simp [checkCode] at hc
  | cons a c ih =>
    intro is S S' env stk s hc hrel
    have hlen := length_of_stackRel hrel
    cases a with
    | push w =>
      simp only [checkCode] at hc
      exact ih is _ S' env _ s hc (stackRel_cons rfl hrel)
    | pushL l =>
      simp only [checkCode] at hc
      split at hc
      · rename_i hl
        obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hl
        simp only [runCode, hw]
        exact ih is _ S' env _ s hc (stackRel_cons (by simp [evalOpL, hw]) hrel)
      · simp at hc
    | dup k =>
      simp only [checkCode] at hc
      split at hc
      · simp only [runCode, if_pos (show 1 ≤ k ∧ k ≤ 16 ∧ k ≤ stk.length by omega)]
        exact ih is _ S' env _ s hc
          (stackRel_cons (stackRel_getD hrel (show k - 1 < S.length by omega) _ _) hrel)
      · simp at hc
    | swap k =>
      simp only [checkCode] at hc
      split at hc
      · simp only [runCode, if_pos (show 1 ≤ k ∧ k ≤ 16 ∧ k < stk.length by omega)]
        refine ih is _ S' env _ s hc ?_
        unfold StackRel at *; rw [map_swapAt, hrel, map_swapAt]
      · simp at hc
    | pop =>
      obtain _ | ⟨x, S₀⟩ := S
      · simp [checkCode] at hc
      obtain _ | ⟨y, stk₀⟩ := stk
      · simp at hlen
      simp only [checkCode] at hc
      simp only [runCode]
      exact ih is S₀ S' env stk₀ s hc (List.cons.inj hrel).2
    | exec o n m =>
      cases is with
      | nil => simp [checkCode] at hc
      | cons i is =>
        simp only [checkCode] at hc
        split at hc
        · rename_i hcond
          obtain ⟨rfl, hna, hn, hm, htake, hnd, hfresh⟩ := hcond
          have hnle : n ≤ stk.length := by
            have := congrArg List.length htake
            simp only [List.length_take] at this
            omega
          have hargs : i.args.mapM (evalOpL addr env) = some (stk.take n) := by
            rw [← htake]; exact mapM_of_stackRel (stackRel_take hrel n)
          simp only [runPlainL, if_neg hna, runCode, if_pos hnle, execPlainL, hargs,
            Option.bind_eq_bind, Option.bind_some]
          cases hx : EvmInterface.exec i.op (stk.take n) s with
          | none => simp [CodeMatch]
          | some r =>
            obtain ⟨outs, s'⟩ := r
            simp only [Option.bind_some]
            by_cases hl : outs.length = m
            · simp only [if_pos (show outs.length = i.outs.length by omega), if_pos hl,
                Option.pure_def, Option.bind_some]
              have hset := setAll_spec i.outs outs env hnd (by omega)
              refine ih is _ S' _ _ s' hc (stackRel_append ?_ ?_)
              · unfold StackRel; rw [List.map_map]; exact hset.2
              · exact stackRel_frame (stackRel_drop hrel n) hfresh hset.1
            · simp only [if_neg (show ¬ outs.length = i.outs.length by omega), if_neg hl]
              simp [CodeMatch]
        · simp at hc
    | assert =>
      obtain _ | ⟨i, is⟩ := is
      · simp [checkCode] at hc
      obtain _ | ⟨a, S₀⟩ := S
      · simp [checkCode] at hc
      obtain _ | ⟨x, stk₀⟩ := stk
      · simp at hlen
      simp only [checkCode] at hc
      split at hc
      · rename_i hcond
        obtain ⟨hop, hargs⟩ := hcond
        simp only [StackRel, List.map_cons, List.cons.injEq] at hrel
        simp only [runPlainL, hop, if_true, hargs, hrel.1, Option.bind_eq_bind,
          Option.bind_some, runCode]
        by_cases hx : x = 0
        · simp [hx, CodeMatch]
        · simp only [hx, if_false]
          exact ih is S₀ S' env stk₀ s hc hrel.2
      · simp at hc

/-! ## Soundness of the function checker -/

private theorem find?_spec {β γ : Type} [BEq γ] [LawfulBEq γ] {bs : List β} {key : β → γ} {l : γ}
    {b : β} (h : bs.find? (fun x => key x == l) = some b) : b ∈ bs ∧ key b = l :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-- The φ copy as a function of the variable: distinct single outputs, every source defined. -/
private theorem applyPhisL_spec (addr : LabelAddr) (p : Label) (old : Env) :
    ∀ (phis : List Inst) (acc : Env),
      (∀ i ∈ phis, ∃ x, i.outs = [x]) → ((phiDefs phis).map Prod.fst).Nodup →
      (∀ i ∈ phis, ∃ o w, phiPick p i.args = some o ∧ evalOpL addr old o = some w) →
      ∃ env₁, phis.foldlM (init := acc) (fun acc i => do
          let src ← phiPick p i.args
          let w ← evalOpL addr old src
          match i.outs with
          | [x] => pure (acc.set x w)
          | _ => none) = some env₁ ∧
        ∀ y, env₁ y = match (phiDefs phis).lookup y with
          | some args => (phiPick p args).bind (evalOpL addr old)
          | none => acc y
  | [], acc, _, _, _ => ⟨acc, rfl, fun y => by simp [phiDefs]⟩
  | i :: rest, acc, hout, hnd, hsrc => by
    obtain ⟨x, hx⟩ := hout i (by simp)
    obtain ⟨o, w, ho, hw⟩ := hsrc i (by simp)
    have hdefs : phiDefs (i :: rest) = (x, i.args) :: phiDefs rest := by
      simp [phiDefs, hx]
    rw [hdefs, List.map_cons, List.nodup_cons] at hnd
    obtain ⟨env₁, h₁, h₂⟩ := applyPhisL_spec addr p old rest (acc.set x w)
      (fun j hj => hout j (List.mem_cons_of_mem _ hj)) hnd.2
      (fun j hj => hsrc j (List.mem_cons_of_mem _ hj))
    refine ⟨env₁, ?_, fun y => ?_⟩
    · simpa only [List.foldlM_cons, Option.bind_eq_bind, ho, hw, hx, Option.bind_some,
        Option.pure_def] using h₁
    · rw [h₂ y, hdefs]
      by_cases hyx : y = x
      · subst hyx
        have hnone : (phiDefs rest).lookup y = none := List.lookup_eq_none_iff.2 fun q hq =>
          bne_iff_ne.2 fun heq => hnd.1 (List.mem_map.mpr ⟨q, hq, heq.symm⟩)
        simp [hnone, List.lookup, Env.set, ho, hw]
      · simp [List.lookup, beq_false_of_ne hyx, Env.set, hyx]

private theorem mapM_rel {α β : Type} {f : α → Option β} {g : α → Option Word}
    {h : β → Option Word} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' →
      (∀ a ∈ l, ∀ b, f a = some b → g a = h b) → l.map g = l'.map h
  | [], l', hm, _ => by simp at hm; subst hm; rfl
  | a :: as, l', hm, hgh => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at hm
    obtain ⟨b, hb, bs, hbs, rfl⟩ := hm
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨hgh a (by simp) b hb,
      mapM_rel hbs (fun a' ha' b' hb' => hgh a' (List.mem_cons_of_mem _ ha') b' hb')⟩

private theorem evalOpL_of_mem {addr : LabelAddr} {S : List Operand} {env : Env}
    {stk : List Word} (h : StackRel addr S env stk) {o : Operand} (ho : o ∈ S) :
    ∃ w, evalOpL addr env o = some w := by
  have : evalOpL addr env o ∈ stk.map some := by
    rw [← h]; exact List.mem_map.mpr ⟨o, ho, rfl⟩
  obtain ⟨w, _, hw⟩ := List.mem_map.mp this
  exact ⟨w, hw.symm⟩

/-- **The edge lemma.** Along an accepted edge `p → l` the φ copy succeeds, and afterwards block
`l`'s layout holds the concrete stack. -/
private theorem edge_phis {addr : LabelAddr} {f : Func} {layout : Label → List Operand}
    {p l : Label} {S : List Operand} {b : Block} {env : Env} {stk : List Word}
    (he : edgeOk addr f layout p l S = true) (hb : f.find? l = some b)
    (hrel : StackRel addr S env stk) :
    ∃ env₁, applyPhisL addr p env b.phis = some env₁ ∧ StackRel addr (layout l) env₁ stk := by
  simp only [edgeOk, hb, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at he
  obtain ⟨⟨hphi, hnd⟩, hmap⟩ := he
  have hout : ∀ i ∈ b.phis, ∃ x, i.outs = [x] := by
    intro i hi
    have := (hphi i hi).1
    simp only [beq_iff_eq] at this
    match h : i.outs, this with
    | [x], _ => exact ⟨x, rfl⟩
  have hsrc : ∀ i ∈ b.phis, ∃ o w, phiPick p i.args = some o ∧ evalOpL addr env o = some w := by
    intro i hi
    have := (hphi i hi).2
    split at this
    · rename_i o ho
      refine ⟨o, ?_⟩
      cases o with
      | lit w => exact ⟨w, ho, rfl⟩
      | lbl l' =>
        simp only [srcOk] at this
        obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp this
        exact ⟨w, ho, by simp [evalOpL, hw]⟩
      | var v =>
        simp only [srcOk, decide_eq_true_eq] at this
        obtain ⟨w, hw⟩ := evalOpL_of_mem hrel this
        exact ⟨w, ho, hw⟩
    · simp at this
  obtain ⟨env₁, h₁, h₂⟩ := applyPhisL_spec addr p env b.phis env hout hnd hsrc
  refine ⟨env₁, h₁, ?_⟩
  unfold StackRel
  rw [← hrel]
  refine mapM_rel hmap (fun o _ o' ho' => ?_)
  cases o with
  | var y =>
    simp only [substPhi] at ho'
    simp only [evalOpL, h₂ y]
    cases hl : (phiDefs b.phis).lookup y with
    | some args =>
      simp only [hl] at ho'
      simp only [ho', Option.bind_some]
      cases o' <;> rfl
    | none =>
      simp only [hl, Option.some.injEq] at ho'
      subst ho'
      rfl
  | _ => simp only [substPhi, Option.some.injEq] at ho'; subst ho'; rfl

/-- The invariant at block entry: the start (the entry block, empty stack), or an accepted edge
from `prev` whose exit stack holds the concrete stack. -/
@[expose] def EntryRel (addr : LabelAddr) (f : Func) (layout : Label → List Operand)
    (prev cur : Label) (env : Env) (stk : List Word) : Prop :=
  (cur = f.entry ∧ stk = []) ∨ ∃ S, edgeOk addr f layout prev cur S = true ∧ StackRel addr S env stk

/-- How the two results of a run correspond: the Venom function faults, or both end the same. -/
@[expose] def ResultMatch {σ : Type} (rs rv : Result σ) : Prop := rv = .fault ∨ rs = rv

private theorem execTermL_jmp {addr : LabelAddr} {env : Env} {t : Inst} {l : Label}
    (hop : t.op = .jmp) (ha : t.args = [.lbl l]) : execTermL addr env t = some (.goto l) := by
  rcases t with ⟨op, args, outs⟩
  simp only at hop ha; subst hop ha; rfl

private theorem execTermL_jnz {addr : LabelAddr} {env : Env} {t : Inst} {c : Operand}
    {tl el : Label} (hop : t.op = .jnz) (ha : t.args = [c, .lbl tl, .lbl el])
    (hc : isLbl c = false) :
    execTermL addr env t = (evalOpL addr env c).map (fun w => .goto (if w = 0 then el else tl)) := by
  rcases t with ⟨op, args, outs⟩
  simp only at hop ha; subst hop ha
  cases c with
  | lbl _ => simp [isLbl] at hc
  | lit w => rfl
  | var v => simp only [execTermL, execTerm, evalOp, evalOpL]; cases env v <;> rfl

private theorem execTermL_djmp {addr : LabelAddr} {env : Env} {t : Inst} {c : Operand}
    {ts : List Operand} (hop : t.op = .djmp) (ha : t.args = c :: ts) :
    execTermL addr env t = (evalOpL addr env c).bind (fun w => (djmpPick addr w ts).map .goto) := by
  rcases t with ⟨op, args, outs⟩
  simp only at hop ha; subst hop ha
  simp only [execTermL, if_true, Option.bind_eq_bind]
  cases evalOpL addr env c with
  | none => rfl
  | some w => simp only [Option.bind_some]; cases djmpPick addr w ts <;> rfl

private theorem execTermL_halt {addr : LabelAddr} {env : Env} {t : Inst}
    (hop : t.op = .stop ∨ t.op = .ret ∨ t.op = .evmReturn) : execTermL addr env t = some .halt := by
  rcases t with ⟨op, args, outs⟩
  simp only at hop
  rcases hop with rfl | rfl | rfl <;> rfl

private theorem execTermL_revert {addr : LabelAddr} {env : Env} {t : Inst}
    (hop : t.op = .revert) : execTermL addr env t = some .revert := by
  rcases t with ⟨op, args, outs⟩
  simp only at hop; subst hop; rfl

private theorem asLabels_spec : ∀ {ts : List Operand} {ls : List Label},
    asLabels ts = some ls → ts = ls.map .lbl
  | [], ls, h => by simp only [asLabels, Option.some.injEq] at h; subst h; rfl
  | .lbl l :: rest, ls, h => by
    simp only [asLabels, Option.map_eq_some_iff] at h
    obtain ⟨ls', h', rfl⟩ := h
    simp [asLabels_spec h']
  | .lit _ :: _, _, h => by simp [asLabels] at h
  | .var _ :: _, _, h => by simp [asLabels] at h

/-- **Soundness of the function checker**, from any related block entry (induction on the fuel). -/
theorem checkFunc_sound_from {σ : Type} [EvmInterface σ] (addr : LabelAddr) {f : Func}
    {sf : SFunc} {layout : Label → List Operand} (hc : checkFunc addr f sf layout = true) :
    ∀ (n : Nat) (prev cur : Label) (env : Env) (stk : List Word) (s : σ),
      EntryRel addr f layout prev cur env stk →
      ResultMatch (runS addr sf n cur stk s) (runL addr f n prev cur env s) := by
  simp only [checkFunc, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff, List.all_eq_true] at hc
  obtain ⟨⟨⟨_, hlay⟩, hentryB⟩, hblocks⟩ := hc
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _; right; rfl
  | succ n ih =>
    intro prev cur env stk s hrel
    obtain ⟨b, hb, env₁, hphi, hrel₁⟩ : ∃ b, f.find? cur = some b ∧ ∃ env₁,
        applyPhisL addr prev env b.phis = some env₁ ∧ StackRel addr (layout cur) env₁ stk := by
      rcases hrel with ⟨rfl, rfl⟩ | ⟨S, he, hS⟩
      · split at hentryB
        · rename_i b hb
          refine ⟨b, hb, env, ?_, ?_⟩
          · simp only [List.isEmpty_iff] at hentryB; simp [applyPhisL, hentryB]
          · simp [StackRel, hlay]
        · simp at hentryB
      · cases hb : f.find? cur with
        | none => simp [edgeOk, hb] at he
        | some b =>
          obtain ⟨env₁, h₁, h₂⟩ := edge_phis he hb hS
          exact ⟨b, rfl, env₁, h₁, h₂⟩
    obtain ⟨hbmem, hblabel⟩ := find?_spec hb
    have hcb := hblocks b hbmem
    simp only [checkBlock] at hcb
    rcases hsb : sf.find? b.label with _ | sb
    · simp [hsb] at hcb
    rcases ht : b.term? with _ | t
    · simp [hsb, ht] at hcb
    simp only [hsb, ht] at hcb
    rw [hblabel] at hsb hcb
    cases hr : checkCode addr b.body sb.code (layout cur) with
    | none => simp [hr] at hcb
    | some S =>
      simp only [hr] at hcb
      have hm := checkCode_sound addr sb.code b.body (layout cur) S env₁ stk s hr hrel₁
      simp only [runS, runL, hb, hsb, runBlockL, hphi, ht, Option.bind_eq_bind, Option.bind_some]
      revert hm
      generalize runPlainL addr env₁ s b.body = rv
      generalize runCode addr sb.code stk s = rs
      intro hm
      rcases rv with _ | (⟨env₂, s₂⟩ | s₂) <;> rcases rs with _ | (⟨stk₂, s₂'⟩ | s₂') <;>
        simp only [CodeMatch] at hm
      · left; rfl
      · obtain ⟨rfl, hS⟩ := hm
        simp only [Option.bind_some]
        have hex : ∀ l S', edgeOk addr f layout cur l S' = true → ∃ sbl ∈ sf.blocks, sbl.label = l := by
          intro l S' he
          rcases hfl : f.find? l with _ | bl
          · simp [edgeOk, hfl] at he
          obtain ⟨hblm, rfl⟩ := find?_spec hfl
          have hcbl := hblocks bl hblm
          simp only [checkBlock] at hcbl
          rcases hsbl : sf.find? bl.label with _ | sbl
          · simp [hsbl] at hcbl
          exact ⟨sbl, find?_spec hsbl⟩
        unfold checkTerm at hcb
        split at hcb
        · rename_i l l' hop hargs hst
          simp only [Bool.and_eq_true, beq_iff_eq] at hcb
          obtain ⟨rfl, he⟩ := hcb
          simp only [hst, execTermL_jmp hop hargs, Option.bind_some, Option.pure_def]
          exact ih _ _ _ _ _ (Or.inr ⟨S, he, hS⟩)
        · rename_i c tl el tl' el' fix hop hargs hst
          simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hcb
          obtain ⟨⟨⟨rfl, rfl⟩, hnl⟩, hrest⟩ := hcb
          rcases S with _ | ⟨c', S'⟩
          · simp at hrest
          simp only [Bool.and_eq_true, beq_iff_eq] at hrest
          obtain ⟨⟨rfl, het⟩, hfix⟩ := hrest
          rcases stk₂ with _ | ⟨x, stk₃⟩
          · simp [StackRel] at hS
          simp only [StackRel, List.map_cons, List.cons.injEq] at hS
          obtain ⟨hcx, hS'⟩ := hS
          simp only [hst, execTermL_jnz hop hargs hnl, hcx, Option.map_some, Option.bind_some,
            Option.pure_def]
          by_cases hx : x = 0
          · simp only [hx, if_true]
            cases hcf : checkCode addr [] fix S' with
            | none => simp [hcf] at hfix
            | some S'' =>
              simp only [hcf] at hfix
              have hm := checkCode_sound addr fix [] S' S'' env₂ stk₃ s₂ hcf hS'
              simp only [runPlainL] at hm
              revert hm
              generalize runCode addr fix stk₃ s₂ = rf
              intro hm
              rcases rf with _ | (⟨stk₄, s₄⟩ | s₄) <;> simp only [CodeMatch] at hm
              obtain ⟨rfl, hS''⟩ := hm
              exact ih _ _ _ _ _ (Or.inr ⟨S'', hfix, hS''⟩)
          · simp only [hx, if_false]
            exact ih _ _ _ _ _ (Or.inr ⟨S', het, hS'⟩)
        · rename_i c ts hop hargs hst
          rcases S with _ | ⟨c', S'⟩
          · simp at hcb
          cases hls : asLabels ts with
          | none => simp [hls] at hcb
          | some ls =>
            simp only [hls, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true,
              bne_iff_ne, ne_eq] at hcb
            obtain ⟨⟨rfl, hedges⟩, hinj⟩ := hcb
            rcases stk₂ with _ | ⟨x, stk₃⟩
            · simp [StackRel] at hS
            simp only [StackRel, List.map_cons, List.cons.injEq] at hS
            obtain ⟨hcx, hS'⟩ := hS
            simp only [hst, execTermL_djmp hop hargs, hcx, Option.bind_some]
            cases hpick : djmpPick addr x ts with
            | none => left; rfl
            | some l =>
              obtain ⟨hlm, hal⟩ := djmpPick_sound addr x hpick
              rw [asLabels_spec hls] at hlm
              have hl : l ∈ ls := by simpa using hlm
              have he := hedges l hl
              obtain ⟨sbl, hsblm, hsbll⟩ := hex l S' he
              obtain ⟨b', hb'⟩ : ∃ b', sf.blocks.find? (fun b' => addr b'.label == some x) = some b' :=
                Option.isSome_iff_exists.mp (List.find?_isSome.2 ⟨sbl, hsblm, by simp [hsbll, hal]⟩)
              obtain ⟨hb'm, hb'a⟩ := find?_spec hb'
              have hlab : b'.label = l :=
                (hinj b' hb'm l hl).elim (absurd (hb'a.trans hal.symm)) (by simpa using ·)
              simp only [Option.map_some, Option.pure_def, Option.bind_some, hb', hlab]
              exact ih _ _ _ _ _ (Or.inr ⟨S', he, hS'⟩)
        all_goals try (rename_i hop hst; simp only [hst, execTermL_halt (t := t) (by simp [hop]),
          Option.bind_some, Option.pure_def]; exact .inr rfl)
        · rename_i hop hst
          simp only [hst, execTermL_revert hop, Option.bind_some, Option.pure_def]
          right; rfl
        · simp at hcb
      · subst hm; right; rfl

/-- **Soundness of the function checker.** If `checkFunc` accepts the stack function `sf` for the
Venom function `f` with layouts `layout`, then for every fuel, every machine interface, every
machine state and every label-address map, either the Venom function faults (a `djmp` to a value
that is no listed label's address is the only fault the stack side need not reproduce), or the
stack function run from its entry on the empty stack ends exactly as the Venom function run from
its entry on the empty environment. -/
theorem checkFunc_sound {σ : Type} [EvmInterface σ] (addr : LabelAddr) {f : Func} {sf : SFunc}
    {layout : Label → List Operand} (h : checkFunc addr f sf layout = true) (n : Nat) (s : σ) :
    runL addr f n "" f.entry Env.empty s = .fault ∨
      runS addr sf n sf.entry [] s = runL addr f n "" f.entry Env.empty s := by
  have he : f.entry = sf.entry := by
    simp only [checkFunc, Bool.and_eq_true, beq_iff_eq] at h; exact h.1.1.1
  rw [← he]
  exact checkFunc_sound_from addr h n "" f.entry Env.empty [] s (Or.inl ⟨rfl, rfl⟩)

/-- **Refinement form.** A finished run of the Venom function (halted or reverted) is the run of
the accepted stack function with the same fuel; so is a run that is out of fuel. -/
theorem checkFunc_refines {σ : Type} [EvmInterface σ] (addr : LabelAddr) {f : Func} {sf : SFunc}
    {layout : Label → List Operand} (h : checkFunc addr f sf layout = true) (n : Nat) (s : σ)
    (hv : runL addr f n "" f.entry Env.empty s ≠ .fault) :
    runS addr sf n sf.entry [] s = runL addr f n "" f.entry Env.empty s :=
  (checkFunc_sound addr h n s).resolve_left hv

/-! ## What the `djmp` condition guarantees -/

/-- **No collision with any stack block.** If `checkTerm` accepts a `djmp` with targets `ls`, then no
stack block other than `l` has `l`'s address, for every target `l`, including blocks that are not
targets. (Injectivity of the address map on `ls` alone is weaker and is not enough: the stack
`JUMP` searches all blocks; the tests refute that weaker checker.) -/
theorem checkTerm_djmp_noCollide {addr : LabelAddr} {f : Func} {sf : SFunc}
    {layout : Label → List Operand} {lbl : Label} {t : Inst} {S : List Operand} {c : Operand}
    {ts : List Operand} {ls : List Label}
    (h : checkTerm addr f sf layout lbl t .djump S = true) (hop : t.op = .djmp)
    (ht : t.args = c :: ts) (hls : asLabels ts = some ls) {sb : SBlock} (hsb : sb ∈ sf.blocks)
    {l : Label} (hl : l ∈ ls) (he : addr sb.label = addr l) : sb.label = l := by
  unfold checkTerm at h
  rw [hop, ht] at h
  simp only at h
  rcases S with _ | ⟨c', S'⟩
  · simp at h
  · simp only [hls, Bool.and_eq_true, List.all_eq_true] at h
    simpa [he] using h.2 sb hsb l hl

/-- **Injectivity on the targets.** Corollary: two targets with a stack block and the same address
are the same label. -/
theorem checkTerm_djmp_inj {addr : LabelAddr} {f : Func} {sf : SFunc}
    {layout : Label → List Operand} {lbl : Label} {t : Inst} {S : List Operand} {c : Operand}
    {ts : List Operand} {ls : List Label}
    (h : checkTerm addr f sf layout lbl t .djump S = true) (hop : t.op = .djmp)
    (ht : t.args = c :: ts) (hls : asLabels ts = some ls) {l₁ l₂ : Label} (h₂ : l₂ ∈ ls)
    (hb : ∃ sb ∈ sf.blocks, sb.label = l₁) (he : addr l₁ = addr l₂) : l₁ = l₂ := by
  obtain ⟨sb, hsb, rfl⟩ := hb
  exact checkTerm_djmp_noCollide h hop ht hls hsb h₂ he

end EvmYul.Venom.StackLowering
