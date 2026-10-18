module

public import EvmYul.Venom.LoweringCheck

public section

/-!
# Lowering control-flow graphs to stack code: stack layouts across blocks and φs at block edges

`LoweringCheck.lean` checks one basic block from a given symbolic stack. A function has many
blocks, and the stack a block leaves must be the stack each successor expects, **after** the φ copy
of that edge. This module adds the control flow to both sides and a checker for whole functions.

**Venom side** (`VFunc`). Blocks of the straight-line fragment with leading φs
`%x = phi @p₁, a₁, @p₂, a₂, …` (stored as `(x, [(p₁, a₁), (p₂, a₂), …])`) and a terminator: `jmp`,
`jnz c, @t, @e` (zero goes to `@e`, as in Venom and `Cfg.lean`) or a halt. `runCfg` runs it with fuel:
the φs of a block are a **parallel** copy (`applyPhisF` reads every source from the store at block
entry), then the body (`runBody`, the block-level form of `run`), then the terminator.

**Stack side** (`SFunc`). Blocks of `SAsm` code with a terminator `jump l`, `jumpi t e` (pops the
condition) or `halts`. `runSCfg` runs it; its gas is that of the assembled bytes: `JUMPDEST` on
entering a block, `PUSH2` + `JUMP`/`JUMPI` for the terminators (`assembleCfg`).

**The checker** (`checkCfg`). Each block carries an entry *layout*: the operands its stack holds,
top first. A block's code is checked symbolically from its layout (`checkBody`, the body form of
`validateLowering`, with the same freshness condition). At an edge `b → l` the exit stack must equal
`layout l` with every φ output of `l` replaced by its source for predecessor `b` (`edgeOk`); the φ
outputs must be distinct, every φ must have a source for `b`, and that source must be a literal or
on the exit stack, so that the φ copy cannot fault. A `jnz` additionally needs its condition on
top, and the rest of the stack must fit **both** successors. The entry block has no φs and an
empty layout.

**Theorem** (`checkCfg_sound`). If the checker accepts, then for **every fuel**, every machine state
and every interpretation of the primitive effects, the stack function and the Venom function end
the same way: the same outcome, terminator data and final state, or both fault, or both run out of
fuel. The proof is an induction on the fuel whose invariant is the edge relation; inside a block it
is the body lemma `checkBody_sound`.

The block-level runners are not a second semantics: `run_eq_runBody` and `runSAsm_eq_runSBody`
prove that on a single block they are `run` and `runSAsm`.
-/

namespace EvmYul.Venom

open GasConstants

/-! ## Block-level runners -/

@[expose] section

/-- How a block body ends: it falls through with its store or stack (`cont`), or it halts
(`exit`: a terminator or a failed `assert`). -/
inductive BOut (σ α : Type) where
  /-- The body ran to its end. -/
  | cont (x : α) (s : σ) (g : ℕ)
  /-- The run ended inside the body. -/
  | exit (f : Final σ)

end

variable {σ : Type}

/-- The result of a whole run from a body result: falling off the end stops (as in `run`). -/
@[expose] def BOut.finish {α : Type} (P : Prims σ) : BOut σ α → Final σ
  | .cont _ s g => ⟨.stopped, [], s, g + P.haltCost .stop s []⟩
  | .exit f => f

/-- `run` for one block body: the same equations, but the end of the list falls through. -/
@[expose] def runBody (P : Prims σ) : Program → Store → σ → ℕ → Option (BOut σ Store)
  | [], st, s, g => some (.cont st s g)
  | .pure dst o args :: rest, st, s, g =>
    if args.length = o.arity then do
      let vs ← evalArgs st args
      runBody P rest (st.set dst (o.eval vs)) s (g + operandGas * args.length + o.gas)
    else none
  | .eff dst e args :: rest, st, s, g =>
    if args.length = e.arity ∧ dst.isSome = e.produces then do
      let vs ← evalArgs st args
      let g' := g + operandGas * args.length + P.cost e s vs
      match dst with
      | some d => runBody P rest (st.set d (P.apply e s vs).1) (P.apply e s vs).2 g'
      | none => runBody P rest st (P.apply e s vs).2 g'
    else none
  | .assert a :: rest, st, s, g => do
    let x ← evalOperand st a
    if x = word 0 then
      some (.exit ⟨.reverted, [word 0, word 0], s,
        g + operandGas + assertPassGas + assertFailGas + P.haltCost .revert s [word 0, word 0]⟩)
    else runBody P rest st s (g + operandGas + assertPassGas)
  | .halt h args :: _, st, s, g =>
    if args.length = h.arity then do
      let vs ← evalArgs st args
      some (.exit ⟨h.outcome, vs, s, g + operandGas * args.length + P.haltCost h s vs⟩)
    else none

/-- `runSAsm` for one block of stack code: the same equations, but the end falls through. -/
@[expose] def runSBody (P : Prims σ) : List SAsm → List UInt256 → σ → ℕ →
    Option (BOut σ (List UInt256))
  | [], stk, s, g => some (.cont stk s g)
  | .push n :: c, stk, s, g => runSBody P c (n :: stk) s (g + Gverylow)
  | .dup k :: c, stk, s, g =>
    if 1 ≤ k ∧ k ≤ 16 ∧ k ≤ stk.length then
      runSBody P c (stk.getD (k - 1) default :: stk) s (g + Gverylow)
    else none
  | .swap k :: c, stk, s, g =>
    if 1 ≤ k ∧ k ≤ 16 ∧ k < stk.length then runSBody P c (swapTop k stk) s (g + Gverylow)
    else none
  | .pop :: c, stk, s, g =>
    match stk with
    | [] => none
    | _ :: stk' => runSBody P c stk' s (g + Gbase)
  | .op o :: c, stk, s, g =>
    if o.arity ≤ stk.length then
      runSBody P c (o.eval (stk.take o.arity) :: stk.drop o.arity) s (g + o.gas)
    else none
  | .eff e :: c, stk, s, g =>
    if e.arity ≤ stk.length then
      runSBody P c (if e.produces then (P.apply e s (stk.take e.arity)).1 :: stk.drop e.arity
                  else stk.drop e.arity)
        (P.apply e s (stk.take e.arity)).2 (g + P.cost e s (stk.take e.arity))
    else none
  | .assertJ :: c, stk, s, g =>
    match stk with
    | [] => none
    | x :: stk' =>
      if x = word 0 then
        some (.exit ⟨.reverted, [word 0, word 0], s,
          g + assertPassGas + assertFailGas + P.haltCost .revert s [word 0, word 0]⟩)
      else runSBody P c stk' s (g + assertPassGas)
  | .halt h :: _, stk, s, g =>
    if h.arity ≤ stk.length then
      some (.exit ⟨h.outcome, stk.take h.arity, s, g + P.haltCost h s (stk.take h.arity)⟩)
    else none

/-- **`runBody` is `run` on one block**: running a body and stopping at its end is `run`. -/
theorem run_eq_runBody (P : Prims σ) :
    ∀ (p : Program) (st : Store) (s : σ) (g : ℕ),
      run P p st s g = (runBody P p st s g).map (BOut.finish P)
  | [], _, _, _ => rfl
  | .pure dst o args :: rest, st, s, g => by
    simp only [run, runBody]
    split
    · cases evalArgs st args with
      | none => rfl
      | some vs => exact run_eq_runBody P rest _ s _
    · rfl
  | .eff dst e args :: rest, st, s, g => by
    simp only [run, runBody]
    split
    · cases evalArgs st args with
      | none => rfl
      | some vs => cases dst <;> exact run_eq_runBody P rest _ _ _
    · rfl
  | .assert a :: rest, st, s, g => by
    simp only [run, runBody]
    cases evalOperand st a with
    | none => rfl
    | some x =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      split
      · rfl
      · exact run_eq_runBody P rest st s _
  | .halt h args :: _, st, s, g => by
    simp only [run, runBody]
    split
    · cases evalArgs st args <;> rfl
    · rfl

/-- **`runSBody` is `runSAsm` on one block**. -/
theorem runSAsm_eq_runSBody (P : Prims σ) (c : List SAsm) :
    ∀ (stk : List UInt256) (s : σ) (g : ℕ),
      runSAsm P c stk s g = (runSBody P c stk s g).map (BOut.finish P) := by
  induction c with
  | nil => intros; rfl
  | cons a c ih =>
    intro stk s g
    cases a <;> (try cases stk) <;> simp only [runSAsm, runSBody] <;> (try split) <;>
      first | rfl | exact ih _ _ _

/-! ## The body checker -/

@[expose] section

/-- Result of checking a body: it falls through with symbolic stack `S`, or it halts. -/
inductive BodyCheck where
  /-- Falls through; the stack then holds `S` (top first). -/
  | cont (S : List Operand)
  /-- Ends in a matched terminator. -/
  | exit
  deriving Repr, DecidableEq

end

/-- `validateLowering` for one block body: the same conditions (the freshness condition included),
but the end of both lists falls through with the symbolic stack, and a halt must be matched by a
halt (falling through on one side only is rejected). -/
@[expose] def checkBody : Program → List SAsm → List Operand → Option BodyCheck
  | p, .push n :: c, S => checkBody p c (.lit n :: S)
  | p, .dup k :: c, S =>
    if 1 ≤ k ∧ k ≤ 16 ∧ k ≤ S.length then checkBody p c (S.getD (k - 1) default :: S) else none
  | p, .swap k :: c, S =>
    if 1 ≤ k ∧ k ≤ 16 ∧ k < S.length then checkBody p c (swapTop k S) else none
  | p, .pop :: c, S =>
    match S with
    | [] => none
    | _ :: S' => checkBody p c S'
  | [], [], S => some (.cont S)
  | .pure d o args :: rest, .op o' :: c, S =>
    if o = o' ∧ args.length = o.arity ∧ S.take o.arity = args ∧ freshIn d (S.drop o.arity) = true
    then checkBody rest c (.var d :: S.drop o.arity) else none
  | .eff dst e args :: rest, .eff e' :: c, S =>
    if e = e' ∧ args.length = e.arity ∧ S.take e.arity = args then
      match dst with
      | some d =>
        if e.produces = true ∧ freshIn d (S.drop e.arity) = true then
          checkBody rest c (.var d :: S.drop e.arity)
        else none
      | none => if e.produces = false then checkBody rest c (S.drop e.arity) else none
    else none
  | .assert a :: rest, .assertJ :: c, a' :: S => if a = a' then checkBody rest c S else none
  | .halt h args :: _, .halt h' :: _, S =>
    if h = h' ∧ args.length = h.arity ∧ S.take h.arity = args then some .exit else none
  | _, _, _ => none

/-- The symbolic stack `S` holds, in store `st`, exactly the values of the concrete stack `stk`. -/
@[expose] def StackRel (S : List Operand) (st : Store) (stk : List UInt256) : Prop :=
  S.map (evalOperand st) = stk.map some

/-- How a checked body's two runs correspond: falling through with the same machine state and
related stacks (only when the check fell through), halting with the same observation, or both
failing. -/
@[expose] def BodyMatch (r : BodyCheck) :
    Option (BOut σ Store) → Option (BOut σ (List UInt256)) → Prop
  | some (.cont st s _), some (.cont stk s' _) =>
    match r with
    | .cont S => s = s' ∧ StackRel S st stk
    | .exit => False
  | some (.exit f), some (.exit f') => f.obs = f'.obs
  | none, none => True
  | _, _ => False

private theorem stackRel_cons {st : Store} {S : List Operand} {stk : List UInt256} {o : Operand}
    {x : UInt256} (ho : evalOperand st o = some x) (h : StackRel S st stk) :
    StackRel (o :: S) st (x :: stk) := by
  unfold StackRel at *; simp [ho, h]

/-- **Soundness of the body checker** (induction on the stack code). If `checkBody` accepts code `c`
for body `p` from symbolic stack `S`, and `S` holds the values of the concrete stack, then the two
block runs correspond (`BodyMatch`): both fall through with the same state and the checker's exit
stack related to the concrete one, or both halt with the same observation, or both fail. -/
theorem checkBody_sound (P : Prims σ) :
    ∀ (c : List SAsm) (p : Program) (S : List Operand) (st : Store) (stk : List UInt256) (s : σ)
      (g g' : ℕ) (r : BodyCheck), checkBody p c S = some r → StackRel S st stk →
      BodyMatch r (runBody P p st s g') (runSBody P c stk s g) := by
  intro c
  induction c with
  | nil =>
    intro p S st stk s g g' r hv hrel
    cases p with
    | nil =>
      simp only [checkBody, Option.some.injEq] at hv; subst hv
      exact ⟨rfl, hrel⟩
    | cons i rest => cases i <;> simp [checkBody] at hv
  | cons a c ih =>
    intro p S st stk s g g' r hv hrel
    have hlen := length_of_rel hrel
    cases a with
    | push n =>
      simp only [checkBody] at hv
      exact ih p _ st _ s _ g' r hv (stackRel_cons rfl hrel)
    | dup k =>
      simp only [checkBody] at hv
      split at hv
      · simp only [runSBody, if_pos (show 1 ≤ k ∧ k ≤ 16 ∧ k ≤ stk.length by omega)]
        exact ih p _ st _ s _ g' r hv
          (stackRel_cons (rel_getD hrel (show k - 1 < S.length by omega) _ _) hrel)
      · simp at hv
    | swap k =>
      simp only [checkBody] at hv
      split at hv
      · simp only [runSBody, if_pos (show 1 ≤ k ∧ k ≤ 16 ∧ k < stk.length by omega)]
        exact ih p _ st _ s _ g' r hv (rel_swap k hrel)
      · simp at hv
    | pop =>
      obtain _ | ⟨x, S'⟩ := S
      · simp [checkBody] at hv
      obtain _ | ⟨y, stk'⟩ := stk
      · simp at hlen
      simp only [checkBody] at hv
      simp only [runSBody]
      exact ih p S' st stk' s _ g' r hv (List.cons.inj hrel).2
    | op o' =>
      cases p with
      | cons i rest =>
        cases i with
        | pure d o args =>
          simp only [checkBody] at hv
          split at hv
          · rename_i hc
            obtain ⟨rfl, hlenA, htake, hfresh⟩ := hc
            obtain ⟨har, hargs⟩ := take_rel hrel hlenA htake
            simp only [runSBody, if_pos har, runBody, if_pos hlenA, hargs, Option.bind_eq_bind,
              Option.bind_some]
            exact ih rest _ _ _ s _ _ r hv (rel_push_fresh (rel_drop hrel _) hfresh _)
          · simp at hv
        | _ => simp [checkBody] at hv
      | _ => simp [checkBody] at hv
    | eff e' =>
      cases p with
      | cons i rest =>
        cases i with
        | eff dst e args =>
          simp only [checkBody] at hv
          split at hv
          · rename_i hc
            obtain ⟨rfl, hlenA, htake⟩ := hc
            obtain ⟨har, hargs⟩ := take_rel hrel hlenA htake
            cases dst with
            | some d =>
              simp only at hv
              split at hv
              · rename_i hc'
                obtain ⟨hp, hfresh⟩ := hc'
                simp only [runSBody, if_pos har, hp, if_true, runBody, hargs, Option.bind_eq_bind,
                  Option.bind_some,
                  if_pos (show args.length = e.arity ∧ (some d).isSome = true by simp [hlenA])]
                exact ih rest _ _ _ _ _ _ r hv (rel_push_fresh (rel_drop hrel _) hfresh _)
              · simp at hv
            | none =>
              simp only at hv
              split at hv
              · rename_i hp
                simp only [runSBody, if_pos har, hp, Bool.false_eq_true, if_false, runBody, hargs,
                  Option.bind_eq_bind, Option.bind_some,
                  if_pos (show args.length = e.arity ∧ (none : Option ℕ).isSome = false by
                    simp [hlenA])]
                exact ih rest _ _ _ _ _ _ r hv (rel_drop hrel _)
              · simp at hv
          · simp at hv
        | _ => simp [checkBody] at hv
      | _ => simp [checkBody] at hv
    | assertJ =>
      cases p with
      | cons i rest =>
        cases i with
        | assert a =>
          obtain _ | ⟨a', S'⟩ := S
          · simp [checkBody] at hv
          obtain _ | ⟨x, stk'⟩ := stk
          · simp at hlen
          simp only [checkBody] at hv
          split at hv
          · subst_vars
            simp only [StackRel, List.map_cons, List.cons.injEq] at hrel
            simp only [runSBody, runBody, hrel.1, Option.bind_eq_bind, Option.bind_some]
            split
            · simp [BodyMatch, Final.obs]
            · exact ih rest S' st stk' s _ _ r hv hrel.2
          · simp at hv
        | _ => simp [checkBody] at hv
      | _ => simp [checkBody] at hv
    | halt h' =>
      cases p with
      | cons i rest =>
        cases i with
        | halt h args =>
          simp only [checkBody] at hv
          split at hv
          · rename_i hc
            obtain ⟨rfl, hlenA, htake⟩ := hc
            obtain ⟨har, hargs⟩ := take_rel hrel hlenA htake
            simp [runSBody, if_pos har, runBody, hlenA, hargs, BodyMatch, Final.obs]
          · simp at hv
        | _ => simp [checkBody] at hv
      | _ => simp [checkBody] at hv

/-! ## Control-flow graphs -/

@[expose] section

/-- A Venom block terminator. -/
inductive Term where
  /-- `jmp @l`. -/
  | jmp (l : ℕ)
  /-- `jnz c, @t, @e`: to `@t` if `c ≠ 0`, to `@e` if `c = 0`. -/
  | jnz (c : Operand) (t e : ℕ)
  /-- A halting terminator (`stop`, `return`, `revert`). -/
  | halt (h : Halt) (args : List Operand)
  deriving Repr, Inhabited

end

@[expose] section

/-- A Venom block: label, φs `(x, [(pred, source), …])`, body, terminator. -/
structure VBlock where
  /-- The label. -/
  label : ℕ
  /-- The φs: `%x = phi @p₁, a₁, …` is `(x, [(p₁, a₁), …])`. -/
  phis : List (ℕ × List (ℕ × Operand))
  /-- The body (pure operations, effects, `assert`). -/
  body : Program
  /-- The terminator. -/
  term : Term
  deriving Repr, Inhabited

end

@[expose] section

/-- A Venom function: entry label and blocks. -/
structure VFunc where
  /-- The entry label. -/
  entry : ℕ
  /-- The blocks. -/
  blocks : List VBlock
  deriving Repr, Inhabited

end

@[expose] section

/-- A stack-code terminator. -/
inductive STerm where
  /-- `PUSH2 l; JUMP`. -/
  | jump (l : ℕ)
  /-- `PUSH2 t; JUMPI; PUSH2 e; JUMP`: pops the condition; to `t` if it is non-zero. -/
  | jumpi (t e : ℕ)
  /-- `STOP` (reached only if the code did not halt already). -/
  | halts
  deriving Repr, DecidableEq, Inhabited

end

@[expose] section

/-- A block of stack code. -/
structure SBlock where
  /-- The label. -/
  label : ℕ
  /-- The code. -/
  code : List SAsm
  /-- The terminator. -/
  term : STerm
  deriving Repr, Inhabited

end

@[expose] section

/-- A function in stack code. -/
structure SFunc where
  /-- The entry label. -/
  entry : ℕ
  /-- The blocks. -/
  blocks : List SBlock
  deriving Repr, Inhabited

end

@[expose] section

/-- The result of a CFG run: finished with `a`, a fault, or out of fuel. -/
inductive CfgOut (α : Type) where
  /-- Finished. -/
  | done (a : α)
  /-- A static error. -/
  | fault
  /-- The fuel ran out. -/
  | fuelOut
  deriving Repr, DecidableEq

end

/-- Map the finished value of a CFG result. -/
@[expose] def CfgOut.map {α β : Type} (f : α → β) : CfgOut α → CfgOut β
  | .done a => .done (f a)
  | .fault => .fault
  | .fuelOut => .fuelOut

/-- The block with label `l`. -/
@[expose] def VFunc.find? (f : VFunc) (l : ℕ) : Option VBlock := f.blocks.find? (·.label == l)

/-- The block with label `l`. -/
@[expose] def SFunc.find? (f : SFunc) (l : ℕ) : Option SBlock := f.blocks.find? (·.label == l)

/-- What a block executes as straight-line code: its body, then its terminator if that halts. -/
@[expose] def VBlock.code (b : VBlock) : Program :=
  b.body ++ match b.term with
    | .halt h args => [.halt h args]
    | _ => []

/-- The φs of a block entered from `prev`, as a **parallel** copy: every source is read from `st`,
the store at block entry. Entering the entry block (`prev = none`) with φs faults. -/
@[expose] def applyPhisF (prev : Option ℕ) (st : Store) (phis : List (ℕ × List (ℕ × Operand))) :
    Option Store :=
  phis.foldlM (init := st) fun acc (x, srcs) => do
    let p ← prev
    let o ← srcs.lookup p
    let v ← evalOperand st o
    pure (acc.set x v)

/-- Run a Venom function for at most `fuel` blocks, from block `cur` entered from `prev`. (Jumps
are free on this side: gas is not part of the soundness claim.) -/
@[expose] def runCfg (P : Prims σ) (f : VFunc) : ℕ → Option ℕ → ℕ → Store → σ → ℕ → CfgOut (Final σ)
  | 0, _, _, _, _, _ => .fuelOut
  | n + 1, prev, cur, st, s, g =>
    match f.find? cur with
    | none => .fault
    | some b =>
      match applyPhisF prev st b.phis with
      | none => .fault
      | some st₁ =>
        match runBody P b.code st₁ s g with
        | none => .fault
        | some (.exit fin) => .done fin
        | some (.cont st₂ s₂ g₂) =>
          match b.term with
          | .jmp l => runCfg P f n (some cur) l st₂ s₂ g₂
          | .jnz c t e =>
            match evalOperand st₂ c with
            | none => .fault
            | some v => runCfg P f n (some cur) (if v = word 0 then e else t) st₂ s₂ g₂
          | .halt _ _ => .fault

/-- Run a stack function for at most `fuel` blocks, from block `cur`. The gas is that of the
assembled bytes (`assembleCfg`): `JUMPDEST` on entering a block, `PUSH2` and `JUMP` (`W_mid`) or
`JUMPI` (`W_high`), and for a `jumpi` that falls through also its `PUSH2 e; JUMP`. -/
@[expose] def runSCfg (P : Prims σ) (f : SFunc) : ℕ → ℕ → List UInt256 → σ → ℕ → CfgOut (Final σ)
  | 0, _, _, _, _ => .fuelOut
  | n + 1, cur, stk, s, g =>
    match f.find? cur with
    | none => .fault
    | some b =>
      match runSBody P b.code stk s (g + Gjumpdest) with
      | none => .fault
      | some (.exit fin) => .done fin
      | some (.cont stk₂ s₂ g₂) =>
        match b.term with
        | .jump l => runSCfg P f n l stk₂ s₂ (g₂ + Gverylow + Gmid)
        | .jumpi t e =>
          match stk₂ with
          | [] => .fault
          | x :: stk₃ =>
            if x = word 0 then runSCfg P f n e stk₃ s₂ (g₂ + Gverylow + Ghigh + Gverylow + Gmid)
            else runSCfg P f n t stk₃ s₂ (g₂ + Gverylow + Ghigh)
        | .halts => .done ⟨.stopped, [], s₂, g₂ + P.haltCost .stop s₂ []⟩

/-! ## The function checker -/

/-- An operand at an edge into a block with φs `phis` from predecessor `pred`: a φ output becomes
its source for `pred` (`none` if it has none), anything else stays. -/
@[expose] def substPhi (phis : List (ℕ × List (ℕ × Operand))) (pred : ℕ) : Operand → Option Operand
  | .var x =>
    match phis.lookup x with
    | some srcs => srcs.lookup pred
    | none => some (.var x)
  | .lit n => some (.lit n)

/-- Is the operand a literal? -/
@[expose] def Operand.isLit : Operand → Bool
  | .lit _ => true
  | .var _ => false

/-- The edge `pred → l` leaves symbolic stack `S`: block `l` exists, its φ outputs are distinct,
every φ has a source for `pred` that is a literal or on `S`, and `S` is `layout l` with the φ
outputs replaced by their sources. -/
@[expose] def edgeOk (f : VFunc) (layout : ℕ → List Operand) (pred l : ℕ) (S : List Operand) :
    Bool :=
  match f.find? l with
  | none => false
  | some b =>
    decide ((b.phis.map Prod.fst).Nodup) &&
      b.phis.all (fun φ => match φ.2.lookup pred with
        | some o => o.isLit || decide (o ∈ S)
        | none => false) &&
      decide ((layout l).mapM (substPhi b.phis pred) = some S)

/-- Check one Venom block against its stack block: the code from the block's layout, then the
terminators and their edges. -/
@[expose] def checkBlock (f : VFunc) (sf : SFunc) (layout : ℕ → List Operand) (b : VBlock) : Bool :=
  match sf.find? b.label with
  | none => false
  | some sb =>
    match checkBody b.code sb.code (layout b.label) with
    | none => false
    | some .exit => true
    | some (.cont S) =>
      match b.term, sb.term with
      | .jmp l, .jump l' => l == l' && edgeOk f layout b.label l S
      | .jnz c t e, .jumpi t' e' =>
        t == t' && e == e' &&
          match S with
          | c' :: S' => c == c' && edgeOk f layout b.label t S' && edgeOk f layout b.label e S'
          | [] => false
      | _, _ => false

/-- **The function checker.** Same entry; the entry block exists, has no φs and an empty layout;
every Venom block passes `checkBlock`. -/
@[expose] def checkCfg (f : VFunc) (sf : SFunc) (layout : ℕ → List Operand) : Bool :=
  f.entry == sf.entry && (layout f.entry).isEmpty &&
    (match f.find? f.entry with
     | some b => b.phis.isEmpty
     | none => false) &&
    f.blocks.all (checkBlock f sf layout)

/-! ## Soundness -/

private theorem find?_spec {β : Type} {bs : List β} {key : β → ℕ} {l : ℕ} {b : β}
    (h : bs.find? (fun x => key x == l) = some b) : b ∈ bs ∧ key b = l :=
  ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

/-- The φ copy as a function of the variable (distinct outputs, every source defined). -/
private theorem applyPhisF_spec (p : ℕ) (st : Store) :
    ∀ (phis : List (ℕ × List (ℕ × Operand))) (acc : Store),
      (phis.map Prod.fst).Nodup →
      (∀ φ ∈ phis, ∃ o v, φ.2.lookup p = some o ∧ evalOperand st o = some v) →
      ∃ st₁, phis.foldlM (init := acc) (fun acc (x, srcs) => do
          let p ← some p
          let o ← srcs.lookup p
          let v ← evalOperand st o
          pure (acc.set x v)) = some st₁ ∧
        ∀ y, st₁ y = match phis.lookup y with
          | some srcs => (srcs.lookup p).bind (evalOperand st)
          | none => acc y
  | [], acc, _, _ => ⟨acc, rfl, fun y => by simp [List.lookup]⟩
  | (x, srcs) :: rest, acc, hnd, hsrc => by
    obtain ⟨o, v, ho, hv⟩ := hsrc (x, srcs) (by simp)
    have hnd' : (rest.map Prod.fst).Nodup := (List.nodup_cons.mp hnd).2
    have hx : x ∉ rest.map Prod.fst := (List.nodup_cons.mp hnd).1
    obtain ⟨st₁, h₁, h₂⟩ := applyPhisF_spec p st rest (acc.set x v) hnd'
      (fun φ hφ => hsrc φ (List.mem_cons_of_mem _ hφ))
    refine ⟨st₁, ?_, fun y => ?_⟩
    · simpa only [List.foldlM_cons, Option.bind_eq_bind, Option.bind_some, ho, hv,
        Option.pure_def] using h₁
    · rw [h₂ y]
      by_cases hyx : y = x
      · subst hyx
        have hnone : rest.lookup y = none := List.lookup_eq_none_iff.2 fun q hq =>
          bne_iff_ne.2 fun heq => hx (List.mem_map.mpr ⟨q, hq, heq.symm⟩)
        simp [hnone, List.lookup, Store.set, ho, hv]
      · simp [List.lookup, beq_false_of_ne hyx, Store.set, hyx]

private theorem mapM_rel {α β : Type} {f : α → Option β} {g : α → Option UInt256}
    {h : β → Option UInt256} :
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

private theorem evalOperand_of_mem {st : Store} {S : List Operand} {stk : List UInt256}
    (h : StackRel S st stk) {o : Operand} (ho : o ∈ S) : ∃ v, evalOperand st o = some v := by
  have : evalOperand st o ∈ stk.map some := by
    rw [← h]; exact List.mem_map.mpr ⟨o, ho, rfl⟩
  obtain ⟨v, _, hv⟩ := List.mem_map.mp this
  exact ⟨v, hv.symm⟩

/-- **The edge lemma.** Along an accepted edge `p → l` the φ copy succeeds, and afterwards block
`l`'s layout holds the values of the concrete stack. -/
private theorem edge_phis {f : VFunc} {layout : ℕ → List Operand} {p l : ℕ} {S : List Operand}
    {b : VBlock} {st : Store} {stk : List UInt256} (he : edgeOk f layout p l S = true)
    (hb : f.find? l = some b) (hrel : StackRel S st stk) :
    ∃ st₁, applyPhisF (some p) st b.phis = some st₁ ∧ StackRel (layout l) st₁ stk := by
  simp only [edgeOk, hb, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at he
  obtain ⟨⟨hnd, hsrc⟩, hmap⟩ := he
  have hsrc' : ∀ φ ∈ b.phis, ∃ o v, φ.2.lookup p = some o ∧ evalOperand st o = some v := by
    intro φ hφ
    have := hsrc φ hφ
    split at this
    · rename_i o ho
      refine ⟨o, ?_⟩
      cases o with
      | lit n => exact ⟨n, ho, rfl⟩
      | var v =>
        simp only [Operand.isLit, Bool.false_or, decide_eq_true_eq] at this
        obtain ⟨w, hw⟩ := evalOperand_of_mem hrel this
        exact ⟨w, ho, hw⟩
    · simp at this
  obtain ⟨st₁, h₁, h₂⟩ := applyPhisF_spec p st b.phis st hnd hsrc'
  refine ⟨st₁, h₁, ?_⟩
  unfold StackRel
  rw [← hrel]
  refine mapM_rel hmap (fun o _ o' ho' => ?_)
  cases o with
  | lit n => simp only [substPhi, Option.some.injEq] at ho'; subst ho'; rfl
  | var y =>
    simp only [substPhi] at ho'
    simp only [evalOperand, h₂ y]
    split at ho' <;> [simp [ho']; (cases ho'; simp)]

/-- The invariant at block entry: either the start (no predecessor, the entry block, empty
stack), or an accepted edge from `p` whose exit stack holds the concrete stack. -/
@[expose] def EntryRel (f : VFunc) (layout : ℕ → List Operand) (prev : Option ℕ) (cur : ℕ)
    (st : Store) (stk : List UInt256) : Prop :=
  (prev = none ∧ cur = f.entry ∧ stk = []) ∨
    ∃ p S, prev = some p ∧ edgeOk f layout p cur S = true ∧ StackRel S st stk

/-- **Soundness of the function checker**, from any related block entry (induction on the fuel). -/
theorem checkCfg_sound_from (P : Prims σ) {f : VFunc} {sf : SFunc} {layout : ℕ → List Operand}
    (hc : checkCfg f sf layout = true) :
    ∀ (n : ℕ) (prev : Option ℕ) (cur : ℕ) (st : Store) (stk : List UInt256) (s : σ) (g g' : ℕ),
      EntryRel f layout prev cur st stk →
      (runSCfg P sf n cur stk s g).map Final.obs = (runCfg P f n prev cur st s g').map Final.obs := by
  simp only [checkCfg, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff, List.all_eq_true] at hc
  obtain ⟨⟨⟨hentry, hlay⟩, hentryB⟩, hblocks⟩ := hc
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ _ _; rfl
  | succ n ih =>
    intro prev cur st stk s g g' hrel
    -- the block, its φs and the layout relation after them
    obtain ⟨b, hb, st₁, hphi, hrel₁⟩ : ∃ b, f.find? cur = some b ∧ ∃ st₁,
        applyPhisF prev st b.phis = some st₁ ∧ StackRel (layout cur) st₁ stk := by
      rcases hrel with ⟨rfl, rfl, rfl⟩ | ⟨p, S, rfl, he, hS⟩
      · split at hentryB
        · rename_i b hb
          refine ⟨b, hb, st, ?_, ?_⟩
          · simp at hentryB; simp [applyPhisF, hentryB]
          · simp [StackRel, hlay]
        · simp at hentryB
      · cases hb : f.find? cur with
        | none => simp [edgeOk, hb] at he
        | some b =>
          obtain ⟨st₁, h₁, h₂⟩ := edge_phis he hb hS
          exact ⟨b, rfl, st₁, h₁, h₂⟩
    obtain ⟨hbmem, hblabel⟩ := find?_spec hb
    have hcb := hblocks b hbmem
    simp only [checkBlock] at hcb
    split at hcb
    · simp at hcb
    rename_i sb hsb
    rw [hblabel] at hsb hcb
    simp only [runSCfg, runCfg, hb, hsb, hphi]
    cases hr : checkBody b.code sb.code (layout cur) with
    | none => simp [hr] at hcb
    | some r =>
      have hm := checkBody_sound P sb.code b.code (layout cur) st₁ stk s (g + Gjumpdest) g' r hr
        hrel₁
      simp only [hr] at hcb
      revert hm
      generalize runBody P b.code st₁ s g' = rv
      generalize runSBody P sb.code stk s (g + Gjumpdest) = rs
      intro hm
      rcases rv with _ | (⟨st₂, s₂, g₂⟩ | fv) <;> rcases rs with _ | (⟨stk₂, s₂', g₂'⟩ | fs) <;>
        simp only [BodyMatch] at hm
      · rfl
      · cases r with
        | exit => exact absurd hm id
        | cont S =>
          obtain ⟨rfl, hS⟩ := hm
          simp only at hcb ⊢
          split at hcb
          · rename_i l l' hbt hst
            simp only [Bool.and_eq_true, beq_iff_eq] at hcb
            obtain ⟨rfl, he⟩ := hcb
            simp only [hbt, hst]
            exact ih _ _ _ _ _ _ _ (Or.inr ⟨cur, S, rfl, he, hS⟩)
          · rename_i c t e t' e' hbt hst
            simp only [Bool.and_eq_true, beq_iff_eq] at hcb
            obtain ⟨⟨rfl, rfl⟩, hcS⟩ := hcb
            simp only [hbt, hst]
            cases S with
            | nil => simp at hcS
            | cons c' S' =>
              simp only [Bool.and_eq_true, beq_iff_eq] at hcS
              obtain ⟨⟨rfl, het⟩, hee⟩ := hcS
              cases stk₂ with
              | nil => simp [StackRel] at hS
              | cons x stk₃ =>
                simp only [StackRel, List.map_cons, List.cons.injEq] at hS
                obtain ⟨hcx, hS'⟩ := hS
                simp only [hcx]
                by_cases hx : x = word 0
                · simp only [hx, if_true]
                  exact ih _ _ _ _ _ _ _ (Or.inr ⟨cur, S', rfl, hee, hS'⟩)
                · simp only [hx, if_false]
                  exact ih _ _ _ _ _ _ _ (Or.inr ⟨cur, S', rfl, het, hS'⟩)
          · simp at hcb
      · simp [CfgOut.map, hm]

/-- **Soundness of the function checker.** If `checkCfg` accepts the stack function `sf` for the
Venom function `f` with layouts `layout`, then for every fuel, every machine state, every
interpretation of the primitive effects and any gas counters, running `sf` from its entry on the
empty stack and running `f` from its entry on the empty store end the same way: the same outcome,
terminator data and final state, or both fault, or both run out of fuel. -/
theorem checkCfg_sound (P : Prims σ) {f : VFunc} {sf : SFunc} {layout : ℕ → List Operand}
    (h : checkCfg f sf layout = true) (n : ℕ) (s : σ) (g g' : ℕ) :
    (runSCfg P sf n sf.entry [] s g).map Final.obs =
      (runCfg P f n none f.entry Store.empty s g').map Final.obs := by
  have he : f.entry = sf.entry := by
    simp only [checkCfg, Bool.and_eq_true, beq_iff_eq] at h; exact h.1.1.1
  rw [← he]
  exact checkCfg_sound_from P h n none f.entry Store.empty [] s g g' (Or.inl ⟨rfl, rfl, rfl⟩)

end EvmYul.Venom
