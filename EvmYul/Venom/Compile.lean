module

public import EvmYul.Venom.Semantics
public import EvmYul.ProofTags

public section

/-!
# Compiling the Venom straight-line fragment to EVM stack code, with a correctness proof

**Scheme.** Every SSA variable stays on the EVM stack where it was produced; the stack *layout* `L`
lists the variables from the top down. An operand is loaded with `PUSH32 n` (literal) or `DUPk`
(variable at depth `k − 1`, counting the temporaries already pushed), and the operands are pushed
last-first, so that operand `i` is `μₛ[i]` when the operation runs. `assert a` becomes
`ISZERO; PUSH2 R; JUMPI` with `R` a shared `JUMPDEST; PUSH0; PUSH0; REVERT` block (`Assemble.lean`).
A variable deeper than `DUP16` can reach makes compilation fail (`none`): the scheme has no
`SWAP`/`POP` scheduling, which is what the Vyper compiler's own stack scheduler adds.

`Asm` is the EVM instruction subset the compiler emits, with its stack semantics `runAsm`; the
assembler (`Assemble.lean`) turns it into bytecode, and that last step is checked against `Θ` by
the build-time tests, not proved.

**Theorem** (`compile_correct`). If `compile p = some c`, then running `c` on the empty stack gives
exactly the result of the Venom semantics: same outcome, same terminator data, same final state and
**the same gas**, for every machine state and every choice of primitive effects. The stack-height
claim of the plan (`height' = height − pops + pushes`) is a consequence (`pushArgs_run`).
-/

namespace EvmYul.Venom

open GasConstants

@[expose] section

/-- The EVM instructions the compiler emits. -/
inductive Asm where
  /-- `PUSH32 n`. -/
  | push (n : UInt256)
  /-- `DUPk`, `1 ≤ k ≤ 16`. -/
  | dup (k : ℕ)
  /-- The EVM instruction of a pure operation. -/
  | op (o : PureOp)
  /-- The EVM instruction of an effect. -/
  | eff (e : Eff)
  /-- `ISZERO; PUSH2 R; JUMPI` to the shared revert block `R`. -/
  | assertJ
  /-- `STOP`, `RETURN` or `REVERT`. -/
  | halt (h : Halt)
  deriving Repr, DecidableEq, Inhabited

end

variable {σ : Type}

/-- Stack semantics of `Asm` code (top of stack first), with gas. Running off the end stops, as
on the EVM. `none` is a stack underflow or an invalid `DUP`. -/
@[expose] def runAsm (P : Prims σ) : List Asm → List UInt256 → σ → ℕ → Option (Final σ)
  | [], _, s, g => some ⟨.stopped, [], s, g + P.haltCost .stop s []⟩
  | .push n :: c, stk, s, g => runAsm P c (n :: stk) s (g + Gverylow)
  | .dup k :: c, stk, s, g =>
    if 1 ≤ k ∧ k ≤ 16 ∧ k ≤ stk.length then runAsm P c (stk.getD (k - 1) default :: stk) s (g + Gverylow)
    else none
  | .op o :: c, stk, s, g =>
    if o.arity ≤ stk.length then runAsm P c (o.eval (stk.take o.arity) :: stk.drop o.arity) s (g + o.gas)
    else none
  | .eff e :: c, stk, s, g =>
    if e.arity ≤ stk.length then
      runAsm P c (if e.produces then (P.apply e s (stk.take e.arity)).1 :: stk.drop e.arity
                  else stk.drop e.arity)
        (P.apply e s (stk.take e.arity)).2 (g + P.cost e s (stk.take e.arity))
    else none
  | .assertJ :: c, stk, s, g =>
    match stk with
    | [] => none
    | x :: stk' =>
      if x = word 0 then
        some ⟨.reverted, [word 0, word 0], s,
          g + assertPassGas + assertFailGas + P.haltCost .revert s [word 0, word 0]⟩
      else runAsm P c stk' s (g + assertPassGas)
  | .halt h :: _, stk, s, g =>
    if h.arity ≤ stk.length then some ⟨h.outcome, stk.take h.arity, s, g + P.haltCost h s (stk.take h.arity)⟩
    else none

/-- The code loading one operand, with `t` temporaries above the variables of layout `L`. -/
@[expose] def pushOperand (L : List ℕ) (t : ℕ) : Operand → Option Asm
  | .lit n => some (.push n)
  | .var v => if v ∈ L ∧ L.idxOf v + t + 1 ≤ 16 then some (.dup (L.idxOf v + t + 1)) else none

/-- The code loading a list of operands in order, starting with `t` temporaries. -/
@[expose] def pushRev (L : List ℕ) : ℕ → List Operand → Option (List Asm)
  | _, [] => some []
  | t, x :: xs => do
    let a ← pushOperand L t x
    let r ← pushRev L (t + 1) xs
    some (a :: r)

/-- The code loading the operands of an instruction, last first (so operand `i` ends at `μₛ[i]`). -/
@[expose] def pushArgs (L : List ℕ) (args : List Operand) : Option (List Asm) := pushRev L 0 args.reverse

/-- Compile a program with stack layout `L`. -/
@[expose] def compileFrom : List ℕ → Program → Option (List Asm)
  | _, [] => some [.halt .stop]
  | L, .pure dst o args :: rest =>
    if args.length = o.arity then do
      let c ← pushArgs L args
      let r ← compileFrom (dst :: L) rest
      some (c ++ .op o :: r)
    else none
  | L, .eff dst e args :: rest =>
    if args.length = e.arity ∧ dst.isSome = e.produces then do
      let c ← pushArgs L args
      let r ← compileFrom (match dst with | some d => d :: L | none => L) rest
      some (c ++ .eff e :: r)
    else none
  | L, .assert a :: rest => do
    let c ← pushArgs L [a]
    let r ← compileFrom L rest
    some (c ++ .assertJ :: r)
  | L, .halt h args :: _ =>
    if args.length = h.arity then do
      let c ← pushArgs L args
      some (c ++ [.halt h])
    else none

/-- Compile a program (empty stack, no variables). -/
@[expose] def compile (p : Program) : Option (List Asm) := compileFrom [] p

/-! ## Correctness -/

/-- The stack `stk` holds the variables of layout `L` with their values in `st`. -/
@[expose] def LayoutOK (L : List ℕ) (st : Store) (stk : List UInt256) : Prop :=
  stk.length = L.length ∧ ∀ v ∈ L, st v = some (stk.getD (L.idxOf v) default)

theorem LayoutOK.empty : LayoutOK [] Store.empty [] := ⟨rfl, fun _ h => by simp at h⟩

theorem LayoutOK.cons {L : List ℕ} {st : Store} {stk : List UInt256} (h : LayoutOK L st stk)
    (d : ℕ) (x : UInt256) : LayoutOK (d :: L) (st.set d x) (x :: stk) := by
  refine ⟨by simp [h.1], fun v hv => ?_⟩
  by_cases hvd : v = d
  · subst hvd; simp [Store.set, List.idxOf_cons_self]
  · simpa [Store.set, hvd, List.idxOf_cons, Ne.symm hvd] using h.2 v (by simpa [hvd] using hv)

@[reviewed_generic "`Option` traversal of a reversed list (Venom compiler proof)"]
theorem mapM_reverse_option {α β : Type} (f : α → Option β) (l : List α) :
    l.reverse.mapM f = (l.mapM f).map List.reverse := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [List.reverse_cons, List.mapM_append, ih]
    cases h₁ : xs.mapM f <;> cases h₂ : f x <;> simp [List.mapM_cons, h₁, h₂]

@[reviewed_generic "`Option` traversal keeps the length (Venom compiler proof)"]
theorem mapM_length_option {α β : Type} (f : α → Option β) :
    ∀ (l : List α) {vs : List β}, l.mapM f = some vs → vs.length = l.length
  | [], vs, h => by simp at h; simp [← h]
  | x :: xs, vs, h => by
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y, _, ys, hys, rfl⟩ := h
    simp [mapM_length_option f xs hys]

/-- Loading operands: the code pushes their values (in reverse list order) and charges
`W_verylow` per operand. -/
theorem pushRev_run (P : Prims σ) {L : List ℕ} {st : Store} {base : List UInt256}
    (hL : LayoutOK L st base) :
    ∀ (xs : List Operand) (temps : List UInt256) (c : List Asm),
      pushRev L temps.length xs = some c →
      ∃ vs, xs.mapM (evalOperand st) = some vs ∧
        ∀ rest s g, runAsm P (c ++ rest) (temps ++ base) s g =
          runAsm P rest (vs.reverse ++ temps ++ base) s (g + Gverylow * xs.length)
  | [], temps, c, h => by
    simp only [pushRev, Option.some.injEq] at h; subst h
    exact ⟨[], rfl, fun rest s g => by simp⟩
  | x :: xs, temps, c, h => by
    simp only [pushRev, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨a, ha, r, hr, rfl⟩ := h
    cases x with
    | lit n =>
      simp only [pushOperand, Option.some.injEq] at ha; subst ha
      obtain ⟨vs, hvs, hrun⟩ := pushRev_run P hL xs (n :: temps) r (by simpa using hr)
      refine ⟨n :: vs, by simp [List.mapM_cons, evalOperand, hvs], fun rest s g => ?_⟩
      simp only [List.cons_append, runAsm]
      rw [show n :: (temps ++ base) = (n :: temps) ++ base from rfl, hrun]
      simp [List.length_cons, Nat.mul_succ, Nat.add_assoc, Nat.add_comm Gverylow]
    | var v =>
      simp only [pushOperand] at ha
      split at ha
      · rename_i hv
        simp only [Option.some.injEq] at ha; subst ha
        obtain ⟨hvL, hk⟩ := hv
        have hidx : L.idxOf v < L.length := List.idxOf_lt_length_iff.mpr hvL
        set y := base.getD (L.idxOf v) default with hy
        obtain ⟨vs, hvs, hrun⟩ := pushRev_run P hL xs (y :: temps) r (by simpa using hr)
        refine ⟨y :: vs, by simp [List.mapM_cons, evalOperand, hL.2 v hvL, hvs, hy],
          fun rest s g => ?_⟩
        have hget : (temps ++ base).getD (L.idxOf v + temps.length + 1 - 1) default = y := by
          rw [show L.idxOf v + temps.length + 1 - 1 = temps.length + L.idxOf v by omega,
            List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
          simp [hy, List.getD_eq_getElem?_getD]
        have hcond : 1 ≤ L.idxOf v + temps.length + 1 ∧ L.idxOf v + temps.length + 1 ≤ 16 ∧
            L.idxOf v + temps.length + 1 ≤ (temps ++ base).length := by
          simp only [List.length_append, hL.1]; omega
        simp only [List.cons_append, runAsm, if_pos hcond, hget]
        rw [show y :: (temps ++ base) = (y :: temps) ++ base from rfl, hrun]
        simp [List.length_cons, Nat.mul_succ, Nat.add_assoc, Nat.add_comm Gverylow]
      · simp at ha

/-- Loading the operands of an instruction: afterwards `μₛ[i]` is the value of operand `i`, the
stack has grown by the number of operands, and `W_verylow` per operand was charged. -/
theorem pushArgs_run (P : Prims σ) {L : List ℕ} {st : Store} {stk : List UInt256}
    (hL : LayoutOK L st stk) {args : List Operand} {c : List Asm} (h : pushArgs L args = some c) :
    ∃ vs, evalArgs st args = some vs ∧ vs.length = args.length ∧
      ∀ rest s g, runAsm P (c ++ rest) stk s g =
        runAsm P rest (vs ++ stk) s (g + operandGas * args.length) := by
  obtain ⟨vs, hvs, hrun⟩ := pushRev_run P hL args.reverse [] c h
  have hmap : evalArgs st args = some vs.reverse := by
    have := mapM_reverse_option (evalOperand st) args
    rcases h' : args.mapM (evalOperand st) with _ | w <;> simp [h', hvs] at this
    simp [evalArgs, h', this]
  have hlen : vs.length = args.length := by
    simpa using mapM_length_option (evalOperand st) args.reverse hvs
  exact ⟨vs.reverse, hmap, by simp [hlen], fun rest s g => by simpa [operandGas] using hrun rest s g⟩

/-- **Compiler correctness**, from any layout: compiled code run on a stack matching the layout
gives exactly the Venom result, gas included. -/
theorem compileFrom_correct (P : Prims σ) :
    ∀ (p : Program) (L : List ℕ) (st : Store) (stk : List UInt256) (s : σ) (g : ℕ) (c : List Asm),
      LayoutOK L st stk → compileFrom L p = some c → runAsm P c stk s g = run P p st s g
  | [], L, st, stk, s, g, c, _, h => by
    simp only [compileFrom, Option.some.injEq] at h; subst h
    simp [runAsm, run, Halt.arity, Halt.outcome]
  | .pure dst o args :: rest, L, st, stk, s, g, c, hL, h => by
    simp only [compileFrom] at h
    split at h
    · rename_i hlen
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨c₁, hc₁, r, hr, rfl⟩ := h
      obtain ⟨vs, hvs, hvl, hrun⟩ := pushArgs_run P hL hc₁
      rw [hrun]
      simp only [runAsm, if_pos (by simp [hvl, hlen] : o.arity ≤ (vs ++ stk).length),
        List.take_left' (hvl.trans hlen), List.drop_left' (hvl.trans hlen), run, if_pos hlen, hvs,
        Option.bind_eq_bind, Option.bind_some]
      exact compileFrom_correct P rest (dst :: L) _ _ s _ r (hL.cons dst _) hr
    · simp at h
  | .eff dst e args :: rest, L, st, stk, s, g, c, hL, h => by
    simp only [compileFrom] at h
    split at h
    · rename_i hcond
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨c₁, hc₁, r, hr, rfl⟩ := h
      obtain ⟨vs, hvs, hvl, hrun⟩ := pushArgs_run P hL hc₁
      rw [hrun]
      simp only [runAsm, if_pos (by simp [hvl, hcond.1] : e.arity ≤ (vs ++ stk).length),
        List.take_left' (hvl.trans hcond.1), List.drop_left' (hvl.trans hcond.1), run,
        if_pos hcond, hvs, Option.bind_eq_bind, Option.bind_some]
      cases dst with
      | some d =>
        simp only [← hcond.2, Option.isSome_some, if_true]
        exact compileFrom_correct P rest (d :: L) _ _ _ _ r (hL.cons d _) hr
      | none =>
        simp only [← hcond.2, Option.isSome_none, Bool.false_eq_true, if_false]
        exact compileFrom_correct P rest L _ _ _ _ r hL hr
    · simp at h
  | .assert a :: rest, L, st, stk, s, g, c, hL, h => by
    simp only [compileFrom, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨c₁, hc₁, r, hr, rfl⟩ := h
    obtain ⟨vs, hvs, hvl, hrun⟩ := pushArgs_run P hL hc₁
    rw [hrun]
    match vs, hvs, hvl with
    | [x], hvs, _ =>
      have hx : evalOperand st a = some x := by
        simp only [evalArgs, List.mapM_cons, List.mapM_nil] at hvs
        cases h' : evalOperand st a <;> simp_all
      simp only [run, hx, Option.bind_eq_bind, Option.bind_some]
      simp only [List.singleton_append, runAsm, List.length_singleton, Nat.mul_one]
      split
      · simp [Nat.add_assoc]
      · exact compileFrom_correct P rest L st stk s _ r hL hr
  | .halt hh args :: _, L, st, stk, s, g, c, hL, h => by
    simp only [compileFrom] at h
    split at h
    · rename_i hlen
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨c₁, hc₁, rfl⟩ := h
      obtain ⟨vs, hvs, hvl, hrun⟩ := pushArgs_run P hL hc₁
      rw [hrun]
      simp [runAsm, run, hvl, hlen, hvs, List.take_left' (hvl.trans hlen)]
    · simp at h

/-- **Compiler correctness.** Compiled code, run from the empty stack, gives exactly the result of
the Venom semantics from the empty store: outcome, terminator data, final state and gas, for every
machine state and every interpretation of the primitive effects. -/
theorem compile_correct (P : Prims σ) {p : Program} {c : List Asm} (h : compile p = some c)
    (s : σ) (g : ℕ) : runAsm P c [] s g = run P p Store.empty s g :=
  compileFrom_correct P p [] _ [] s g c LayoutOK.empty h

end EvmYul.Venom
