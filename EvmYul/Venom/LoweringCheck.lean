module

public import EvmYul.Venom.Compile

public section

/-!
# Checking a lowering of Venom to EVM stack code, `SWAP` and `POP` included

`Compile.lean` proves one fixed lowering scheme correct: every variable stays where it was
produced, operands are copied with `DUPk`, and there is no `SWAP` or `POP`. The Vyper compiler's own
stack scheduler is a heuristic that emits `SWAP` and `POP`. Proving each version of such a heuristic
correct would mean redoing the proof whenever it changes, so this file proves a **checker**
instead. The scheduler stays untrusted: the checker accepts or rejects each basic block and its
stack code, and every accepted pair is correct (`validateLowering_sound`).

**Stack code.** `SAsm` extends the compiler's `Asm` with `SWAPk` and `POP`. `runSAsm` is its stack
semantics, and on the image of `Asm` it is exactly `runAsm`, gas included (`runSAsm_embed`).

**The checker** (`validateLowering`) runs the stack code symbolically. A stack slot holds a Venom
operand: a literal, or the SSA variable whose value it carries. `PUSH`, `DUP`, `SWAP` and `POP`
rearrange the symbolic stack. When the code reaches an operation, it must be the next Venom
instruction, and the top of the symbolic stack must be exactly that instruction's operand list. The
result then becomes the symbol `%d`.

**Freshness** (the falsified first design). Naming a stack slot by its variable is sound only if
the variable is never assigned again while an older copy is still on the stack. The checker
therefore demands that `%d` does not occur in the rest of the stack when `%d` is defined. Without
this condition it accepts a wrong lowering of a program that assigns a variable twice (the
counterexample `naiveValidate` in `LoweringCheckTests.lean`).

**Theorem** (`validateLowering_sound`). If the checker accepts code `c` for program `p` from an
empty stack, then `c` and `p` end the same way: same outcome, same terminator data, same final
machine state, for every machine state and every interpretation of the primitive effects. Gas is not
part of this claim: a schedule with `SWAP`/`POP` costs a different amount, and the gas of
`Compile.lean`'s own scheme is proved separately (`validateLowering_compile_gas`).

**Gas of checked code** (`validateLowering_gas`). The Venom semantics charges `W_verylow` per
operand (`loadGas`); a schedule pays for its own `PUSH`/`DUP`/`SWAP`/`POP` instead (`shuffleGas`).
Every other charge is the same, because the checker forces the same effects on the same operands
in the same states. So for every accepted pair: `gas(p) ≤ gas(c) + loadGas p`,
`gas(c) ≤ gas(p) + shuffleGas c`, and, when `p` has no `assert` (nothing is cut short),
`gas(c) + loadGas p = gas(p) + shuffleGas c` exactly. For the proved compiler's code
`shuffleGas = loadGas` (`compileFrom_shuffleGas`), which gives `compile_correct`'s equal gas back.
-/

namespace EvmYul.Venom

open GasConstants

@[expose] section

/-- Stack code: the compiler's `Asm` together with the scheduling instructions `SWAPk` and `POP`. -/
inductive SAsm where
  /-- `PUSH32 n`. -/
  | push (n : UInt256)
  /-- `DUPk`, `1 ≤ k ≤ 16`. -/
  | dup (k : ℕ)
  /-- `SWAPk`, `1 ≤ k ≤ 16`: exchange the top with the item `k` places below it. -/
  | swap (k : ℕ)
  /-- `POP`. -/
  | pop
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

/-- The `SAsm` instruction of an `Asm` instruction. -/
@[expose] def Asm.toSAsm : Asm → SAsm
  | .push n => .push n
  | .dup k => .dup k
  | .op o => .op o
  | .eff e => .eff e
  | .assertJ => .assertJ
  | .halt h => .halt h

/-- `SWAPk` on a list, top first: exchange item `0` with item `k`. The caller checks
`k < l.length`. -/
@[expose] def swapTop {α : Type} (k : ℕ) : List α → List α
  | [] => []
  | x :: xs => xs.getD (k - 1) x :: xs.set (k - 1) x

variable {σ : Type}

/-- Stack semantics of `SAsm` code (top of stack first), with gas. It is `runAsm` with two more
cases: `SWAPk` (`W_verylow`) and `POP` (`W_base`). `none` is a stack underflow or an invalid
`DUP`/`SWAP`. -/
@[expose] def runSAsm (P : Prims σ) : List SAsm → List UInt256 → σ → ℕ → Option (Final σ)
  | [], _, s, g => some ⟨.stopped, [], s, g + P.haltCost .stop s []⟩
  | .push n :: c, stk, s, g => runSAsm P c (n :: stk) s (g + Gverylow)
  | .dup k :: c, stk, s, g =>
    if 1 ≤ k ∧ k ≤ 16 ∧ k ≤ stk.length then runSAsm P c (stk.getD (k - 1) default :: stk) s (g + Gverylow)
    else none
  | .swap k :: c, stk, s, g =>
    if 1 ≤ k ∧ k ≤ 16 ∧ k < stk.length then runSAsm P c (swapTop k stk) s (g + Gverylow)
    else none
  | .pop :: c, stk, s, g =>
    match stk with
    | [] => none
    | _ :: stk' => runSAsm P c stk' s (g + Gbase)
  | .op o :: c, stk, s, g =>
    if o.arity ≤ stk.length then runSAsm P c (o.eval (stk.take o.arity) :: stk.drop o.arity) s (g + o.gas)
    else none
  | .eff e :: c, stk, s, g =>
    if e.arity ≤ stk.length then
      runSAsm P c (if e.produces then (P.apply e s (stk.take e.arity)).1 :: stk.drop e.arity
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
      else runSAsm P c stk' s (g + assertPassGas)
  | .halt h :: _, stk, s, g =>
    if h.arity ≤ stk.length then some ⟨h.outcome, stk.take h.arity, s, g + P.haltCost h s (stk.take h.arity)⟩
    else none

/-- `SAsm` extends `Asm` conservatively: on embedded `Asm` code, `runSAsm` is `runAsm`, gas
included. -/
theorem runSAsm_embed (P : Prims σ) (c : List Asm) :
    ∀ (stk : List UInt256) (s : σ) (g : ℕ), runSAsm P (c.map Asm.toSAsm) stk s g = runAsm P c stk s g := by
  induction c with
  | nil => simp [runSAsm, runAsm]
  | cons a c ih =>
    intro stk s g
    cases a
    case assertJ =>
      cases stk <;> simp only [List.map_cons, Asm.toSAsm, runSAsm, runAsm]
      split <;> simp [ih]
    all_goals simp only [List.map_cons, Asm.toSAsm, runSAsm, runAsm] <;> (try split) <;> simp [ih]

/-- What a run observes besides gas: outcome, terminator data and final machine state. -/
@[expose] def Final.obs (f : Final σ) : Outcome × List UInt256 × σ := (f.outcome, f.data, f.state)

/-- `%d` occurs nowhere in the symbolic stack `S`. -/
@[expose] def freshIn (d : ℕ) (S : List Operand) : Bool := S.all (· != .var d)

/-- The lowering checker. `validateLowering p c S` holds when stack code `c`, started on a stack
whose slots carry the operands `S` (top first), runs the Venom program `p`. -/
@[expose] def validateLowering : Program → List SAsm → List Operand → Bool
  | p, .push n :: c, S => validateLowering p c (.lit n :: S)
  | p, .dup k :: c, S =>
    decide (1 ≤ k ∧ k ≤ 16 ∧ k ≤ S.length) && validateLowering p c (S.getD (k - 1) default :: S)
  | p, .swap k :: c, S =>
    decide (1 ≤ k ∧ k ≤ 16 ∧ k < S.length) && validateLowering p c (swapTop k S)
  | p, .pop :: c, S =>
    match S with
    | [] => false
    | _ :: S' => validateLowering p c S'
  | [], [], _ => true
  | [], .halt .stop :: _, _ => true
  | .pure d o args :: rest, .op o' :: c, S =>
    o == o' && args.length == o.arity && S.take o.arity == args && freshIn d (S.drop o.arity) &&
      validateLowering rest c (.var d :: S.drop o.arity)
  | .eff dst e args :: rest, .eff e' :: c, S =>
    e == e' && args.length == e.arity && S.take e.arity == args &&
      match dst with
      | some d => e.produces && freshIn d (S.drop e.arity) &&
          validateLowering rest c (.var d :: S.drop e.arity)
      | none => !e.produces && validateLowering rest c (S.drop e.arity)
  | .assert a :: rest, .assertJ :: c, a' :: S => a == a' && validateLowering rest c S
  | .halt h args :: _, .halt h' :: _, S =>
    h == h' && args.length == h.arity && S.take h.arity == args
  | _, _, _ => false

/-! ## Soundness -/

theorem length_of_rel {st : Store} {S : List Operand} {stk : List UInt256}
    (h : S.map (evalOperand st) = stk.map some) : S.length = stk.length := by
  simpa using congrArg List.length h

/-- The stack relation is preserved by `take`. -/
theorem rel_take {st : Store} {S : List Operand} {stk : List UInt256}
    (h : S.map (evalOperand st) = stk.map some) (n : ℕ) :
    (S.take n).map (evalOperand st) = (stk.take n).map some := by
  rw [List.map_take, h, List.map_take]

/-- The stack relation is preserved by `drop`. -/
theorem rel_drop {st : Store} {S : List Operand} {stk : List UInt256}
    (h : S.map (evalOperand st) = stk.map some) (n : ℕ) :
    (S.drop n).map (evalOperand st) = (stk.drop n).map some := by
  rw [List.map_drop, h, List.map_drop]

/-- Operands related to a concrete stack evaluate to it. -/
theorem evalArgs_of_rel {st : Store} :
    ∀ {S : List Operand} {stk : List UInt256},
      S.map (evalOperand st) = stk.map some → evalArgs st S = some stk
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: xs, y :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    have := evalArgs_of_rel (st := st) h.2
    simp only [evalArgs, List.mapM_cons] at this ⊢
    simp [h.1, this]

/-- Assigning a variable that does not occur in the symbolic stack keeps the relation. -/
theorem rel_set_fresh {st : Store} {S : List Operand} {stk : List UInt256} {d : ℕ}
    (h : S.map (evalOperand st) = stk.map some) (hf : freshIn d S = true) (x : UInt256) :
    S.map (evalOperand (st.set d x)) = stk.map some := by
  rw [← h]
  refine List.map_congr_left fun o ho => ?_
  simp only [freshIn, List.all_eq_true, bne_iff_ne, ne_eq] at hf
  cases o with
  | lit n => rfl
  | var v => simp [evalOperand, Store.set, show v ≠ d from fun h => hf _ ho (h ▸ rfl)]

/-- Pushing a freshly assigned variable keeps the stack relation. -/
theorem rel_push_fresh {st : Store} {S : List Operand} {stk : List UInt256} {d : ℕ}
    (h : S.map (evalOperand st) = stk.map some) (hf : freshIn d S = true) (x : UInt256) :
    (Operand.var d :: S).map (evalOperand (st.set d x)) = (x :: stk).map some := by
  simp only [List.map_cons, evalOperand, Store.set, if_true]
  rw [rel_set_fresh h hf]

/-- The operands a checked instruction takes from the top of the stack evaluate to the concrete
top of the stack, which is long enough. -/
theorem take_rel {st : Store} {S args : List Operand} {stk : List UInt256} {n : ℕ}
    (hrel : S.map (evalOperand st) = stk.map some) (hlenA : args.length = n)
    (htake : S.take n = args) : n ≤ stk.length ∧ evalArgs st args = some (stk.take n) := by
  refine ⟨?_, htake ▸ evalArgs_of_rel (rel_take hrel _)⟩
  have := congrArg List.length htake
  have := length_of_rel hrel
  simp at *; omega

/-- `swapTop` commutes with `map`. -/
theorem map_swapTop {α β : Type} (f : α → β) (k : ℕ) :
    ∀ l : List α, (swapTop k l).map f = swapTop k (l.map f)
  | [] => rfl
  | x :: xs => by simp [swapTop, List.map_set]

/-- The stack relation is preserved by `swapTop`. -/
theorem rel_swap {st : Store} {S : List Operand} {stk : List UInt256} (k : ℕ)
    (h : S.map (evalOperand st) = stk.map some) :
    (swapTop k S).map (evalOperand st) = (swapTop k stk).map some := by
  rw [map_swapTop, h, map_swapTop]

/-- An in-range slot of a related symbolic stack evaluates to the concrete slot. -/
theorem rel_getD {st : Store} {S : List Operand} {stk : List UInt256} {i : ℕ}
    (h : S.map (evalOperand st) = stk.map some) (hi : i < S.length) (d₁ : Operand) (d₂ : UInt256) :
    evalOperand st (S.getD i d₁) = some (stk.getD i d₂) := by
  have hi' : i < stk.length := length_of_rel h ▸ hi
  simpa [List.getD_eq_getElem?_getD, hi, hi'] using congrArg (·[i]?) h

/-- **Soundness of the lowering checker**, from any symbolic stack: if the checker accepts code `c`
for program `p` from symbolic stack `S`, and the concrete stack `stk` carries the values of `S` in
store `st`, then `c` and `p` end the same way (outcome, terminator data, final machine state), for
every machine state, every interpretation of the primitive effects and any gas counters. -/
theorem validateLowering_sound_from (P : Prims σ) :
    ∀ (c : List SAsm) (p : Program) (S : List Operand) (st : Store) (stk : List UInt256) (s : σ)
      (g g' : ℕ), validateLowering p c S = true → S.map (evalOperand st) = stk.map some →
      (runSAsm P c stk s g).map Final.obs = (run P p st s g').map Final.obs := by
  intro c
  induction c with
  | nil =>
    intro p S st stk s g g' hv _
    cases p with
    | nil => simp [runSAsm, run, Final.obs]
    | cons i rest => cases i <;> simp [validateLowering] at hv
  | cons a c ih =>
    intro p S st stk s g g' hv hrel
    have hlen := length_of_rel hrel
    cases a with
    | push n =>
      simp only [validateLowering] at hv
      simp only [runSAsm]
      exact ih p _ st _ s _ g' hv (by simp [hrel, evalOperand])
    | dup k =>
      simp only [validateLowering, Bool.and_eq_true, decide_eq_true_eq] at hv
      obtain ⟨⟨hk1, hk2, hk3⟩, hv⟩ := hv
      simp only [runSAsm, if_pos (show 1 ≤ k ∧ k ≤ 16 ∧ k ≤ stk.length by omega)]
      refine ih p _ st _ s _ g' hv ?_
      rw [List.map_cons, List.map_cons, hrel, rel_getD hrel (show k - 1 < S.length by omega)]
    | swap k =>
      simp only [validateLowering, Bool.and_eq_true, decide_eq_true_eq] at hv
      obtain ⟨⟨hk1, hk2, hk3⟩, hv⟩ := hv
      simp only [runSAsm, if_pos (show 1 ≤ k ∧ k ≤ 16 ∧ k < stk.length by omega)]
      exact ih p _ st _ s _ g' hv (rel_swap k hrel)
    | pop =>
      obtain _ | ⟨x, S'⟩ := S
      · simp [validateLowering] at hv
      obtain _ | ⟨y, stk'⟩ := stk
      · simp at hlen
      simp only [validateLowering] at hv
      simp only [runSAsm]
      exact ih p S' st stk' s _ g' hv (List.cons.inj hrel).2
    | op o' =>
      cases p with
      | cons i rest =>
        cases i with
        | pure d o args =>
          simp only [validateLowering, Bool.and_eq_true, beq_iff_eq] at hv
          obtain ⟨⟨⟨⟨rfl, hlenA⟩, htake⟩, hfresh⟩, hv⟩ := hv
          obtain ⟨har, hargs⟩ := take_rel hrel hlenA htake
          simp only [runSAsm, if_pos har, run, if_pos hlenA, hargs, Option.bind_eq_bind,
            Option.bind_some]
          exact ih rest _ _ _ s _ _ hv (rel_push_fresh (rel_drop hrel _) hfresh _)
        | _ => simp [validateLowering] at hv
      | _ => simp [validateLowering] at hv
    | eff e' =>
      cases p with
      | cons i rest =>
        cases i with
        | eff dst e args =>
          simp only [validateLowering, Bool.and_eq_true, beq_iff_eq] at hv
          obtain ⟨⟨⟨rfl, hlenA⟩, htake⟩, hv⟩ := hv
          obtain ⟨har, hargs⟩ := take_rel hrel hlenA htake
          cases dst with
          | some d =>
            simp only [Bool.and_eq_true] at hv
            obtain ⟨⟨hp, hfresh⟩, hv⟩ := hv
            simp only [runSAsm, if_pos har, hp, if_true, run, hargs, Option.bind_eq_bind,
              Option.bind_some, if_pos (show args.length = e.arity ∧ (some d).isSome = true by
                simp [hlenA])]
            exact ih rest _ _ _ _ _ _ hv (rel_push_fresh (rel_drop hrel _) hfresh _)
          | none =>
            simp only [Bool.and_eq_true, Bool.not_eq_true'] at hv
            obtain ⟨hp, hv⟩ := hv
            simp only [runSAsm, if_pos har, hp, Bool.false_eq_true, if_false, run, hargs,
              Option.bind_eq_bind, Option.bind_some,
              if_pos (show args.length = e.arity ∧ (none : Option ℕ).isSome = false by simp [hlenA])]
            exact ih rest _ _ _ _ _ _ hv (rel_drop hrel _)
        | _ => simp [validateLowering] at hv
      | _ => simp [validateLowering] at hv
    | assertJ =>
      cases p with
      | cons i rest =>
        cases i with
        | assert a =>
          obtain _ | ⟨a', S'⟩ := S
          · simp [validateLowering] at hv
          obtain _ | ⟨x, stk'⟩ := stk
          · simp at hlen
          simp only [validateLowering, Bool.and_eq_true, beq_iff_eq] at hv
          obtain ⟨rfl, hv⟩ := hv
          simp only [List.map_cons, List.cons.injEq] at hrel
          simp only [runSAsm, run, hrel.1, Option.bind_eq_bind, Option.bind_some]
          split
          · simp [Final.obs]
          · exact ih rest S' st stk' s _ _ hv hrel.2
        | _ => simp [validateLowering] at hv
      | _ => simp [validateLowering] at hv
    | halt h' =>
      cases p with
      | nil =>
        cases h' with
        | stop => simp [runSAsm, run, Final.obs, Halt.arity, Halt.outcome]
        | _ => simp [validateLowering] at hv
      | cons i rest =>
        cases i with
        | halt h args =>
          simp only [validateLowering, Bool.and_eq_true, beq_iff_eq] at hv
          obtain ⟨⟨rfl, hlenA⟩, htake⟩ := hv
          obtain ⟨har, hargs⟩ := take_rel hrel hlenA htake
          simp [runSAsm, if_pos har, run, hlenA, hargs, Final.obs]
        | _ => simp [validateLowering] at hv

/-- **Soundness of the lowering checker.** If the checker accepts stack code `c` for the Venom
program `p` from the empty stack, then running `c` from the empty stack and running `p` from the
empty store end the same way: same outcome, same terminator data, same final machine state, for every
machine state and every interpretation of the primitive effects. -/
theorem validateLowering_sound (P : Prims σ) {p : Program} {c : List SAsm}
    (h : validateLowering p c [] = true) (s : σ) (g g' : ℕ) :
    (runSAsm P c [] s g).map Final.obs = (run P p Store.empty s g').map Final.obs :=
  validateLowering_sound_from P c p [] Store.empty [] s g g' h rfl

/-- For code produced by the proved compiler of `Compile.lean` (embedded in `SAsm`), the gas is
also the gas of the Venom semantics: `runSAsm_embed` and `compile_correct` together. -/
theorem validateLowering_compile_gas (P : Prims σ) {p : Program} {c : List Asm}
    (h : compile p = some c) (s : σ) (g : ℕ) :
    runSAsm P (c.map Asm.toSAsm) [] s g = run P p Store.empty s g := by
  rw [runSAsm_embed, compile_correct P h]

/-! ## Gas of checked code -/

/-- Gas the Venom semantics charges for loading operands, up to and including the first terminator:
`W_verylow` per operand (the loads of `Compile.lean`'s scheme, which a schedule replaces by its own
stack instructions). -/
@[expose] def loadGas : Program → ℕ
  | [] => 0
  | .pure _ _ args :: rest => operandGas * args.length + loadGas rest
  | .eff _ _ args :: rest => operandGas * args.length + loadGas rest
  | .assert _ :: rest => operandGas + loadGas rest
  | .halt _ args :: _ => operandGas * args.length

/-- Gas of the stack instructions of a schedule up to its first terminator: `W_verylow` for `PUSH`,
`DUP` and `SWAP`, `W_base` for `POP`. -/
@[expose] def shuffleGas : List SAsm → ℕ
  | [] => 0
  | .push _ :: c => Gverylow + shuffleGas c
  | .dup _ :: c => Gverylow + shuffleGas c
  | .swap _ :: c => Gverylow + shuffleGas c
  | .pop :: c => Gbase + shuffleGas c
  | .halt _ :: _ => 0
  | .op _ :: c => shuffleGas c
  | .eff _ :: c => shuffleGas c
  | .assertJ :: c => shuffleGas c

/-- The program has no `assert`, so no run of it is cut short before its terminator. -/
@[expose] def assertFree (p : Program) : Bool :=
  p.all fun | .assert _ => false | _ => true

/-- The three gas laws for one pair of results (`r'` of the stack code, started with `g` gas
consumed; `r` of the Venom program, started with `g'`), with load gas `L` and shuffle gas `Sh`. -/
@[expose] def GasLaws (L Sh : ℕ) (A : Bool) (g g' : ℕ) (r' r : Option (Final σ)) : Prop :=
  ∀ f' f, r' = some f' → r = some f →
    f.gas + g ≤ f'.gas + g' + L ∧ f'.gas + g' ≤ f.gas + g + Sh ∧
      (A = true → f'.gas + g' + L = f.gas + g + Sh)

private theorem GasLaws.shuffle {L Sh k : ℕ} {A : Bool} {g g' : ℕ} {r' r : Option (Final σ)}
    (h : GasLaws L Sh A (g + k) g' r' r) : GasLaws L (k + Sh) A g g' r' r := by
  intro f' f h' h''
  obtain ⟨h₁, h₂, h₃⟩ := h f' f h' h''
  exact ⟨by omega, by omega, fun hA => by have := h₃ hA; omega⟩

private theorem GasLaws.load {L Sh m k : ℕ} {A : Bool} {g g' : ℕ} {r' r : Option (Final σ)}
    (h : GasLaws L Sh A (g + k) (g' + m + k) r' r) : GasLaws (m + L) Sh A g g' r' r := by
  intro f' f h' h''
  obtain ⟨h₁, h₂, h₃⟩ := h f' f h' h''
  exact ⟨by omega, by omega, fun hA => by have := h₃ hA; omega⟩

private theorem GasLaws.weaken {L Sh : ℕ} {A : Bool} {g g' : ℕ} {r' r : Option (Final σ)}
    (h : GasLaws L Sh A g g' r' r) : GasLaws L Sh false g g' r' r :=
  fun f' f h' h'' => ⟨(h f' f h' h'').1, (h f' f h' h'').2.1, nofun⟩

/-- **Gas of checked code**, from any symbolic stack (induction on the stack code, along the
soundness proof). For an accepted pair, any run of the code and any run of the program satisfy the
three laws of `GasLaws` with `L = loadGas p` and `Sh = shuffleGas c`. -/
theorem validateLowering_gas_from (P : Prims σ) :
    ∀ (c : List SAsm) (p : Program) (S : List Operand) (st : Store) (stk : List UInt256) (s : σ)
      (g g' : ℕ), validateLowering p c S = true → S.map (evalOperand st) = stk.map some →
      GasLaws (loadGas p) (shuffleGas c) (assertFree p) g g' (runSAsm P c stk s g)
        (run P p st s g') := by
  intro c
  induction c with
  | nil =>
    intro p S st stk s g g' hv _
    cases p with
    | nil =>
      intro f' f h' h
      simp only [runSAsm, run, Option.some.injEq] at h' h
      subst h' h
      simp [loadGas, shuffleGas]
      omega
    | cons i rest => cases i <;> simp [validateLowering] at hv
  | cons a c ih =>
    intro p S st stk s g g' hv hrel
    have hlen := length_of_rel hrel
    cases a with
    | push n =>
      simp only [validateLowering] at hv
      simp only [runSAsm, shuffleGas]
      exact GasLaws.shuffle (ih p _ st _ s _ g' hv (by simp [hrel, evalOperand]))
    | dup k =>
      simp only [validateLowering, Bool.and_eq_true, decide_eq_true_eq] at hv
      obtain ⟨⟨hk1, hk2, hk3⟩, hv⟩ := hv
      simp only [runSAsm, if_pos (show 1 ≤ k ∧ k ≤ 16 ∧ k ≤ stk.length by omega), shuffleGas]
      refine GasLaws.shuffle (ih p _ st _ s _ g' hv ?_)
      rw [List.map_cons, List.map_cons, hrel, rel_getD hrel (show k - 1 < S.length by omega)]
    | swap k =>
      simp only [validateLowering, Bool.and_eq_true, decide_eq_true_eq] at hv
      obtain ⟨⟨hk1, hk2, hk3⟩, hv⟩ := hv
      simp only [runSAsm, if_pos (show 1 ≤ k ∧ k ≤ 16 ∧ k < stk.length by omega), shuffleGas]
      exact GasLaws.shuffle (ih p _ st _ s _ g' hv (rel_swap k hrel))
    | pop =>
      obtain _ | ⟨x, S'⟩ := S
      · simp [validateLowering] at hv
      obtain _ | ⟨y, stk'⟩ := stk
      · simp at hlen
      simp only [validateLowering] at hv
      simp only [runSAsm, shuffleGas]
      exact GasLaws.shuffle (ih p S' st stk' s _ g' hv (List.cons.inj hrel).2)
    | op o' =>
      cases p with
      | cons i rest =>
        cases i with
        | pure d o args =>
          simp only [validateLowering, Bool.and_eq_true, beq_iff_eq] at hv
          obtain ⟨⟨⟨⟨rfl, hlenA⟩, htake⟩, hfresh⟩, hv⟩ := hv
          obtain ⟨har, hargs⟩ := take_rel hrel hlenA htake
          simp only [runSAsm, if_pos har, run, if_pos hlenA, hargs, Option.bind_eq_bind,
            Option.bind_some, loadGas, shuffleGas, assertFree, List.all_cons]
          exact GasLaws.load (ih rest _ _ _ s _ _ hv (rel_push_fresh (rel_drop hrel _) hfresh _))
        | _ => simp [validateLowering] at hv
      | _ => simp [validateLowering] at hv
    | eff e' =>
      cases p with
      | cons i rest =>
        cases i with
        | eff dst e args =>
          simp only [validateLowering, Bool.and_eq_true, beq_iff_eq] at hv
          obtain ⟨⟨⟨rfl, hlenA⟩, htake⟩, hv⟩ := hv
          obtain ⟨har, hargs⟩ := take_rel hrel hlenA htake
          cases dst with
          | some d =>
            simp only [Bool.and_eq_true] at hv
            obtain ⟨⟨hp, hfresh⟩, hv⟩ := hv
            simp only [runSAsm, if_pos har, hp, if_true, run, hargs, Option.bind_eq_bind,
              Option.bind_some, loadGas, shuffleGas, assertFree, List.all_cons,
              if_pos (show args.length = e.arity ∧ (some d).isSome = true by simp [hlenA])]
            exact GasLaws.load (ih rest _ _ _ _ _ _ hv (rel_push_fresh (rel_drop hrel _) hfresh _))
          | none =>
            simp only [Bool.and_eq_true, Bool.not_eq_true'] at hv
            obtain ⟨hp, hv⟩ := hv
            simp only [runSAsm, if_pos har, hp, Bool.false_eq_true, if_false, run, hargs,
              Option.bind_eq_bind, Option.bind_some, loadGas, shuffleGas, assertFree, List.all_cons,
              if_pos (show args.length = e.arity ∧ (none : Option ℕ).isSome = false by simp [hlenA])]
            exact GasLaws.load (ih rest _ _ _ _ _ _ hv (rel_drop hrel _))
        | _ => simp [validateLowering] at hv
      | _ => simp [validateLowering] at hv
    | assertJ =>
      cases p with
      | cons i rest =>
        cases i with
        | assert a =>
          obtain _ | ⟨a', S'⟩ := S
          · simp [validateLowering] at hv
          obtain _ | ⟨x, stk'⟩ := stk
          · simp at hlen
          simp only [validateLowering, Bool.and_eq_true, beq_iff_eq] at hv
          obtain ⟨rfl, hv⟩ := hv
          simp only [List.map_cons, List.cons.injEq] at hrel
          simp only [runSAsm, run, hrel.1, Option.bind_eq_bind, Option.bind_some, loadGas,
            shuffleGas, assertFree, List.all_cons]
          split
          · intro f' f h' h
            simp only [Option.some.injEq] at h' h
            subst h' h
            simp only [Bool.false_and, Bool.false_eq_true, false_implies, and_true]
            constructor <;> omega
          · exact GasLaws.weaken (GasLaws.load (ih rest S' st stk' s _ _ hv hrel.2))
        | _ => simp [validateLowering] at hv
      | _ => simp [validateLowering] at hv
    | halt h' =>
      cases p with
      | nil =>
        cases h' with
        | stop =>
          intro f' f hf' hf
          simp only [runSAsm, run, Halt.arity, Nat.zero_le, if_true, List.take_zero,
            Option.some.injEq] at hf' hf
          subst hf' hf
          simp [loadGas, shuffleGas]
          omega
        | _ => simp [validateLowering] at hv
      | cons i rest =>
        cases i with
        | halt h args =>
          simp only [validateLowering, Bool.and_eq_true, beq_iff_eq] at hv
          obtain ⟨⟨rfl, hlenA⟩, htake⟩ := hv
          obtain ⟨har, hargs⟩ := take_rel hrel hlenA htake
          intro f' f hf' hf
          simp only [runSAsm, if_pos har, run, if_pos hlenA, hargs, Option.bind_eq_bind,
            Option.bind_some, Option.some.injEq] at hf' hf
          subst hf' hf
          simp only [loadGas, shuffleGas]
          exact ⟨by omega, by omega, fun _ => by omega⟩
        | _ => simp [validateLowering] at hv

/-- **Gas bound for checked code.** If the checker accepts stack code `c` for program `p`, then for
every machine state, every interpretation of the primitive effects, and runs that both finish
(`f'` of the code, `f` of the program, both started with no gas consumed):

* `gas(p) ≤ gas(c) + loadGas p`: the code saves at most the program's operand loads;
* `gas(c) ≤ gas(p) + shuffleGas c`: the code spends at most its own stack instructions more;
* if `p` has no `assert`, exactly `gas(c) + loadGas p = gas(p) + shuffleGas c`. -/
theorem validateLowering_gas (P : Prims σ) {p : Program} {c : List SAsm}
    (h : validateLowering p c [] = true) (s : σ) {f' f : Final σ}
    (hc : runSAsm P c [] s 0 = some f') (hp : run P p Store.empty s 0 = some f) :
    f.gas ≤ f'.gas + loadGas p ∧ f'.gas ≤ f.gas + shuffleGas c ∧
      (assertFree p = true → f'.gas + loadGas p = f.gas + shuffleGas c) := by
  simpa using validateLowering_gas_from P c p [] Store.empty [] s 0 0 h rfl f' f hc hp

private theorem shuffleGas_pushRev {L : List ℕ} :
    ∀ (t : ℕ) (xs : List Operand) (c : List Asm) (rest : List SAsm), pushRev L t xs = some c →
      shuffleGas (c.map Asm.toSAsm ++ rest) = Gverylow * xs.length + shuffleGas rest
  | _, [], c, rest, h => by
    simp only [pushRev, Option.some.injEq] at h; subst h; simp
  | t, x :: xs, c, rest, h => by
    simp only [pushRev, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨a, ha, r, hr, rfl⟩ := h
    have ih := shuffleGas_pushRev (t + 1) xs r rest hr
    cases x <;> simp only [pushOperand] at ha <;> (try split at ha) <;>
      simp only [Option.some.injEq, reduceCtorEq] at ha <;> subst ha <;>
      simp only [List.map_cons, List.cons_append, Asm.toSAsm, shuffleGas, ih, List.length_cons] <;>
      ring

private theorem shuffleGas_pushArgs {L : List ℕ} {args : List Operand} {c : List Asm}
    (h : pushArgs L args = some c) (rest : List SAsm) :
    shuffleGas (c.map Asm.toSAsm ++ rest) = operandGas * args.length + shuffleGas rest := by
  simpa [operandGas] using shuffleGas_pushRev 0 args.reverse c rest h

/-- **The proved compiler spends on its stack instructions exactly the load gas.** With
`compile_correct` (equal gas) this is the exact law of `validateLowering_gas` for compiled code,
`asserts` included. -/
theorem compileFrom_shuffleGas :
    ∀ (p : Program) (L : List ℕ) (c : List Asm), compileFrom L p = some c →
      shuffleGas (c.map Asm.toSAsm) = loadGas p
  | [], L, c, h => by
    simp only [compileFrom, Option.some.injEq] at h; subst h; rfl
  | .pure dst o args :: rest, L, c, h => by
    simp only [compileFrom] at h
    split at h <;> simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
      reduceCtorEq] at h
    obtain ⟨c₁, hc₁, r, hr, rfl⟩ := h
    rw [List.map_append, shuffleGas_pushArgs hc₁, List.map_cons, Asm.toSAsm, shuffleGas,
      compileFrom_shuffleGas rest _ r hr, loadGas]
  | .eff dst e args :: rest, L, c, h => by
    simp only [compileFrom] at h
    split at h <;> simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
      reduceCtorEq] at h
    obtain ⟨c₁, hc₁, r, hr, rfl⟩ := h
    rw [List.map_append, shuffleGas_pushArgs hc₁, List.map_cons, Asm.toSAsm, shuffleGas,
      compileFrom_shuffleGas rest _ r hr, loadGas]
  | .assert a :: rest, L, c, h => by
    simp only [compileFrom, Option.bind_eq_bind, Option.bind_eq_some_iff,
      Option.some.injEq] at h
    obtain ⟨c₁, hc₁, r, hr, rfl⟩ := h
    rw [List.map_append, shuffleGas_pushArgs hc₁, List.map_cons, Asm.toSAsm, shuffleGas,
      compileFrom_shuffleGas rest _ r hr, loadGas]
    simp
  | .halt hh args :: _, L, c, h => by
    simp only [compileFrom] at h
    split at h <;> simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
      reduceCtorEq] at h
    obtain ⟨c₁, hc₁, rfl⟩ := h
    rw [List.map_append, shuffleGas_pushArgs hc₁]
    simp [Asm.toSAsm, shuffleGas, loadGas]

end EvmYul.Venom
