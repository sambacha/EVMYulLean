module

public import EvmYul.Venom.Syntax

public section

/-!
# Venom IR: big-step semantics of the straight-line fragment, with gas

The semantics is parametric in the machine state `σ` and in the primitive effects `Prims σ`
(what `sload`, `mstore`, `calldataload`, … do and cost). The compiler correctness theorem
(`EvmYul/Venom/Compile.lean`) holds for **every** choice of `Prims`, so it says nothing about the
primitives themselves; the build-time tests instantiate them with a byte-level reference model and
compare against the project's EVM `Θ` (`EvmYul/Venom/ThetaTests.lean`).

Gas is part of the result. The cost of an instruction is the gas of the EVM code that the compiler
of `Compile.lean` emits for it, stated here directly as a formula of the instruction (one
`PUSH32`/`DUPn` per operand, `W_verylow` each, plus the operation's own price); the compiler theorem
proves that the compiled code is charged exactly this. It is the gas of **this** compilation scheme,
not of the Vyper compiler's scheme (which also emits `SWAP`/`POP` and schedules the stack).
-/

namespace EvmYul.Venom

open GasConstants

/-- The primitive effects over a machine state `σ`. -/
structure Prims (σ : Type) where
  /-- Value (ignored for `sstore`/`mstore`) and new state of an effect on its operand values. -/
  apply : Eff → σ → List UInt256 → UInt256 × σ
  /-- Gas of the effect's EVM instruction (static and dynamic part) in state `σ`. -/
  cost : Eff → σ → List UInt256 → ℕ
  /-- Gas of a terminator's EVM instruction (memory expansion for `return`/`revert`). -/
  haltCost : Halt → σ → List UInt256 → ℕ

@[expose] section

/-- How a run ended. -/
inductive Outcome where
  /-- `stop`, or the end of the block. -/
  | stopped
  /-- `return`. -/
  | returned
  /-- `revert`, or a failed `assert`. -/
  | reverted
  deriving Repr, DecidableEq, Inhabited

end

/-- The outcome of a terminator. -/
@[expose] def Halt.outcome : Halt → Outcome
  | .stop => .stopped
  | .ret => .returned
  | .revert => .reverted

/-- The result of a run. -/
structure Final (σ : Type) where
  /-- How it ended. -/
  outcome : Outcome
  /-- The terminator's operand values (`[ofs, len]` for `return`/`revert`, `[]` for `stop`). -/
  data : List UInt256
  /-- The final machine state. -/
  state : σ
  /-- Gas consumed. -/
  gas : ℕ

/-- Gas of loading one operand (`PUSH32` or `DUPn`). -/
@[expose] def operandGas : ℕ := Gverylow

/-- Gas of an `assert` whose condition holds: `ISZERO`, `PUSH2 revert`, `JUMPI`. -/
@[expose] def assertPassGas : ℕ := Gverylow + Gverylow + Ghigh

/-- Extra gas of a failing `assert` before its `REVERT`: `JUMPDEST`, `PUSH0`, `PUSH0`. -/
@[expose] def assertFailGas : ℕ := Gjumpdest + Gbase + Gbase

/-- The SSA store: values of the variables defined so far. -/
@[expose] abbrev Store := ℕ → Option UInt256

/-- The empty store. -/
@[expose] def Store.empty : Store := fun _ => none

/-- `st` with `%v := x`. -/
@[expose] def Store.set (st : Store) (v : ℕ) (x : UInt256) : Store := fun w => if w = v then some x else st w

/-- The value of an operand (`none` for an undefined variable). -/
@[expose] def evalOperand (st : Store) : Operand → Option UInt256
  | .var v => st v
  | .lit n => some n

/-- The values of an operand list. -/
@[expose] def evalArgs (st : Store) (args : List Operand) : Option (List UInt256) := args.mapM (evalOperand st)

variable {σ : Type}

/-- Run a straight-line program from store `st`, state `s`, gas `g` consumed so far. `none` is a
static error: an undefined variable, or an operand list of the wrong length. -/
@[expose] def run (P : Prims σ) : Program → Store → σ → ℕ → Option (Final σ)
  | [], _, s, g => some ⟨.stopped, [], s, g + P.haltCost .stop s []⟩
  | .pure dst o args :: rest, st, s, g =>
    if args.length = o.arity then do
      let vs ← evalArgs st args
      run P rest (st.set dst (o.eval vs)) s (g + operandGas * args.length + o.gas)
    else none
  | .eff dst e args :: rest, st, s, g =>
    if args.length = e.arity ∧ dst.isSome = e.produces then do
      let vs ← evalArgs st args
      let g' := g + operandGas * args.length + P.cost e s vs
      match dst with
      | some d => run P rest (st.set d (P.apply e s vs).1) (P.apply e s vs).2 g'
      | none => run P rest st (P.apply e s vs).2 g'
    else none
  | .assert a :: rest, st, s, g => do
    let x ← evalOperand st a
    if x = word 0 then
      some ⟨.reverted, [word 0, word 0], s,
        g + operandGas + assertPassGas + assertFailGas + P.haltCost .revert s [word 0, word 0]⟩
    else run P rest st s (g + operandGas + assertPassGas)
  | .halt h args :: _, st, s, g =>
    if args.length = h.arity then do
      let vs ← evalArgs st args
      some ⟨h.outcome, vs, s, g + operandGas * args.length + P.haltCost h s vs⟩
    else none

end EvmYul.Venom
