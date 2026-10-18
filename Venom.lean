namespace Venom

/-! ## 1. Raw, faithful substrate (mirrors IRFunction / IRBasicBlock / IRInstruction) -/

abbrev Word  := BitVec 256
abbrev Var   := String
abbrev Label := String

inductive Operand where
  | lit (w : Word) | var (v : Var) | lbl (l : Label)
  deriving Repr, DecidableEq

inductive Op where
  | assign | phi | add | sub | mul | lt | iszero
  | mload | mstore | sload | sstore
  | jmp | jnz | djmp | ret | stop | revert | invoke | alloca
  deriving Repr, DecidableEq

structure Inst where
  op   : Op
  args : List Operand
  outs : List Var
  deriving Repr

structure Block where
  label : Label
  insts : List Inst          -- φs first, terminator last
  deriving Repr

structure Func where
  name   : String
  entry  : Label
  blocks : List Block
  deriving Repr

def Op.isTerm : Op → Bool
  | .jmp | .jnz | .djmp | .ret | .stop | .revert => true
  | _ => false

def Block.term? (b : Block) : Option Inst :=
  match b.insts.getLast? with
  | some i => if i.op.isTerm then some i else none
  | none   => none

def Inst.targets (i : Inst) : List Label :=
  i.args.filterMap fun | .lbl l => some l | _ => none

def Block.succs (b : Block) : List Label := (b.term?.map Inst.targets).getD []
def Block.phis  (b : Block) : List Inst  := b.insts.takeWhile (·.op == .phi)
def Func.find?  (f : Func) (l : Label) : Option Block := f.blocks.find? (·.label == l)

/-- Decidable structural well-formedness (dominance/strictness would be a second, separate check). -/
def Func.check (f : Func) : Bool :=
  (f.find? f.entry).isSome &&
  f.blocks.all fun b => b.term?.isSome && b.succs.all fun l => (f.find? l).isSome

/-! ## 2. The EVM interface: the *only* place EVMYulLean (or a fork) is mentioned -/

class EvmInterface (σ : Type) where
  /-- Non-control-flow opcode semantics over the machine state. In the real development this
      is a thin adapter over EVMYulLean's shared `EvmYul.step` primops. -/
  exec : Op → List Word → σ → Option (List Word × σ)

abbrev Env := Var → Option Word
def Env.empty : Env := fun _ => none
def Env.set (e : Env) (v : Var) (w : Word) : Env := fun x => if x = v then some w else e x

def evalOp (e : Env) : Operand → Option Word
  | .lit w => some w
  | .var v => e v
  | .lbl _ => none

/-- φ syntax as in Venom text: `%x = phi @p1, %a, @p2, %b`. -/
def phiPick (prev : Label) : List Operand → Option Operand
  | .lbl l :: v :: rest => if l = prev then some v else phiPick prev rest
  | _ => none

/-! ## 3. Fuel-indexed semantics; φs are a *parallel* copy read from the pre-block env -/

inductive Next where | goto (l : Label) | halt | revert
inductive Result (σ : Type) where
  | halted (s : σ) | reverted (s : σ) | fault | fuelOut

def Result.IsTerminal {σ : Type} : Result σ → Prop
  | .halted _ | .reverted _ => True
  | _ => False

section
variable {σ : Type} [EvmInterface σ]

def applyPhis (prev : Label) (old : Env) (phis : List Inst) : Option Env :=
  phis.foldlM (init := old) fun acc i => do
    let src ← phiPick prev i.args
    let w   ← evalOp old src
    match i.outs with
    | [x] => pure (acc.set x w)
    | _   => none

def execPlain (env : Env) (s : σ) (i : Inst) : Option (Env × σ) := do
  let ws ← i.args.mapM (evalOp env)
  let (outs, s') ← EvmInterface.exec i.op ws s
  if outs.length = i.outs.length then
    pure ((i.outs.zip outs).foldl (fun e (x, w) => e.set x w) env, s')
  else none

def execTerm (env : Env) (i : Inst) : Option Next :=
  match i.op, i.args with
  | .jmp,    [.lbl l]            => some (.goto l)
  | .jnz,    [c, .lbl t, .lbl e] => do
      let w ← evalOp env c
      some (.goto (if w = 0 then e else t))
  | .stop,   _                   => some .halt
  | .ret,    _                   => some .halt   -- placeholder: real `ret` pops a frame
  | .revert, _                   => some .revert
  | _,       _                   => none

def runBlock (b : Block) (prev : Label) (env : Env) (s : σ) : Option (Next × Env × σ) := do
  let env ← applyPhis prev env b.phis
  let term ← b.term?
  let plain := (b.insts.drop b.phis.length).dropLast
  let (env, s) ← plain.foldlM (fun (p : Env × σ) i => execPlain p.1 p.2 i) (env, s)
  let n ← execTerm env term
  pure (n, env, s)

def run (f : Func) : Nat → Label → Label → Env → σ → Result σ
  | 0,     _,    _,   _,   _ => .fuelOut
  | n + 1, prev, cur, env, s =>
    match f.find? cur with
    | none   => .fault
    | some b =>
      match runBlock b prev env s with
      | none                      => .fault
      | some (.goto l, env', s')  => run f n cur l env' s'
      | some (.halt, _, s')       => .halted s'
      | some (.revert, _, s')     => .reverted s'
end

/-! ## 4. Refinement (not equivalence): a pass may turn an out-of-fuel/gas run into a success. -/

def Refines (src tgt : Func) : Prop :=
  ∀ (σ : Type) [EvmInterface σ] (fuel : Nat) (s : σ) (r : Result σ),
    run src fuel "" src.entry Env.empty s = r → r.IsTerminal →
    ∃ fuel', run tgt fuel' "" tgt.entry Env.empty s = r

theorem Refines.refl (f : Func) : Refines f f :=
  fun _ _ fuel _ _ h _ => ⟨fuel, h⟩

/-- The lesson from vyper-hol's audit ("nothing composes the pipeline"): compose from day one. -/
theorem Refines.trans {a b c : Func} (h₁ : Refines a b) (h₂ : Refines b c) : Refines a c := by
  intro σ _ fuel s r hr ht
  obtain ⟨f₁, hb⟩ := h₁ σ fuel s r hr ht
  exact h₂ σ f₁ s r hb ht

/-- Translation-validation interface: an *untrusted* Python pass + a *verified* checker. -/
structure Validator where
  check : Func → Func → Bool
  sound : ∀ a b, check a b = true → Refines a b

/-- A pipeline trace `f₀ → f₁ → … → fₙ` is accepted iff every adjacent pair is. -/
def Validator.chain (v : Validator) : List Func → Bool
  | a :: b :: rest => v.check a b && v.chain (b :: rest)
  | _              => true

theorem Validator.chain_sound (v : Validator) :
    ∀ (a b : Func) (rest : List Func), v.chain (a :: b :: rest) = true →
      Refines a ((b :: rest).getLast (List.cons_ne_nil _ _)) := by
  intro a b rest
  induction rest generalizing a b with
  | nil =>
    intro h
    simp [Validator.chain] at h
    exact v.sound a b h
  | cons c rest ih =>
    intro h
    rw [Validator.chain, Bool.and_eq_true] at h
    have h1 := v.sound a b h.1
    have h2 := ih b c h.2
    simpa using Refines.trans h1 h2


/-! ## 5. Regression test: φ is a *parallel* copy (the "swap problem").
    Compile-time `#guard`: building this file fails if the semantics regress. -/
section Examples

local instance : EvmInterface (List Word) where
  exec
    | .sstore, [v], s => some ([], s ++ [v])
    | .sub, [a, b], s => some ([a - b], s)
    | _, _, _         => none

def swapLoop : Func := { name := "swap", entry := "entry", blocks := [
  { label := "entry", insts := [ { op := .jmp, args := [.lbl "loop"], outs := [] } ] },
  { label := "loop", insts := [
      { op := .phi, args := [.lbl "entry", .lit 1, .lbl "loop", .var "y"], outs := ["x"] },
      { op := .phi, args := [.lbl "entry", .lit 2, .lbl "loop", .var "x"], outs := ["y"] },
      { op := .phi, args := [.lbl "entry", .lit 3, .lbl "loop", .var "m"], outs := ["n"] },
      { op := .sstore, args := [.var "x"], outs := [] },
      { op := .sub,    args := [.var "n", .lit 1], outs := ["m"] },
      { op := .jnz,    args := [.var "m", .lbl "loop", .lbl "done"], outs := [] } ] },
  { label := "done", insts := [ { op := .stop, args := [], outs := [] } ] } ] }

#guard swapLoop.check
#guard match run (σ := List Word) swapLoop 50 "" "entry" Env.empty [] with
  | .halted s => s.map BitVec.toNat == [1, 2, 1]
  | _         => false

end Examples
end Venom
