module

public import EvmYul.FFI.Primitives
public meta import EvmYul.FFI.Primitives
public import EvmYul.Venom.ThetaTestHarness
public meta import EvmYul.Venom.ThetaTestHarness
public import EvmYul.Testing.Counted
public meta import EvmYul.Testing.Counted
public import Plausible
public meta import Plausible

@[expose] public meta section

/-!
# Tests of the cross-block lowering checker and of whole-function bytecode on `Θ`

`BlockLowering.lean` checks a whole stack function against a Venom function with φs (`checkCfg`,
proved sound by `checkCfg_sound`), and `Assemble.lean` lays the blocks out as bytes
(`assembleCfg`). This module is an FFI test root: the bytes run on the project's EVM `Θ` during the
build. Each section names the `TESTING.md` rule it applies.

The stack code comes from an **untrusted scheduler** written here (`schedule`): live-variable
layouts at block entries, the compiler's `DUP` scheme inside a block, and at every edge a shuffle
that pushes the successor's layout (with its φs replaced by the sources of this edge) and removes
the old stack with `SWAPk; POP` pairs. The checker, not the scheduler, is what the theorem trusts.

1. **§1 Unit checks (concrete business values).** A loop that swaps two values through φs
   (`%a = phi …, %b` and `%b = phi …, %a`, a **parallel** copy) stores `2` and `1` after three
   iterations, on `Θ` and in the Venom semantics; a schedule that resolves the φs one after the other
   stores `2` and `2`, and `checkCfg` rejects it. A summing loop stores `55` for `n = 10`. The byte
   layout puts a `JUMPDEST` at every block offset; broken schedules (a missing `SWAP`, a wrong jump
   target, φs in the entry block) are rejected.
2. **§2 Diamonds (counted, A2).** Random `jnz` diamonds with a φ join: the scheduler's output is
   accepted, and `Θ` on `assembleCfg` agrees with the Venom function (outcome, output, storage
   slots `0…7`) and with `runSCfg` on gas **exactly**.
3. **§3 Counted loops (counted, A2).** Random loops of `0…3` iterations whose back edge carries
   three φs, one of them reading another φ of the same block.
4. **§4 Soundness against a buggy scheduler.** Whenever `checkCfg` accepts the output of the
   sequential-φ scheduler, `Θ` agrees with the Venom function; how often it rejects is printed.
5. **§5 Canaries (E1).** A checker without the edge condition, the sequential-φ schedules run
   unchecked, and the Venom gas (free jumps) in place of the stack gas must each be refuted.
-/

namespace EvmYul.Venom.BlockLoweringTests

open EvmYul.Venom EvmYul.Venom.ThetaTests Plausible Plausible.Decorations

/-- Literal operand (shadows `EvmYul.L`, the 63/64 rule). -/
def L (n : ℕ) : Operand := .lit (word n)

/-! ## The untrusted scheduler -/

/-- Variables of an operand. -/
def opVars : Operand → List ℕ
  | .var v => [v]
  | .lit _ => []

/-- Variables an instruction reads. -/
def instrUses : Instr → List ℕ
  | .pure _ _ args | .eff _ _ args | .halt _ args => args.flatMap opVars
  | .assert a => opVars a

/-- The variable an instruction defines. -/
def instrDef : Instr → Option ℕ
  | .pure d _ _ => some d
  | .eff d _ _ => d
  | _ => none

/-- Variables a terminator reads (a halt's operands belong to the block's code). -/
def termUses : Term → List ℕ
  | .jnz c _ _ => opVars c
  | _ => []

/-- Successor labels. -/
def succs : Term → List ℕ
  | .jmp l => [l]
  | .jnz _ t e => [t, e]
  | .halt _ _ => []

/-- Variables live before `p` when `after` is live after it. -/
def liveBefore (p : Program) (after : List ℕ) : List ℕ :=
  p.foldr (fun i live => (instrUses i ++ live.filter (fun v => instrDef i != some v)).eraseDups)
    after

/-- φ outputs of a block. -/
def phiDefs (b : VBlock) : List ℕ := b.phis.map Prod.fst

/-- Variables the φs of `b` read on the edge from `pred`. -/
def phiUsesFrom (b : VBlock) (pred : ℕ) : List ℕ :=
  b.phis.flatMap fun (_, srcs) => ((srcs.lookup pred).map opVars).getD []

/-- One liveness step for block `b`: live after its φs, given the current estimate `live`. -/
def liveStep (f : VFunc) (live : ℕ → List ℕ) (b : VBlock) : List ℕ :=
  let out := (succs b.term).flatMap fun l =>
    match f.find? l with
    | some s => (live l).filter (· ∉ phiDefs s) ++ phiUsesFrom s b.label
    | none => []
  liveBefore b.code (termUses b.term ++ out)

/-- `n` rounds of the liveness fixpoint. -/
def liveRounds (f : VFunc) : ℕ → List (ℕ × List ℕ)
  | 0 => f.blocks.map fun b => (b.label, [])
  | n + 1 =>
    let prev := liveRounds f n
    f.blocks.map fun b => (b.label, liveStep f (fun l => (prev.lookup l).getD []) b)

/-- Variables live at the start of block `l`'s body. -/
def liveOf (f : VFunc) (l : ℕ) : List ℕ :=
  ((liveRounds f (2 * f.blocks.length + 2)).lookup l).getD []

/-- Sorted without duplicates. -/
def sortNat (l : List ℕ) : List ℕ := l.eraseDups.mergeSort fun a b => decide (a ≤ b)

/-- The entry layout of block `l` (top first): empty for the entry block; otherwise its live
variables, joined with those of the other target of a `jnz` that targets `l` (both targets of a
`jnz` see the same stack). -/
def layoutOf (f : VFunc) (l : ℕ) : List ℕ :=
  if l = f.entry then [] else
  let sib := f.blocks.flatMap fun b => match b.term with
    | .jnz _ t e => if t = l then [e] else if e = l then [t] else []
    | _ => []
  sortNat (liveOf f l ++ sib.flatMap (liveOf f))

/-- The layouts as operands (the form `checkCfg` takes). -/
def layoutFn (f : VFunc) (l : ℕ) : List Operand := (layoutOf f l).map .var

/-- Load an operand onto symbolic stack `S` (`DUP` of its newest copy, or `PUSH`). -/
def loadO (S : List Operand) : Operand → Option SAsm
  | .lit n => some (.push n)
  | .var v =>
    let i := S.idxOf (.var v)
    if i < S.length ∧ i + 1 ≤ 16 then some (.dup (i + 1)) else none

/-- Load operands in order (the last ends on top), returning the code and the new stack. -/
def loadAll : List Operand → List Operand → Option (List SAsm × List Operand)
  | S, [] => some ([], S)
  | S, o :: os => do
    let a ← loadO S o
    let (r, S') ← loadAll (o :: S) os
    pure (a :: r, S')

/-- Lower a block's code from symbolic stack `S`; returns the code and the stack at its end. -/
def lowerCode : List Operand → Program → Option (List SAsm × List Operand)
  | S, [] => some ([], S)
  | S, .pure d o args :: rest => do
    let (c, S₁) ← loadAll S args.reverse
    let (r, S₂) ← lowerCode (.var d :: S₁.drop args.length) rest
    pure (c ++ .op o :: r, S₂)
  | S, .eff dst e args :: rest => do
    let (c, S₁) ← loadAll S args.reverse
    let S₂ := match dst with
      | some d => .var d :: S₁.drop args.length
      | none => S₁.drop args.length
    let (r, S₃) ← lowerCode S₂ rest
    pure (c ++ .eff e :: r, S₃)
  | S, .assert a :: rest => do
    let (c, S₁) ← loadAll S [a]
    let (r, S₂) ← lowerCode (S₁.drop 1) rest
    pure (c ++ .assertJ :: r, S₂)
  | S, .halt h args :: _ => do
    let (c, _) ← loadAll S args.reverse
    pure (c ++ [.halt h], [])

/-- Turn stack `S` into `X`: push `X` rotated right by `|S|`, then `|S|` times `SWAPk; POP`
(`k = |X|`), each of which moves the top below the other `k − 1` new entries and drops one old
entry. -/
def shuffle (S X : List Operand) : Option (List SAsm) :=
  if S = X then some [] else
  let m := S.length
  let k := X.length
  if k = 0 then some (List.replicate m .pop) else
  if 16 < k then none else do
  let (c, _) ← loadAll S (X.rotateRight (m % k)).reverse
  pure (c ++ (List.replicate m [SAsm.swap k, .pop]).flatten)

/-- How a scheduler maps an operand of a successor's layout to this edge. -/
abbrev Subst := List (ℕ × List (ℕ × Operand)) → ℕ → Operand → Option Operand

/-- The stack the edge `pred → l` must leave: `l`'s layout through the φs. -/
def edgeTarget (subst : Subst) (f : VFunc) (pred l : ℕ) : Option (List Operand) := do
  let b ← f.find? l
  (layoutOf f l).mapM fun v => subst b.phis pred (.var v)

/-- Lower one block. -/
def lowerBlock (subst : Subst) (f : VFunc) (b : VBlock) : Option SBlock := do
  let (c, S) ← lowerCode (layoutFn f b.label) b.code
  match b.term with
  | .halt _ _ => pure ⟨b.label, c, .halts⟩
  | .jmp l => do
    let sh ← shuffle S (← edgeTarget subst f b.label l)
    pure ⟨b.label, c ++ sh, .jump l⟩
  | .jnz cnd t e => do
    let sh ← shuffle S (cnd :: (← edgeTarget subst f b.label t))
    pure ⟨b.label, c ++ sh, .jumpi t e⟩

/-- Lower a function block by block. -/
def lowerCfg (subst : Subst) (f : VFunc) : Option SFunc := do
  pure ⟨f.entry, ← f.blocks.mapM (lowerBlock subst f)⟩

/-- **The scheduler under test**: φs resolved as the parallel copy (`substPhi`). -/
def schedule (f : VFunc) : Option SFunc := lowerCfg substPhi f

/-- φs resolved **one after the other** (the classic lost-copy bug): a φ whose source is an
earlier φ output of the same block reads that output's new value. -/
def seqSubst : Subst := fun phis pred o =>
  let rec go (done : List (ℕ × Operand)) : List (ℕ × List (ℕ × Operand)) →
      Option (List (ℕ × Operand))
    | [] => some done
    | (x, srcs) :: rest => do
      let src ← srcs.lookup pred
      let v := match src with
        | .var y => (done.lookup y).getD src
        | .lit _ => src
      go ((x, v) :: done) rest
  match o with
  | .var x => do
    let m ← go [] phis
    pure ((m.lookup x).getD o)
  | .lit n => some (.lit n)

/-- The buggy scheduler (sequential φs). -/
def scheduleSeq (f : VFunc) : Option SFunc := lowerCfg seqSubst f

/-! ## Running on `Θ` -/

/-- Block budget of every run (the loops below take at most `2 · 10 + 3` blocks). -/
def fuel : ℕ := 64

/-- `Θ` on `assembleCfg sf` agrees with the Venom function `f` under the reference model on
outcome, output bytes and storage slots `0…7`, and with `runSCfg` (or `gasModel`) on gas. -/
def cfgAgrees (f : VFunc) (sf : SFunc) (kvs : List (ℕ × ℕ)) (data : List UInt8) (value : ℕ)
    (gasModel : Option ℕ := none) : Bool :=
  let s₀ := Ref.init kvs data value
  match runCfg refPrims f fuel none f.entry Store.empty s₀ 0,
      runSCfg refPrims sf fuel sf.entry [] s₀ 0, assembleCfg sf with
  | .done fv, .done fs, some code =>
    match onTheta code kvs data value with
    | some r =>
      r.outcome == fv.outcome.frame && r.output.toList == fv.output &&
        (List.range 8).all (fun k => r.slot k == expectedSlot fv kvs k) &&
        r.gasUsed == gasModel.getD fs.gas
    | none => false
  | _, _, _ => false

/-- The Venom result of a function under the reference model. -/
def venomRun (f : VFunc) (kvs : List (ℕ × ℕ)) (data : List UInt8) : CfgOut (Final Ref) :=
  runCfg refPrims f fuel none f.entry Store.empty (Ref.init kvs data 0) 0

/-- Storage slot `k` on `Θ` after running the assembled stack function. -/
def thetaSlot (sf : SFunc) (kvs : List (ℕ × ℕ)) (data : List UInt8) (k : ℕ) : Option ℕ := do
  let code ← assembleCfg sf
  let r ← onTheta code kvs data 0
  pure (r.slot k)

/-- Storage slot `k` of a finished Venom run. -/
def venomSlot (f : VFunc) (kvs : List (ℕ × ℕ)) (data : List UInt8) (k : ℕ) : Option ℕ :=
  match venomRun f kvs data with
  | .done fv => some (expectedSlot fv kvs k)
  | _ => none

/-- The 32-byte big-endian encoding of a small number. -/
def word32 (n : ℕ) : List UInt8 := (List.range 32).map fun i => UInt8.ofNat (n / 256 ^ (31 - i))

/-! ## §1 Fixtures -/

/-- Swap two values through φs, three times:
```
@0: jmp @1
@1: %1 = phi @0, 0, @2, %4      ; i
    %2 = phi @0, 1, @2, %3      ; a ← b
    %3 = phi @0, 2, @2, %2      ; b ← a   (parallel: the old a)
    %5 = lt %1, 3
    jnz %5, @2, @3
@2: %4 = add %1, 1
    jmp @1
@3: sstore 0, %2; sstore 1, %3; stop
```
The parallel copy ends with `a = 2, b = 1`; a sequential copy ends with `a = b = 2`. -/
def swapLoop : VFunc :=
  { entry := 0, blocks := [
    ⟨0, [], [], .jmp 1⟩,
    ⟨1, [(1, [(0, L 0), (2, V 4)]), (2, [(0, L 1), (2, V 3)]), (3, [(0, L 2), (2, V 2)])],
      [.pure 5 .lt [V 1, L 3]], .jnz (V 5) 2 3⟩,
    ⟨2, [], [.pure 4 .add [V 1, L 1]], .jmp 1⟩,
    ⟨3, [], [.eff none .sstore [L 0, V 2], .eff none .sstore [L 1, V 3]], .halt .stop []⟩] }

/-- Sum `1 + … + n` with `n` the first call-data word; stores the sum to slot 0 and returns it:
```
@0: %1 = calldataload 0; jmp @1
@1: %2 = phi @0, 0, @2, %5      ; i
    %3 = phi @0, 0, @2, %6      ; s
    %4 = lt %2, %1
    jnz %4, @2, @3
@2: %5 = add %2, 1; %6 = add %3, %5; jmp @1
@3: sstore 0, %3; mstore 0, %3; return 0, 32
``` -/
def sumLoop : VFunc :=
  { entry := 0, blocks := [
    ⟨0, [], [.eff (some 1) .calldataload [L 0]], .jmp 1⟩,
    ⟨1, [(2, [(0, L 0), (2, V 5)]), (3, [(0, L 0), (2, V 6)])], [.pure 4 .lt [V 2, V 1]],
      .jnz (V 4) 2 3⟩,
    ⟨2, [], [.pure 5 .add [V 2, L 1], .pure 6 .add [V 3, V 5]], .jmp 1⟩,
    ⟨3, [], [.eff none .sstore [L 0, V 3], .eff none .mstore [L 0, V 3]],
      .halt .ret [L 0, L 32]⟩] }

/-- Replace the code of block `l`. -/
def mapCode (sf : SFunc) (l : ℕ) (g : List SAsm → List SAsm) : SFunc :=
  { sf with blocks := sf.blocks.map fun b => if b.label = l then { b with code := g b.code } else b }

/-- Replace the terminator of block `l`. -/
def setTerm (sf : SFunc) (l : ℕ) (t : STerm) : SFunc :=
  { sf with blocks := sf.blocks.map fun b => if b.label = l then { b with term := t } else b }

/-- Accepted by `checkCfg` with the scheduler's layouts. -/
def accepted (f : VFunc) (sf : SFunc) : Bool := checkCfg f sf (layoutFn f)

/-- §1 unit checks; each must be `true`. -/
def unitChecks : List (String × Bool) :=
  let swapS := schedule swapLoop
  let seqS := scheduleSeq swapLoop
  let sumS := schedule sumLoop
  [("swap loop: the parallel-φ schedule is accepted by checkCfg",
      swapS.any (accepted swapLoop)),
   ("swap loop on Θ: slot 0 = 2 and slot 1 = 1 (three parallel swaps of 1, 2)",
      swapS.any fun sf => thetaSlot sf [] [] 0 == some 2 && thetaSlot sf [] [] 1 == some 1),
   ("swap loop in the Venom semantics: slot 0 = 2 and slot 1 = 1",
      venomSlot swapLoop [] [] 0 == some 2 && venomSlot swapLoop [] [] 1 == some 1),
   ("swap loop: Θ = Venom (outcome, output, storage) and Θ gas = runSCfg gas",
      swapS.any fun sf => cfgAgrees swapLoop sf [] [] 0),
   ("swap loop: the sequential-φ schedule differs and is rejected by checkCfg",
      seqS.any fun sf => !(swapS.any fun sf' => sf'.blocks.map (·.code) == sf.blocks.map (·.code)) &&
        !accepted swapLoop sf),
   ("swap loop: the sequential-φ schedule stores slot 1 = 2 on Θ (the lost copy)",
      seqS.any fun sf => thetaSlot sf [] [] 1 == some 2),
   ("sum loop: n = 10 stores 55 and returns the 32-byte word 55 on Θ",
      sumS.any fun sf => accepted sumLoop sf && thetaSlot sf [] (word32 10) 0 == some 55 &&
        (match assembleCfg sf with
         | some code => (onTheta code [] (word32 10) 0).any (·.output.toList == word32 55)
         | none => false)),
   ("sum loop: n = 0, 1, 2, 7 store 0, 1, 3, 28 on Θ and in the Venom semantics",
      sumS.any fun sf => [(0, 0), (1, 1), (2, 3), (7, 28)].all fun (n, s) =>
        thetaSlot sf [] (word32 n) 0 == some s && venomSlot sumLoop [] (word32 n) 0 == some s),
   ("sum loop: Θ = Venom and Θ gas = runSCfg gas for n = 0 … 9",
      sumS.any fun sf => (List.range 10).all fun n => cfgAgrees sumLoop sf [] (word32 n) 0),
   ("assembleCfg: a JUMPDEST at every block offset, size = Σ sblockSize + 4",
      swapS.any fun sf => match assembleCfg sf with
        | some code =>
          (blockOffsets 0 sf.blocks).all (fun (_, o) => code.toList.getD o 0 == 0x5b) &&
            code.size == (sf.blocks.map sblockSize).sum + 4
        | none => false),
   ("rejected: the loop body without the SWAP of its shuffle",
      swapS.any fun sf => !accepted swapLoop (mapCode sf 2 fun c => c.filter fun
        | .swap _ => false
        | _ => true)),
   ("rejected: the loop header jumping to the exit on both branches",
      swapS.any fun sf => !accepted swapLoop (setTerm sf 1 (.jumpi 3 3))),
   ("rejected: φs in the entry block",
      let bad : VFunc := { swapLoop with blocks := swapLoop.blocks.map fun b =>
        if b.label = 0 then { b with phis := [(9, [(0, L 0)])] } else b }
      swapS.any fun sf => !checkCfg bad sf (layoutFn swapLoop))]

/-! ## Random functions -/

/-- An operand: a literal, or one of the 6 newest variables in scope. -/
def opnd (sc : List ℕ) (a b : ℕ) : Operand :=
  if a % 3 = 0 ∨ sc.isEmpty then .lit (word (mkLit a b)) else .var (sc.getD (a % min 6 sc.length) 0)

/-- A random straight-line body of at most 4 instructions, variables `base, base + 1, …`, over the
variables in scope `sc` (newest first). Returns the body and the new scope. -/
def genBody (sc : List ℕ) (base : ℕ) (xs : List (ℕ × ℕ × ℕ)) : Program × List ℕ :=
  (xs.take 4).zipIdx.foldl (fun (acc : Program × List ℕ) ((k, a, b), j) =>
    let (p, sc) := acc
    let d := base + j
    let o₁ := opnd sc a b
    let o₂ := opnd sc (a + b + 1) (b / 2 + k)
    match k % 6 with
    | 0 | 1 | 2 =>
      let o := pureOps.getD (a % pureOps.length) .add
      (p ++ [.pure d o (if o.arity = 1 then [o₁] else [o₁, o₂])], d :: sc)
    | 3 => (p ++ [.eff (some d) .calldataload [L (b % 64)]], d :: sc)
    | 4 => (p ++ [.eff (some d) .sload [L (b % 4)]], d :: sc)
    | _ => (p ++ [.eff none .sstore [L (b % 4), o₂]], sc)) ([], sc)

/-- A halting terminator: `stop`, `return 0, 32` or `revert 0, 32`. -/
def haltOf (t : ℕ) : Term :=
  match t % 3 with
  | 0 => .halt .stop []
  | 1 => .halt .ret [L 0, L 32]
  | _ => .halt .revert [L 0, L 32]

/-- A random diamond:
```
@0: %100 = calldataload 0; <body>; jnz cond, @1, @2
@1: <body>; sstore 7, 1; jmp @3        @2: <body>; sstore 7, 2; jmp @3
@3: %400 = phi @1, …, @2, …; %401 = phi @1, …, @2, …
    <body>; sstore 0, %401; mstore 0, %400; stop | return 0, 32 | revert 0, 32
```
Slot 7 records the branch taken. -/
def diamond (x₀ x₁ x₂ x₃ : List (ℕ × ℕ × ℕ)) (c t : ℕ) : VFunc :=
  let (p₀, s₀) := genBody [100] 101 x₀
  let cond := match c % 4 with
    | 0 => L 0
    | 1 => L 1
    | _ => opnd s₀ (c / 4 * 3 + 1) c
  let (p₁, s₁) := genBody s₀ 200 x₁
  let (p₂, s₂) := genBody s₀ 300 x₂
  let (p₃, _) := genBody (400 :: 401 :: s₀) 500 x₃
  { entry := 0, blocks := [
    ⟨0, [], .eff (some 100) .calldataload [L 0] :: p₀, .jnz cond 1 2⟩,
    ⟨1, [], p₁ ++ [.eff none .sstore [L 7, L 1]], .jmp 3⟩,
    ⟨2, [], p₂ ++ [.eff none .sstore [L 7, L 2]], .jmp 3⟩,
    ⟨3, [(400, [(1, opnd s₁ (c + 1) t), (2, opnd s₂ (t + 1) c)]),
         (401, [(1, opnd s₁ (t + 2) (c + 2)), (2, opnd s₂ (c + t + 2) 7)])],
      p₃ ++ [.eff none .sstore [L 0, V 401], .eff none .mstore [L 0, V 400]], haltOf t⟩] }

/-- A random counted loop of `n = (first call-data byte) / 64` iterations (`0 … 3`):
```
@0: %100 = calldataload 0; %101 = shr 254, %100; <body>; jmp @1
@1: %200 = phi @0, 0, @2, %302                 ; i
    %201 = phi @0, …, @2, %303                 ; acc
    %202 = phi @0, …, @2, %201                 ; the previous acc (reads another φ)
    %203 = lt %200, %101
    jnz %203, @2, @3
@2: <body>; %302 = add %200, 1; %303 = op %201, …; jmp @1
@3: sstore 0, %201; sstore 1, %202; mstore 0, %200; stop | return 0, 32 | revert 0, 32
```
`w` picks how the φs interact: as shown (`w % 3 = 0`: a sequential copy loses the old `%201`),
with `%202` listed before `%201` (`1`: a sequential copy happens to be right), or with `%202` reading
`%302` on the back edge (`2`: no φ reads another). -/
def loopFn (x₀ xB : List (ℕ × ℕ × ℕ)) (a b t w : ℕ) : VFunc :=
  let (p₀, s₀) := genBody [101, 100] 102 x₀
  let (pB, sB) := genBody (203 :: 202 :: 201 :: 200 :: s₀) 310 xB
  let o := pureOps.getD (a % (pureOps.length - 1)) .add
  let phiI := (200, [(0, L 0), (2, V 302)])
  let phiAcc := (201, [(0, opnd s₀ a b), (2, V 303)])
  let phiPrev := (202, [(0, opnd s₀ b a), (2, V (if w % 3 = 2 then 302 else 201))])
  { entry := 0, blocks := [
    ⟨0, [], [.eff (some 100) .calldataload [L 0], .pure 101 .shr [L 254, V 100]] ++ p₀, .jmp 1⟩,
    ⟨1, if w % 3 = 1 then [phiI, phiPrev, phiAcc] else [phiI, phiAcc, phiPrev],
      [.pure 203 .lt [V 200, V 101]], .jnz (V 203) 2 3⟩,
    ⟨2, [], pB ++ [.pure 302 .add [V 200, L 1], .pure 303 o [V 201, opnd sB (b + 1) a]], .jmp 1⟩,
    ⟨3, [], [.eff none .sstore [L 0, V 201], .eff none .sstore [L 1, V 202],
             .eff none .mstore [L 0, V 200]], haltOf t⟩] }

/-- Call data whose first byte selects `n % 4` loop iterations. -/
def loopData (n : ℕ) (cd : List ℕ) : List UInt8 := UInt8.ofNat (n % 4 * 64 + n / 4 % 64) :: mkData cd

/-- Scheduled, accepted, and equal to the Venom function on `Θ` (gas exact). -/
def lawFor (sched : VFunc → Option SFunc) (f : VFunc) (kvs : List (ℕ × ℕ)) (data : List UInt8) :
    Bool :=
  match sched f with
  | some sf => accepted f sf && cfgAgrees f sf kvs data 0
  | none => false

/-! ## §5 Canary support -/

/-- `checkBlock` **without the edge condition** (the stack after a block is not compared with the
successor's layout through its φs). -/
def checkBlockNoEdge (sf : SFunc) (layout : ℕ → List Operand) (b : VBlock) : Bool :=
  match sf.find? b.label with
  | none => false
  | some sb =>
    match checkBody b.code sb.code (layout b.label) with
    | none => false
    | some .exit => true
    | some (.cont S) =>
      match b.term, sb.term with
      | .jmp l, .jump l' => l == l'
      | .jnz c t e, .jumpi t' e' =>
        t == t' && e == e' && match S with
          | c' :: _ => c == c'
          | [] => false
      | _, _ => false

/-- `checkCfg` without the edge condition. -/
def checkCfgNoEdge (f : VFunc) (sf : SFunc) (layout : ℕ → List Operand) : Bool :=
  f.entry == sf.entry && (layout f.entry).isEmpty && f.blocks.all (checkBlockNoEdge sf layout)

/-! ## Running -/

/-- Seeded configuration (`TESTING.md` E3). -/
def cfg : Configuration := { numInst := 300, maxSize := 30, randomSeed := some 20261012,
                             quiet := true }

/-- Fail the build on a counterexample or on too few valid inputs (counts printed). -/
def expectHolds (name : String) (p : Prop)
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] : IO Unit :=
  discard <| EvmYul.CountedTesting.holdsCore cfg name p' (EvmYul.CountedTesting.defaultMinValid cfg)

/-- Mutation test: fail the build unless a counterexample is found (counts printed). -/
def expectRefuted (name : String) (p : Prop)
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] : IO Unit :=
  discard <| EvmYul.CountedTesting.refutedCore cfg name p'

/-- Deterministic random triples for the coverage lines. -/
def triples (i n : ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range (i % n)).map fun j => (mix (i * 31 + j) % 6, mix (i + 7 * j) % 97, mix (i * j + 5) % 89)

/-- Run everything; throws on the first failure. -/
def runAll : IO Unit := do
  -- §1
  for (name, ok) in unitChecks do
    unless ok do throw <| IO.userError s!"unit check failed: {name}"
  IO.println s!"§1 cross-block lowering: {unitChecks.length} unit checks passed"
  -- §2
  expectHolds "§2 diamonds: scheduled, accepted by checkCfg, Θ = Venom, Θ gas = runSCfg"
    (∀ (x₀ x₁ x₂ x₃ : List (ℕ × ℕ × ℕ)) (c t : ℕ) (kv : List (ℕ × ℕ)) (cd : List ℕ),
      lawFor schedule (diamond x₀ x₁ x₂ x₃ c t) (mkKvs kv) (mkData cd) = true)
  let dgen := (List.range 300).map fun i =>
    (diamond (triples i 5) (triples (i + 1) 5) (triples (i + 2) 5) (triples (i + 3) 5) (mix i % 50)
      (mix (i + 9) % 7), mkData ((List.range (i % 7)).map fun j => mix (i + j)))
  let dres := dgen.map fun (f, data) => (f, venomRun f [] data)
  let branch (k : ℕ) := (dres.filter fun (_, r) => match r with
    | .done fv => fv.state.storage 7 == k
    | _ => false).length
  let dOut (o : Outcome) := (dres.filter fun (_, r) => match r with
    | .done fv => fv.outcome == o
    | _ => false).length
  let dSched := (dgen.filter fun (f, _) => (schedule f).isSome).length
  IO.println s!"§2 coverage (300 diamonds): scheduled {dSched}, then-branch {branch 1}, \
    else-branch {branch 2}; stopped {dOut .stopped}, returned {dOut .returned}, reverted \
    {dOut .reverted}"
  unless dSched ≥ 250 ∧ branch 1 ≥ 50 ∧ branch 2 ≥ 50 ∧ dOut .stopped ≥ 30 ∧ dOut .returned ≥ 30 ∧
      dOut .reverted ≥ 30 do
    throw <| IO.userError "§2 coverage: a region is empty or too small (A2)"
  -- §3
  expectHolds "§3 counted loops: scheduled, accepted by checkCfg, Θ = Venom, Θ gas = runSCfg"
    (∀ (x₀ xB : List (ℕ × ℕ × ℕ)) (a b t w n : ℕ) (kv : List (ℕ × ℕ)) (cd : List ℕ),
      lawFor schedule (loopFn x₀ xB a b t w) (mkKvs kv) (loopData n cd) = true)
  let lgen := (List.range 300).map fun i =>
    (loopFn (triples i 5) (triples (i + 4) 5) (mix i % 40) (mix (i + 1) % 40) (mix (i + 2) % 9) i,
      loopData (mix (i + 3) % 16) ((List.range (i % 5)).map fun j => mix (i * j)))
  let iters (k : ℕ) := (lgen.filter fun (f, data) => match venomRun f [] data with
    | .done fv => read32 fv.state.mem 0 == k
    | _ => false).length
  let lSched := (lgen.filter fun (f, _) => (schedule f).isSome).length
  IO.println s!"§3 coverage (300 loops): scheduled {lSched}; iterations 0: {iters 0}, 1: {iters 1}, \
    2: {iters 2}, 3: {iters 3}"
  unless lSched ≥ 250 ∧ iters 0 ≥ 30 ∧ iters 2 + iters 3 ≥ 100 do
    throw <| IO.userError "§3 coverage: a region is empty or too small (A2)"
  -- §4
  expectHolds "§4 soundness: whenever checkCfg accepts a sequential-φ schedule, Θ = Venom"
    (∀ (x₀ xB : List (ℕ × ℕ × ℕ)) (a b t w n : ℕ) (cd : List ℕ),
      (match scheduleSeq (loopFn x₀ xB a b t w) with
       | some sf => !accepted (loopFn x₀ xB a b t w) sf ||
           cfgAgrees (loopFn x₀ xB a b t w) sf [] (loopData n cd) 0
       | none => true) = true)
  let seqRes := lgen.filterMap fun (f, _) => (scheduleSeq f).map (accepted f)
  let rej := (seqRes.filter (!·)).length
  IO.println s!"§4 coverage (300 loops): sequential-φ schedules {seqRes.length}, accepted by \
    checkCfg (the order happened to be right, or no φ reads another) {seqRes.length - rej}, \
    rejected {rej}"
  unless rej ≥ 50 ∧ seqRes.length - rej ≥ 100 do
    throw <| IO.userError "§4 coverage: the accepted or the rejected region is too small (A2)"
  -- §5
  expectRefuted "§5 canary: a checker without the edge condition is unsound"
    (∀ (x₀ xB : List (ℕ × ℕ × ℕ)) (a b t w n : ℕ) (cd : List ℕ),
      (match scheduleSeq (loopFn x₀ xB a b t w) with
       | some sf => !checkCfgNoEdge (loopFn x₀ xB a b t w) sf (layoutFn (loopFn x₀ xB a b t w)) ||
           cfgAgrees (loopFn x₀ xB a b t w) sf [] (loopData n cd) 0
       | none => true) = true)
  expectRefuted "§5 canary: sequential-φ schedules run unchecked agree with Venom on Θ"
    (∀ (x₀ xB : List (ℕ × ℕ × ℕ)) (a b t w n : ℕ) (cd : List ℕ),
      (match scheduleSeq (loopFn x₀ xB a b t w) with
       | some sf => cfgAgrees (loopFn x₀ xB a b t w) sf [] (loopData n cd) 0
       | none => true) = true)
  expectRefuted "§5 canary: Θ gas = the Venom gas (jumps and JUMPDESTs free)"
    (∀ (x₀ x₁ x₂ x₃ : List (ℕ × ℕ × ℕ)) (c t : ℕ),
      (let f := diamond x₀ x₁ x₂ x₃ c t
       match schedule f, venomRun f [] [] with
       | some sf, .done fv => cfgAgrees f sf [] [] 0 (gasModel := some fv.gas)
       | _, _ => true) = true)
  IO.println "cross-block lowering: standing caveat (D1): the scheduler, the generators and the \
    reference model are test code; the checker's soundness is the theorem checkCfg_sound"

#eval runAll

end EvmYul.Venom.BlockLoweringTests
