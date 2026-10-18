module

public import EvmYul.FFI.Primitives
public meta import EvmYul.FFI.Primitives
public import EvmYul.Venom.StackLowering
public meta import EvmYul.Venom.StackLowering
public import EvmYul.Venom.Text
public meta import EvmYul.Venom.Text
public import EvmYul.Venom.EvmMachine
public meta import EvmYul.Venom.EvmMachine
public import EvmYul.Venom.ThetaTestHarness
public meta import EvmYul.Venom.ThetaTestHarness
public import EvmYul.Testing.Counted
public meta import EvmYul.Testing.Counted
public import Plausible
public meta import Plausible

@[expose] public meta section

/-!
# Tests of `djmp` on real Vyper output and of the full-CFG lowering checker

`Cfg.lean` §7 gives `djmp` its meaning through label addresses (`runL`); `StackLowering.lean`
checks stack code for whole functions of the control-flow-graph language (`checkFunc`, proved
sound by `checkFunc_sound`). This module is an FFI test root: the real Vyper bytecode runs on `Θ`
during the build. Each section names the `TESTING.md` rule it applies.

The stack code comes from an **untrusted scheduler** written here (`schedFunc`): live-variable
layouts (joined over the targets of each `djmp`, which all see the same stack), and before every
instruction and at every edge a *compaction* that pushes exactly the operands needed (with `DUP`,
`PUSH` and `PUSH @label`) and removes the rest with `SWAPm; POP` pairs. A `jnz` whose two
successors expect different stacks gets fix-up code on its fall-through path. The checker, not the
scheduler, is what the theorem trusts.

1. **§1 `djmp` on real Vyper output (A2, D1).** The parsed `store.vy` (Vyper 0.4.3), with its
   `djmp` **unresolved**, runs under the project's EVM (`evmInterface`) with the label addresses
   read off Vyper's own bytecode (the jump table at the end of the code), and agrees with that
   bytecode on `Θ`: outcome, storage slot 0, the word returned by `get()`. Unit checks with concrete
   values (`set(5)` stores 5, `bump` overflow reverts, `get()` returns 41), a counted property over
   all four calls, and a second route: the same runs as the earlier `jnz` resolution of the
   dispatch. A wrong address map (the buckets exchanged) must be refuted.
2. **§2 The real function lowered (A2).** The scheduler's stack code for `store.vy` is accepted by
   `checkFunc`, and under `evmInterface` it ends as the Venom function and as Vyper's bytecode.
3. **§3 Random functions (counted, A2).** Generated functions with a `djmp` through a jump table
   (some entries are not the address of any target), buckets with `assert`, a two-result
   instruction and label operands, a φ join and a loop whose back edge swaps two values through
   φs; their `jnz` needs fix-up code. The scheduler's code is accepted, and the stack run ends as
   the Venom run; every region (halted, reverted, Venom fault) is counted.
4. **§4 Soundness against perturbed code, and canaries (E1).** Randomly perturbed stack code: when
   `checkFunc` accepts it, the runs agree (counted). A copy of the checker with one condition
   removed must be refuted for each of: the edge condition, the `djmp` address-collision
   condition, the `jnz` fall-through edge (code with its fix-up code dropped), and the freshness
   condition (on a fixed non-SSA block).
-/

namespace EvmYul.Venom.StackLoweringTests

open EvmYul.Venom EvmYul.Venom.Cfg EvmYul.Venom.StackLowering EvmYul.Venom.Text
  EvmYul.Venom.EvmMachine Plausible Plausible.Decorations

/-! ## The untrusted scheduler -/

/-- Variables of an operand. -/
def opVars : Cfg.Operand → List Var
  | .var v => [v]
  | _ => []

/-- Variables an ordinary instruction reads. -/
def instUses (i : Inst) : List Var := i.args.flatMap opVars

/-- Variables a terminator reads. -/
def termUses (t : Inst) : List Var :=
  match t.op, t.args with
  | .jnz, c :: _ | .djmp, c :: _ => opVars c
  | _, _ => []

/-- The φ outputs of a block. -/
def phiOutsOf (b : Block) : List Var := b.phis.flatMap (·.outs)

/-- Variables the φs of `b` read on the edge from `pred`. -/
def phiUsesFrom (b : Block) (pred : Label) : List Var :=
  b.phis.flatMap fun i => ((phiPick pred i.args).map opVars).getD []

/-- Variables live before `body` when `after` is live after it. -/
def liveBefore (body : List Inst) (after : List Var) : List Var :=
  body.foldr (fun i live => (instUses i ++ live.filter (· ∉ i.outs)).eraseDups) after

/-- Variables live at the terminator of `b` (its own uses and what its successors need). -/
def liveAtTerm (f : Func) (live : Label → List Var) (b : Block) : List Var :=
  let out := b.succs.flatMap fun l =>
    match f.find? l with
    | some s => (live l).filter (· ∉ phiOutsOf s) ++ phiUsesFrom s b.label
    | none => []
  ((match b.term? with | some t => termUses t | none => []) ++ out).eraseDups

/-- The other targets of every `djmp` that targets `l` (they all see the same stack). -/
def djmpSibs (f : Func) (l : Label) : List Label :=
  f.blocks.flatMap fun b =>
    match b.term? with
    | some t => if t.op = .djmp ∧ l ∈ t.targets then t.targets else []
    | none => []

/-- The `djmp` group of `l`: the labels reachable from `l` through "both targets of one `djmp`"
(the transitive closure of `djmpSibs`; all of them must see the same stack, since one `djmp` leaves
one stack for all its targets). `|blocks|` rounds reach the fixpoint. -/
def djmpGroup (f : Func) (l : Label) : List Label :=
  (List.range f.blocks.length).foldl (fun g _ => (g ++ g.flatMap (djmpSibs f)).eraseDups) [l]

/-- Look a label up in a table (`[]` if absent). Tables are passed as data so that each is computed
once per function: a `Label → …` closure built by a definition would be recomputed at every call. -/
def lookupIn {α : Type} (tbl : List (Label × List α)) (l : Label) : List α := (tbl.lookup l).getD []

/-- The `djmp` group of every block. -/
def groupTable (f : Func) : List (Label × List Label) :=
  f.blocks.map fun b => (b.label, djmpGroup f b.label)

/-- `n` rounds of the liveness fixpoint (live at the start of each body). A block's set is joined
over its `djmp` group (`gt`; a label missing from `gt` is its own group): the one stack a `djmp`
leaves must hold what every block of the group needs, so the predecessor must keep all of it
alive. -/
def liveRounds (gt : List (Label × List Label)) (f : Func) : Nat → List (Label × List Var)
  | 0 => f.blocks.map fun b => (b.label, [])
  | n + 1 =>
    let prev := liveRounds gt f n
    let raw := f.blocks.map fun b => (b.label, liveBefore b.body (liveAtTerm f (lookupIn prev) b))
    raw.map fun (l, _) => (l, (((gt.lookup l).getD [l]).flatMap (lookupIn raw)).eraseDups)

/-- Variables live at the start of each block's body. -/
def liveTable (f : Func) : List (Label × List Var) :=
  liveRounds (groupTable f) f (2 * f.blocks.length + 2)

/-- The first version of `liveTable`: no join over `djmp` groups (kept as the falsified
alternative). -/
def liveTableDirect (f : Func) : List (Label × List Var) :=
  liveRounds [] f (2 * f.blocks.length + 2)

/-- The sorted layout of a set of live variables. -/
def sortedLayout (vs : List Var) : List Cfg.Operand :=
  (vs.eraseDups.mergeSort fun a b => !decide (b < a)).map .var

/-- The entry layout of each block (top first): empty for the entry block; otherwise the live
variables of its whole `djmp` group, sorted. -/
def layoutTable (f : Func) : List (Label × List Cfg.Operand) :=
  let gt := groupTable f
  let lt := liveTable f
  f.blocks.map fun b => (b.label, if b.label = f.entry then [] else
    sortedLayout ((lookupIn gt b.label).flatMap (lookupIn lt)))

/-- The first version of `layoutTable`: liveness without the group join, layouts joined over the
*direct* `djmp` siblings only. Kept as the falsified alternative (§3): two `djmp`s sharing a target
need the transitive group, in the layouts and in the liveness of the blocks that end in a `djmp`. -/
def layoutTableDirect (f : Func) : List (Label × List Cfg.Operand) :=
  let lt := liveTableDirect f
  f.blocks.map fun b => (b.label, if b.label = f.entry then [] else
    sortedLayout (lookupIn lt b.label ++ (djmpSibs f b.label).flatMap (lookupIn lt)))

/-- One push of `o` onto the symbolic stack `cur`. -/
def pushOne (cur : List Cfg.Operand) : Cfg.Operand → Option SOp
  | .lit w => some (.push w)
  | .lbl l => some (.pushL l)
  | .var v => (cur.findIdx? (· == .var v)).bind fun i => if i < 16 then some (.dup (i + 1)) else none

/-- Push the operands `os` in order (the last one ends on top). -/
def buildOn (cur : List Cfg.Operand) : List Cfg.Operand → Option (List SOp)
  | [] => some []
  | o :: os => do
    let c ← pushOne cur o
    let rest ← buildOn (o :: cur) os
    pure (c :: rest)

/-- Code that turns the symbolic stack `S` into exactly `T` (top first): push `T` rotated right by
`|S| mod |T|`, then `|S|` times `SWAP|T|; POP`, each of which rotates the top `|T|` items left by
one and removes one old item. -/
def compact (S T : List Cfg.Operand) : Option (List SOp) :=
  let k := S.length
  let m := T.length
  if m = 0 then some (List.replicate k .pop)
  else do
    let r := k % m
    let R := T.drop (m - r) ++ T.take (m - r)
    let c ← buildOn S R.reverse
    if m ≤ 16 then pure (c ++ (List.replicate k [SOp.swap m, .pop]).flatten) else none

/-- The stack an edge `pred → l` must leave: `l`'s layout with its φs replaced. -/
def edgeLayout (lay : Label → List Cfg.Operand) (f : Func) (pred l : Label) :
    Option (List Cfg.Operand) := do
  let bl ← f.find? l
  (lay l).mapM (StackLowering.substPhi bl.phis pred)

/-- Schedule one block. -/
def schedBlock (lay : Label → List Cfg.Operand) (live : Label → List Var) (f : Func) (b : Block) :
    Option StackLowering.SBlock := do
  let t ← b.term?
  let atTerm := liveAtTerm f live b
  let body := b.body
  let step : (List SOp × List Cfg.Operand) → (Inst × Nat) → Option (List SOp × List Cfg.Operand) :=
    fun (code, S) (i, idx) => do
      let after := liveBefore (body.drop (idx + 1)) atTerm
      let keep := (S.filterMap fun
        | .var v => if v ∈ after ∧ v ∉ i.outs then some (Cfg.Operand.var v) else none
        | _ => none).eraseDups
      let c ← compact S (i.args ++ keep)
      if i.op = .assert then pure (code ++ c ++ [.assert], keep)
      else pure (code ++ c ++ [.exec i.op i.args.length i.outs.length], i.outs.map .var ++ keep)
  let (code, S) ← body.zipIdx.foldlM step ([], lay b.label)
  match t.op, t.args with
  | .jmp, [.lbl l] => do
    let T ← edgeLayout lay f b.label l
    let c ← compact S T
    pure { label := b.label, code := code ++ c, term := .jump l }
  | .jnz, [c, .lbl tl, .lbl el] => do
    let Tt ← edgeLayout lay f b.label tl
    let Te ← edgeLayout lay f b.label el
    let cc ← compact S (c :: Tt)
    let fix ← compact Tt Te
    pure { label := b.label, code := code ++ cc, term := .jumpi tl el fix }
  | .djmp, c :: ts => do
    let ls ← asLabels ts
    let l ← ls.head?
    let T ← edgeLayout lay f b.label l
    let cc ← compact S (c :: T)
    pure { label := b.label, code := code ++ cc, term := .djump }
  | .revert, _ => pure { label := b.label, code := code, term := .revert }
  | _, _ => pure { label := b.label, code := code, term := .halt }

/-- Schedule a function with the layouts `lay` (`none` if the scheduler cannot). -/
def schedWith (lay : Label → List Cfg.Operand) (f : Func) : Option StackLowering.SFunc := do
  let live := lookupIn (liveTable f)
  let bs ← f.blocks.mapM (schedBlock lay live f)
  pure { entry := f.entry, blocks := bs }

/-- Schedule a function (`none` if the scheduler cannot). -/
def schedFunc (f : Func) : Option StackLowering.SFunc := schedWith (lookupIn (layoutTable f)) f

/-- The scheduler's output with layouts `lay`, if `checkFunc` accepts it with those layouts. -/
def loweredWith (lay : Label → List Cfg.Operand) (addr : LabelAddr) (f : Func) :
    Option StackLowering.SFunc :=
  match schedWith lay f with
  | some sf => if checkFunc addr f sf lay then some sf else none
  | none => none

/-- The scheduler's output, if `checkFunc` accepts it with the scheduler's layouts. -/
def lowered (addr : LabelAddr) (f : Func) : Option StackLowering.SFunc := loweredWith (lookupIn (layoutTable f)) addr f

/-! ## §1 `djmp` on real Vyper output -/

/-- The recorded `vyper -f bb_runtime` output for `store.vy`. -/
def fixturePath : System.FilePath := "docs/research/venom/store_bb_runtime_0.4.3.txt"

/-- The jump-table labels of the fixture, in table order (`data readonly { dbsection
selector_buckets: db @selector_bucket_0; db @selector_bucket_1 }`). -/
def bucketLabels : List Label := ["selector_bucket_0", "selector_bucket_1"]

/-- The label addresses read off Vyper's bytecode: the jump table of `2·|bucketLabels|` bytes is
the end of the code (`selector_buckets` is its offset) and holds each bucket's offset as a
big-endian 2-byte word. Every other label has no address. -/
def addrFromCode (code : ByteArray) : LabelAddr := fun l =>
  let n := bucketLabels.length
  let base := code.size - 2 * n
  if l = "selector_buckets" then some (BitVec.ofNat 256 base)
  else match bucketLabels.idxOf? l with
    | some j => some (BitVec.ofNat 256 ((code.get! (base + 2 * j)).toNat * 256 +
        (code.get! (base + 2 * j + 1)).toNat))
    | none => none

/-- The same map with the two buckets exchanged (the canary). -/
def addrSwapped (code : ByteArray) : LabelAddr := fun l =>
  if l = "selector_bucket_0" then addrFromCode code "selector_bucket_1"
  else if l = "selector_bucket_1" then addrFromCode code "selector_bucket_0"
  else addrFromCode code l

/-- The four calls of the sweep: `set(x)`, `bump(x)`, `get()`, and a foreign selector. -/
def callOf (sel : Nat) (x : Nat) : Nat × List Nat :=
  match sel % 4 with
  | 0 => (0x60fe47b1, [x])
  | 1 => (0xb20eb4c4, [x])
  | 2 => (0x0c55699c, [])
  | _ => (ThetaTests.mix x % 2 ^ 32, [x])

/-- Initial values of slot 0: boundary values (overflow of `bump` from `2²⁵⁶ − 1`) and seeds. -/
def slotOf0 (k : Nat) : Nat := [0, 1, 2 ^ 256 - 1, 2 ^ 255, 41].getD (k % 5) (ThetaTests.mix k)

/-- A Venom or stack run on the EVM agrees with Vyper's bytecode on `Θ`: outcome, slot 0, and the
returned word for a successful `get()`. -/
def agrees (r : Result EVM.State) (code : ByteArray) (sel x slot0 value : Nat) : Bool :=
  let (s, args) := callOf sel x
  let data := (Vyper.calldata s args).toList
  let kvs := [(0, slot0)]
  match r, Vyper.execute code kvs ⟨data.toArray⟩ value with
  | .halted st, some v =>
    v.outcome == .success && slotOf st 0 == v.slot 0 &&
      (if s = 0x0c55699c then v.output.toList == (st.memory.readWithPadding 64 32).toList
       else v.output.isEmpty)
  | .reverted _, some v => v.outcome == .revert && v.slot 0 == slot0 % 2 ^ 256
  | _, _ => false

/-- The machine state a call starts in: Vyper's bytecode is the running code (`CODECOPY` reads the
jump table from it). -/
def startOf (code : ByteArray) (sel x slot0 value : Nat) : EVM.State :=
  let (s, args) := callOf sel x
  initState code [(0, slot0)] (Vyper.calldata s args).toList value

/-- The parsed function with its `djmp`, run with label addresses. -/
def venomRun (addr : LabelAddr) (f : Func) (code : ByteArray) (sel x slot0 value : Nat) :
    Result EVM.State :=
  runL addr f 100 "" f.entry Env.empty (startOf code sel x slot0 value)

/-- The stack function, run with label addresses. -/
def stackRun (addr : LabelAddr) (sf : StackLowering.SFunc) (code : ByteArray)
    (sel x slot0 value : Nat) : Result EVM.State :=
  runS addr sf 100 sf.entry [] (startOf code sel x slot0 value)

/-- The earlier resolution of the dispatch (`TextTests.lean`): drop the jump-table read and jump on
the bucket index `%4` with `jnz %4, @selector_bucket_1, @selector_bucket_0`. -/
def resolveDjmp (f : Func) : Func :=
  { f with blocks := f.blocks.map fun b =>
    if b.label = f.entry then
      { b with insts := b.insts.takeWhile (fun i => !i.args.contains (.lbl "selector_buckets")) ++
        [⟨.jnz, [.var "4", .lbl "selector_bucket_1", .lbl "selector_bucket_0"], []⟩] }
    else b }

/-- Outcome tag and slot 0 of a run (for comparing two Venom routes). -/
def tagOf (r : Result EVM.State) : Option (Nat × Nat) :=
  match r with
  | .halted st => some (0, slotOf st 0)
  | .reverted st => some (1, slotOf st 0)
  | _ => none

/-! ## §3 Random functions -/

@[expose] section

/-- The state of the test machine: call data, a jump table (read by `mload`), and a log of
`sstore`s. -/
structure TS where
  /-- Call data words (`calldataload i`). -/
  input : List Cfg.Word
  /-- The jump table (`mload i`). -/
  table : List Cfg.Word
  /-- The `sstore` log: key, value, key, value, … -/
  log : List Cfg.Word
  deriving BEq, Repr

end

/-- The test machine. `invoke` is given two results (`a + b`, `a · b`) to exercise
multi-result instructions; the other opcodes are arithmetic, reads and the log. -/
def testMachine : EvmInterface TS where
  exec
    | .calldataload, [i], s => some ([s.input.getD i.toNat 0], s)
    | .mload, [i], s => some ([s.table.getD i.toNat 0], s)
    | .add, [a, b], s => some ([a + b], s)
    | .sub, [a, b], s => some ([a - b], s)
    | .xor, [a, b], s => some ([a ^^^ b], s)
    | .and, [a, b], s => some ([a &&& b], s)
    | .lt, [a, b], s => some ([if a < b then 1 else 0], s)
    | .iszero, [a], s => some ([if a = 0 then 1 else 0], s)
    | .assign, [a], s => some ([a], s)
    | .invoke, [a, b], s => some ([a + b, a * b], s)
    | .sstore, [k, v], s => some ([], { s with log := s.log ++ [k, v] })
    | _, _, _ => none

/-- A literal. -/
def L (n : Nat) : Cfg.Operand := .lit (BitVec.ofNat 256 n)

/-- A variable. -/
def V (v : Var) : Cfg.Operand := .var v

/-- An instruction. -/
def I (op : Op) (args : List Cfg.Operand) (outs : List Var) : Inst := ⟨op, args, outs⟩

/-- The body of bucket `j` from its seeds: additions, `xor` with the input `%x`, the two-result
`invoke`, an `assert` (reverting when the running value is below a small bound), a store, and an
addition of the bucket's own address (a label operand). Returns the body and its last value. -/
def bucketBody (j : Nat) (seeds : List Nat) : List Inst × Var :=
  seeds.zipIdx.foldl (fun (acc, prev) (sd, t) =>
    let v := s!"b{j}_{t}"
    match sd % 6 with
    | 0 => (acc ++ [I .add [V prev, L (sd / 6 % 50)] [v]], v)
    | 1 => (acc ++ [I .xor [V prev, V "x"] [v]], v)
    | 2 => (acc ++ [I .invoke [V prev, V "x"] [v, v ++ "q"]],
            if sd / 6 % 2 = 0 then v else v ++ "q")
    | 3 => (acc ++ [I .lt [V prev, L (sd / 6 % 8)] [v ++ "c"], I .iszero [V (v ++ "c")] [v ++ "z"],
                    I .assert [V (v ++ "z")] []], prev)
    | 4 => (acc ++ [I .sstore [L j, V prev] []], prev)
    | _ => (acc ++ [I .add [.lbl s!"b{j}", V prev] [v]], v)) ([], "x")

/-- How bucket `j` ends: `stop`, `revert`, or a jump to the join. -/
def bucketEnds (ts : List Nat) (j : Nat) : Nat := ts.getD j 2 % 4

/-- A generated function: `entry` reads `%k`, `%x`, loads a jump-table entry and `djmp`s to one of
`m` buckets; buckets that jump to `join` pass their last value through a φ; `loop` runs
`(r mod 4) + 1` times, swapping `%y`, `%z` through φs and logging under key `100 + %c`; `done` logs `%z`. The blocks
`join`, `loop`, `done` come before the buckets (so an address shared with a bucket would be found
first by the stack `JUMP`). -/
def genFunc (m : Nat) (bseeds : List (List Nat)) (ts : List Nat) : Func :=
  let m := m % 3 + 1
  let buckets := (List.range m).map fun j =>
    let (body, last) := bucketBody j ((bseeds.getD j []).take 6)
    let term := match bucketEnds ts j with
      | 0 => I .stop [] []
      | 1 => I .revert [] []
      | _ => I .jmp [.lbl "join"] []
    ((⟨s!"b{j}", body ++ [term]⟩ : Block), last)
  let preds := (List.range m).filter fun j => bucketEnds ts j ≥ 2
  let lastOf (j : Nat) : Var := ((buckets.map (·.2)).getD j "x")
  let phiArgs := preds.flatMap fun j => [Cfg.Operand.lbl s!"b{j}", V (lastOf j)]
  let entry : Block := { label := "entry", insts := [
    I .calldataload [L 0] ["k"], I .calldataload [L 1] ["x"], I .and [V "k", L 3] ["i"],
    I .mload [V "i"] ["a"],
    I .djmp (V "a" :: (List.range m).map fun j => .lbl s!"b{j}") [] ] }
  let join : Block := { label := "join", insts := [
    I .phi phiArgs ["r"], I .and [V "r", L 3] ["n"], I .jmp [.lbl "loop"] [] ] }
  let loop : Block := { label := "loop", insts := [
    I .phi [.lbl "join", V "n", .lbl "loop", V "c2"] ["c"],
    I .phi [.lbl "join", V "x", .lbl "loop", V "z"] ["y"],
    I .phi [.lbl "join", L 7, .lbl "loop", V "y"] ["z"],
    I .add [V "c", L 100] ["ck"],
    I .sstore [V "ck", V "y"] [],
    I .sub [V "c", L 1] ["c2"],
    I .jnz [V "c", .lbl "loop", .lbl "done"] [] ] }
  let done : Block := { label := "done", insts := [ I .sstore [L 99, V "z"] [], I .stop [] [] ] }
  { name := "gen", entry := "entry", blocks := [entry, join, loop, done] ++ buckets.map (·.1) }

/-- Label addresses: bucket `j` at `10 + 7j`; `join`, `loop`, `done` at `500…502`, or, with
`collide`, `join` at bucket 0's address. -/
def genAddr (collide : Bool) : LabelAddr := fun l =>
  if l = "join" then some (if collide then 10 else 500)
  else if l = "loop" then some 501 else if l = "done" then some 502
  else match (List.range 3).find? (fun j => s!"b{j}" = l) with
    | some j => some (BitVec.ofNat 256 (10 + 7 * j))
    | none => none

/-- The jump table: entry `e` is bucket `tbl[e] mod m`'s address, or (one value in five) an address
of no bucket. -/
def genTable (m : Nat) (tbl : List Nat) : List Cfg.Word :=
  let m := m % 3 + 1
  (List.range 4).map fun e =>
    let t := tbl.getD e e
    if t % 5 = 4 then 999 else BitVec.ofNat 256 (10 + 7 * (t % m))

/-- The start state: call data `[k, x]`, the table, an empty log. -/
def genState (m k x : Nat) (tbl : List Nat) : TS :=
  { input := [BitVec.ofNat 256 k, BitVec.ofNat 256 x], table := genTable m tbl, log := [] }

/-- A result as data: outcome tag and the log. -/
def resKey : Result TS → Nat × List Nat
  | .halted s => (0, s.log.map BitVec.toNat)
  | .reverted s => (1, s.log.map BitVec.toNat)
  | .fault => (2, [])
  | .fuelOut => (3, [])

/-- `ResultMatch` as a Boolean. -/
def matchB (rs rv : Result TS) : Bool := resKey rv == (2, []) || resKey rs == resKey rv

/-- The Venom run of a generated function. -/
def genVenom (addr : LabelAddr) (f : Func) (st : TS) : Result TS :=
  @runL TS testMachine addr f 30 "" f.entry Env.empty st

/-- The Venom run with explicit fuel (in blocks). -/
def genVenomF (fuel : Nat) (addr : LabelAddr) (f : Func) (st : TS) : Result TS :=
  @runL TS testMachine addr f fuel "" f.entry Env.empty st

/-- Loop iterations of a run: the log keys in `100…103`. -/
def loopIters (r : Result TS) : Nat :=
  match r with
  | .halted s | .reverted s =>
    ((s.log.zipIdx.filter fun (w, i) => i % 2 = 0 ∧ 100 ≤ w.toNat ∧ w.toNat < 104)).length
  | _ => 0

/-- The run reached `done` (its log has key 99). -/
def reachedDone (r : Result TS) : Bool :=
  match r with
  | .halted s => s.log.zipIdx.any fun (w, i) => i % 2 = 0 ∧ w.toNat = 99
  | _ => false

/-- The stack run of a stack function. -/
def genStack (addr : LabelAddr) (sf : StackLowering.SFunc) (st : TS) : Result TS :=
  @runS TS testMachine addr sf 30 sf.entry [] st


/-- The scheduler's output for a generated function. -/
def genLowered (collide : Bool) (m : Nat) (bseeds : List (List Nat)) (ts : List Nat) :
    Option StackLowering.SFunc :=
  lowered (genAddr collide) (genFunc m bseeds ts)

/-- §3: the scheduler's code is accepted and the stack run ends as the Venom run. -/
def genAgrees (m : Nat) (bseeds : List (List Nat)) (ts tbl : List Nat) (k x : Nat) : Bool :=
  let f := genFunc m bseeds ts
  let st := genState m k x tbl
  match genLowered false m bseeds ts with
  | some sf => matchB (genStack (genAddr false) sf st) (genVenom (genAddr false) f st)
  | none => false

/-! ## §4 Perturbed code and mutant checkers -/

/-- Insert `xs` at position `i` of `c`. -/
def insertAt (c : List SOp) (i : Nat) (xs : List SOp) : List SOp := c.take i ++ xs ++ c.drop i

/-- One perturbation of a block, chosen by the seed (one time in three at the end of the code, where
the edge compaction is): delete an instruction; insert `PUSH; POP`,
`DUP1; POP`, `SWAP1; SWAP1` (harmless), a lone `POP`, `SWAP1`, `PUSH 0` or `DUP2`; or drop the
`jnz` fix-up code. -/
def perturbBlock (sd : Nat) (b : StackLowering.SBlock) : StackLowering.SBlock :=
  let c := b.code
  let i := if sd / 16 % 3 = 0 then c.length else (sd / 48) % (c.length + 1)
  match sd % 9 with
  | 0 => { b with code := c.eraseIdx i }
  | 1 => { b with code := insertAt c i [.push 5, .pop] }
  | 2 => { b with code := insertAt c i [.dup 1, .pop] }
  | 3 => { b with code := insertAt c i [.swap 1, .swap 1] }
  | 4 => { b with code := insertAt c i [.pop] }
  | 5 => { b with code := insertAt c i [.swap 1] }
  | 6 => { b with code := insertAt c i [.push 0] }
  | 7 => { b with code := insertAt c i [.dup 2] }
  | _ => match b.term with
    | .jumpi t e _ => { b with term := .jumpi t e [] }
    | _ => { b with code := insertAt c i [.swap 1] }

/-- Perturb the block chosen by each seed. -/
def perturb (sf : StackLowering.SFunc) (seeds : List Nat) : StackLowering.SFunc :=
  seeds.foldl (fun sf sd =>
    let j := (sd / 7) % (max sf.blocks.length 1)
    { sf with blocks := sf.blocks.modify j (perturbBlock (sd / 3)) }) sf

/-- `checkCode` with the freshness condition removable (`fresh = false`: the mutant). -/
def checkCodeM (fresh : Bool) (addr : LabelAddr) : List Inst → List SOp → List Cfg.Operand →
    Option (List Cfg.Operand)
  | is, .push w :: c, S => checkCodeM fresh addr is c (.lit w :: S)
  | is, .pushL l :: c, S => if (addr l).isSome then checkCodeM fresh addr is c (.lbl l :: S) else none
  | is, .dup k :: c, S =>
    if 1 ≤ k ∧ k ≤ 16 ∧ k ≤ S.length then checkCodeM fresh addr is c (S.getD (k - 1) (.lit 0) :: S)
    else none
  | is, .swap k :: c, S =>
    if 1 ≤ k ∧ k ≤ 16 ∧ k < S.length then checkCodeM fresh addr is c (swapAt k S) else none
  | is, .pop :: c, S =>
    match S with
    | [] => none
    | _ :: S' => checkCodeM fresh addr is c S'
  | [], [], S => some S
  | i :: is, .exec o n m :: c, S =>
    if i.op = o ∧ i.op ≠ .assert ∧ i.args.length = n ∧ i.outs.length = m ∧ S.take n = i.args ∧
        i.outs.Nodup ∧ (!fresh || i.outs.all (fun x => freshC x (S.drop n))) = true then
      checkCodeM fresh addr is c (i.outs.map .var ++ S.drop n)
    else none
  | i :: is, .assert :: c, a :: S =>
    if i.op = .assert ∧ i.args = [a] then checkCodeM fresh addr is c S else none
  | _, _, _ => none

/-- `checkTerm` with one condition removed by `mode`: 1 the edge condition, 2 the `djmp`
address-collision condition, 3 the fall-through edge of a `jnz` (its fix-up code need only be
well formed); 5 weakens the collision condition to injectivity of the address map on the `djmp`'s
own targets; 0 removes nothing. -/
def checkTermM (mode : Nat) (addr : LabelAddr) (f : Func) (sf : StackLowering.SFunc)
    (layout : Label → List Cfg.Operand) (lbl : Label) (t : Inst) (st : StackLowering.STerm)
    (S : List Cfg.Operand) : Bool :=
  let edge := fun l S => mode == 1 || StackLowering.edgeOk addr f layout lbl l S
  match t.op, t.args, st with
  | .jmp, [.lbl l], .jump l' => l == l' && edge l S
  | .jnz, [c, .lbl tl, .lbl el], .jumpi tl' el' fix =>
    tl == tl' && el == el' && !isLbl c &&
      match S with
      | c' :: S' =>
        c == c' && edge tl S' &&
          match checkCodeM true addr [] fix S' with
          | some S'' => mode == 3 || edge el S''
          | none => false
      | [] => false
  | .djmp, c :: ts, .djump =>
    match S, asLabels ts with
    | c' :: S', some ls =>
      c == c' && ls.all (fun l => edge l S') &&
        (mode == 2 ||
          if mode == 5 then ls.all (fun l₁ => ls.all fun l₂ => addr l₁ != addr l₂ || l₁ == l₂)
          else sf.blocks.all (fun sb => ls.all fun l => addr sb.label != addr l || sb.label == l))
    | _, _ => false
  | .stop, _, .halt | .ret, _, .halt | .evmReturn, _, .halt => true
  | .revert, _, .revert => true
  | _, _, _ => false

/-- `checkFunc` with one condition removed by `mode` (4: freshness). -/
def checkFuncM (mode : Nat) (addr : LabelAddr) (f : Func) (sf : StackLowering.SFunc)
    (layout : Label → List Cfg.Operand) : Bool :=
  f.entry == sf.entry && (layout f.entry).isEmpty &&
    (match f.find? f.entry with
     | some b => b.phis.isEmpty
     | none => false) &&
    f.blocks.all fun b =>
      match sf.find? b.label, b.term? with
      | some sb, some t =>
        match checkCodeM (mode != 4) addr b.body sb.code (layout b.label) with
        | some S => checkTermM mode addr f sf layout b.label t sb.term S
        | none => false
      | _, _ => false

/-- §4: if the checker (`mode`) accepts the perturbed scheduler output, the runs agree. -/
def perturbOk (mode : Nat) (collide : Bool) (m : Nat) (bseeds : List (List Nat)) (ts tbl : List Nat)
    (k x : Nat) (pseeds : List Nat) : Bool :=
  let f := genFunc m bseeds ts
  let addr := genAddr collide
  let st := genState m k x tbl
  match schedFunc f with
  | some sf0 =>
    let sf := perturb sf0 (pseeds.take 2)
    !checkFuncM mode addr f sf (lookupIn (layoutTable f)) || matchB (genStack addr sf st) (genVenom addr f st)
  | none => false

/-- The perturbed code of `perturbOk` (`none` if the scheduler fails). -/
def perturbed (m : Nat) (bseeds : List (List Nat)) (ts pseeds : List Nat) : Option StackLowering.SFunc :=
  (schedFunc (genFunc m bseeds ts)).map (perturb · (pseeds.take 2))

/-- §4: the scheduler's code with every `jnz` fix-up code dropped, accepted by checker `mode` ⇒ the
runs agree. -/
def noFixOk (mode : Nat) (m : Nat) (bseeds : List (List Nat)) (ts tbl : List Nat) (k x : Nat) : Bool :=
  let f := genFunc m bseeds ts
  let st := genState m k x tbl
  match schedFunc f with
  | some sf0 =>
    let sf := { sf0 with blocks := sf0.blocks.map fun b => match b.term with
      | .jumpi t e _ => { b with term := .jumpi t e [] }
      | _ => b }
    !checkFuncM mode (genAddr false) f sf (lookupIn (layoutTable f)) ||
      matchB (genStack (genAddr false) sf st) (genVenom (genAddr false) f st)
  | none => false

/-- §4: the perturbed code is accepted (to count the valid inputs of `perturbOk`). -/
def perturbAccepted (m : Nat) (bseeds : List (List Nat)) (ts : List Nat) (pseeds : List Nat) : Bool :=
  let f := genFunc m bseeds ts
  match schedFunc f with
  | some sf0 => checkFunc (genAddr false) f (perturb sf0 (pseeds.take 2)) (lookupIn (layoutTable f))
  | none => false

/-- §4 freshness canary: `%a = 1; %a = 2; sstore 0, %a` (not SSA) with code that keeps the first
`%a` below the second and stores the stale one (`DUP2`). -/
def staleFunc : Func :=
  { name := "stale", entry := "entry", blocks := [{ label := "entry", insts := [
      I .assign [L 1] ["a"], I .assign [L 2] ["a"], I .sstore [L 0, V "a"] [], I .stop [] []] }] }

/-- The stack code of the freshness canary. -/
def staleCode : StackLowering.SFunc :=
  { entry := "entry", blocks := [{ label := "entry", term := .halt, code := [
      .push 1, .exec .assign 1 1, .push 2, .exec .assign 1 1, .dup 2, .push 0, .exec .sstore 2 0] }] }

/-- The faithful mode of the mutant code checker is `checkCode`. -/
theorem checkCodeM_true (addr : LabelAddr) :
    ∀ is c S, checkCodeM true addr is c S = checkCode addr is c S := by
  intro is c S
  induction c generalizing is S with
  | nil => cases is <;> rfl
  | cons o c ih =>
    cases o <;> cases is <;> cases S <;> simp [checkCodeM, checkCode, ih]

/-- The faithful mode of the mutant terminator checker is `checkTerm`. -/
theorem checkTermM_zero (addr : LabelAddr) (f : Func) (sf : StackLowering.SFunc)
    (layout : Label → List Cfg.Operand) (lbl : Label) (t : Inst) (st : StackLowering.STerm)
    (S : List Cfg.Operand) :
    checkTermM 0 addr f sf layout lbl t st S = checkTerm addr f sf layout lbl t st S := by
  unfold checkTermM checkTerm
  simp only [checkCodeM_true]
  rfl

/-- **Faithfulness of the mutant checker.** Mode 0 is `checkFunc`, so each canary differs from the
proved checker in exactly the condition its mode removes. -/
theorem checkFuncM_zero (addr : LabelAddr) (f : Func) (sf : StackLowering.SFunc)
    (layout : Label → List Cfg.Operand) :
    checkFuncM 0 addr f sf layout = checkFunc addr f sf layout := by
  unfold checkFuncM checkFunc StackLowering.checkBlock
  simp only [checkTermM_zero, show ((0 : Nat) != 4) = true from rfl, checkCodeM_true]
  rfl

/-- Two `djmp`s sharing a target: `p` dispatches to `A` or `S`, `q` to `S` or `B`. The three
targets form one `djmp` group and need one layout. -/
def twoDjmp : Func :=
  { name := "two", entry := "entry", blocks := [
    { label := "entry", insts := [I .calldataload [L 0] ["k"], I .calldataload [L 1] ["x"],
        I .calldataload [L 2] ["y"], I .mload [V "k"] ["a"], I .jnz [V "x", .lbl "p", .lbl "q"] []] },
    { label := "p", insts := [I .djmp [V "a", .lbl "A", .lbl "S"] []] },
    { label := "q", insts := [I .djmp [V "a", .lbl "S", .lbl "B"] []] },
    { label := "A", insts := [I .sstore [L 0, V "x"] [], I .stop [] []] },
    { label := "S", insts := [I .sstore [L 1, V "y"] [], I .stop [] []] },
    { label := "B", insts := [I .sstore [L 2, V "k"] [], I .stop [] []] }] }

/-- Addresses for `twoDjmp`. -/
def twoAddr : LabelAddr := fun l =>
  if l = "A" then some 10 else if l = "S" then some 17 else if l = "B" then some 24
  else if l = "p" then some 500 else if l = "q" then some 501 else none

/-- A start state for `twoDjmp`: `%k = k mod 4`, the table maps entries to `A`, `S`, `B` or no
target. -/
def twoState (k x y : Nat) (tbl : List Nat) : TS :=
  { input := [BitVec.ofNat 256 (k % 4), BitVec.ofNat 256 x, BitVec.ofNat 256 y],
    table := (List.range 4).map fun e => [10, 17, 24, 999].getD (tbl.getD e e % 4) 999, log := [] }

/-! ## Running -/

/-- Seeded configuration (`TESTING.md` E3). -/
def cfg : Configuration := { numInst := 300, maxSize := 30, randomSeed := some 20261015,
                             quiet := true }

/-- Fail the build on a counterexample or on too few valid inputs (counts printed). -/
def expectHolds (name : String) (p : Prop)
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] : IO Unit :=
  discard <| EvmYul.CountedTesting.holdsCore cfg name p' (EvmYul.CountedTesting.defaultMinValid cfg)

/-- Mutation test: fail the build unless a counterexample is found (counts printed). -/
def expectRefuted (name : String) (p : Prop)
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] : IO Unit :=
  discard <| EvmYul.CountedTesting.refutedCore cfg name p'

/-- `expectHolds` with more samples and an explicit floor on the valid inputs (for a guarded law
whose guard holds for a known fraction of the inputs; the floor is checked, A2). -/
def expectHoldsN (n minValid : Nat) (name : String) (p : Prop)
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] : IO Unit :=
  discard <| EvmYul.CountedTesting.holdsCore { cfg with numInst := n } name p' minValid

/-- Fail unless every named check holds. -/
def unitChecks (sec : String) (checks : List (String × Bool)) : IO Unit := do
  for (name, ok) in checks do
    unless ok do throw <| IO.userError s!"{sec} unit check failed: {name}"
  IO.println s!"{sec}: {checks.length} unit checks passed"

/-- Run everything; throws on the first failure. -/
def runAll : IO Unit := do
  let text ← IO.FS.readFile fixturePath
  let some f := parseFunc? text | throw <| IO.userError "§1: the fixture does not parse"
  let some cell := ThetaTests.storeVenom | throw <| IO.userError "§1: no store@0.4.3/venom fixture"
  let some code := cell.code? | throw <| IO.userError "§1: the fixture has no bytecode"
  let addr := addrFromCode code
  -- §1
  let slotAfter (r : Result EVM.State) : Option Nat := match r with
    | .halted st => some (slotOf st 0)
    | _ => none
  unitChecks "§1 djmp unresolved on store.vy" [
    ("the function is well formed with djmp (Func.wfD) and every djmp target has an address",
      f.wfD && f.addrOk addr),
    ("the function still contains its djmp", f.blocks.any fun b => b.insts.any (·.op == .djmp)),
    ("the jump table holds two JUMPDEST offsets inside the code",
      (bucketLabels.all fun l => match addr l with
        | some w => w.toNat < code.size && code.get! w.toNat == 0x5b
        | none => false)),
    ("both offsets are valid jump destinations of the EVM (D_J: a JUMPDEST not inside PUSH data)",
      (bucketLabels.all fun l => match addr l with
        | some w => (EvmYul.EVM.D_J code (EvmYul.UInt256.ofNat 0)).contains (EvmYul.UInt256.ofNat w.toNat)
        | none => false)),
    ("the table (last 4 bytes) follows a halting REVERT (0xfd), so it is never executed as code",
      code.get! (code.size - 5) == 0xfd),
    ("without label addresses the djmp faults (runL noAddr = run, no dispatch)",
      match venomRun noAddr f code 0 5 0 0 with | .fault => true | _ => false),
    ("set(5) from 0 stores 5", agrees (venomRun addr f code 0 5 0 0) code 0 5 0 0 &&
        slotAfter (venomRun addr f code 0 5 0 0) == some 5),
    ("bump(3) from 4 stores 7", agrees (venomRun addr f code 1 3 4 0) code 1 3 4 0 &&
        slotAfter (venomRun addr f code 1 3 4 0) == some 7),
    ("bump(1) from 2^256 - 1 reverts", agrees (venomRun addr f code 1 1 (2 ^ 256 - 1) 0) code 1 1
        (2 ^ 256 - 1) 0 && (match venomRun addr f code 1 1 (2 ^ 256 - 1) 0 with
          | .reverted _ => true | _ => false)),
    ("get() from 41 returns the word 41", agrees (venomRun addr f code 2 0 41 0) code 2 0 41 0 &&
        (match venomRun addr f code 2 0 41 0 with
         | .halted st => (st.memory.readWithPadding 64 32).toList == Vyper.word 41
         | _ => false)),
    ("set(5) with value 1 reverts (non-payable)", agrees (venomRun addr f code 0 5 0 1) code 0 5 0 1),
    ("with the buckets exchanged, set(5) no longer stores 5",
      slotAfter (venomRun (addrSwapped code) f code 0 5 0 0) != some 5)]
  let bytes5b := (List.range code.size).filter fun i => code.get! i == 0x5b
  let validJ := (EvmYul.EVM.D_J code (EvmYul.UInt256.ofNat 0)).toList.map (·.toNat)
  IO.println s!"§1 jump destinations: {bytes5b.length} bytes 0x5b in the code, of them {(bytes5b.filter (· ∈ validJ)).length} valid (D_J); bucket offsets {bucketLabels.map fun l => (addr l).map BitVec.toNat}"
  expectHolds "§1 store.vy with djmp (runL, addresses from Vyper's jump table) = Vyper's bytecode on Θ"
    (∀ (sel x k v : Nat), agrees (venomRun addr f code sel x (slotOf0 k) (v % 2)) code sel x
      (slotOf0 k) (v % 2) = true)
  expectHolds "§1 djmp semantics = the earlier jnz resolution of the dispatch (outcome, slot 0)"
    (∀ (sel x k v : Nat), (tagOf (venomRun addr f code sel x (slotOf0 k) (v % 2)) ==
      tagOf (Cfg.runEntry (resolveDjmp f) 100 (startOf code sel x (slotOf0 k) (v % 2))) &&
      (tagOf (venomRun addr f code sel x (slotOf0 k) (v % 2))).isSome) = true)
  expectRefuted "§1 canary: djmp with the bucket addresses exchanged = Vyper's bytecode"
    (∀ (sel x k v : Nat), agrees (venomRun (addrSwapped code) f code sel x (slotOf0 k) (v % 2))
      code sel x (slotOf0 k) (v % 2) = true)
  -- §2
  let some sf := lowered addr f | throw <| IO.userError "§2: the scheduler's store.vy code is rejected"
  unitChecks "§2 store.vy lowered to stack code" [
    ("checkFunc accepts it", checkFunc addr f sf (lookupIn (layoutTable f))),
    ("it has one stack block per Venom block", sf.blocks.length == f.blocks.length),
    ("its dispatch is a stack djump", sf.blocks.any fun b => match b.term with
      | .djump => true | _ => false),
    ("set(5) from 0 stores 5 (stack code)", agrees (stackRun addr sf code 0 5 0 0) code 0 5 0 0),
    ("get() from 41 returns 41 (stack code)", agrees (stackRun addr sf code 2 0 41 0) code 2 0 41 0)]
  expectHolds "§2 lowered store.vy (stack code, runS) = Vyper's bytecode on Θ"
    (∀ (sel x k v : Nat), agrees (stackRun addr sf code sel x (slotOf0 k) (v % 2)) code sel x
      (slotOf0 k) (v % 2) = true)
  expectHolds "§2 lowered store.vy (runS) = parsed store.vy (runL), outcome and slot 0"
    (∀ (sel x k v : Nat), (tagOf (stackRun addr sf code sel x (slotOf0 k) (v % 2)) ==
      tagOf (venomRun addr f code sel x (slotOf0 k) (v % 2))) = true)
  -- §3
  unitChecks "§3 generated functions" [
    ("a generated function is well formed and every djmp target has an address",
      (List.range 30).all fun i =>
        let g := genFunc i [[i, i + 1], [i * 3]] [i, i / 3, i / 9]
        g.wfD && g.addrOk (genAddr false)),
    ("the scheduler output is accepted for 100 generated functions",
      (List.range 100).all fun i => (genLowered false i
        ((List.range 3).map fun j => (List.range 6).map fun t => ThetaTests.mix (i * 31 + j * 7 + t))
        ((List.range 3).map fun j => ThetaTests.mix (i + j))).isSome),
    ("some lowered jnz carries non-empty fix-up code",
      (List.range 50).any fun i => match genLowered false i [] [2, 2, 2] with
        | some sf => sf.blocks.any fun b => match b.term with
          | .jumpi _ _ fix => !fix.isEmpty | _ => false
        | none => false),
    ("the freshness canary: checkFunc rejects the stale code, the mutant accepts it",
      !checkFunc noAddr staleFunc staleCode (fun _ => []) &&
        checkFuncM 4 noAddr staleFunc staleCode (fun _ => [])),
    ("the freshness canary: the accepted stale code stores 1 where Venom stores 2",
      resKey (genStack noAddr staleCode ⟨[], [], []⟩) == (0, [0, 1]) &&
        resKey (genVenom noAddr staleFunc ⟨[], [], []⟩) == (0, [0, 2]))]
  unitChecks "§3 two djmps sharing a target" [
    ("twoDjmp is well formed and its djmp targets have addresses", twoDjmp.wfD && twoDjmp.addrOk twoAddr),
    ("the djmp group of A is {A, S, B}", (djmpGroup twoDjmp "A").length == 3),
    ("falsified: with direct-sibling layouts the scheduled code is rejected",
      (loweredWith (lookupIn (layoutTableDirect twoDjmp)) twoAddr twoDjmp).isNone),
    ("with group layouts it is accepted", (lowered twoAddr twoDjmp).isSome)]
  expectHolds "§3 twoDjmp lowered (group layouts): runS = runL"
    (∀ (k x y : Nat) (tbl : List Nat), (match lowered twoAddr twoDjmp with
      | some sf => matchB (genStack twoAddr sf (twoState k x y tbl))
          (genVenom twoAddr twoDjmp (twoState k x y tbl))
      | none => false) = true)
  expectHolds "§3 scheduled code accepted by checkFunc, and runS = runL (TS machine)"
    (∀ (m : Nat) (bseeds : List (List Nat)) (ts tbl : List Nat) (k x : Nat),
      genAgrees m bseeds ts tbl k x = true)
  let samples := (List.range 300).map fun i =>
    let m := i
    let bs := (List.range 3).map fun j => (List.range 6).map fun t => ThetaTests.mix (i * 13 + j * 5 + t)
    let ts := (List.range 3).map fun j => ThetaTests.mix (i * 3 + j)
    let tbl := (List.range 4).map fun j => ThetaTests.mix (i * 11 + j)
    genVenom (genAddr false) (genFunc m bs ts) (genState m (ThetaTests.mix i) (ThetaTests.mix (i + 1)) tbl)
  let cnt (k : Nat) := (samples.filter fun r => (resKey r).1 == k).length
  IO.println s!"§3 coverage (300 generated runs): halted {cnt 0}, reverted {cnt 1}, Venom fault {cnt 2}, \
    out of fuel {cnt 3}"
  unless cnt 0 ≥ 30 ∧ cnt 1 ≥ 30 ∧ cnt 2 ≥ 15 do
    throw <| IO.userError "§3 coverage: a region is empty or too small (A2)"
  let inputs := (List.range 300).map fun i =>
    let bs := (List.range 3).map fun j => (List.range 6).map fun t => ThetaTests.mix (i * 13 + j * 5 + t)
    let ts := (List.range 3).map fun j => ThetaTests.mix (i * 3 + j)
    let tbl := (List.range 4).map fun j => ThetaTests.mix (i * 11 + j)
    (genFunc i bs ts, genState i (ThetaTests.mix i) (ThetaTests.mix (i + 1)) tbl)
  let iters (n : Nat) := (samples.filter fun r => reachedDone r && loopIters r == n).length
  let ends := inputs.flatMap fun (g, _) => g.blocks.filterMap fun b => b.term?.map (·.op)
  let endCnt (o : Op) := (ends.filter (· == o)).length
  IO.println s!"§3 coverage: runs reaching done {(samples.filter reachedDone).length} with 1/2/3/4 loop \
    iterations {iters 1}/{iters 2}/{iters 3}/{iters 4}; terminators stop {endCnt .stop}, revert \
    {endCnt .revert}, jmp {endCnt .jmp}, jnz {endCnt .jnz}, djmp {endCnt .djmp}"
  unless iters 1 ≥ 5 ∧ iters 2 ≥ 5 ∧ iters 3 ≥ 5 ∧ iters 4 ≥ 5 ∧ endCnt .stop ≥ 30 ∧ endCnt .revert ≥ 30 do
    throw <| IO.userError "§3 coverage: a loop count or a terminator kind is too rare (A2)"
  unitChecks "§3 fuel (in blocks; a run visits at most entry, bucket, join, 4 × loop, done = 8)" [
    ("fuel 8 gives the same result as fuel 30 and 300 on the 300 sample runs",
      inputs.all fun (g, st) => resKey (genVenomF 8 (genAddr false) g st) == resKey (genVenomF 30 (genAddr false) g st) &&
        resKey (genVenomF 300 (genAddr false) g st) == resKey (genVenomF 30 (genAddr false) g st)),
    ("the bound is tight: fuel 7 runs out on some sample",
      inputs.any fun (g, st) => resKey (genVenomF 7 (genAddr false) g st) == (3, []))]
  -- §4
  -- mode 0 of the mutant checker is `checkFunc` by `checkFuncM_zero` (proved above)
  let acc := ((List.range 300).filter fun i => perturbAccepted i [[i], [i * 5]] [i % 4, i / 4 % 4]
    [ThetaTests.mix i, ThetaTests.mix (i + 3)]).length
  IO.println s!"§4 coverage: checkFunc accepts {acc}/300 perturbed functions"
  unless 30 ≤ acc ∧ acc ≤ 270 do
    throw <| IO.userError "§4 coverage: perturbations all accepted or all rejected (A2)"
  expectHoldsN 500 100
    "§4 perturbed stack code: accepted by checkFunc ⇒ runS = runL (guarded; colliding addresses too)"
    (∀ (c : Bool) (m : Nat) (bseeds : List (List Nat)) (ts tbl : List Nat) (k x p0 : Nat)
      (pseeds : List Nat), (match perturbed m bseeds ts (p0 :: pseeds) with
        | some sf => checkFunc (genAddr c) (genFunc m bseeds ts) sf (lookupIn (layoutTable (genFunc m bseeds ts)))
        | none => false) = true →
      perturbOk 0 c m bseeds ts tbl k x (p0 :: pseeds) = true)
  expectRefuted "§4 canary: checker without the edge condition is sound"
    (∀ (m : Nat) (bseeds : List (List Nat)) (ts tbl : List Nat) (k x p0 : Nat) (pseeds : List Nat),
      perturbOk 1 false m bseeds ts tbl k x (p0 :: pseeds) = true)
  expectRefuted "§4 canary: checker without the djmp address-collision condition is sound"
    (∀ (m : Nat) (bseeds : List (List Nat)) (ts tbl : List Nat) (k x : Nat),
      perturbOk 2 true m bseeds ts tbl k x [] = true)
  expectRefuted "§4 canary: collision condition weakened to injectivity on the djmp's own targets"
    (∀ (m : Nat) (bseeds : List (List Nat)) (ts tbl : List Nat) (k x : Nat),
      perturbOk 5 true m bseeds ts tbl k x [] = true)
  let withFix := (List.range 100).filter fun i => match schedFunc (genFunc i [[i]] [2, 2, 2]) with
    | some sf => sf.blocks.any fun b => match b.term with | .jumpi _ _ fix => !fix.isEmpty | _ => false
    | none => false
  unitChecks "§4 jnz fix-up code dropped" [
    (s!"{withFix.length}/100 generated functions need fix-up code (at least 50)", withFix.length ≥ 50),
    ("checkFunc rejects each of them once its fix-up code is dropped",
      withFix.all fun i => !checkFuncM 0 (genAddr false) (genFunc i [[i]] [2, 2, 2])
        { entry := "entry", blocks := ((schedFunc (genFunc i [[i]] [2, 2, 2])).map (·.blocks)).getD [] |>.map
            fun b => match b.term with | .jumpi t e _ => { b with term := .jumpi t e [] } | _ => b }
        (lookupIn (layoutTable (genFunc i [[i]] [2, 2, 2]))))]
  expectRefuted "§4 canary: checker without the jnz fall-through edge condition is sound"
    (∀ (m : Nat) (bseeds : List (List Nat)) (ts tbl : List Nat) (k x : Nat),
      noFixOk 3 m bseeds ts tbl k x = true)
  IO.println "Venom djmp / stack lowering: standing caveats (D1): stack-instruction gas and the byte \
    encoding of jumps and jump tables are not modelled; the scheduler is untrusted (checkFunc is what \
    checkFunc_sound trusts)"

#eval runAll

end EvmYul.Venom.StackLoweringTests
