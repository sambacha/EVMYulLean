module

public import EvmYul.FFI.Primitives
public meta import EvmYul.FFI.Primitives
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
# Tests of the Venom text parser and printer

`Text.lean` reads `vyper -f bb_runtime` text into the CFG layer and prints it back. This module is an
FFI test root: the parsed real compiler output runs on the project's EVM next to the real bytecode.
Each section names the `TESTING.md` rule it applies.

1. **§1 The recorded Vyper output (concrete values).** `docs/research/venom/store_bb_runtime_0.4.3.txt`
   (`store.vy`, Vyper 0.4.3) parses to one function `__main_entry` with five blocks whose labels and
   instruction counts are the ones counted by hand in the text; hexadecimal selectors are read as
   their values; every block's successors equal the `OUT=[…]` list that Vyper printed in the comment
   on its label line (an independent oracle in the same file). Syntax errors are rejected.
2. **§2 Round trip (counted).** For random functions (identifier names, every opcode, boundary
   literals up to `2²⁵⁶ − 1`, zero to two outputs) `parseFuncs (printFunc f) = [f]`; and parsing is
   unchanged by formatting noise (comments, `#` lines, blank lines, indentation, hexadecimal
   literals, a data section).
3. **§3 Parsed output = compiled output (counted, A2).** The parsed function, with its `djmp`
   (a jump through the data section) resolved to `jnz` on the bucket index that the function itself
   computes, runs under `evmInterface` and agrees with Vyper's own bytecode for `store.vy` on `Θ`:
   outcome, storage slot 0, and the returned word of `get()`. (Gas is not compared: the resolved
   `djmp` skips the `codecopy` of the jump table.)
4. **§4 Canaries (E1).** An opcode table where `ret` also prints as `return`, a printer that
   truncates literals to 64 bits, and a `djmp` resolution with the buckets swapped must each be
   refuted.
-/

namespace EvmYul.Venom.TextTests

open EvmYul.Venom EvmYul.Venom.Cfg EvmYul.Venom.Text EvmYul.Venom.EvmMachine Plausible
  Plausible.Decorations

/-! ## §1 The recorded output -/

/-- The recorded `vyper -f bb_runtime` output for `store.vy`. -/
def fixturePath : System.FilePath := "docs/research/venom/store_bb_runtime_0.4.3.txt"

/-- Labels and the `OUT=[…]` successor lists that Vyper printed in the comments of the label lines
(read from the raw text, independently of the parser). -/
def outComments (text : String) : List (String × List String) :=
  (splitC '\n' text.toList).filterMap fun line =>
    let t := trimC line
    match (splitC ';' t) with
    | [lbl, cmt] =>
      let l := trimC lbl
      let c := trimC cmt
      if l.getLast? = some ':' ∧ ['O', 'U', 'T', '=', '['].isPrefixOf c then
        let inner := (c.drop 5).takeWhile (· ≠ ']')
        let outs := if (trimC inner).isEmpty then [] else
          (splitC ',' inner).map fun s => String.ofList (trimC s)
        some (String.ofList l.dropLast, outs)
      else none
    | _ => none

/-- A copy `%x = n`. -/
def isCopyOf (i : Inst) (x : String) (n : Nat) : Bool :=
  i.op == .assign && i.outs == [x] && i.args == [.lit (BitVec.ofNat 256 n)]

/-- Every instruction of a function. -/
def allInsts (f : Func) : List Inst := f.blocks.flatMap (·.insts)

/-- Syntax errors: each must be rejected. -/
def badTexts : List (String × String) :=
  [("unknown opcode", "function f {\n  a:\n    %1 = frobnicate 1\n    stop\n}\n"),
   ("unclosed function", "function f {\n  a:\n    stop\n"),
   ("instruction before the first label", "function f {\n    stop\n  a:\n    stop\n}\n"),
   ("variable without a name", "function f {\n  a:\n    %1 = add %, 1\n    stop\n}\n"),
   ("output that is not a variable", "function f {\n  a:\n    5 = add 1, 2\n    stop\n}\n"),
   ("bad hexadecimal digit", "function f {\n  a:\n    %1 = 0x1g\n    stop\n}\n"),
   ("text outside any section", "stop\n"),
   ("a copy without an output", "function f {\n  a:\n    %1\n}\n")]

/-- §1 unit checks on the recorded text; each must be `true`. -/
def fixtureChecks (text : String) : List (String × Bool) :=
  let parsed := parseFunc? text
  let f := parsed.getD ⟨"", "", []⟩
  let find (l : String) := (f.find? l).map (·.insts) |>.getD []
  [("parses to exactly one function, named __main_entry, entry = __main_entry",
      parsed.isSome && f.name == "__main_entry" && f.entry == "__main_entry"),
   ("five blocks, in the printed order",
      f.blocks.map (·.label) ==
        ["__main_entry", "selector_bucket_1", "selector_bucket_0", "6_then", "9_if_exit"]),
   ("instruction counts per block, counted by hand: 16, 17, 4, 22, 15",
      f.blocks.map (·.insts.length) == [16, 17, 4, 22, 15]),
   ("%54 = 0x60fe47b1 is the copy of 1627277233 (set's selector)",
      (find "selector_bucket_1").any (isCopyOf · "54" 0x60fe47b1) && 0x60fe47b1 = 1627277233),
   ("%69 = 0xc55699c is get's selector 206924188",
      (find "9_if_exit").any (isCopyOf · "69" 206924188)),
   ("%47 = %2 is a copy of a variable",
      (find "__main_entry").any fun i => i.op == .assign && i.outs == ["47"] && i.args == [.var "2"]),
   ("jnz %43, @9_if_exit, @6_then: condition first, then the non-zero and zero targets",
      (find "selector_bucket_0").getLast? == some ⟨.jnz, [.var "43", .lbl "9_if_exit",
        .lbl "6_then"], []⟩),
   ("return %73, %72 is the EVM return; codecopy has three operands and no output",
      (find "9_if_exit").getLast? == some ⟨.evmReturn, [.var "73", .var "72"], []⟩ &&
        (find "__main_entry").any fun i =>
          i.op == .codecopy && i.args == [.var "51", .var "6", .var "50"] && i.outs == []),
   ("every block's successors = the OUT=[…] list in Vyper's comment (5 blocks)",
      let outs := outComments text
      outs.length == 5 && outs.all fun (l, ss) => (f.find? l).any (·.succs == ss)),
   ("the data section is skipped and comments are dropped",
      allInsts f |>.all fun i => i.args.all fun | .lbl l => l != "selector_buckets" || i.op == .add
                                                 | _ => true),
   ("printing and parsing again gives the same function",
      parseFunc? (printFunc f) == some f),
   ("printing is idempotent through the parser",
      (parseFunc? (printFunc f)).map printFunc == some (printFunc f)),
   ("the raw output is not well formed (djmp), as Cfg.lean's Func.wf says",
      !f.wf)] ++
  badTexts.map fun (name, t) => (s!"rejected: {name}", (parseFuncs t).isNone)

/-! ## §2 Random functions -/

/-- Identifier names, including the shapes Vyper prints (`50`, `9_if_exit`, `__main_entry`). -/
def namePool : List String :=
  ["50", "1", "x", "acc2", "9_if_exit", "__main_entry", "selector_bucket_0", "a_b_c", "Z9", "_"]

/-- A name from the pool. -/
def nameOf (k : Nat) : String := namePool.getD (k % namePool.length) "x"

/-- Boundary literals. -/
def litOf (k : Nat) : Cfg.Word :=
  BitVec.ofNat 256 ([0, 1, 9, 10, 15, 16, 255, 256, 2 ^ 64, 2 ^ 128 + 1, 2 ^ 255, 2 ^ 256 - 1].getD
    (k % 12) (ThetaTests.mix k))

/-- A random operand. -/
def operandOf (k : Nat) : Cfg.Operand :=
  match k % 3 with
  | 0 => .lit (litOf (k / 3))
  | 1 => .var (nameOf (k / 3))
  | _ => .lbl (nameOf (k / 3))

/-- A random instruction: opcode, up to four operands, up to two outputs; one in five is a copy
`%x = a` (the most frequent line in Vyper's output). The opcode index `7o + outs` reaches every
opcode with the small numbers that the random generator produces. -/
def instOf (o : Nat) (args : List Nat) (outs : Nat) : Inst :=
  if outs % 5 = 4 then ⟨.assign, [operandOf (args.headD o)], [nameOf o]⟩ else
  ⟨allOps.getD ((o * 7 + outs) % allOps.length) .add, (args.take 4).map operandOf,
   (List.range (outs % 3)).map fun j => nameOf (outs / 3 + j)⟩

/-- A random function: block `j` is labelled with its own pool name (the label list may repeat:
the parser does not need unique labels); the entry is the first block. -/
def funcOf (n : Nat) (bs : List (Nat × List (Nat × List Nat × Nat))) : Func :=
  let blocks := bs.map fun (l, is) => (⟨nameOf l, is.map fun (o, a, u) => instOf o a u⟩ : Block)
  ⟨nameOf n, (blocks.head?.map (·.label)).getD "", blocks⟩

/-- An operand printed with noise: literals in hexadecimal when `h` is odd. -/
def noisyOperand (h : Nat) : Cfg.Operand → String
  | .lit w => if h % 2 = 1 then "0x" ++ String.ofList (Nat.toDigits 16 w.toNat) else toString w.toNat
  | o => printOperand o

/-- A function printed with formatting noise chosen by the seeds `ns`. -/
def printNoisy (f : Func) (ns : List Nat) : String :=
  let seed (k : Nat) := ns.getD (k % max ns.length 1) k
  let inst (k : Nat) (i : Inst) : String :=
    let args := ", ".intercalate (i.args.map (noisyOperand (seed k)))
    let rhs := if i.op = .assign ∧ i.args.length = 1 ∧ i.outs ≠ [] then args
      else if i.args.isEmpty then opName i.op else opName i.op ++ "   " ++ args
    let line := match i.outs with
      | [] => rhs
      | outs => ",".intercalate (outs.map ("%" ++ ·)) ++ " = " ++ rhs
    String.ofList (List.replicate (seed (k + 1) % 7) ' ') ++ line ++
      (if seed (k + 2) % 3 = 0 then "  ; OUT=[noise] = x, y" else "") ++ "\n" ++
      (if seed (k + 3) % 4 = 0 then "\n   \n" else "")
  "# header comment\n\n" ++ "function " ++ f.name ++ " {  ; open\n" ++
    String.join (f.blocks.zipIdx.map fun (b, j) =>
      " " ++ b.label ++ ":   ; label comment\n" ++
        String.join (b.insts.zipIdx.map fun (i, k) => inst (j * 31 + k) i)) ++
    "}  ; close function " ++ f.name ++ "\n\ndata readonly {\n  dbsection t:\n    db @x\n}\n"

/-- Mutant opcode table: `ret` prints as `return` too. -/
def opNameCollide : Op → String
  | .ret => "return"
  | o => opName o

/-- `printFunc` with a different operand and opcode printer (for the mutants). -/
def printWith (opn : Op → String) (opd : Cfg.Operand → String) (f : Func) : String :=
  let inst (i : Inst) : String :=
    let args := ", ".intercalate (i.args.map opd)
    let rhs := if i.op = .assign ∧ i.args.length = 1 ∧ i.outs ≠ [] then args
      else if i.args.isEmpty then opn i.op else opn i.op ++ " " ++ args
    match i.outs with
    | [] => rhs
    | outs => ", ".intercalate (outs.map ("%" ++ ·)) ++ " = " ++ rhs
  "function " ++ f.name ++ " {\n" ++ "\n".intercalate (f.blocks.map fun b =>
    "  " ++ b.label ++ ":\n" ++ String.join (b.insts.map fun i => "      " ++ inst i ++ "\n")) ++
    "}\n"

/-- Mutant operand printer: literals truncated to 64 bits. -/
def printOperand64 : Cfg.Operand → String
  | .lit w => toString (w.toNat % 2 ^ 64)
  | o => printOperand o

/-! ## §3 Parsed output on the EVM against Vyper's bytecode -/

/-- Resolve the `djmp` of the entry block: drop the jump-table read (`add @selector_buckets, …`,
`codecopy`, `mload`, from the first instruction that mentions `@selector_buckets` on) and jump on
the bucket index `%4 = and 1, selector` that the function computed: `jnz %4, @bucket₁, @bucket₀`
(the table is `db @selector_bucket_0, db @selector_bucket_1`). With `swapped` the buckets are
exchanged (the canary). -/
def resolveDjmp (f : Func) (swapped : Bool := false) : Func :=
  let (b₀, b₁) := if swapped then ("selector_bucket_1", "selector_bucket_0")
    else ("selector_bucket_0", "selector_bucket_1")
  { f with blocks := f.blocks.map fun b =>
    if b.label = f.entry then
      { b with insts := b.insts.takeWhile (fun i => !i.args.contains (.lbl "selector_buckets")) ++
        [⟨.jnz, [.var "4", .lbl b₁, .lbl b₀], []⟩] }
    else b }

/-- The four calls of the sweep: `set(x)`, `bump(x)`, `get()`, and a foreign selector. -/
def callOf (sel : Nat) (x : Nat) : Nat × List Nat :=
  match sel % 4 with
  | 0 => (0x60fe47b1, [x])
  | 1 => (0xb20eb4c4, [x])
  | 2 => (0x0c55699c, [])
  | _ => (ThetaTests.mix x % 2 ^ 32, [x])

/-- The parsed function on the EVM agrees with Vyper's bytecode on `Θ`: outcome, slot 0, and the
returned word for a successful `get()`. -/
def agreesWithVyper (f : Func) (code : ByteArray) (sel x slot0 value : Nat) : Bool :=
  let (s, args) := callOf sel x
  let data := (Vyper.calldata s args).toList
  let kvs := [(0, slot0)]
  match Cfg.runEntry f 100 (initState .empty kvs data value), Vyper.execute code kvs ⟨data.toArray⟩ value with
  | .halted st, some r =>
    r.outcome == .success && slotOf st 0 == r.slot 0 &&
      (if s = 0x0c55699c then r.output.toList == (st.memory.readWithPadding 64 32).toList
       else r.output.isEmpty)
  | .reverted _, some r => r.outcome == .revert && r.slot 0 == slot0 % 2 ^ 256
  | _, _ => false

/-- Initial values of slot 0: boundary values (overflow of `bump` from `2²⁵⁶ − 1`) and seeds. -/
def slotOf0 (k : Nat) : Nat := [0, 1, 2 ^ 256 - 1, 2 ^ 255, 41].getD (k % 5) (ThetaTests.mix k)

/-! ## Running -/

/-- Seeded configuration (`TESTING.md` E3). -/
def cfg : Configuration := { numInst := 300, maxSize := 30, randomSeed := some 20261014,
                             quiet := true }

/-- Fail the build on a counterexample or on too few valid inputs (counts printed). -/
def expectHolds (name : String) (p : Prop)
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] : IO Unit :=
  discard <| EvmYul.CountedTesting.holdsCore cfg name p' (EvmYul.CountedTesting.defaultMinValid cfg)

/-- Mutation test: fail the build unless a counterexample is found (counts printed). -/
def expectRefuted (name : String) (p : Prop)
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] : IO Unit :=
  discard <| EvmYul.CountedTesting.refutedCore cfg name p'

/-- Run everything; throws on the first failure. -/
def runAll : IO Unit := do
  let text ← IO.FS.readFile fixturePath
  -- §1
  let checks := fixtureChecks text
  for (name, ok) in checks do
    unless ok do throw <| IO.userError s!"§1 unit check failed: {name}"
  IO.println s!"§1 store.vy Venom text: {checks.length} unit checks passed"
  let some f := parseFunc? text | throw <| IO.userError "§1: the fixture does not parse"
  -- §2
  expectHolds "§2 parseFuncs (printFunc f) = [f] (identifier names, every opcode, 256-bit literals)"
    (∀ (n : Nat) (bs : List (Nat × List (Nat × List Nat × Nat))),
      (parseFuncs (printFunc (funcOf n bs)) == some [funcOf n bs]) = true)
  expectHolds "§2 parsing ignores formatting noise (comments, #, blank lines, indentation, hex, data)"
    (∀ (n : Nat) (bs : List (Nat × List (Nat × List Nat × Nat))) (ns : List Nat),
      (parseFuncs (printNoisy (funcOf n bs) ns) == some [funcOf n bs]) = true)
  -- the same small numbers (below 31) as the random generator
  let gen := (List.range 300).map fun i =>
    funcOf i ((List.range (i % 5)).map fun j => (ThetaTests.mix (i + j) % 31,
      (List.range ((i + j) % 6)).map fun k => (ThetaTests.mix (i * 7 + j + k) % 31,
        (List.range (k % 5)).map (fun m => ThetaTests.mix (i + j * k + m) % 31),
        ThetaTests.mix (k + i) % 31)))
  let insts := gen.flatMap allInsts
  let ops := insts.flatMap (·.args)
  let cnt (p : Cfg.Operand → Bool) := (ops.filter p).length
  IO.println s!"§2 coverage (300 functions): instructions {insts.length}; operands: literals \
    {cnt fun | .lit _ => true | _ => false}, of them ≥ 2^64 {cnt fun | .lit w => w.toNat ≥ 2 ^ 64 | _ => false}, \
    variables {cnt fun | .var _ => true | _ => false}, labels {cnt fun | .lbl _ => true | _ => false}; \
    copies printed as %x = a {(insts.filter fun i => i.op == .assign && i.args.length == 1 && !i.outs.isEmpty).length}, \
    two outputs {(insts.filter (·.outs.length == 2)).length}; opcodes used \
    {(allOps.filter fun o => insts.any (·.op == o)).length}/{allOps.length}"
  unless (allOps.filter fun o => insts.any (·.op == o)).length = allOps.length ∧
      (insts.filter fun i => i.op == .assign && i.args.length == 1 && !i.outs.isEmpty).length ≥ 100 do
    throw <| IO.userError "§2 coverage: an opcode or the copy form is too rare (A2)"
  -- §3
  let some cell := ThetaTests.storeVenom | throw <| IO.userError "§3: no store@0.4.3/venom fixture"
  let some code := cell.code? | throw <| IO.userError "§3: the fixture has no bytecode"
  let g := resolveDjmp f
  unless g.wf do throw <| IO.userError "§3: the resolved function is not well formed (Func.wf)"
  let named : List (String × Bool) :=
    [("set(5) from 0 stores 5", agreesWithVyper g code 0 5 0 0 &&
        (match Cfg.runEntry g 100 (initState .empty [(0, 0)] (Vyper.calldata 0x60fe47b1 [5]).toList 0) with
         | .halted st => slotOf st 0 == 5
         | _ => false)),
     ("bump(3) from 4 stores 7", agreesWithVyper g code 1 3 4 0 &&
        (match Cfg.runEntry g 100 (initState .empty [(0, 4)] (Vyper.calldata 0xb20eb4c4 [3]).toList 0) with
         | .halted st => slotOf st 0 == 7
         | _ => false)),
     ("bump(1) from 2^256 - 1 reverts (overflow assert)", agreesWithVyper g code 1 1 (2 ^ 256 - 1) 0 &&
        (match Cfg.runEntry g 100 (initState .empty [(0, 2 ^ 256 - 1)] (Vyper.calldata 0xb20eb4c4 [1]).toList 0) with
         | .reverted _ => true
         | _ => false)),
     ("get() from 41 returns the word 41", agreesWithVyper g code 2 0 41 0 &&
        (match Cfg.runEntry g 100 (initState .empty [(0, 41)] (Vyper.calldata 0x0c55699c []).toList 0) with
         | .halted st => (st.memory.readWithPadding 64 32).toList == Vyper.word 41
         | _ => false)),
     ("set(5) with value 1 reverts (non-payable)", agreesWithVyper g code 0 5 0 1)]
  for (name, ok) in named do
    unless ok do throw <| IO.userError s!"§3 unit check failed: {name}"
  IO.println s!"§3 parsed store.vy on the EVM = Vyper bytecode on Θ: {named.length} unit checks passed"
  expectHolds "§3 parsed Venom (djmp resolved) under evmInterface = Vyper's bytecode on Θ"
    (∀ (sel x k v : Nat), agreesWithVyper g code sel x (slotOf0 k) (v % 2) = true)
  let runs := (List.range 300).map fun i =>
    let (s, args) := callOf i (ThetaTests.mix i % 1000)
    Cfg.runEntry g 100 (initState .empty [(0, slotOf0 (i / 4))]
      (Vyper.calldata s args).toList ((i / 3) % 2))
  let halted := (runs.filter fun | .halted _ => true | _ => false).length
  let reverted := (runs.filter fun | .reverted _ => true | _ => false).length
  IO.println s!"§3 coverage (300 calls over set/bump/get/foreign): halted {halted}, reverted {reverted}"
  unless halted ≥ 50 ∧ reverted ≥ 50 do
    throw <| IO.userError "§3 coverage: a region is empty or too small (A2)"
  -- §4
  expectRefuted "§4 canary: ret also printed as return (the table is no longer injective)"
    (∀ (n : Nat) (bs : List (Nat × List (Nat × List Nat × Nat))),
      (parseFuncs (printWith opNameCollide printOperand (funcOf n bs)) == some [funcOf n bs]) = true)
  expectRefuted "§4 canary: literals printed truncated to 64 bits"
    (∀ (n : Nat) (bs : List (Nat × List (Nat × List Nat × Nat))),
      (parseFuncs (printWith opName printOperand64 (funcOf n bs)) == some [funcOf n bs]) = true)
  expectRefuted "§4 canary: djmp resolved with the buckets swapped"
    (∀ (sel x k v : Nat), agreesWithVyper (resolveDjmp f (swapped := true)) code sel x (slotOf0 k)
      (v % 2) = true)
  IO.println "Venom text: standing caveat (D1): one recorded contract is the fixture; the round trip \
    is tested, not proved, apart from the opcode table (opOfName?_opName)"

#eval runAll

end EvmYul.Venom.TextTests
