module

public import EvmYul.Venom.Cfg

public section

/-!
# Venom text: a parser and a printer for control-flow graphs

`vyper -f bb_runtime --experimental-codegen` prints a contract's Venom IR as text
(`docs/research/venom/store_bb_runtime_0.4.3.txt` is the recorded output for `store.vy`). This module
reads that text into the CFG layer of `Cfg.lean` (`parseFuncs`) and prints CFG functions back
(`printFunc`), so that real compiler output can be run (`EvmMachine.lean`) and checked
(`Dominance.lean`).

**The format read.**
```
function NAME {
  LABEL:  ; comment
      %x = op a, b, …          ; an instruction with an output
      op a, b, …               ; an instruction without one
      %x = a                   ; a copy (`assign`)
  LABEL: …
}  ; comment
data readonly { … }            ; data sections are skipped
```
Operands are `%name` (a variable), `@name` (a label) and decimal or `0x` hexadecimal literals
(reduced modulo `2²⁵⁶`). Lines starting with `#` and everything after `;` are comments. The entry of
a function is its first block (Venom prints the entry first). The EVM `return` is the opcode
`evmReturn`; every other opcode is written as its constructor name (`opName`).

**Guarantees.** The opcode table is proved to round-trip (`opOfName?_opName`), so a printed opcode
is always read back as itself. The round trip of whole functions, `parseFuncs (printFunc f) = [f]`
for functions with identifier names and the entry first, is tested by counted property tests in
`TextTests.lean`, with the recorded Vyper output as a fixture.
-/

namespace EvmYul.Venom.Text

open EvmYul.Venom.Cfg

deriving instance DecidableEq for Inst
deriving instance DecidableEq for Block
deriving instance DecidableEq for Func

/-! ## Opcode names -/

/-- The text name of an opcode. -/
@[expose] def opName : Op → String
  | .assign => "assign" | .phi => "phi" | .add => "add" | .sub => "sub" | .mul => "mul"
  | .lt => "lt" | .iszero => "iszero" | .mload => "mload" | .mstore => "mstore"
  | .sload => "sload" | .sstore => "sstore" | .jmp => "jmp" | .jnz => "jnz" | .djmp => "djmp"
  | .ret => "ret" | .stop => "stop" | .revert => "revert" | .invoke => "invoke"
  | .alloca => "alloca" | .div => "div" | .mod => "mod" | .and => "and" | .or => "or"
  | .xor => "xor" | .shl => "shl" | .shr => "shr" | .gt => "gt" | .eq => "eq"
  | .calldataload => "calldataload" | .calldatasize => "calldatasize"
  | .callvalue => "callvalue" | .codecopy => "codecopy" | .assert => "assert"
  | .evmReturn => "return"

/-- Every opcode. -/
@[expose] def allOps : List Op :=
  [.assign, .phi, .add, .sub, .mul, .lt, .iszero, .mload, .mstore, .sload, .sstore, .jmp, .jnz,
   .djmp, .ret, .stop, .revert, .invoke, .alloca, .div, .mod, .and, .or, .xor, .shl, .shr, .gt,
   .eq, .calldataload, .calldatasize, .callvalue, .codecopy, .assert, .evmReturn]

/-- The opcode with a given text name. -/
@[expose] def opOfName? (s : String) : Option Op := allOps.find? (opName · == s)

/-- **The opcode table round-trips**: the printed name of every opcode is read back as that
opcode (so in particular no two opcodes share a name). -/
theorem opOfName?_opName (o : Op) : opOfName? (opName o) = some o := by
  cases o <;> decide

/-- No two opcodes print the same. -/
theorem opName_injective {o o' : Op} (h : opName o = opName o') : o = o' :=
  Option.some.inj (by rw [← opOfName?_opName o, h, opOfName?_opName])

/-! ## Printing -/

/-- Print an operand: a literal in decimal, `%v`, `@l`. -/
@[expose] def printOperand : Operand → String
  | .lit w => toString w.toNat
  | .var v => "%" ++ v
  | .lbl l => "@" ++ l

/-- Print an instruction: `%x = a` for a copy with one operand and an output, otherwise
`[%x, … =] op [a, …]`. -/
@[expose] def printInst (i : Inst) : String :=
  let args := ", ".intercalate (i.args.map printOperand)
  let rhs :=
    if i.op = .assign ∧ i.args.length = 1 ∧ i.outs ≠ [] then args
    else if i.args.isEmpty then opName i.op
    else opName i.op ++ " " ++ args
  match i.outs with
  | [] => rhs
  | outs => ", ".intercalate (outs.map ("%" ++ ·)) ++ " = " ++ rhs

/-- Print a block: its label line, then one instruction per line. -/
@[expose] def printBlock (b : Block) : String :=
  "  " ++ b.label ++ ":\n" ++ String.join (b.insts.map fun i => "      " ++ printInst i ++ "\n")

/-- Print a function (blocks in order, so the entry should come first). -/
@[expose] def printFunc (f : Func) : String :=
  "function " ++ f.name ++ " {\n" ++ "\n".intercalate (f.blocks.map printBlock) ++ "}\n"

/-! ## Parsing -/

/-- Drop leading and trailing white space. -/
@[expose] def trimC (cs : List Char) : List Char :=
  ((cs.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace).reverse

/-- Split at every occurrence of `sep` (tail recursive: whole files are split into lines). -/
@[expose] def splitC (sep : Char) (cs : List Char) : List (List Char) :=
  go cs [] []
where
  /-- `cur` is the current piece reversed, `acc` the finished pieces in reverse order. -/
  go : List Char → List Char → List (List Char) → List (List Char)
    | [], cur, acc => (cur.reverse :: acc).reverse
    | c :: cs, cur, acc => if c = sep then go cs [] (cur.reverse :: acc) else go cs (c :: cur) acc

/-- The value of a hexadecimal digit. -/
@[expose] def hexDigit? (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- A natural number in base `b` from its digits (`none` if empty or a digit is invalid). -/
@[expose] def natOf? (b : Nat) (cs : List Char) : Option Nat :=
  if cs.isEmpty then none else
  cs.foldlM (fun acc c => do
    let d ← hexDigit? c
    if d < b then some (acc * b + d) else none) 0

/-- Is the name a non-empty identifier (letters, digits, `_`)? Such names print and parse back
unchanged. -/
@[expose] def isIdent (s : String) : Bool :=
  !s.isEmpty && s.toList.all fun c => c.isAlphanum || c == '_'

/-- Parse an operand. -/
@[expose] def parseOperand (cs : List Char) : Option Operand :=
  match cs with
  | '%' :: v => if isIdent (String.ofList v) then some (.var (String.ofList v)) else none
  | '@' :: l => if isIdent (String.ofList l) then some (.lbl (String.ofList l)) else none
  | '0' :: 'x' :: h => (natOf? 16 h).map fun n => .lit (BitVec.ofNat 256 n)
  | _ => (natOf? 10 cs).map fun n => .lit (BitVec.ofNat 256 n)

/-- Parse a comma-separated operand list (empty text: no operands). -/
@[expose] def parseArgs (cs : List Char) : Option (List Operand) :=
  if (trimC cs).isEmpty then some [] else (splitC ',' cs).mapM fun a => parseOperand (trimC a)

/-- Parse the right-hand side of an instruction: a lone operand (a copy), or an opcode name and its
operands. -/
@[expose] def parseRhs (cs : List Char) (outs : List Var) : Option Inst :=
  let cs := trimC cs
  match parseOperand cs with
  | some o => if outs.isEmpty then none else some ⟨.assign, [o], outs⟩
  | none =>
    let name := cs.takeWhile (!·.isWhitespace)
    do
      let op ← opOfName? (String.ofList name)
      let args ← parseArgs (cs.drop name.length)
      pure ⟨op, args, outs⟩

/-- The position of the first `" = "` in a line. -/
@[expose] def eqPos? (cs : List Char) : Option Nat :=
  (List.range cs.length).find? fun i => (cs.drop i).take 3 == [' ', '=', ' ']

/-- Parse an instruction line. -/
@[expose] def parseInst (cs : List Char) : Option Inst :=
  match eqPos? cs with
  | some i => do
    let outs ← (splitC ',' (cs.take i)).mapM fun o =>
      match trimC o with
      | '%' :: v => if isIdent (String.ofList v) then some (String.ofList v) else none
      | _ => none
    parseRhs (cs.drop (i + 3)) outs
  | none => parseRhs cs []

/-- A line without its comment (`#` lines, and everything after `;`), trimmed. -/
@[expose] def cleanLine (cs : List Char) : List Char :=
  match trimC cs with
  | '#' :: _ => []
  | t => trimC (t.takeWhile (· ≠ ';'))

@[expose] section

/-- Parser state: outside any section, inside a data section, or inside a function (its name and
its blocks so far, newest first, each with its instructions newest first). -/
inductive PState where
  /-- Between sections. -/
  | outside
  /-- Inside a data section (skipped). -/
  | data
  /-- Inside a function. -/
  | func (name : String) (blocks : List (Label × List Inst))

end

/-- Close a function: blocks in order, entry = first block. -/
@[expose] def closeFunc (name : String) (blocks : List (Label × List Inst)) : Func :=
  let bs := blocks.reverse.map fun (l, is) => (⟨l, is.reverse⟩ : Block)
  { name, entry := (bs.head?.map (·.label)).getD "", blocks := bs }

/-- One line: the new state and the functions finished so far (`none` on a syntax error). -/
@[expose] def parseLine (st : PState × List Func) (raw : List Char) : Option (PState × List Func) :=
  let (s, done) := st
  let cs := cleanLine raw
  if cs.isEmpty then some st else
  match s with
  | .outside =>
    if ['f', 'u', 'n', 'c', 't', 'i', 'o', 'n', ' '].isPrefixOf cs ∧ cs.getLast? = some '{' then
      let name := trimC ((cs.drop 9).dropLast)
      if isIdent (String.ofList name) then some (.func (String.ofList name) [], done) else none
    else if ['d', 'a', 't', 'a', ' '].isPrefixOf cs ∧ cs.getLast? = some '{' then some (.data, done)
    else none
  | .data => if cs = ['}'] then some (.outside, done) else some st
  | .func name blocks =>
    if cs = ['}'] then some (.outside, done ++ [closeFunc name blocks])
    else if cs.getLast? = some ':' then
      let l := String.ofList cs.dropLast
      if isIdent l then some (.func name ((l, []) :: blocks), done) else none
    else
      match blocks with
      | [] => none
      | (l, is) :: rest => (parseInst cs).map fun i => (.func name ((l, i :: is) :: rest), done)

/-- **Parse Venom text** into its functions (`none` on a syntax error or an unclosed function). -/
@[expose] def parseFuncs (text : String) : Option (List Func) := do
  let (s, fs) ← (splitC '\n' text.toList).foldlM parseLine (PState.outside, [])
  match s with
  | .outside => pure fs
  | _ => none

/-- Parse text holding exactly one function. -/
@[expose] def parseFunc? (text : String) : Option Func :=
  match parseFuncs text with
  | some [f] => some f
  | _ => none

end EvmYul.Venom.Text
