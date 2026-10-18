module

public import EvmYul.Vyper.Harness
public import EvmYul.Yul.Gas.CostMono
public import EvmYul.Solc.Fixture

public section

/-!
# Running solc output on the EVM, and its Yul source on the Yul model (solc matrix harness)

`docs/SOLC_VYPER_PLAN.md`, Step 3. A cell of `EvmYul/Solc/Fixtures.lean` is the bytecode solc
emitted for a corpus program; `EvmYul/Solc/Corpus.lean` is the *same source text* elaborated by the
project's Yul parser. This module runs both sides:

* **EVM side.** The bytecode runs on the project's message-call semantics `Θ` (through the V1
  harness `Vyper.execute`), with calldata = the 32-byte words of the arguments and empty storage.
* **Yul side.** The parsed program runs on the project's Yul interpreter `exec` (for its storage
  effect) and on the Yul gas meter `runF cancunFn` (for the model's gas), from a state whose
  calldata is the same bytes.

Proof obligations discharged here:

* `wordsData_size`: the calldata of `k` words is `32 k` bytes;
* `opcodes_length_le`: the disassembler never invents instructions (used by the classifier);
* `storageRemainder` is defined from the **specified** price of a fresh nonzero `SSTORE`
  (`sstoreFreshSpec = G_coldsload + G_sset`, EIP-2929 + EIP-2200), and `remainder_sound` relates it
  to the model's `SSTORE` floor. It used to be defined from the price measured on `Θ`
  (`sstoreFreshGas?`), which made every expected value depending on it follow `Θ`: a mispriced
  `SSTORE` would have shifted the expectation along with the result. The measurement is now a
  *check* (`MatrixTests` §3: `sstoreFreshGas? = some sstoreFreshSpec`), not a definition.

The gap reported by the tests is `compiled gas − storage remainder − model gas`. The storage
remainder is the part of `SSTORE`'s price that the model leaves to the EVM layer
(`cancun_prim_le_C'`): every corpus program writes each of slots 0 and 1 at most once, from empty
storage, and only nonzero values (`tools/solc/corpus`, documented there), so the remainder is
`(number of nonzero slots) × (fresh nonzero SSTORE − model SSTORE price)`.
-/

namespace EvmYul.Solc

open EvmYul.Vyper (execute Run ofHex? hexOf)
open EvmYul.Yul Ast Gas EVM

/-! ## EVM side -/

/-- Calldata: the 32-byte big-endian words of `args`, no selector (the corpus reads raw words). -/
def wordsData (args : List ℕ) : ByteArray := ⟨(args.flatMap Vyper.word).toArray⟩

theorem wordsData_size (args : List ℕ) : (wordsData args).size = 32 * args.length := by
  simp only [wordsData, ByteArray.size, List.size_toArray]
  induction args with
  | nil => rfl
  | cons a as ih => simp [List.flatMap_cons, Vyper.word_length, ih, Nat.mul_succ, Nat.add_comm]

/-- The bytecode of a cell (`none` if the hex is malformed). -/
def Cell.code? (c : Cell) : Option ByteArray := ofHex? c.runtimeHex

/-- Run `code` on `Θ` with calldata `args`, empty storage, no value. -/
def runCode (code : ByteArray) (args : List ℕ) : Option Run := execute code [] (wordsData args)

/-- Run a cell on `Θ`. -/
def Cell.run? (c : Cell) (args : List ℕ) : Option Run := do runCode (← c.code?) args

/-- Gas `Θ` charges for one `SSTORE` of a nonzero value into a fresh (cold, empty) slot, measured
by running `PUSH1 1; PUSH0; SSTORE; STOP` and subtracting the two pushes (`G_verylow + G_base`). -/
def sstoreFreshGas? : Option ℕ :=
  (runCode ⟨#[0x60, 0x01, 0x5f, 0x55, 0x00]⟩ []).bind fun r =>
    if r.ok && 5 ≤ r.gasUsed then some (r.gasUsed - 5) else none

/-- The specified price of one `SSTORE` of a nonzero value into a cold, empty slot: the EIP-2929
cold-access surcharge plus EIP-2200's `G_sset`. -/
def sstoreFreshSpec : ℕ := GasConstants.Gcoldsload + GasConstants.Gsset

/-- The model's price for `SSTORE` (the state-independent floor of its fee group). -/
def modelSstore : ℕ := cancunFn.prim (.StackMemFlow .SSTORE)

/-- The part of a fresh nonzero `SSTORE` the model leaves to the EVM layer. -/
def sstoreRemainder : ℕ := sstoreFreshSpec - modelSstore

/-- Storage remainder of a run: one `sstoreRemainder` per nonzero slot among `0, 1`. -/
def storageRemainder (r : Run) : ℕ :=
  ((([0, 1] : List ℕ).filter fun k => r.slot k ≠ 0).length) * sstoreRemainder

/-- The specified price is at least the model's price (an instance of `cancun_prim_le_C'`), so the
remainder loses nothing: `modelSstore + sstoreRemainder = sstoreFreshSpec`. -/
theorem remainder_sound (hle : modelSstore ≤ sstoreFreshSpec) :
    modelSstore + sstoreRemainder = sstoreFreshSpec := by
  simp only [sstoreRemainder]; omega

/-! ## Disassembly and classification -/

/-- The instruction bytes of `code`, with `PUSH` immediates skipped (`fuel` bounds the walk). -/
def opcodesAux : ℕ → List UInt8 → List UInt8
  | 0, _ => []
  | _, [] => []
  | fuel + 1, b :: rest =>
    if 0x60 ≤ b.toNat ∧ b.toNat ≤ 0x7f then b :: opcodesAux fuel (rest.drop (b.toNat - 0x5f))
    else b :: opcodesAux fuel rest

/-- The instruction bytes of `code`. -/
def opcodes (code : ByteArray) : List UInt8 := opcodesAux code.size code.toList

theorem opcodesAux_length_le : ∀ (fuel : ℕ) (bs : List UInt8), (opcodesAux fuel bs).length ≤ bs.length
  | 0, _ => by simp [opcodesAux]
  | _ + 1, [] => by simp [opcodesAux]
  | fuel + 1, b :: rest => by
    simp only [opcodesAux]
    split
    · have := opcodesAux_length_le fuel (rest.drop (b.toNat - 0x5f))
      simp only [List.length_cons, List.length_drop] at this ⊢; omega
    · have := opcodesAux_length_le fuel rest
      simp only [List.length_cons]; omega

theorem opcodes_length_le (code : ByteArray) : (opcodes code).length ≤ code.toList.length :=
  opcodesAux_length_le code.size code.toList

/-- How many times instruction `op` occurs. -/
def countOp (code : ByteArray) (op : UInt8) : ℕ := ((opcodes code).filter (· == op)).length

/-- `JUMP`, `JUMPI`, `ISZERO`, `STOP`. -/
def opJUMP : UInt8 := 0x56
def opJUMPI : UInt8 := 0x57
def opISZERO : UInt8 := 0x15
def opSTOP : UInt8 := 0x00

@[expose] section

/-- The lowering families of the `if` statement observed in `docs/SOLC_VYPER_PLAN.md` R1/R2. -/
inductive IfFamily where
  /-- Body inline, condition negated with `ISZERO` before the `JUMPI` (solc ≤ 0.8.20, no
  optimizer). -/
  | inlineNegated
  /-- Body placed out of line and jumped back from (solc ≥ 0.8.21, no optimizer). -/
  | outOfLine
  /-- No negation and no unconditional jump: the optimizer duplicated the `STOP` (every optimized
  cell, and the SSA-CFG generator). -/
  | duplicatedStop
  deriving DecidableEq, Repr

end

/-- Classify the `if` lowering of a compiled `if_store`; `none` for an unknown shape (which fails
the build: a new compiler form must be looked at, not silently accepted). -/
def classifyIf (code : ByteArray) : Option IfFamily :=
  let jumpi := countOp code opJUMPI
  let jump := countOp code opJUMP
  let isz := countOp code opISZERO
  let stops := countOp code opSTOP
  if jumpi ≠ 1 then none
  else if isz = 1 ∧ jump = 0 then some .inlineNegated
  else if isz = 0 ∧ jump = 1 then some .outOfLine
  else if isz = 0 ∧ jump = 0 ∧ 2 ≤ stops then some .duplicatedStop
  else none

/-- Does any unconditional jump survive (a user-function call needs one to return)? -/
def callSurvives (code : ByteArray) : Bool := countOp code opJUMP > 0

/-! ## Yul side -/

/-- The Yul start state: the code owner (address `default`) has an account, calldata = `args`, and
the frame may write state (`perm`, as in the EVM frame of `Vyper.execute`). -/
def yulStart (args : List ℕ) : Yul.State :=
  let base : SharedState .Yul :=
    { (default : SharedState .Yul) with
      accountMap := Std.TreeMap.insert ∅ (default : AccountAddress) default }
  .Ok { base with executionEnv := { base.executionEnv with calldata := wordsData args, perm := true } } ∅

/-- Storage slot `k` of the code owner in a Yul state (`none` if the state is not `Ok`). -/
def yulSlot (s : Yul.State) (k : ℕ) : Option ℕ :=
  match s with
  | .Ok ss _ =>
    match ss.accountMap.get? (default : AccountAddress) with
    | some a => some (a.storage.getD (.ofNat k) ⟨0⟩).toNat
    | none => some 0
  | _ => none

/-- Slots `0, 1` after running the program on the Yul interpreter with `fuel` (`none` on any
error, including running out of fuel). -/
def yulSlots (p : YulContract) (fuel : ℕ) (args : List ℕ) : Option (List ℕ) :=
  match exec fuel p.dispatcher (some p) (yulStart args) with
  | .ok s => do pure [← yulSlot s 0, ← yulSlot s 1]
  | .error _ => none

/-- The Yul model's run with cost model `c`, iteration budget `n` and call-depth budget `d`: slots
`0, 1` after the run, and the gas. -/
def modelRun (c : FnCostModel) (p : YulContract) (n d : ℕ) (args : List ℕ) :
    Option (List ℕ × ℕ) := do
  let (r, g) ← runF c (some p) n d p.dispatcher (yulStart args)
  match r with
  | .ok s => pure ([← yulSlot s 0, ← yulSlot s 1], g)
  | .error _ => none

/-- Budgets large enough for every sweep point (`runF_mono`: more budget, same answer). -/
def bigN : ℕ := 64
def bigD : ℕ := 64

/-- The model's gas (Cancun prices) on the corpus program. -/
def modelGas? (p : YulContract) (args : List ℕ) : Option ℕ :=
  (modelRun cancunFn p bigN bigD args).map (·.2)

/-- The gap: compiled gas minus the storage remainder minus the model's gas (as an integer; a
negative gap means the compiled code is cheaper than the model). -/
def gap? (c : Cell) (p : YulContract) (args : List ℕ) : Option ℤ := do
  let r ← c.run? args
  let m ← modelGas? p args
  if r.ok then pure ((r.gasUsed : ℤ) - storageRemainder r - m) else none

end EvmYul.Solc
