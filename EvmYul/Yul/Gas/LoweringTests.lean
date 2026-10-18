module

public import EvmYul.EVM.Gas.NestedTestHarness
public meta import EvmYul.EVM.Gas.NestedTestHarness
public import EvmYul.Yul.Gas.Functions.OracleTestHarness
public meta import EvmYul.Yul.Gas.Functions.OracleTestHarness
@[expose] public meta section

/-!
# What the Yul model's control-flow prices mean in EVM gas (the 11-gas branch, the 21-gas call)

The Yul cost model prices a conditional branch at `cancun.branch = G_high + G_jumpdest = 11` and a
user-function call at `cancunFn.call = G_verylow + 2 (G_mid + G_jumpdest) = 21`. These numbers stand
for EVM code that a compiler emits, so no check inside the Yul semantics can confirm them. This file
checks everything about them that **can** be checked here, by assembling the standard lowerings of
`if`, `for` and a function call into EVM bytecode and **executing it on this project's EVM
semantics** (`Θ`, the message-call frame), measuring the gas actually charged.

1. **Where the constants come from.** Executing `JUMPI` (not taken) followed by `JUMPDEST` costs
   exactly `cancun.branch`; executing `PUSH ret; JUMP; JUMPDEST; JUMP; JUMPDEST` costs exactly
   `cancunFn.call`. So the constants are the EVM prices of those instruction sequences, and they
   are not hand-typed numbers.
2. **What a real lowering costs (golden values, both branch directions).** The canonical `if`
   lowering `ISZERO; PUSH tag; JUMPI; …; tag: JUMPDEST` adds **17** gas; with the `ISZERO` folded
   away (negated conditions) it adds **14**; a `for` iteration adds **29** gas of control flow
   (plus 9 gas of operand pushes/dups the model never prices); a nullary call adds **24**, and a
   unary call with a result adds **27** (the extra `PUSH` of the function label and a `SWAP1`).
3. **The law that relates them**: every price of the model is **at most** the measured overhead of
   every lowering here, and strictly below it. The Yul model is a *floor* on compiled control flow,
   the same way `cancun_prim_le_C'` makes it a floor on builtins. Consequently the Yul bounds
   (`gasS`, `gasLS`, `gasF`) bound the *model's* gas, and they are **not** upper bounds on the gas
   of compiled code: operand traffic (`PUSH`/`DUP`/`SWAP`) is unpriced, and branches and calls are
   underpriced by 3–18 gas each **on these templates**. On real solc output the smallest `if` gap
   is 2 (the optimized skip path, 13 gas), and an inlined call costs 0, so neither the "gap ≥ 3"
   of `floorHolds` nor the floor itself holds for every compiler setting; see
   `EvmYul/Solc/MatrixTests.lean` (§2 R3, §3 L3) and `runF_costMono` / `inlining_breaks_floor`.
4. **Calibration keeps every guarantee.** All Yul theorems are generic in the cost model. A model
   whose `branch` and `call` prices are *read off the measurements above* (`measuredFn`) is checked
   with the same bound law (`runF ≤ gasF`) and the same second-route oracle as `cancunFn`, so a user
   who calibrates prices against their compiler keeps both.

*Which* lowering a particular solc version and optimizer setting emits is measured on real
compiler output in `EvmYul/Solc/MatrixTests.lean` (pinned solc 0.8.13 … 0.8.37, optimizer off/on);
`docs/CONJECTURES.md` K13–K15 record the results.
-/

namespace EvmYul.Yul.GasTests.LoweringTests

open Plausible EVM EVM.NestedTests Ast Relational Gas CompleteTests
open EvmYul.Testing.EvmFixtures
  OracleTests

/-! ## A two-pass assembler with labels -/

/-- An assembly item. -/
inductive Asm where
  /-- A one-byte instruction. -/
  | op (b : UInt8)
  /-- `PUSH32 v` (the full 256-bit value). -/
  | push32 (v : ℕ)
  /-- `PUSH1 v`, `v < 256`. -/
  | push1 (v : ℕ)
  /-- `PUSH1 label` (the program is shorter than 256 bytes). -/
  | pushLabel (l : String)
  /-- A `JUMPDEST` with a label. -/
  | label (l : String)

/-- Opcodes used below. -/
def STOP : UInt8 := 0x00
def ADD : UInt8 := 0x01
def LT : UInt8 := 0x10
def ISZERO : UInt8 := 0x15
def POP : UInt8 := 0x50
def JUMP : UInt8 := 0x56
def JUMPI : UInt8 := 0x57
def JUMPDEST : UInt8 := 0x5b
def DUP2 : UInt8 := 0x81
def SWAP1 : UInt8 := 0x90

/-- Size in bytes. -/
def Asm.size : Asm → ℕ
  | .op _ | .label _ => 1
  | .push1 _ | .pushLabel _ => 2
  | .push32 _ => 33

/-- Offsets of the labels. -/
def labels (xs : List Asm) : List (String × ℕ) :=
  (xs.foldl (fun (acc, off) x =>
    match x with
    | .label l => ((l, off) :: acc, off + x.size)
    | _ => (acc, off + x.size)) ([], 0)).1

/-- Assemble to bytecode. -/
def assemble (xs : List Asm) : ByteArray :=
  let ls := labels xs
  ⟨(xs.map fun x => match x with
    | .op b => #[b]
    | .push1 v => #[0x60, v.toUInt8]
    | .pushLabel l => #[0x60, ((ls.lookup l).getD 0).toUInt8]
    | .label _ => #[JUMPDEST]
    | .push32 v => #[0x7f] ++ ((List.range 32).reverse.map fun i => (v / 256 ^ i % 256).toUInt8).toArray
    ).toArray.flatten⟩

/-! ## Measuring gas on the EVM semantics -/

/-- Gas given to each measured frame. -/
def budget : ℕ := 1000000

/-- Gas charged by `Θ` for running `xs` (which must end in `STOP`); `none` if the frame fails. -/
def gasUsed (xs : List Asm) : Option ℕ :=
  (θGasLeft? (assemble xs) budget).map (budget - ·)

/-- `n` copies of `JUMPDEST` (1 gas each): a body of known cost. -/
def bodyOf (n : ℕ) : List Asm := List.replicate n (.op JUMPDEST)

/-- The overhead of a lowering: gas of the template minus gas of the same straight-line work
(condition, and the body when it runs). -/
def overhead (template baseline : List Asm) : Option ℕ := do
  let t ← gasUsed template
  let b ← gasUsed baseline
  if b ≤ t then pure (t - b) else none

/-- `if c { body }`, canonical: `c; ISZERO; PUSH end; JUMPI; body; end: JUMPDEST`. -/
def ifCanon (c : ℕ) (k : ℕ) : List Asm :=
  [.push32 c, .op ISZERO, .pushLabel "end", .op JUMPI] ++ bodyOf k ++ [.label "end", .op STOP]

/-- `if` with the negation folded into the condition: `c'; PUSH end; JUMPI; body; end:`. The body
runs when `c' = 0`. -/
def ifInv (c' : ℕ) (k : ℕ) : List Asm :=
  [.push32 c', .pushLabel "end", .op JUMPI] ++ bodyOf k ++ [.label "end", .op STOP]

/-- The straight-line work of an `if` whose body runs (`taken`) or not. -/
def ifBase (c : ℕ) (k : ℕ) (taken : Bool) : List Asm :=
  [.push32 c] ++ (if taken then bodyOf k else []) ++ [.op STOP]

/-- Overhead of the canonical `if` on condition `c`, body of cost `k`. -/
def ifCanonOverhead (c k : ℕ) : Option ℕ := overhead (ifCanon c k) (ifBase c k (c % 2 ^ 256 ≠ 0))

/-- Overhead of the folded `if` on condition `c'`, body of cost `k`. -/
def ifInvOverhead (c' k : ℕ) : Option ℕ := overhead (ifInv c' k) (ifBase c' k (c' % 2 ^ 256 = 0))

/-- `for { } lt(i, k) { i := add(i, 1) } { }` with `i` on the stack, as solc lays it out. -/
def forLoop (k : ℕ) : List Asm :=
  [.push1 0, .label "loop", .push1 k, .op DUP2, .op LT, .op ISZERO, .pushLabel "end", .op JUMPI,
   .label "post", .push1 1, .op ADD, .pushLabel "loop", .op JUMP, .label "end", .op STOP]

/-- EVM gas of one more iteration of `forLoop` (difference of two trip counts). -/
def forIterGas : Option ℕ := do
  let a ← gasUsed (forLoop 5)
  let b ← gasUsed (forLoop 4)
  pure (a - b)

/-- The part of one iteration that is operand traffic the Yul model never prices:
`PUSH1 k; DUP2; PUSH1 1`, measured after a preamble `PUSH1 0` (the loop variable) that is
subtracted again. -/
def forOperandGas : Option ℕ := do
  let a ← gasUsed [.push1 0, .push1 5, .op DUP2, .push1 1, .op STOP]
  let p ← gasUsed [.push1 0, .op STOP]
  pure (a - p)

/-- Nullary call: `PUSH ret; PUSH f; JUMP; ret: JUMPDEST; STOP; f: JUMPDEST; JUMP`. -/
def call0 : List Asm :=
  [.pushLabel "ret", .pushLabel "f", .op JUMP, .label "ret", .op STOP, .label "f", .op JUMP]

/-- Unary call with a result, `inc(x)`: `PUSH ret; PUSH x; PUSH f; JUMP; ret: JUMPDEST; STOP;
f: JUMPDEST; PUSH1 1; ADD; SWAP1; JUMP`. -/
def call1 (x : ℕ) : List Asm :=
  [.pushLabel "ret", .push1 x, .pushLabel "f", .op JUMP, .label "ret", .op STOP,
   .label "f", .push1 1, .op ADD, .op SWAP1, .op JUMP]

/-- The work of `inc(x)` that is not call overhead: `PUSH1 x; PUSH1 1; ADD`. -/
def call1Base (x : ℕ) : List Asm := [.push1 x, .push1 1, .op ADD, .op STOP]

/-! ## 1. Where the constants come from -/

/-- EVM gas of `JUMPI` (not taken) then `JUMPDEST`, isolated by difference. -/
def jumpiJumpdestGas : Option ℕ :=
  overhead [.push1 0, .pushLabel "d", .op JUMPI, .label "d", .op STOP] [.push1 0, .push1 0, .op STOP]

/-- EVM gas of `PUSH ret; JUMP; JUMPDEST; JUMP; JUMPDEST`: the nullary call without the `PUSH` of
the function label (`call0` minus one `PUSH1`). -/
def callCoreGas : Option ℕ := do
  let a ← gasUsed call0
  let p ← gasUsed [.push1 0, .op STOP]
  pure (a - p)

/-! ## The calibrated model -/

/-- A cost model whose control-flow prices are read off the measurements (canonical `if`, unary
call). It is still a floor for loops and for calls of higher arity; its role is to show that the
guarantees hold for whatever prices a user calibrates. -/
def measuredFn : FnCostModel :=
  { cancunFn with branch := (ifCanonOverhead 1 0).getD 0,
                  call := (overhead (call1 7) (call1Base 7)).getD 0 }

/-! ## 2–4. Checks -/

/-- Named unit checks; each must evaluate to `true`. -/
def unitChecks : List (String × Bool) :=
  [ ("assembler: PUSH32 encodes 2^256 - 1 as 32 bytes 0xff",
      (assemble [.push32 (2 ^ 256 - 1)]).toList == 0x7f :: List.replicate 32 0xff),
    ("assembler: labels resolve to their JUMPDEST offsets",
      labels call0 == [("f", 7), ("ret", 5)]),
    ("measured: JUMPI (not taken) + JUMPDEST = 11 = cancun.branch",
      jumpiJumpdestGas == some 11 && cancun.branch == 11),
    ("measured: PUSH + JUMP + JUMPDEST + JUMP + JUMPDEST = 21 = cancunFn.call",
      callCoreGas == some 21 && cancunFn.call == 21),
    ("golden: canonical if adds 17 (taken)", ifCanonOverhead 1 4 == some 17),
    ("golden: canonical if adds 17 (not taken)", ifCanonOverhead 0 4 == some 17),
    ("golden: folded if adds 14 (both directions)",
      ifInvOverhead 0 4 == some 14 && ifInvOverhead 1 4 == some 14),
    ("golden: a for iteration costs 44 on the EVM", forIterGas == some 44),
    ("golden: of which 9 are operand pushes/dups the model never prices", forOperandGas == some 9),
    ("golden: nullary call adds 24", gasUsed call0 == some 24),
    ("golden: unary call with result adds 27", overhead (call1 7) (call1Base 7) == some 27),
    ("the Yul meter charges 17 per iteration of the same loop (branch 11 + LT 3 + ADD 3)",
      let p (k : ℕ) := withInit [.For (call .LT [.Var (vr 1), lit k])
        [.Let [vr 1] (some (call .ADD [.Var (vr 1), lit 1]))] []]
      match mObsF 6 1 (p 5), mObsF 6 1 (p 4) with
      | some (_, a), some (_, b) => a - b == 17
      | _, _ => false),
    ("the calibrated model reads 17 and 27 off the measurements",
      measuredFn.branch == 17 && measuredFn.call == 27)
  ]

/-- The control-flow overheads the model's two prices stand for, with the model price. -/
def floorTable : List (String × ℕ × Option ℕ) :=
  [("if (canonical, taken)", cancun.branch, ifCanonOverhead 1 4),
   ("if (canonical, not taken)", cancun.branch, ifCanonOverhead 0 4),
   ("if (folded ISZERO)", cancun.branch, ifInvOverhead 0 4),
   ("for iteration (control flow only)", cancun.branch,
     do let i ← forIterGas; let o ← forOperandGas; pure (i - o - 6)),
   ("call, nullary", cancunFn.call, gasUsed call0),
   ("call, unary with result", cancunFn.call, overhead (call1 7) (call1Base 7))]

/-- `price ≤ measured` with a gap of at least 3 (the model is a strict floor). -/
def floorHolds (price : ℕ) (measured : Option ℕ) : Bool :=
  measured.any fun m => price + 3 ≤ m

/-- Run every check; throws on the first failure. -/
def runAll : IO Unit := do
  for (name, ok) in unitChecks do
    unless ok do throw <| IO.userError s!"unit check failed: {name}"
  IO.println s!"{unitChecks.length} lowering unit checks passed"
  -- 3. The floor law, on every template.
  let mut rows := #[]
  for (name, price, m) in floorTable do
    unless floorHolds price m do
      throw <| IO.userError s!"floor law violated: {name}: model {price}, measured {m}"
    rows := rows.push s!"{name}: model {price}, EVM {m.getD 0} (gap {m.getD 0 - price})"
  IO.println s!"K13 lowering floor: {String.intercalate "; " rows.toList}"
  -- Canary: the floor check can fail (a price at the measured overhead is rejected).
  unless !floorHolds 17 (ifCanonOverhead 1 4) && !floorHolds 24 (gasUsed call0) do
    throw <| IO.userError "floor canary: a price equal to the overhead was accepted"
  -- 2. The overhead does not depend on the condition value or the body (exhaustive grid with
  --    boundary values, then random 256-bit conditions).
  let conds := [0, 1, 2, 255, 256, 2 ^ 128, 2 ^ 255, 2 ^ 256 - 1]
  let mut taken := 0
  let mut skipped := 0
  for c in conds do
    for k in List.range 12 do
      unless ifCanonOverhead c k == some 17 ∧ ifInvOverhead c k == some 14 do
        throw <| IO.userError s!"if overhead depends on c = {c}, body = {k}"
      if c = 0 then skipped := skipped + 1 else taken := taken + 1
  IO.println s!"if-overhead grid: {conds.length * 12} templates ({taken} with the body taken, \
    {skipped} skipped), canonical 17 and folded 14 in every case"
  expectHolds "if overhead is 17 (canonical) and 14 (folded) for every 256-bit condition"
    (∀ c : UInt256, ∀ k : ℕ,
      ifCanonOverhead c.toNat (k % 16) = some 17 ∧ ifInvOverhead c.toNat (k % 16) = some 14)
  -- 4. Calibration keeps the guarantees: the bound law and the second-route oracle for
  --    `measuredFn`.
  yHolds "calibrated model: every metered run costs at most gasF"
    (∀ init ns : List ℕ,
      CountedTesting.WhenSome ((runF measuredFn (some codeT) 8 7 (genFProg false init ns) sF).map
        (·.2)) fun g => g ≤ gasF measuredFn tblT 8 7 (genFProg false init ns))
  yHolds "calibrated model: runF gas = the self-counting program's counter"
    (∀ init ns : List ℕ,
      CountedTesting.WhenSome (oracle measuredFn true (oFuel ns) (genFProg false init ns)) fun o =>
        meter measuredFn (genFProg false init ns) == some o)
  -- Canary: the Cancun meter does not match the calibrated oracle (the prices really differ).
  yRefuted "canary: cancunFn gas = the calibrated oracle's counter"
    (∀ init ns : List ℕ,
      CountedTesting.WhenSome (oracle measuredFn true (oFuel ns) (genFProg false init ns)) fun o =>
        meter cancunFn (genFProg false init ns) == some o)

#eval runAll

end EvmYul.Yul.GasTests.LoweringTests
