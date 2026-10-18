module

public import EvmYul.Venom.LoweringCheck
public meta import EvmYul.Venom.LoweringCheck

@[expose] public meta section

/-!
# Test harness of `LoweringCheckTests`

The definitions that `LoweringCheckTests.lean` runs and that other test files reuse (the `Θ` tests
of stack code in `ThetaTests.lean`, the gas tests): the state-dependent test machine, the fixture
programs and their hand-written schedules, the random program decoder and the untrusted
schedulers (`lowerWith`, `pad`). `GUIDELINES.md` Rule 3 keeps shared fixtures in a harness module
(layout check L10). Every declaration keeps its name and namespace.
-/

namespace EvmYul.Venom.LoweringCheckTests

open EvmYul.Venom GasConstants

/-! ## Test machine and fixtures -/

/-- The last value written to key `k` in a log of `[key, value]` pairs (`0` if none). -/
def lookupLog (log : List UInt256) (k : UInt256) : UInt256 :=
  let rec go : List UInt256 → UInt256 → UInt256
    | key :: v :: rest, acc => go rest (if key = k then v else acc)
    | _, acc => acc
  go log (word 0)

/-- A test machine over a write log. Its effects and costs depend on the state, so a lowering that
reorders or drops an effect is visible in the result. -/
def testPrims : Prims (List UInt256) where
  apply e s vs := match e with
    | .callvalue => (word 7, s)
    | .calldatasize => (word s.length, s)
    | .calldataload => (word ((vs.getD 0 (word 0)).toNat * 3 + 1), s)
    | .sload => (lookupLog s (vs.getD 0 (word 0)), s)
    | .mload => (word (s.length + (vs.getD 0 (word 0)).toNat), s)
    | .sstore => (word 0, s ++ [vs.getD 0 (word 0), vs.getD 1 (word 0)])
    | .mstore => (word 0, s ++ [vs.getD 1 (word 0), vs.getD 1 (word 0)])
  cost _ s vs := 100 + s.length + vs.length
  haltCost _ s _ := 7 + s.length

/-- Primitive effects that do nothing and cost nothing (for kernel-decided checks). -/
def unitPrims : Prims Unit := ⟨fun _ _ _ => (word 0, ()), fun _ _ _ => 0, fun _ _ _ => 0⟩

/-- Outcome, data and state of a stack-code run and of a Venom run agree (test machine). -/
def sameObs (p : Program) (c : List SAsm) : Bool :=
  decide ((runSAsm testPrims c [] [] 0).map Final.obs = (run testPrims p Store.empty [] 0).map Final.obs)

/-- The compiled code of a program, embedded in `SAsm`. -/
def compiledS (p : Program) : Option (List SAsm) := (compile p).map (·.map Asm.toSAsm)

/-! ## Fixture programs and their schedules -/

/-- Literal operand. -/
def L (n : ℕ) : Operand := .lit (word n)

/-- `%0 = calldataload 0; %1 = calldataload 32; %2 = sub %0, %1; sstore 0, %2; return %2, %1`. -/
def subProg : Program :=
  [.eff (some 0) .calldataload [L 0], .eff (some 1) .calldataload [L 32],
   .pure 2 .sub [.var 0, .var 1], .eff none .sstore [L 0, .var 2],
   .halt .ret [.var 2, .var 1]]

/-- `subProg` scheduled with `SWAP1`: `%0` and `%1` are loaded in list order, then swapped. -/
def subSwapped : List SAsm :=
  [.push (word 0), .eff .calldataload, .push (word 32), .eff .calldataload,
   .dup 2, .dup 2, .swap 1, .op .sub,
   .dup 1, .push (word 0), .eff .sstore,
   .dup 2, .dup 2, .halt .ret]

/-- The same code without its `SWAP1`: computes `%1 − %0`. -/
def subUnswapped : List SAsm := subSwapped.filter (· != .swap 1)

/-- `d + 1` variables `%0 … %d`, then `return 0, %0`: loading `%0` needs `DUP(d + 1)` in the
compiler's scheme. -/
def deepProg (d : ℕ) : Program :=
  (List.range (d + 1)).map (fun i => .pure i .add [L i, L 1]) ++ [.halt .ret [L 0, .var 0]]

/-- `deepProg d` scheduled with `POP`: every `%i` with `i ≥ 1` is dead, so it is popped at once. -/
def deepPopped (d : ℕ) : List SAsm :=
  [.push (word 1), .push (word 0), .op .add] ++
    ((List.range d).flatMap fun j => [.push (word 1), .push (word (j + 1)), .op .add, .pop]) ++
    [.dup 1, .push (word 0), .halt .ret]

/-! ## Random programs and schedulers -/

/-- The 14 pure operations. -/
def pureOps : List PureOp :=
  [.add, .sub, .mul, .div, .mod, .and, .or, .xor, .shl, .shr, .lt, .gt, .eq, .iszero]

/-- A boundary-biased literal. -/
def mkLit (b : ℕ) : UInt256 :=
  match b % 6 with
  | 0 => word 0
  | 1 => word 1
  | 2 => word (2 ^ 256 - 1)
  | 3 => word (2 ^ 255)
  | 4 => word 255
  | _ => word b

/-- An operand: a literal, or one of the variables defined so far. -/
def mkOperand (defs : List ℕ) (a b : ℕ) : Operand :=
  if a % 3 = 0 ∨ defs.isEmpty then .lit (mkLit b) else .var (defs.getD (a % defs.length) 0)

/-- Decode a random program. Instruction `i` defines `%i`, except that with `redefine` set it may
reuse an earlier variable (not SSA). With `asserts` off there is no `assert`. -/
def decodeProg (xs : List (ℕ × ℕ × ℕ × ℕ)) (t : ℕ) (redefine asserts : Bool) : Program :=
  let step := fun (acc : List Instr × List ℕ) (x : (ℕ × ℕ × ℕ × ℕ) × ℕ) =>
    let ((k, a, b, c), i) := x
    let (is, defs) := acc
    let dst := if redefine ∧ c % 3 = 0 ∧ !defs.isEmpty then defs.getD (c % defs.length) 0 else i + 1000
    let defs' := if defs.contains dst then defs else dst :: defs
    let op₁ := mkOperand defs a b
    let op₂ := mkOperand defs (a / 3 + c) (b + c)
    match k % 8 with
    | 0 | 1 | 2 | 3 =>
      let o := pureOps.getD (b % 14) .add
      (is ++ [.pure dst o (if o.arity = 1 then [op₁] else [op₁, op₂])], defs')
    | 4 => (is ++ [.eff (some dst) .sload [op₁]], defs')
    | 5 => (is ++ [.eff none .sstore [op₁, op₂]], defs)
    | 6 => (is ++ [.eff (some dst) (if c % 2 = 0 then .calldataload else .mload) [op₁]], defs')
    | _ =>
      if asserts then (is ++ [.assert (if c % 4 = 0 then .lit (word 0) else op₁)], defs)
      else (is ++ [.eff (some dst) .callvalue []], defs')
  let (is, defs) := xs.zipIdx.foldl step ([], [])
  let r₁ := mkOperand defs t (t + 1)
  let r₂ := mkOperand defs (t + 2) (t + 3)
  is ++ [match t % 3 with
    | 0 => .halt .stop []
    | 1 => .halt .ret [r₁, r₂]
    | _ => .halt .revert [r₁, r₂]]

/-- Position of variable `v` in layout `L` (top first): the newest copy, or with `oldest` the
oldest copy. -/
def slotOf (oldest : Bool) (L : List ℕ) (v : ℕ) : Option ℕ :=
  if v ∈ L then some (if oldest then L.length - 1 - L.reverse.idxOf v else L.idxOf v) else none

/-- Load one operand with `t` temporaries above the layout. -/
def loadOp (oldest : Bool) (L : List ℕ) (t : ℕ) : Operand → Option SAsm
  | .lit n => some (.push n)
  | .var v => (slotOf oldest L v).bind fun i => if i + t + 1 ≤ 16 then some (.dup (i + t + 1)) else none

/-- Load operands in the given order (the first ends deepest). -/
def loadSeq (oldest : Bool) (L : List ℕ) : ℕ → List Operand → Option (List SAsm)
  | _, [] => some []
  | t, x :: xs => do
    let a ← loadOp oldest L t x
    let r ← loadSeq oldest L (t + 1) xs
    some (a :: r)

/-- Load the operands of an instruction so that operand `i` ends at `μₛ[i]`. With `swapped`, two
operands are loaded in list order and put right with `SWAP1`. -/
def loadArgs (oldest swapped : Bool) (L : List ℕ) (args : List Operand) : Option (List SAsm) :=
  if swapped ∧ args.length = 2 then (loadSeq oldest L 0 args).map (· ++ [.swap 1])
  else loadSeq oldest L 0 args.reverse

/-- An untrusted scheduler (test support): the compiler's scheme, with the choices `oldest`
(load the oldest copy of a variable) and `swapped` (binary operands through `SWAP1`). -/
def lowerWith (oldest swapped : Bool) : List ℕ → Program → Option (List SAsm)
  | _, [] => some [.halt .stop]
  | L, .pure dst o args :: rest => do
    let c ← loadArgs oldest swapped L args
    let r ← lowerWith oldest swapped (dst :: L) rest
    some (c ++ .op o :: r)
  | L, .eff dst e args :: rest => do
    let c ← loadArgs oldest swapped L args
    let r ← lowerWith oldest swapped (match dst with | some d => d :: L | none => L) rest
    some (c ++ .eff e :: r)
  | L, .assert a :: rest => do
    let c ← loadArgs oldest swapped L [a]
    let r ← lowerWith oldest swapped L rest
    some (c ++ .assertJ :: r)
  | L, .halt h args :: _ => do
    let c ← loadArgs oldest swapped L args
    some (c ++ [.halt h])

/-- Insert `PUSH n; POP` before the instructions at the positions in `pos` (mod the code length,
so never after the final terminator). -/
def pad (pos : List ℕ) (c : List SAsm) : List SAsm × ℕ :=
  let n := c.length
  let hits := fun j => (pos.filter fun q => q % max n 1 = j).length
  ((c.zipIdx.flatMap fun (a, j) =>
    (List.replicate (hits j) [SAsm.push (word j), SAsm.pop]).flatten ++ [a]),
   (List.range n).foldl (fun s j => s + hits j) 0)

/-- Gas of a stack-code run and of a Venom run on the test machine. -/
def gasOf (p : Program) (c : List SAsm) : Option ℕ × Option ℕ :=
  ((runSAsm testPrims c [] [] 0).map Final.gas, (run testPrims p Store.empty [] 0).map Final.gas)

end EvmYul.Venom.LoweringCheckTests
