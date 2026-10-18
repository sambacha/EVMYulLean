module

public import EvmYul.Venom.Assemble
public meta import EvmYul.Venom.Assemble
public import EvmYul.Vyper.Fixtures
public meta import EvmYul.Vyper.Fixtures

@[expose] public meta section

/-!
# Test harness of `ThetaTests`

The definitions that `ThetaTests.lean` runs and that other test files reuse (the machine-interface
tests of `EvmMachineTests.lean`, the cross-block tests): the agreement check between `Θ` and the
Venom semantics, the real `store.vy` fragments, and the random program decoders with their
boundary-biased literals, memory offsets and storage pools. `GUIDELINES.md` Rule 3 keeps shared
fixtures in a harness module (layout check L10). Every declaration keeps its name and namespace.
-/

namespace EvmYul.Venom.ThetaTests

open EvmYul.Venom GasConstants

/-! ## The check -/

/-- Storage slot `k` expected after a run: the initial value after a revert, else the model's. -/
def expectedSlot (f : Final Ref) (kvs : List (ℕ × ℕ)) (k : ℕ) : ℕ :=
  if f.outcome = .reverted then (kvs.lookup k).getD 0 % 2 ^ 256 else f.state.storage k

/-- `Θ` on the assembled code `c` agrees with the Venom result of `p` under `P`. -/
def agreesWith (P : Prims Ref) (c : List Asm) (p : Program) (kvs : List (ℕ × ℕ))
    (data : List UInt8) (value : ℕ) : Bool :=
  match run P p Store.empty (Ref.init kvs data value) 0 with
  | none => false
  | some f =>
    match onTheta (assemble c) kvs data value with
    | none => false
    | some r =>
      r.outcome == f.outcome.frame && r.output.toList == f.output &&
        (List.range 8).all (fun k => r.slot k == expectedSlot f kvs k) &&
        r.gasUsed == f.gas

/-- The full check with this compiler and the reference model; a compilation failure fails. -/
def agrees (p : Program) (kvs : List (ℕ × ℕ)) (data : List UInt8) (value : ℕ) : Bool :=
  match compile p with
  | some c => agreesWith refPrims c p kvs data value
  | none => false

/-! ## Real Vyper output: the `store.vy` fragments -/

/-- Literal operand. -/
def L (n : ℕ) : Operand := .lit (word n)

/-- Variable operand. -/
def V (n : ℕ) : Operand := .var n

/-- `%1 = calldataload 0; %2 = shr 224, %1; %d = xor sel, %2; %e = iszero %d; assert %e`: the
selector check of a bucket. -/
def selectorCheck (sel d e : ℕ) : Program :=
  [.eff (some 1) .calldataload [L 0], .pure 2 .shr [L 224, V 1], .pure d .xor [L sel, V 2],
   .pure e .iszero [V d], .assert (V e)]

/-- `selector_bucket_1` of `store.vy` (`set(uint256)`), from `vyper 0.4.3 -f bb_runtime`. -/
def setProg : Program :=
  selectorCheck 0x60fe47b1 42 8 ++
  [.eff (some 10) .calldatasize [], .pure 11 .gt [L 36, V 10], .eff (some 9) .callvalue [],
   .pure 12 .or [V 9, V 11], .pure 13 .iszero [V 12], .assert (V 13),
   .eff (some 15) .calldataload [L 4], .eff none .sstore [L 0, V 15], .halt .stop []]

/-- `6_then` of `store.vy` (`bump(uint256)`), with its `jnz` on the selector as an `assert`. -/
def bumpProg : Program :=
  selectorCheck 0xb20eb4c4 43 44 ++
  [.eff (some 19) .calldatasize [], .pure 20 .gt [L 36, V 19], .eff (some 18) .callvalue [],
   .pure 21 .or [V 18, V 20], .pure 22 .iszero [V 21], .assert (V 22),
   .eff (some 23) .sload [L 0], .eff (some 26) .calldataload [L 4], .pure 28 .add [V 23, V 26],
   .pure 30 .lt [V 28, V 23], .pure 31 .iszero [V 30], .assert (V 31),
   .eff none .sstore [L 0, V 28], .halt .stop []]

/-- The fixture cell `store@0.4.3/venom` (real Vyper output). -/
def storeVenom : Option Vyper.Cell :=
  Vyper.fixtures.find? fun c => c.contract == "store" && c.vyper == "0.4.3" && c.codegen == .venom

/-! ## Random program decoders -/

/-- Boundary literals. -/
def litPool : List ℕ := [0, 1, 2, 31, 32, 255, 256, 2 ^ 128, 2 ^ 255, 2 ^ 256 - 1]

/-- A pseudo-random 256-bit word from a small seed. -/
def mix (x : ℕ) : ℕ :=
  (x + 1) * 0x9E3779B97F4A7C15F39CC0605CEDC8341082276BF3A27251F86C6A11D0C18E95 % 2 ^ 256

/-- A literal from a selector `c` and a seed `x`: boundary or pseudo-random. -/
def mkLit (c x : ℕ) : ℕ := if c % 2 = 0 then litPool.getD (x % litPool.length) 0 else mix x

/-- An operand: a literal, or one of the 8 newest variables (so `DUP` depth stays ≤ 9). -/
def mkOperand (vars : List ℕ) (c x : ℕ) : Operand :=
  if c % 3 = 0 ∨ vars.isEmpty then .lit (word (mkLit c x))
  else .var (vars.getD (x % min 8 vars.length) 0)

/-- A memory offset below 2048: half the time the small seed itself, half the time a pseudo-random
offset. (Plausible's naturals stay below the size bound, here 30, so the seed alone would never
expand memory past 22 words, where the quadratic term `words² / 512` of the memory cost starts to
be non-zero, and a memory cost without that term would go unnoticed.) -/
def memOfs (sel b : ℕ) : ℕ := if sel % 2 = 0 then b % 2048 else mix b % 2048

/-- All pure operations. -/
def pureOps : List PureOp :=
  [.add, .sub, .mul, .div, .mod, .and, .or, .xor, .shl, .shr, .lt, .gt, .eq, .iszero]

/-- Decode random tuples into a well-scoped program (variables `%0, %1, …`), ending with a
terminator chosen by `t`. -/
def decodeProg (xs : List (ℕ × ℕ × ℕ × ℕ)) (t : ℕ) : Program := Id.run do
  let mut vars : List ℕ := []
  let mut next := 0
  let mut out : Program := []
  for (k, a, b, c) in xs do
    let o₁ := mkOperand vars b a
    let o₂ := mkOperand vars c (a + b)
    match k % 10 with
    | 0 | 1 | 2 | 3 =>
      let o := pureOps.getD (a % pureOps.length) .add
      out := out ++ [.pure next o (if o.arity = 1 then [o₁] else [o₁, o₂])]
      vars := next :: vars; next := next + 1
    | 4 =>
      out := out ++ [.eff (some next) .calldataload [L (b % 80)]]
      vars := next :: vars; next := next + 1
    | 5 =>
      out := out ++ [.eff (some next) (if a % 2 = 0 then .callvalue else .calldatasize) []]
      vars := next :: vars; next := next + 1
    | 6 => out := out ++ [.eff none .mstore [L (memOfs c b), o₂]]
    | 7 =>
      out := out ++ [.eff (some next) .mload [L (memOfs c b)]]
      vars := next :: vars; next := next + 1
    | 8 =>
      if a % 2 = 0 then
        out := out ++ [.eff (some next) .sload [L (b % 8)]]
        vars := next :: vars; next := next + 1
      else out := out ++ [.eff none .sstore [L (b % 8), o₂]]
    | _ => out := out ++ [.assert (if c % 5 = 0 then L 0 else o₁)]
  let term : Instr := match t % 3 with
    | 0 => .halt .stop []
    | 1 => .halt .ret [L (t % 512), L (t % 65)]
    | _ => .halt .revert [L (t % 512), L (t % 65)]
  return out ++ [term]

/-- Initial storage from random pairs (slots `0 … 7`), one pair per slot (the first one wins).
Duplicate keys must be removed: the `Θ` harness writes the pairs in order (the last one wins) while
the reference model looks a slot up (the first one wins), so a list with a repeated slot describes
two different initial states. -/
def mkKvs (kv : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  (kv.map fun (k, v) => (k % 8, mix v)).foldl
    (fun acc p => if acc.any (·.1 == p.1) then acc else acc ++ [p]) []

/-- Call data from random numbers. -/
def mkData (cd : List ℕ) : List UInt8 := cd.map fun x => UInt8.ofNat (mix x)

/-- Outcome of a decoded program under the reference model (for the coverage line). -/
def outcomeOf (xs : List (ℕ × ℕ × ℕ × ℕ)) (t : ℕ) : Option Outcome :=
  (run refPrims (decodeProg xs t) Store.empty (Ref.init [] [] 0) 0).map (·.outcome)

/-- A small value pool, so that no-op writes, writes of zero and writes restoring the original
value are frequent. -/
def valPool (x : ℕ) : ℕ := [0, 1, 2, 2 ^ 256 - 1].getD (x % 4) 0

/-- Decode random triples into a storage-heavy program on slots `0 … 2`: `sload` (one in three) or
`sstore` of a pooled value, then `stop`. This drives the EIP-2200 `SSTORE` state machine (clean or
dirty slot, zero or non-zero original, no-op write, restoring the original) much harder than the
general decoder, where two writes to the same slot are rare. -/
def decodeStorageProg (ops : List (ℕ × ℕ × ℕ)) : Program := Id.run do
  let mut out : Program := []
  let mut next := 0
  for (k, slot, v) in ops do
    if k % 3 = 0 then
      out := out ++ [.eff (some next) .sload [L (slot % 3)]]
      next := next + 1
    else out := out ++ [.eff none .sstore [L (slot % 3), L (valPool v)]]
  return out ++ [.halt .stop []]

/-- Initial storage of slots `0 … 2` from the value pool. -/
def mkPoolKvs (a b c : ℕ) : List (ℕ × ℕ) := [(0, valPool a), (1, valPool b), (2, valPool c)]

end EvmYul.Venom.ThetaTests
