module

public import EvmYul.UInt256
public import EvmYul.EVM.Gas.Constants

public section

/-!
# Venom IR: the straight-line fragment (syntax and pure operations)

Venom is the SSA intermediate representation of the Vyper compiler (`vyper -f bb_runtime
--experimental-codegen`). This file defines the **straight-line fragment** of one basic block: SSA
assignments of pure operations, environment and storage/memory effects, `assert`, and the three
halting terminators. Control flow between blocks (`jmp`, `jnz`, `djmp`, `phi`, `invoke`, `ret`) is
not part of the fragment.

Operand order follows Venom's text format, which was checked on real compiler output
(`docs/VENOM_PLAN.md` §3): the `i`-th listed operand is the `i`-th stack item `μₛ[i]` of the EVM
instruction, so `%r = sub %a, %b` is `a − b`, `%r = shr %s, %x` is `x >> s` and `sstore %k, %v`
writes `v` to slot `k`.

The pure operations are defined here on natural numbers, from the Yellow Paper's definitions, and
**not** through the interpreter's `UInt256` functions: the build-time differential tests
(`EvmYul/Venom/ThetaTests.lean`) compare the two routes on random 256-bit operands (D1).
-/

namespace EvmYul.Venom

open GasConstants

@[expose] section

/-- An operand: an SSA variable (`%n`) or a literal. -/
inductive Operand where
  /-- The SSA variable `%v`. -/
  | var (v : ℕ)
  /-- A literal word. -/
  | lit (n : UInt256)
  deriving Repr, DecidableEq, Inhabited

end

@[expose] section

/-- Pure (state-independent) operations of the fragment. -/
inductive PureOp where
  /-- `add a b = a + b mod 2²⁵⁶`. -/
  | add
  /-- `sub a b = a − b mod 2²⁵⁶`. -/
  | sub
  /-- `mul a b = a · b mod 2²⁵⁶`. -/
  | mul
  /-- `div a b = ⌊a / b⌋`, `0` if `b = 0`. -/
  | div
  /-- `mod a b = a mod b`, `0` if `b = 0`. -/
  | mod
  /-- Bitwise and. -/
  | and
  /-- Bitwise or. -/
  | or
  /-- Bitwise xor. -/
  | xor
  /-- `shl s x = x · 2ˢ mod 2²⁵⁶` (`0` if `s ≥ 256`). -/
  | shl
  /-- `shr s x = ⌊x / 2ˢ⌋` (`0` if `s ≥ 256`). -/
  | shr
  /-- `lt a b = [a < b]`. -/
  | lt
  /-- `gt a b = [a > b]`. -/
  | gt
  /-- `eq a b = [a = b]`. -/
  | eq
  /-- `iszero a = [a = 0]`. -/
  | iszero
  deriving Repr, DecidableEq, Inhabited

end

/-- Number of operands of a pure operation. -/
@[expose] def PureOp.arity : PureOp → ℕ
  | .iszero => 1
  | _ => 2

/-- A word from a natural number, reduced mod `2²⁵⁶`. -/
@[expose] def word (n : ℕ) : UInt256 := UInt256.ofNat n

/-- `1` if `b`, else `0`. -/
@[expose] def flag (b : Bool) : UInt256 := if b then word 1 else word 0

/-- The value of a binary operation on `a = μₛ[0]`, `b = μₛ[1]` (Yellow Paper, Appendix H). -/
@[expose] def PureOp.eval₂ (o : PureOp) (a b : ℕ) : UInt256 :=
  match o with
  | .add => word (a + b)
  | .sub => word (a + (2 ^ 256 - b))
  | .mul => word (a * b)
  | .div => if b = 0 then word 0 else word (a / b)
  | .mod => if b = 0 then word 0 else word (a % b)
  | .and => word (a &&& b)
  | .or => word (a ||| b)
  | .xor => word (a ^^^ b)
  | .shl => if a ≥ 256 then word 0 else word (b * 2 ^ a)
  | .shr => if a ≥ 256 then word 0 else word (b / 2 ^ a)
  | .lt => flag (decide (a < b))
  | .gt => flag (decide (a > b))
  | .eq => flag (decide (a = b))
  | .iszero => flag (decide (a = 0))

/-- The value of a pure operation on its operand values (missing operands read as `0`; the
compiler and the semantics both reject an operand list of the wrong length). -/
@[expose] def PureOp.eval (o : PureOp) (args : List UInt256) : UInt256 :=
  o.eval₂ ((args.getD 0 default).toNat) ((args.getD 1 default).toNat)

/-- Static gas of the EVM instruction of a pure operation (Cancun): `W_low` for `mul`, `div`,
`mod`, `W_verylow` for the others. -/
@[expose] def PureOp.gas : PureOp → ℕ
  | .mul | .div | .mod => Glow
  | _ => Gverylow

@[expose] section

/-- Effects: operations that read or write the execution environment, storage or memory. -/
inductive Eff where
  /-- `callvalue` (no operand). -/
  | callvalue
  /-- `calldatasize` (no operand). -/
  | calldatasize
  /-- `calldataload ofs`. -/
  | calldataload
  /-- `sload key`. -/
  | sload
  /-- `mload ofs`. -/
  | mload
  /-- `sstore key val` (no result). -/
  | sstore
  /-- `mstore ofs val` (no result). -/
  | mstore
  deriving Repr, DecidableEq, Inhabited

end

/-- Number of operands of an effect. -/
@[expose] def Eff.arity : Eff → ℕ
  | .callvalue | .calldatasize => 0
  | .calldataload | .sload | .mload => 1
  | .sstore | .mstore => 2

/-- Does the effect produce a value? -/
@[expose] def Eff.produces : Eff → Bool
  | .sstore | .mstore => false
  | _ => true

@[expose] section

/-- Halting terminators. -/
inductive Halt where
  /-- `stop`. -/
  | stop
  /-- `return ofs, len`. -/
  | ret
  /-- `revert ofs, len`. -/
  | revert
  deriving Repr, DecidableEq, Inhabited

end

/-- Number of operands of a terminator. -/
@[expose] def Halt.arity : Halt → ℕ
  | .stop => 0
  | _ => 2

@[expose] section

/-- An instruction of the straight-line fragment. -/
inductive Instr where
  /-- `%dst = o args`. -/
  | pure (dst : ℕ) (o : PureOp) (args : List Operand)
  /-- `%dst = e args` (if `e` produces a value) or `e args`. -/
  | eff (dst : Option ℕ) (e : Eff) (args : List Operand)
  /-- `assert a`: revert with empty data unless `a ≠ 0`. -/
  | assert (a : Operand)
  /-- A terminator. -/
  | halt (h : Halt) (args : List Operand)
  deriving Repr, Inhabited

end

/-- A straight-line program: the instructions of one basic block. Running off the end stops. -/
@[expose] abbrev Program := List Instr

end EvmYul.Venom
