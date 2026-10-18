module

public import EvmYul.EVM.Gas.Classification
public import EvmYul.Yul.Ast

public section

/-!
# Yul gas, part 1: one cost table for both languages (analysis, Approach B, item 1)

The gas analysis (§3.2 S6, §5 Approach B) asks for Yul gas accounting that is charged **from the
same cost table** as the EVM meter, so that the two meters cannot drift apart silently (the S2 class
of bugs: an unclassified builtin that costs nothing).

This file provides that single source of truth:

* `toEVM`: every Yul builtin is the EVM instruction of the same name. The function has **no
  wildcard arm**, so a new Yul builtin does not compile until it is mapped. `ofEVM_toEVM` shows the
  map is injective (no two builtins share a twin).
* `yulFeeGroup op := feeGroup (toEVM op)`: the Yul fee classification **is** the EVM one
  (`GasMeter.feeGroup`), by definition.
* `CostModel`: what the metered Yul semantics (`EvmYul/Yul/Gas/Metered.lean`) charges: a price per
  builtin and a price for a conditional branch (`if`, `switch`).
* `cancun`: the instance read off the Cancun EVM table.
  - `cancun_prim_eq_C'`: for every builtin with a state-independent price, the Yul charge equals the
    EVM charge `C'` of its twin **in every EVM state**.
  - `cancun_prim_le_C'`: for every builtin, the Yul charge is at most the EVM charge of its twin in
    every state. The Yul model never over-charges a builtin; for the dynamically priced ones
    (memory copies, `keccak256`, storage, logs, calls, ...) it charges the state-independent floor
    of the price, and the remainder is the dynamic part the EVM layer adds.

What this does **not** claim: that solc compiles a Yul `if` to exactly one `JUMPI` plus one
`JUMPDEST` (`cancun.branch`). Control-flow costs depend on the compiler (analysis §5, Approach B,
"Cons"); `branch` is a parameter of the model, and every theorem in `Metered.lean` is generic in it.
-/

namespace EvmYul
namespace Yul
namespace Gas

open EVM GasConstants GasMeter Ast

/-- The EVM instruction a Yul builtin stands for. No wildcard arm: every Yul builtin is mapped
explicitly, so a new builtin is a compile error here until it is classified. -/
@[expose] def toEVM : PrimOp → Operation .EVM
  | .StopArith op =>
    match op with
    | .STOP => .StopArith .STOP
    | .ADD => .StopArith .ADD
    | .MUL => .StopArith .MUL
    | .SUB => .StopArith .SUB
    | .DIV => .StopArith .DIV
    | .SDIV => .StopArith .SDIV
    | .MOD => .StopArith .MOD
    | .SMOD => .StopArith .SMOD
    | .ADDMOD => .StopArith .ADDMOD
    | .MULMOD => .StopArith .MULMOD
    | .EXP => .StopArith .EXP
    | .SIGNEXTEND => .StopArith .SIGNEXTEND
  | .CompBit op =>
    match op with
    | .LT => .CompBit .LT
    | .GT => .CompBit .GT
    | .SLT => .CompBit .SLT
    | .SGT => .CompBit .SGT
    | .EQ => .CompBit .EQ
    | .ISZERO => .CompBit .ISZERO
    | .AND => .CompBit .AND
    | .OR => .CompBit .OR
    | .XOR => .CompBit .XOR
    | .NOT => .CompBit .NOT
    | .BYTE => .CompBit .BYTE
    | .SHL => .CompBit .SHL
    | .SHR => .CompBit .SHR
    | .SAR => .CompBit .SAR
  | .Keccak op =>
    match op with
    | .KECCAK256 => .Keccak .KECCAK256
  | .Env op =>
    match op with
    | .ADDRESS => .Env .ADDRESS
    | .BALANCE => .Env .BALANCE
    | .ORIGIN => .Env .ORIGIN
    | .CALLER => .Env .CALLER
    | .CALLVALUE => .Env .CALLVALUE
    | .CALLDATALOAD => .Env .CALLDATALOAD
    | .CALLDATASIZE => .Env .CALLDATASIZE
    | .CALLDATACOPY => .Env .CALLDATACOPY
    | .GASPRICE => .Env .GASPRICE
    | .CODESIZE => .Env .CODESIZE
    | .CODECOPY => .Env .CODECOPY
    | .EXTCODESIZE => .Env .EXTCODESIZE
    | .EXTCODECOPY => .Env .EXTCODECOPY
    | .RETURNDATASIZE => .Env .RETURNDATASIZE
    | .RETURNDATACOPY => .Env .RETURNDATACOPY
    | .EXTCODEHASH => .Env .EXTCODEHASH
  | .Block op =>
    match op with
    | .BLOCKHASH => .Block .BLOCKHASH
    | .COINBASE => .Block .COINBASE
    | .TIMESTAMP => .Block .TIMESTAMP
    | .NUMBER => .Block .NUMBER
    | .PREVRANDAO => .Block .PREVRANDAO
    | .GASLIMIT => .Block .GASLIMIT
    | .CHAINID => .Block .CHAINID
    | .SELFBALANCE => .Block .SELFBALANCE
    | .BASEFEE => .Block .BASEFEE
    | .BLOBHASH => .Block .BLOBHASH
    | .BLOBBASEFEE => .Block .BLOBBASEFEE
  | .StackMemFlow op =>
    match op with
    | .POP => .StackMemFlow .POP
    | .MLOAD => .StackMemFlow .MLOAD
    | .MSTORE => .StackMemFlow .MSTORE
    | .SLOAD => .StackMemFlow .SLOAD
    | .SSTORE => .StackMemFlow .SSTORE
    | .MSTORE8 => .StackMemFlow .MSTORE8
    | .MSIZE => .StackMemFlow .MSIZE
    | .GAS => .StackMemFlow .GAS
    | .TLOAD => .StackMemFlow .TLOAD
    | .TSTORE => .StackMemFlow .TSTORE
    | .MCOPY => .StackMemFlow .MCOPY
  | .Log op =>
    match op with
    | .LOG0 => .Log .LOG0
    | .LOG1 => .Log .LOG1
    | .LOG2 => .Log .LOG2
    | .LOG3 => .Log .LOG3
    | .LOG4 => .Log .LOG4
  | .System op =>
    match op with
    | .CREATE => .System .CREATE
    | .CALL => .System .CALL
    | .CALLCODE => .System .CALLCODE
    | .RETURN => .System .RETURN
    | .DELEGATECALL => .System .DELEGATECALL
    | .CREATE2 => .System .CREATE2
    | .STATICCALL => .System .STATICCALL
    | .REVERT => .System .REVERT
    | .INVALID => .System .INVALID
    | .SELFDESTRUCT => .System .SELFDESTRUCT

/-- Left inverse of `toEVM`: the Yul builtin an EVM instruction stands for, if any (`JUMP`, `PC`,
`PUSH`, `DUP`, `SWAP`, ... have no Yul builtin). -/
@[expose] def ofEVM : Operation .EVM → Option PrimOp
  | .StopArith op =>
    match op with
    | .STOP => some (.StopArith .STOP)
    | .ADD => some (.StopArith .ADD)
    | .MUL => some (.StopArith .MUL)
    | .SUB => some (.StopArith .SUB)
    | .DIV => some (.StopArith .DIV)
    | .SDIV => some (.StopArith .SDIV)
    | .MOD => some (.StopArith .MOD)
    | .SMOD => some (.StopArith .SMOD)
    | .ADDMOD => some (.StopArith .ADDMOD)
    | .MULMOD => some (.StopArith .MULMOD)
    | .EXP => some (.StopArith .EXP)
    | .SIGNEXTEND => some (.StopArith .SIGNEXTEND)
  | .CompBit op =>
    match op with
    | .LT => some (.CompBit .LT)
    | .GT => some (.CompBit .GT)
    | .SLT => some (.CompBit .SLT)
    | .SGT => some (.CompBit .SGT)
    | .EQ => some (.CompBit .EQ)
    | .ISZERO => some (.CompBit .ISZERO)
    | .AND => some (.CompBit .AND)
    | .OR => some (.CompBit .OR)
    | .XOR => some (.CompBit .XOR)
    | .NOT => some (.CompBit .NOT)
    | .BYTE => some (.CompBit .BYTE)
    | .SHL => some (.CompBit .SHL)
    | .SHR => some (.CompBit .SHR)
    | .SAR => some (.CompBit .SAR)
  | .Keccak op =>
    match op with
    | .KECCAK256 => some (.Keccak .KECCAK256)
  | .Env op =>
    match op with
    | .ADDRESS => some (.Env .ADDRESS)
    | .BALANCE => some (.Env .BALANCE)
    | .ORIGIN => some (.Env .ORIGIN)
    | .CALLER => some (.Env .CALLER)
    | .CALLVALUE => some (.Env .CALLVALUE)
    | .CALLDATALOAD => some (.Env .CALLDATALOAD)
    | .CALLDATASIZE => some (.Env .CALLDATASIZE)
    | .CALLDATACOPY => some (.Env .CALLDATACOPY)
    | .GASPRICE => some (.Env .GASPRICE)
    | .CODESIZE => some (.Env .CODESIZE)
    | .CODECOPY => some (.Env .CODECOPY)
    | .EXTCODESIZE => some (.Env .EXTCODESIZE)
    | .EXTCODECOPY => some (.Env .EXTCODECOPY)
    | .RETURNDATASIZE => some (.Env .RETURNDATASIZE)
    | .RETURNDATACOPY => some (.Env .RETURNDATACOPY)
    | .EXTCODEHASH => some (.Env .EXTCODEHASH)
  | .Block op =>
    match op with
    | .BLOCKHASH => some (.Block .BLOCKHASH)
    | .COINBASE => some (.Block .COINBASE)
    | .TIMESTAMP => some (.Block .TIMESTAMP)
    | .NUMBER => some (.Block .NUMBER)
    | .PREVRANDAO => some (.Block .PREVRANDAO)
    | .GASLIMIT => some (.Block .GASLIMIT)
    | .CHAINID => some (.Block .CHAINID)
    | .SELFBALANCE => some (.Block .SELFBALANCE)
    | .BASEFEE => some (.Block .BASEFEE)
    | .BLOBHASH => some (.Block .BLOBHASH)
    | .BLOBBASEFEE => some (.Block .BLOBBASEFEE)
  | .StackMemFlow op =>
    match op with
    | .POP => some (.StackMemFlow .POP)
    | .MLOAD => some (.StackMemFlow .MLOAD)
    | .MSTORE => some (.StackMemFlow .MSTORE)
    | .SLOAD => some (.StackMemFlow .SLOAD)
    | .SSTORE => some (.StackMemFlow .SSTORE)
    | .MSTORE8 => some (.StackMemFlow .MSTORE8)
    | .MSIZE => some (.StackMemFlow .MSIZE)
    | .GAS => some (.StackMemFlow .GAS)
    | .TLOAD => some (.StackMemFlow .TLOAD)
    | .TSTORE => some (.StackMemFlow .TSTORE)
    | .MCOPY => some (.StackMemFlow .MCOPY)
    | .JUMP | .JUMPI | .PC | .JUMPDEST => none
  | .Log op =>
    match op with
    | .LOG0 => some (.Log .LOG0)
    | .LOG1 => some (.Log .LOG1)
    | .LOG2 => some (.Log .LOG2)
    | .LOG3 => some (.Log .LOG3)
    | .LOG4 => some (.Log .LOG4)
  | .System op =>
    match op with
    | .CREATE => some (.System .CREATE)
    | .CALL => some (.System .CALL)
    | .CALLCODE => some (.System .CALLCODE)
    | .RETURN => some (.System .RETURN)
    | .DELEGATECALL => some (.System .DELEGATECALL)
    | .CREATE2 => some (.System .CREATE2)
    | .STATICCALL => some (.System .STATICCALL)
    | .REVERT => some (.System .REVERT)
    | .INVALID => some (.System .INVALID)
    | .SELFDESTRUCT => some (.System .SELFDESTRUCT)
  | .Push _ | .Dup _ | .Exchange _ => none

theorem ofEVM_toEVM (op : PrimOp) : ofEVM (toEVM op) = some op := by
  cases op <;> rename_i o <;> cases o <;> rfl

/-- `toEVM` never maps two builtins to the same EVM instruction. -/
theorem toEVM_injective : Function.Injective toEVM := by
  intro a b h
  have := ofEVM_toEVM a
  rw [h, ofEVM_toEVM] at this
  exact (Option.some.inj this).symm

/-- The fee group of a Yul builtin: by definition, the EVM fee group of its twin. -/
@[expose] def yulFeeGroup (op : PrimOp) : FeeGroup := feeGroup (toEVM op)

/-- The state-independent floor of a fee group's price: the static price for the static groups,
and the part of the price that does not depend on the state for the dynamic ones (`C'` adds memory
words, warm/cold surcharges, topics, value transfer, ... on top). -/
@[expose] def _root_.EvmYul.EVM.GasMeter.FeeGroup.floorCost : FeeGroup → ℕ
  | .zero      => Gzero
  | .base      => Gbase
  | .verylow   => Gverylow
  | .low       => Glow
  | .mid       => Gmid
  | .high      => Ghigh
  | .jumpdest  => Gjumpdest
  | .blockhash => Gblockhash
  | .blobhash  => HASH_OPCODE_GAS
  | .transient => Gwarmaccess
  | .copy      => Gverylow
  | .extAccount => Gwarmaccess
  | .exp       => Gexp
  | .extcodecopy => Gwarmaccess
  | .log       => Glog
  | .keccak    => Gkeccak256
  | .create    => Gcreate
  | .sload     => Gwarmaccess
  | .sstore    => Gwarmaccess
  | .call      => Gwarmaccess
  | .selfdestruct => Gselfdestruct
  | .invalid   => 0

/-- For a static group, the floor is the static price. -/
theorem _root_.EvmYul.EVM.GasMeter.FeeGroup.floorCost_of_static {g : FeeGroup} {c : ℕ} (h : g.staticCost? = some c) :
    g.floorCost = c := by
  cases g <;> simp_all [FeeGroup.staticCost?, FeeGroup.floorCost]

/-- What the metered Yul semantics charges. -/
structure CostModel where
  /-- Price of one call of a builtin. -/
  prim : PrimOp → ℕ
  /-- Price of the conditional jump of an `if` or a `switch` (charged once the condition has been
  evaluated). -/
  branch : ℕ

/-- The Cancun cost model, read off the EVM table: a builtin costs the floor of its EVM twin's fee
group; a branch costs one `JUMPI` (`G_high`) plus one `JUMPDEST` (`G_jumpdest`). -/
@[expose] def cancun : CostModel where
  prim op := (yulFeeGroup op).floorCost
  branch := Ghigh + Gjumpdest

/-- **Same table, same price.** For a builtin with a state-independent price, the Yul charge equals
the EVM charge `C'` of its twin, in every EVM state. -/
theorem cancun_prim_eq_C' (op : PrimOp) {c : ℕ} (h : (yulFeeGroup op).staticCost? = some c)
    (s : EVM.State) : cancun.prim op = C' s (toEVM op) := by
  simp only [cancun]
  rw [FeeGroup.floorCost_of_static h, C'_eq_staticCost s (toEVM op) h]

theorem Caccess_ge (a : AccountAddress) (A : Substate) : Gwarmaccess ≤ Caccess a A := by
  unfold Caccess; split <;> simp [Gwarmaccess, Gcoldaccountaccess]

/-- **The Yul model never over-charges a builtin**: for every builtin and every EVM state, the Yul
charge is at most the EVM charge `C'` of its twin. -/
theorem cancun_prim_le_C' (op : PrimOp) (s : EVM.State) : cancun.prim op ≤ C' s (toEVM op) := by
  rcases hs : (yulFeeGroup op).staticCost? with _ | c
  · cases op <;> rename_i o <;> cases o <;>
      simp only [yulFeeGroup, toEVM, feeGroup, FeeGroup.staticCost?, reduceCtorEq] at hs <;>
      simp only [cancun, yulFeeGroup, toEVM, feeGroup, FeeGroup.floorCost] <;> unfold C' <;>
      simp [InstructionGasGroups.Wcopy, InstructionGasGroups.Wextaccount] <;>
      first
        | exact Caccess_ge _ _
        | exact le_add_right (Caccess_ge _ _)
        | exact le_add_left (le_add_right (le_add_right (Caccess_ge _ _)))
        | exact Csload_ge _ _ _
        | exact Csstore_ge _
        | exact Cselfdestruct_ge _
        | omega
        | (split <;> omega)
  · exact (cancun_prim_eq_C' op hs s).le

end Gas
end Yul
end EvmYul
