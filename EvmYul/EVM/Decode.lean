module

public import EvmYul.EVMException
public import EvmYul.EVM.Instr
public import EvmYul.State.ExecutionEnv
public import EvmYul.UInt256
public import EvmYul.Wheels

public section

/-!
# Bytecode decoding and jump destinations

Split from `EvmYul/EVM/Semantics.lean` (Rule 4): reading one instruction and its immediate
argument from the code (`decode`, `fetchInstr`), the address of the next instruction (`N`), and the
set of valid jump destinations `D_J` (YP §9.4.3). The interpreter in `EvmYul/EVM/Semantics.lean`
imports this module; the definitions are unchanged.
-/

namespace EvmYul

namespace EVM

@[expose] def argOnNBytesOfInstr : Operation .EVM → ℕ
  -- | .Push .PUSH0 => 0 is handled as default.
  | .Push .PUSH1 => 1
  | .Push .PUSH2 => 2
  | .Push .PUSH3 => 3
  | .Push .PUSH4 => 4
  | .Push .PUSH5 => 5
  | .Push .PUSH6 => 6
  | .Push .PUSH7 => 7
  | .Push .PUSH8 => 8
  | .Push .PUSH9 => 9
  | .Push .PUSH10 => 10
  | .Push .PUSH11 => 11
  | .Push .PUSH12 => 12
  | .Push .PUSH13 => 13
  | .Push .PUSH14 => 14
  | .Push .PUSH15 => 15
  | .Push .PUSH16 => 16
  | .Push .PUSH17 => 17
  | .Push .PUSH18 => 18
  | .Push .PUSH19 => 19
  | .Push .PUSH20 => 20
  | .Push .PUSH21 => 21
  | .Push .PUSH22 => 22
  | .Push .PUSH23 => 23
  | .Push .PUSH24 => 24
  | .Push .PUSH25 => 25
  | .Push .PUSH26 => 26
  | .Push .PUSH27 => 27
  | .Push .PUSH28 => 28
  | .Push .PUSH29 => 29
  | .Push .PUSH30 => 30
  | .Push .PUSH31 => 31
  | .Push .PUSH32 => 32
  | _ => 0

def N (pc : UInt256) (instr : Operation .EVM) := pc + ⟨1⟩ + .ofNat (argOnNBytesOfInstr instr)

/--
Returns the instruction from `arr` at `pc` assuming it is valid.

The `Push` instruction also returns the argument as an EVM word along with the width of the instruction.
-/
@[expose] def decode (arr : ByteArray) (pc : UInt256) :
  Option (Operation .EVM × Option (UInt256 × Nat)) := do
  let instr ← arr.get? pc.toNat >>= EvmYul.EVM.parseInstr
  let argWidth := argOnNBytesOfInstr instr
  .some (
    instr,
    if argWidth == 0
    then .none
    else .some (EvmYul.uInt256OfByteArray (arr.extract' pc.toNat.succ (pc.toNat.succ + argWidth)), argWidth)
  )

@[expose] def fetchInstr (I : EvmYul.ExecutionEnv .EVM) (pc : UInt256) :
               Except EVM.ExecutionException (Operation .EVM × Option (UInt256 × Nat)) :=
  decode I.code pc |>.option (.error .StackUnderflow) Except.ok

partial def D_J_aux (c : ByteArray) (i : UInt256) (result : Array UInt256) : Array UInt256 :=
  match c.get? i.toNat >>= EvmYul.EVM.parseInstr with
    | none => result
    | some cᵢ => D_J_aux c (N i cᵢ) (if cᵢ = .JUMPDEST then result.push i else result)

@[expose] def D_J (c : ByteArray) (i : UInt256) : Array UInt256 :=
  D_J_aux c i #[]

end EVM

end EvmYul
