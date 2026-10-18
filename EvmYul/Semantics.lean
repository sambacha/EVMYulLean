module

public import EvmYul.Operations

public import EvmYul.Yul.State
public import EvmYul.Yul.Ast
public import EvmYul.Yul.Exception
public import EvmYul.Yul.PrimOps
public import EvmYul.Yul.StateOps

public import EvmYul.EVM.State
public import EvmYul.EVMException
public import EvmYul.EVM.PrimOps
public import EvmYul.EVM.StateOps
public import EvmYul.Wheels

public import EvmYul.UInt256
public import EvmYul.State.BasicOps
public import EvmYul.SharedStateOps
public import EvmYul.MachineStateOps

public import EvmYul.SpongeHash.Keccak256

--

public import Mathlib.Data.BitVec
public import Mathlib.Data.Array.Defs
public import Mathlib.Data.Finmap
public import Mathlib.Data.List.Defs
public import EvmYul.Stack
public import EvmYul.State.AccountMap
public import EvmYul.State.AccountMap
public import EvmYul.State.AccountOps
public import EvmYul.State.ExecutionEnv
public import EvmYul.State.Substate
public import EvmYul.State.TransactionOps

public import EvmYul.EVMException
public import EvmYul.EVM.Gas.Costs
public import EvmYul.EVM.Gas.Constants
public import EvmYul.EVM.State
public import EvmYul.EVM.StateOps
public import EvmYul.EVMException
public import EvmYul.EVM.Instr
public import EvmYul.EVM.PrecompiledContracts.Contracts
public import EvmYul.Operations
public import EvmYul.Pretty
public import EvmYul.SharedStateOps
public import EvmYul.Wheels
public import EvmYul.EllipticCurves
public import EvmYul.UInt256
public import EvmYul.MachineState

/-!
# Instruction semantics shared by the EVM and Yul

`step` for both machines: dispatches every operation to its transformer, written once over the
shared state and run by the EVM interpreter (`EVM/Semantics`) and the Yul interpreter
(`Yul/Interpreter`).
-/

public section

--

namespace EvmYul

section Semantics

open Stack

/--
`Transformer` is the primop-evaluating semantic function type for `Yul` and `EVM`.

- `EVM` is `EVM.State → EVM.State` because the arguments are already contained in `EVM.State.stack`.
- `Yul` is `Yul.State × List Literal → Yul.State × Option Literal` because the evaluation of primops in Yul
  does *not* store results within the state.

Both operations happen in their respecitve `.Exception` error monad.
-/
@[expose] abbrev Transformer : OperationType → Type
  | .EVM => EVM.Transformer
  | .Yul => Yul.Transformer

@[expose] def dispatchInvalid (τ : OperationType) : Transformer τ :=
  match τ with
    | .EVM => λ _ ↦ .error .InvalidInstruction
    | .Yul => λ _ _ ↦ .error Yul.Exception.InvalidInstruction

@[expose] def dispatchUnary (τ : OperationType) : Primop.Unary → Transformer τ :=
  match τ with
    | .EVM => EVM.execUnOp
    | .Yul => Yul.execUnOp

@[expose] def dispatchBinary (τ : OperationType) : Primop.Binary → Transformer τ :=
  match τ with
    | .EVM => EVM.execBinOp
    | .Yul => Yul.execBinOp

@[expose] def dispatchTernary (τ : OperationType) : Primop.Ternary → Transformer τ :=
  match τ with
    | .EVM => EVM.execTriOp
    | .Yul => Yul.execTriOp

@[expose] def dispatchQuartiary (τ : OperationType) : Primop.Quaternary → Transformer τ :=
  match τ with
    | .EVM => EVM.execQuadOp
    | .Yul => Yul.execQuadOp

@[expose] def dispatchExecutionEnvOp (τ : OperationType) (op : ExecutionEnv τ → UInt256) : Transformer τ :=
  match τ with
    | .EVM => EVM.executionEnvOp op
    | .Yul => Yul.executionEnvOp op

@[expose] def dispatchUnaryExecutionEnvOp (τ : OperationType) (op : ExecutionEnv τ → UInt256 → UInt256) : Transformer τ :=
  match τ with
    | .EVM => EVM.unaryExecutionEnvOp op
    | .Yul => Yul.unaryExecutionEnvOp op

@[expose] def dispatchMachineStateOp (τ : OperationType) (op : MachineState → UInt256) : Transformer τ :=
  match τ with
    | .EVM => EVM.machineStateOp op
    | .Yul => Yul.machineStateOp op

@[expose] def dispatchUnaryStateOp (τ : OperationType) (op : State τ → UInt256 → State τ × UInt256) : Transformer τ :=
  match τ with
    | .EVM => EVM.unaryStateOp op
    | .Yul => Yul.unaryStateOp op

@[expose] def dispatchTernaryCopyOp
 (τ : OperationType) (op : SharedState τ → UInt256 → UInt256 → UInt256 → SharedState τ) :
  Transformer τ
:=
  match τ with
    | .EVM => EVM.ternaryCopyOp op
    | .Yul => Yul.ternaryCopyOp op

@[expose] def dispatchQuaternaryCopyOp
 (τ : OperationType) (op : SharedState τ → UInt256 → UInt256 → UInt256 → UInt256 → SharedState τ) :
  Transformer τ
:=
  match τ with
    | .EVM => EVM.quaternaryCopyOp op
    | .Yul => Yul.quaternaryCopyOp op

@[expose] def dispatchBinaryMachineStateOp
 (τ : OperationType) (op : MachineState → UInt256 → UInt256 → MachineState) :
  Transformer τ
:=
  match τ with
    | .EVM => EVM.binaryMachineStateOp op
    | .Yul => Yul.binaryMachineStateOp op

@[expose] def dispatchTernaryMachineStateOp
 (τ : OperationType) (op : MachineState → UInt256 → UInt256 → UInt256 → MachineState) :
  Transformer τ
:=
  match τ with
    | .EVM => EVM.ternaryMachineStateOp op
    | .Yul => Yul.ternaryMachineStateOp op

@[expose] def dispatchBinaryMachineStateOp'
 (τ : OperationType) (op : MachineState → UInt256 → UInt256 → UInt256 × MachineState) :
  Transformer τ
:=
  match τ with
    | .EVM => EVM.binaryMachineStateOp' op
    | .Yul => Yul.binaryMachineStateOp' op

@[expose] def dispatchBinaryStateOp
 (τ : OperationType) (op : State τ → UInt256 → UInt256 → State τ) :
  Transformer τ
:=
  match τ with
    | .EVM => EVM.binaryStateOp op
    | .Yul => Yul.binaryStateOp op

@[expose] def dispatchStateOp (τ : OperationType) (op : State τ → UInt256) : Transformer τ :=
  match τ with
    | .EVM => EVM.stateOp op
    | .Yul => Yul.stateOp op

@[expose] def dispatchLog0 (τ : OperationType) : Transformer τ :=
  match τ with
    | .EVM => EVM.log0Op
    | .Yul => Yul.log0Op

@[expose] def dispatchLog1 (τ : OperationType) : Transformer τ :=
  match τ with
    | .EVM => EVM.log1Op
    | .Yul => Yul.log1Op

@[expose] def dispatchLog2 (τ : OperationType) : Transformer τ :=
  match τ with
    | .EVM => EVM.log2Op
    | .Yul => Yul.log2Op

@[expose] def dispatchLog3 (τ : OperationType) : Transformer τ :=
  match τ with
    | .EVM => EVM.log3Op
    | .Yul => Yul.log3Op

@[expose] def dispatchLog4 (τ : OperationType) : Transformer τ :=
  match τ with
    | .EVM => EVM.log4Op
    | .Yul => Yul.log4Op

@[expose] def L (n : ℕ) := n - n / 64

@[expose] def dup (n : ℕ) : Transformer .EVM :=
  λ s ↦
  let top := s.stack.take n
  if top.length = n then
    .ok <| s.replaceStackAndIncrPC (top.getLast! :: s.stack)
  else
    .error .StackUnderflow

@[expose] def swap (n : ℕ) : Transformer .EVM :=
  λ s ↦
  let top := s.stack.take (n + 1)
  let bottom := s.stack.drop (n + 1)
  if List.length top = (n + 1) then
    .ok <| s.replaceStackAndIncrPC (top.getLast! :: top.tail!.dropLast ++ [top.head!] ++ bottom)
  else
    .error .StackUnderflow

@[expose] def step {τ : OperationType} (op : Operation τ) (arg : Option (UInt256 × Nat) := .none) : Transformer τ := Id.run do
  -- The former `let _ : Id Unit := dbg_trace op.pretty; pure ()` was removed: the binding was unused,
  -- so the compiler eliminated it and it never printed (checked in the generated C). The opt-in
  -- per-instruction trace now lives in `EVM.X`, behind `EVM.traceInstructions`.
  match τ, op with
    -- TODO: Revisit STOP, this is likely not the best way to do it.
    | τ, .STOP =>
      match τ with
        | .EVM => λ evmState ↦ .ok <| {evmState with toMachineState := evmState.toMachineState.setReturnData .empty}
        | .Yul => λ yulState _ ↦ .error (Yul.Exception.YulHalt yulState ⟨0⟩)
    | τ, .ADD =>
      dispatchBinary τ UInt256.add
    | τ, .MUL =>
      dispatchBinary τ UInt256.mul
    | τ, .SUB =>
      dispatchBinary τ UInt256.sub
    | τ, .DIV =>
      dispatchBinary τ UInt256.div
    | τ, .SDIV =>
      dispatchBinary τ UInt256.sdiv
    | τ, .MOD =>
      dispatchBinary τ UInt256.mod
    | τ, .SMOD =>
      dispatchBinary τ UInt256.smod
    | τ, .ADDMOD =>
      dispatchTernary τ UInt256.addMod
    | τ, .MULMOD =>
      dispatchTernary τ UInt256.mulMod
    | τ, .EXP =>
      dispatchBinary τ UInt256.exp
    | τ, .SIGNEXTEND =>
      dispatchBinary τ UInt256.signextend
    | τ, .LT =>
      dispatchBinary τ UInt256.lt
    | τ, .GT =>
      dispatchBinary τ UInt256.gt
    | τ, .SLT =>
      dispatchBinary τ UInt256.slt
    | τ, .SGT =>
      dispatchBinary τ UInt256.sgt
    | τ, .EQ =>
      dispatchBinary τ UInt256.eq
    | τ, .ISZERO =>
      dispatchUnary τ UInt256.isZero
    | τ, .AND =>
      dispatchBinary τ UInt256.land
    | τ, .OR =>
      dispatchBinary τ UInt256.lor
    | τ, .XOR =>
      dispatchBinary τ UInt256.xor
    | τ, .NOT =>
      dispatchUnary τ UInt256.lnot
    | τ, .BYTE =>
      dispatchBinary τ UInt256.byteAt
    | τ, .SHL =>
      dispatchBinary τ (flip UInt256.shiftLeft)
    | τ, .SHR =>
      dispatchBinary τ (flip UInt256.shiftRight)
    | τ, .SAR =>
      dispatchBinary τ UInt256.sar

    | τ, .KECCAK256 =>
      dispatchBinaryMachineStateOp' τ MachineState.keccak256

    | τ, .ADDRESS =>
      dispatchExecutionEnvOp τ (.ofNat ∘ Fin.val ∘ ExecutionEnv.codeOwner)
    | τ, .BALANCE =>
      dispatchUnaryStateOp τ EvmYul.State.balance
    | τ, .ORIGIN =>
      dispatchExecutionEnvOp τ (.ofNat ∘ Fin.val ∘ ExecutionEnv.sender)
    | τ, .CALLER =>
      dispatchExecutionEnvOp τ (.ofNat ∘ Fin.val ∘ ExecutionEnv.source)
    | τ, .CALLVALUE =>
      dispatchExecutionEnvOp τ ExecutionEnv.weiValue
    | τ, .CALLDATALOAD =>
      dispatchUnaryStateOp τ (λ s v ↦ (s, EvmYul.State.calldataload s v))
    | τ, .CALLDATASIZE =>
      dispatchExecutionEnvOp τ (.ofNat ∘ ByteArray.size ∘ ExecutionEnv.calldata)
    | τ, .CALLDATACOPY =>
      dispatchTernaryCopyOp τ .calldatacopy
    | .EVM, .CODESIZE =>
      dispatchExecutionEnvOp .EVM (.ofNat ∘ ByteArray.size ∘ ExecutionEnv.code)
    | .EVM, .CODECOPY =>
      dispatchTernaryCopyOp .EVM .codeCopy
    | τ, .GASPRICE =>
      dispatchExecutionEnvOp τ (.ofNat ∘ ExecutionEnv.gasPrice)
    | .EVM, .EXTCODESIZE =>
      dispatchUnaryStateOp .EVM EvmYul.State.extCodeSize
    | .Yul, .EXTCODESIZE =>
      λ _ _ ↦ .error .YulEXTCODESIZENotImplemented
    | .EVM, .EXTCODECOPY =>
      dispatchQuaternaryCopyOp .EVM EvmYul.SharedState.extCodeCopy'
    | τ, .RETURNDATASIZE =>
      dispatchMachineStateOp τ EvmYul.MachineState.returndatasize
    | .EVM, .RETURNDATACOPY =>
            λ evmState ↦
        match evmState.stack.pop3 with
          | some ⟨stack', μ₀, μ₁, μ₂⟩ => do
            let mState' := evmState.toMachineState.returndatacopy μ₀ μ₁ μ₂
            let evmState' := {evmState with toMachineState := mState'}
            .ok <| evmState'.replaceStackAndIncrPC stack'
          | _ => .error .StackUnderflow
    | .Yul, .RETURNDATACOPY =>
      λ yulState lits ↦
        match lits with
          | [a, b, c] => do
            let mState' := yulState.toSharedState.toMachineState.returndatacopy a b c
            .ok <| (yulState.setMachineState mState', .none)
          | _ => .error .InvalidArguments
    | .EVM, .EXTCODEHASH => dispatchUnaryStateOp .EVM EvmYul.State.extCodeHash

    | τ, .BLOCKHASH => dispatchUnaryStateOp τ (λ s v ↦ (s, EvmYul.State.blockHash s v))
    | τ, .COINBASE => dispatchStateOp τ (.ofNat ∘ Fin.val ∘ EvmYul.State.coinBase)
    | τ, .TIMESTAMP =>
      dispatchStateOp τ EvmYul.State.timeStamp
    | τ, .NUMBER => dispatchStateOp τ EvmYul.State.number
    -- "RANDAO is a pseudorandom value generated by validators on the Ethereum consensus layer"
    -- "the details of generating the RANDAO value on the Beacon Chain is beyond the scope of this paper"
    | τ, .PREVRANDAO => dispatchExecutionEnvOp τ EvmYul.prevRandao
    | τ, .GASLIMIT => dispatchStateOp τ EvmYul.State.gasLimit
    | τ, .CHAINID => dispatchStateOp τ EvmYul.State.chainId
    | τ, .SELFBALANCE => dispatchStateOp τ EvmYul.State.selfbalance
    | τ, .BASEFEE => dispatchExecutionEnvOp τ EvmYul.basefee
    | τ, .BLOBHASH => dispatchUnaryExecutionEnvOp τ blobhash
    | τ, .BLOBBASEFEE => dispatchExecutionEnvOp τ EvmYul.ExecutionEnv.getBlobGasprice

    | .EVM, .POP =>
      λ evmState ↦
      match evmState.stack.pop with
        | some ⟨ s , _ ⟩ => .ok <| evmState.replaceStackAndIncrPC s
        | _ => .error .StackUnderflow

    | .EVM, .MLOAD => λ evmState ↦
      match evmState.stack.pop with
        | some ⟨ s , μ₀ ⟩ => Id.run do
          let (v, mState') := evmState.toMachineState.mload μ₀
          let evmState' := {evmState with toMachineState := mState'}
          .ok <| evmState'.replaceStackAndIncrPC (s.push v)
        | _ => .error .StackUnderflow
    | .Yul, .MLOAD => λ yulState lits ↦
        match lits with
          | [a] =>
            let (v, mState') := yulState.toSharedState.toMachineState.mload a
            let yulState' := yulState.setMachineState mState'
            .ok <| (yulState', some v)
          | _ => .error .InvalidArguments
    | τ, .MSTORE =>
      dispatchBinaryMachineStateOp τ MachineState.mstore
    | τ, .MSTORE8 => dispatchBinaryMachineStateOp τ MachineState.mstore8
    | τ, .SLOAD =>
      dispatchUnaryStateOp τ EvmYul.State.sload
    | τ, .SSTORE =>
      dispatchBinaryStateOp τ EvmYul.State.sstore
    | τ, .TLOAD => dispatchUnaryStateOp τ EvmYul.State.tload
    | τ, .TSTORE => dispatchBinaryStateOp τ EvmYul.State.tstore
    | τ, .MSIZE => dispatchMachineStateOp τ MachineState.msize
    | τ, .GAS =>
      dispatchMachineStateOp τ MachineState.gas
    | τ, .MCOPY => dispatchTernaryMachineStateOp τ MachineState.mcopy

    | τ, .LOG0 => dispatchLog0 τ
    | τ, .LOG1 => dispatchLog1 τ
    | τ, .LOG2 => dispatchLog2 τ
    | τ, .LOG3 => dispatchLog3 τ
    | τ, .LOG4 => dispatchLog4 τ
    | .EVM, .RETURN => dispatchBinaryMachineStateOp .EVM MachineState.evmReturn
    | .Yul, .RETURN => λ yulState lits ↦ 
        match (dispatchBinaryMachineStateOp .Yul MachineState.evmReturn) yulState lits with
          | .error e => .error e
          | .ok (s, v) => .error (Yul.Exception.YulHalt s (v.getD ⟨1⟩))
    | .EVM, .REVERT => dispatchBinaryMachineStateOp .EVM MachineState.evmRevert
    | .Yul, .REVERT => λ yulState lits ↦ 
        match (dispatchBinaryMachineStateOp .Yul MachineState.evmRevert) yulState lits with
          | .error e => .error e
          | .ok (_, _) => .error (Yul.Exception.Revert)
    | .EVM, .SELFDESTRUCT =>
      -- The world-state effect (EIP-6780) is `State.selfDestruct`, shared with the Yul case.
      λ evmState ↦
        match evmState.stack.pop with
          | some ⟨ s , μ₁ ⟩ =>
            let σ' := evmState.toState.selfDestruct (AccountAddress.ofUInt256 μ₁)
            let evmState' :=
              {evmState with
                accountMap := σ'.accountMap
                substate := σ'.substate
              }
            .ok <| evmState'.replaceStackAndIncrPC s
          | _ => .error .StackUnderflow
    | .Yul, .SELFDESTRUCT => λ yulState lits ↦
      -- Same world-state effect as the EVM case (`State.selfDestruct`, EIP-6780); like `STOP`,
      -- `SELFDESTRUCT` then halts execution.
      match lits with
        | [a] =>
            let yulState' :=
              yulState.setState (yulState.toState.selfDestruct (AccountAddress.ofUInt256 a))
            .error (Yul.Exception.YulHalt yulState' ⟨0⟩)
        | _ => .error .InvalidArguments
    | τ, .INVALID => dispatchInvalid τ
    | .EVM, .Push .PUSH0 => λ evmState =>
        .ok <|
          evmState.replaceStackAndIncrPC (evmState.stack.push ⟨0⟩)
    | .EVM, .Push _ => λ evmState => do
        let some (arg, argWidth) := arg | .error .StackUnderflow
        .ok <| evmState.replaceStackAndIncrPC (evmState.stack.push arg) (pcΔ := argWidth.succ)
    | .EVM, .JUMP => λ evmState => do
        match evmState.stack.pop with
          | some ⟨stack , μ₀⟩ =>
            let newPc := μ₀
            .ok <| {evmState with pc := newPc, stack := stack}
          | _ => .error .StackUnderflow
    | .EVM, .JUMPI => λ evmState => do
        match evmState.stack.pop2 with
          | some ⟨stack , μ₀, μ₁⟩ =>
            let newPc := if μ₁ != ⟨0⟩ then μ₀ else evmState.pc + ⟨1⟩
            .ok <| {evmState with pc := newPc, stack := stack}
          | _ => .error .StackUnderflow
    | .EVM, .PC => λ evmState =>
        .ok <| evmState.replaceStackAndIncrPC (evmState.stack.push evmState.pc)
    | .EVM, .JUMPDEST => λ evmState => do
        .ok <| evmState.incrPC
    | .EVM, .DUP1 => dup 1
    | .EVM, .DUP2 => dup 2
    | .EVM, .DUP3 => dup 3
    | .EVM, .DUP4 => dup 4
    | .EVM, .DUP5 => dup 5
    | .EVM, .DUP6 => dup 6
    | .EVM, .DUP7 => dup 7
    | .EVM, .DUP8 => dup 8
    | .EVM, .DUP9 => dup 9
    | .EVM, .DUP10 => dup 10
    | .EVM, .DUP11 => dup 11
    | .EVM, .DUP12 => dup 12
    | .EVM, .DUP13 => dup 13
    | .EVM, .DUP14 => dup 14
    | .EVM, .DUP15 => dup 15
    | .EVM, .DUP16 => dup 16
    | .EVM, .SWAP1 => swap 1
    | .EVM, .SWAP2 => swap 2
    | .EVM, .SWAP3 => swap 3
    | .EVM, .SWAP4 => swap 4
    | .EVM, .SWAP5 => swap 5
    | .EVM, .SWAP6 => swap 6
    | .EVM, .SWAP7 => swap 7
    | .EVM, .SWAP8 => swap 8
    | .EVM, .SWAP9 => swap 9
    | .EVM, .SWAP10 => swap 10
    | .EVM, .SWAP11 => swap 11
    | .EVM, .SWAP12 => swap 12
    | .EVM, .SWAP13 => swap 13
    | .EVM, .SWAP14 => swap 14
    | .EVM, .SWAP15 => swap 15
    | .EVM, .SWAP16 => swap 16
    | .EVM, _ => λ _ ↦ default
    | .Yul, .POP => λ yulState _ ↦ .ok (yulState, .none) -- POP is a no-op for Yul as it discards the value only as a hint to the compiler.
    | .Yul, _ => λ _ _ ↦ default

end Semantics

end EvmYul
