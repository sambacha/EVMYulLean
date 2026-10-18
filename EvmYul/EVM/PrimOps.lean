module

public import EvmYul.Stack
public import EvmYul.EVM.State
public import EvmYul.EVMException
public import EvmYul.EVM.StateOps
public import EvmYul.SharedStateOps

/-!
# EVM primitive operations as state transformers

`Transformer` and the helpers that lift unary to quaternary word functions, environment reads and
state updates into EVM state transformers, used by the shared semantics `EvmYul.Semantics`.
-/

public section

namespace EvmYul

namespace EVM

@[expose] def Transformer := EVM.State → Except EVM.ExecutionException EVM.State

@[expose] def execUnOp (f : Primop.Unary) : Transformer :=
  λ s ↦
    match s.stack.pop with
      | some ⟨stack, μ₀⟩ => Id.run do
        .ok <| s.replaceStackAndIncrPC (stack.push <| f μ₀)
      | _ =>
        .error .StackUnderflow

@[expose] def execBinOp (f : Primop.Binary) : Transformer :=
  λ s ↦
    match s.stack.pop2 with
      | some ⟨stack, μ₀, μ₁⟩ => Id.run do
        let result := f μ₀ μ₁
        .ok <| s.replaceStackAndIncrPC (stack.push result)
      | _ =>
        .error .StackUnderflow

@[expose] def execTriOp (f : Primop.Ternary) : Transformer :=
  λ s ↦
    match s.stack.pop3 with
      | some ⟨stack, μ₀, μ₁, μ₂⟩ => Id.run do
        .ok <| s.replaceStackAndIncrPC (stack.push <| f μ₀ μ₁ μ₂)
      | _ =>
        .error .StackUnderflow

@[expose] def execQuadOp (f : Primop.Quaternary) : Transformer :=
  λ s ↦
    match s.stack.pop4 with
      | some ⟨ stack , μ₀ , μ₁ , μ₂, μ₃ ⟩ => Id.run do
        .ok <| s.replaceStackAndIncrPC (stack.push <| f μ₀ μ₁ μ₂ μ₃)
      | _ =>
        .error .StackUnderflow

@[expose] def executionEnvOp (op : ExecutionEnv .EVM → UInt256) : Transformer :=
  λ evmState ↦ Id.run do
    let result := op evmState.executionEnv
    .ok <|
      evmState.replaceStackAndIncrPC (evmState.stack.push result)

@[expose] def unaryExecutionEnvOp (op : ExecutionEnv .EVM → UInt256 → UInt256) : Transformer :=
  λ evmState ↦
    match evmState.stack.pop with
    | some ⟨ s , μ₀⟩ => Id.run do
      let result := op evmState.executionEnv μ₀
      .ok <|
        evmState.replaceStackAndIncrPC (s.push result)
    | _ => .error .StackUnderflow

@[expose] def machineStateOp (op : MachineState → UInt256) : Transformer :=
  λ evmState ↦ Id.run do
    let result := op evmState.toMachineState
    .ok <|
      evmState.replaceStackAndIncrPC (evmState.stack.push result)

@[expose] def binaryMachineStateOp
  (op : MachineState → UInt256 → UInt256 → MachineState)
    :
  Transformer
:= λ evmState ↦
  match evmState.stack.pop2 with
    | some ⟨ s , μ₀, μ₁ ⟩ => Id.run do
      let mState' := op evmState.toMachineState μ₀ μ₁
      let evmState' := {evmState with toMachineState := mState'}
      .ok <| evmState'.replaceStackAndIncrPC s
    | _ => .error .StackUnderflow

@[expose] def binaryMachineStateOp'
  (op : MachineState → UInt256 → UInt256 → UInt256 × MachineState)
    :
  Transformer
:= λ evmState ↦
  match evmState.stack.pop2 with
    | some ⟨ s , μ₀, μ₁ ⟩ => Id.run do
      let (val, mState') := op evmState.toMachineState μ₀ μ₁
      let evmState' := {evmState with toMachineState := mState'}
      .ok <| evmState'.replaceStackAndIncrPC (s.push val)
    | _ => .error .StackUnderflow

@[expose] def ternaryMachineStateOp
  (op : MachineState → UInt256 → UInt256 → UInt256 → MachineState)
    :
  Transformer
:= λ evmState ↦
  match evmState.stack.pop3 with
    | some ⟨ s , μ₀, μ₁, μ₂ ⟩ => Id.run do
      let mState' := op evmState.toMachineState μ₀ μ₁ μ₂
      let evmState' := {evmState with toMachineState := mState'}
      .ok <| evmState'.replaceStackAndIncrPC s
    | _ => .error .StackUnderflow

@[expose] def binaryStateOp
  (op : EvmYul.State .EVM → UInt256 → UInt256 → EvmYul.State .EVM)
    :
  Transformer
:= λ evmState ↦
  match evmState.stack.pop2 with
    | some ⟨ s , μ₀, μ₁ ⟩ => Id.run do
      let state' := op evmState.toState μ₀ μ₁
      let evmState' := {evmState with toState := state'}
      .ok <| evmState'.replaceStackAndIncrPC s
    | _ => .error .StackUnderflow

@[expose] def stateOp (op : EvmYul.State .EVM → UInt256) : Transformer :=
  λ evmState ↦ Id.run do
    .ok <|
      evmState.replaceStackAndIncrPC (evmState.stack.push <| op evmState.toState)

@[expose] def unaryStateOp
  (op : EvmYul.State .EVM → UInt256 → EvmYul.State .EVM × UInt256)
    :
  Transformer
:= λ evmState ↦
      match evmState.stack.pop with
        | some ⟨stack' , μ₀ ⟩ => Id.run do
          let (state', b) := op evmState.toState μ₀
          let evmState' := {evmState with toState := state'}
          .ok <| evmState'.replaceStackAndIncrPC (stack'.push b)
        | _ => .error .StackUnderflow

@[expose] def ternaryCopyOp
  (op : SharedState .EVM → UInt256 → UInt256 → UInt256 → SharedState .EVM)
    :
  Transformer
:= λ evmState ↦
  match evmState.stack.pop3 with
    | some ⟨ stack' , μ₀, μ₁, μ₂⟩ => Id.run do
      let sState' := op evmState.toSharedState μ₀ μ₁ μ₂
      let evmState' := { evmState with toSharedState := sState'}
      .ok <| evmState'.replaceStackAndIncrPC stack'
    | _ => .error .StackUnderflow

@[expose] def quaternaryCopyOp
  (op : SharedState .EVM → UInt256 → UInt256 → UInt256 → UInt256 → SharedState .EVM)
    :
  Transformer
:=  λ evmState ↦
      match evmState.stack.pop4 with
        | some ⟨ stack' , μ₀, μ₁, μ₂, μ₃⟩ => Id.run do
          let sState' := op evmState.toSharedState μ₀ μ₁ μ₂ μ₃
          let evmState' := { evmState with toSharedState := sState'}
          .ok <| evmState'.replaceStackAndIncrPC stack'
        | _ => .error .StackUnderflow

@[expose] def evmLogOp (evmState : State) (μ₀ μ₁ : UInt256) (t : Array UInt256) : State :=
  let sharedState' := SharedState.logOp μ₀ μ₁ t evmState.toSharedState
  { evmState with toSharedState := sharedState'}

@[expose] def log0Op : Transformer :=
  λ evmState ↦
    match evmState.stack.pop2 with
      | some ⟨stack', μ₀, μ₁⟩ => Id.run do
        let evmState' := evmLogOp evmState μ₀ μ₁ #[]
        .ok <| evmState'.replaceStackAndIncrPC stack'
      | _ => .error .StackUnderflow

@[expose] def log1Op : Transformer :=
  λ evmState ↦
    match evmState.stack.pop3 with
      | some ⟨stack', μ₀, μ₁, μ₂⟩ => Id.run do
        let evmState' := evmLogOp evmState μ₀ μ₁ #[μ₂]
        .ok <| evmState'.replaceStackAndIncrPC stack'
      | _ => .error .StackUnderflow

@[expose] def log2Op : Transformer :=
  λ evmState ↦
    match evmState.stack.pop4 with
      | some ⟨stack', μ₀, μ₁, μ₂, μ₃⟩ => Id.run do
        let evmState' := evmLogOp evmState μ₀ μ₁ #[μ₂, μ₃]
        .ok <| evmState'.replaceStackAndIncrPC stack'
      | _ => .error .StackUnderflow

@[expose] def log3Op : Transformer :=
  λ evmState ↦
    match evmState.stack.pop5 with
      | some ⟨stack', μ₀, μ₁, μ₂, μ₃, μ₄⟩ => Id.run do
        let evmState' := evmLogOp evmState μ₀ μ₁ #[μ₂, μ₃, μ₄]
        .ok <| evmState'.replaceStackAndIncrPC stack'
      | _ => .error .StackUnderflow

@[expose] def log4Op : Transformer :=
  λ evmState ↦
    match evmState.stack.pop6 with
      | some ⟨stack', μ₀, μ₁, μ₂, μ₃, μ₄, μ₅⟩ => Id.run do
        let evmState' := evmLogOp evmState μ₀ μ₁ #[μ₂, μ₃, μ₄, μ₅]
        .ok <| evmState'.replaceStackAndIncrPC stack'
      | _ => .error .StackUnderflow

end EVM

end EvmYul
