module

public import EvmYul.Yul.State
public import EvmYul.Yul.Exception
public import EvmYul.Yul.StateOps
public import EvmYul.SharedStateOps

public import EvmYul.UInt256

public import EvmYul.Wheels

/-!
# Yul primitive operations as state transformers

`Transformer` and the helpers that lift word functions and state updates to Yul state transformers,
used by the shared semantics `EvmYul.Semantics`.
-/

public section

namespace EvmYul

namespace Yul

open Lean Parser


@[expose] def Transformer := Yul.State → List Literal → Except Yul.Exception (Yul.State × Option Literal)

@[expose] def execUnOp (f : Primop.Unary) : Transformer
  | s, [a] => .ok (s, f a)
  | _, _   => throw .InvalidArguments

@[expose] def execBinOp (f : Primop.Binary) : Transformer
  | s, [a, b] => .ok (s, f a b)
  | _, _      => throw .InvalidArguments

@[expose] def execTriOp (f : Primop.Ternary) : Transformer
  | s, [a, b, c] => .ok (s, f a b c)
  | _, _         => throw .InvalidArguments

@[expose] def execQuadOp (f : Primop.Quaternary) : Transformer
  | s, [a, b, c, d] => .ok (s, f a b c d)
  | _, _            => throw .InvalidArguments

@[expose] def executionEnvOp (op : ExecutionEnv .Yul → UInt256) : Transformer :=
  λ yulState _ ↦ .ok (yulState, .some <| op yulState.executionEnv)

@[expose] def unaryExecutionEnvOp (op : ExecutionEnv .Yul → UInt256 → UInt256) : Transformer :=
  λ yulState lits ↦
    match lits with
    | [a] => .ok (yulState, .some <| op yulState.executionEnv a)
    | _ => .error .InvalidArguments

@[expose] def machineStateOp (op : MachineState → UInt256) : Transformer :=
  λ yulState _ ↦ .ok (yulState, .some <| op yulState.toMachineState)

@[expose] def binaryMachineStateOp
  (op : MachineState → UInt256 → UInt256 → MachineState) : Transformer
:= λ yulState lits ↦
  match lits with
    | [a, b] =>
      let mState' := op yulState.toMachineState a b
      let yulState' := yulState.setMachineState mState'
      .ok <| (yulState', none)
    | _ => .error .InvalidArguments

@[expose] def binaryMachineStateOp'
  (op : MachineState → UInt256 → UInt256 → UInt256 × MachineState) : Transformer
:= λ yulState lits ↦
  match lits with
    | [a, b] =>
      let (val, mState') := op yulState.toMachineState a b
      let yulState' := yulState.setMachineState mState'
      .ok <| (yulState', some val)
    | _ => .error .InvalidArguments

@[expose] def ternaryMachineStateOp
  (op : MachineState → UInt256 → UInt256 → UInt256 → MachineState) : Transformer
:= λ yulState lits ↦
  match lits with
    | [a, b, c] =>
      let mState' := op yulState.toMachineState a b c
      let yulState' := yulState.setMachineState mState'
      .ok <| (yulState', none)
    | _ => .error .InvalidArguments

@[expose] def binaryStateOp
  (op : EvmYul.State .Yul → UInt256 → UInt256 → EvmYul.State .Yul) : Transformer
:= λ yulState lits ↦
  match lits with
    | [a, b] =>
      let state' := op yulState.toState a b
      let yulState' := yulState.setState state'
      .ok <| (yulState', none)
    | _ => .error .InvalidArguments

@[expose] def stateOp (op : EvmYul.State .Yul → UInt256) : Transformer :=
  λ yulState _ ↦ .ok (yulState, .some <| op yulState.toState)

@[expose] def unaryStateOp (op : EvmYul.State .Yul → UInt256 → EvmYul.State .Yul × UInt256) : Transformer :=
  λ yulState lits ↦
      match lits with
        | [lit] =>
          let (state', b) := op yulState.toState lit
          let yulState' :=
            yulState.setSharedState { yulState.toSharedState with toState := state' }
          .ok (yulState', some b)
        | _ => .error .InvalidArguments

@[expose] def ternaryCopyOp (op : SharedState .Yul → UInt256 → UInt256 → UInt256 → SharedState .Yul) :
  Transformer
:= λ yulState lits ↦
  match lits with
    | [a, b, c] =>
      let sState' := op yulState.toSharedState a b c
      let yulState' := yulState.setSharedState sState'
      .ok (yulState', none)
    | _ => .error .InvalidArguments

@[expose] def quaternaryCopyOp
  (op : SharedState .Yul → UInt256 → UInt256 → UInt256 → UInt256 → SharedState .Yul) :
  Transformer
:= λ yulState lits ↦
  match lits with
    | [a, b, c, d] =>
      let sState' := op yulState.toSharedState a b c d
      let yulState' := yulState.setSharedState sState'
      .ok (yulState', none)
    | _ => .error .InvalidArguments

@[expose] def yulLogOp (yulState : State) (a b : UInt256) (t : Array UInt256) : State × Option Literal :=
  let sharedState' := SharedState.logOp a b t yulState.toSharedState
  ( yulState.setSharedState sharedState'
  , none
  )

@[expose] def log0Op : Transformer :=
  λ yulState lits ↦
    match lits with
      | [a, b] =>
        .ok <| yulLogOp yulState a b #[]
      | _ => .ok (yulState, none)

@[expose] def log1Op : Transformer :=
  λ yulState lits ↦
    match lits with
      | [a, b, c] =>
        .ok <| yulLogOp yulState a b #[c]
      | _ => .ok (yulState, none)

@[expose] def log2Op : Transformer :=
  λ yulState lits ↦
    match lits with
      | [a, b, c, d] =>
        .ok <| yulLogOp yulState a b #[c, d]
      | _ => .ok (yulState, none)

@[expose] def log3Op : Transformer :=
  λ yulState lits ↦
    match lits with
      | [a, b, c, d, e] =>
        .ok <| yulLogOp yulState a b #[c, d, e]
      | _ => .ok (yulState, none)

@[expose] def log4Op : Transformer :=
  λ yulState lits ↦
    match lits with
      | [a, b, c, d, e, f] =>
        .ok <| yulLogOp yulState a b #[c, d, e, f]
      | _ => .ok (yulState, none)

end Yul

end EvmYul
