module

public import EvmYul.Yul.Interpreter

public section

/-!
# Fuel-free view of Yul primitive calls

`primCall` (in `EvmYul/Yul/Interpreter.lean`) is the only interpreter function in which an external
contract call happens: the CALL, STATICCALL, CALLCODE and DELEGATECALL branches run the callee's
dispatcher through `callDispatcher`. `primCallK` is the same code with that recursive call
abstracted as a parameter `k` (the "continuation" that runs a dispatcher). It contains no fuel.

`primCall_succ_eq_primCallK` shows that the interpreter is exactly `primCallK` instantiated with its
own (fuelled) dispatcher; the relational semantics (`EvmYul/Yul/Relational/Semantics.lean`) uses
`primCallK` instantiated with any dispatcher that is *correct with respect to the relation*.

The body below is a verbatim copy of `primCall`'s body (generated; only `callDispatcher fuel₁` is
renamed to `k`). The equation lemma `primCall_succ_eq_primCallK` is proved by `rfl`, so this file
fails to build if the two drift apart.
-/

namespace EvmYul
namespace Yul
namespace Relational

open Ast

/-- `primCall` with the dispatcher of called contracts abstracted as `k` (no fuel). -/
@[expose] def primCallK (k : Option YulContract → State → Except Yul.Exception (State × List Literal))
    (s₀ : State) (prim : Operation .Yul) (args : List Literal) :
    Except Yul.Exception (State × List Literal) :=
  do
      if ¬s₀.executionEnv.perm ∧ prim ∈ [.CREATE, .CREATE2, .SSTORE, .SELFDESTRUCT, .LOG0, .LOG1, .LOG2, .LOG3, .LOG4, .TSTORE] then throw .StaticModeViolation
      match prim with
      | .CALL =>
        match args with
          | _ :: address_arg :: value :: inOffset :: inSize :: outOffset :: outSize :: _ =>
            if ¬s₀.executionEnv.perm ∧ value ≠ ⟨0⟩ then throw .StaticModeViolation
            let address := AccountAddress.ofUInt256 address_arg
            let calldata₁ := s₀.toMachineState.memory.readWithPadding inOffset.toNat inSize.toNat
            let accountMap₁Opt := (s₀.sharedState.accountMap.transferBalance .Yul s₀.executionEnv.codeOwner address value)
            match accountMap₁Opt with
              | .none =>
                buildContractCallEmptyReturnState s₀ .none ⟨0⟩ -- Insufficient funds: return 0 to indicate error, with empty return data 
              | .some accountMap₁ =>
                if s₀.executionEnv.depth ≥ 1024
                then
                  buildContractCallEmptyReturnState s₀ .none ⟨0⟩ -- Reached depth limit: return 0 to indicate error, with empty return data 
                else
                  match s₀ with
                  | .OutOfFuel => .error .OutOfFuel
                  | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
                  | .Ok sharedState varstore =>
                      match s₀.sharedState.accountMap.get? address with
                        | .none => 
                          buildContractCallEmptyReturnState s₀ accountMap₁ ⟨1⟩ -- No contract at the provided address, return 1 to indicate success, with empty return data. (Like STOP opcode).
                        | .some yulContract =>
                          let executionEnv₁ := { sharedState.executionEnv with
                                                    calldata := calldata₁,
                                                    code := yulContract.code,
                                                    codeOwner := address,
                                                    source := s₀.executionEnv.codeOwner,
                                                    weiValue := value
                                                    depth := s₀.executionEnv.depth + 1
                                                }
                          let sharedState₁ := { sharedState with
                                                  executionEnv := executionEnv₁,
                                                  memory := ByteArray.mk #[],
                                                  accountMap := accountMap₁
                                              }
                          let s₁ : State := .Ok sharedState₁ default
                          
                          match k .none s₁ with
                          | .error (.YulHalt s₂ _) => 
                            let memory₃ := s₂.toMachineState.H_return.copySlice 0 s₀.toMachineState.memory outOffset.toNat (min outSize.toNat s₂.toMachineState.H_return.size)
                            match s₂ with
                              | .OutOfFuel => .error .OutOfFuel
                              | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
                              | .Ok sharedState₂ _ =>
                              
                                -- Restore ExecutionEnv
                                let executionEnv₃ := { sharedState₂.executionEnv with
                                                    calldata := default,
                                                    code := s₀.executionEnv.code,
                                                    codeOwner := s₀.executionEnv.codeOwner,
                                                    source := s₀.executionEnv.source,
                                                    weiValue := s₀.executionEnv.weiValue,
                                                }
                                let sharedState₃ := { sharedState₂ with
                                                        memory := memory₃,
                                                        returnData := s₂.toMachineState.H_return,
                                                        executionEnv := executionEnv₃,
                                                        H_return := ByteArray.empty
                                                    }
                                .ok (.Ok sharedState₃ varstore, [⟨1⟩])
                          | .error e => .error e
                          | .ok (s₂, _) =>
                            
                            /- We note here that if:
                                  `outOffset.toNat + (min outSize.toNat s₂.toMachineState.H_return.size) ≥ UInt256.size`
                                then we are writing beyond the theoretical memory size limit.
                                The yellow paper is unclear on the semantics of this (at the time of writing).
                                We follow the https://github.com/NethermindEth/nethermind execution client (for example).
                                And we expand the memory beyond the theoretical 2^256 bit max size if needed.
                                In practice, this is essentially impossible to occur due to the
                                  prohibitively large gas cost of allocating this much memory.
                                  
                                Similarly in other places in `primCall` where `memory₃` is constructed in this way.
                            -/
                            let memory₃ := s₂.toMachineState.H_return.copySlice 0 s₀.toMachineState.memory outOffset.toNat (min outSize.toNat s₂.toMachineState.H_return.size)
                            match s₂ with
                              | .OutOfFuel => .error .OutOfFuel
                              | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
                              | .Ok sharedState₂ _ =>
                                                                
                                -- Restore ExecutionEnv
                                let executionEnv₃ := { sharedState₂.executionEnv with
                                                    calldata := default,
                                                    code := s₀.executionEnv.code,
                                                    codeOwner := s₀.executionEnv.codeOwner,
                                                    source := s₀.executionEnv.source,
                                                    weiValue := s₀.executionEnv.weiValue,
                                                }
                                let sharedState₃ := { sharedState₂ with
                                                        memory := memory₃,
                                                        returnData := s₂.toMachineState.H_return,
                                                        H_return := ByteArray.empty,
                                                        executionEnv := executionEnv₃
                                                    }
                                .ok (.Ok sharedState₃ varstore, [⟨1⟩])
          | _ => .error .InvalidArguments -- Incorrect number of arguments, this case should be impossible if the Yul code is parsed correctly. Guaranteed by the compiler.
      | .STATICCALL =>
        match args with
          | _ :: address_arg :: inOffset :: inSize :: outOffset :: outSize :: _ =>
            if ¬s₀.executionEnv.perm then throw .StaticModeViolation
            let s₀Static : State := setStatic s₀ false
            let address := AccountAddress.ofUInt256 address_arg
            let calldata₁ := s₀Static.toMachineState.memory.readWithPadding inOffset.toNat inSize.toNat
          
              if s₀Static.toSharedState.executionEnv.depth ≥ 1024
              then
                buildContractCallEmptyReturnState s₀Static .none ⟨0⟩ -- Reached depth limit: return 0 to indicate error, with empty return data 
              else
                match s₀Static with
                | .OutOfFuel => .error .OutOfFuel
                | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
                | .Ok sharedState varstore =>
                    match s₀Static.sharedState.accountMap.get? address with
                      | .none => 
                          buildContractCallEmptyReturnState s₀Static .none ⟨1⟩ -- No contract at the provided address, return 1 to indicate success, with empty return data. (Like STOP opcode).
                      | .some yulContract =>
                        let executionEnv₁ := { s₀Static.executionEnv with
                                                  calldata := calldata₁,
                                                  code := yulContract.code,
                                                  codeOwner := address,
                                                  source := s₀Static.executionEnv.codeOwner,
                                                  weiValue := ⟨0⟩
                                                  depth := s₀Static.toSharedState.executionEnv.depth + 1
                                              }
                        let sharedState₁ := { sharedState with
                                                executionEnv := executionEnv₁,
                                                memory := ByteArray.mk #[],
                                            }
                        let s₁ : State := .Ok sharedState₁ default
                        
                        match k .none s₁ with
                          | .error (.YulHalt s₂ _) =>
                          let memory₃ := s₂.toMachineState.H_return.copySlice 0 s₀Static.toMachineState.memory outOffset.toNat (min outSize.toNat s₂.toMachineState.H_return.size)
                          match s₂ with
                            | .OutOfFuel => .error .OutOfFuel
                            | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
                            | .Ok sharedState₂ _ =>
                              -- Restore ExecutionEnv
                              let executionEnv₃ := { sharedState₂.executionEnv with
                                                    calldata := default,
                                                    code := s₀.executionEnv.code,
                                                    codeOwner := s₀.executionEnv.codeOwner,
                                                    source := s₀.executionEnv.source,
                                                    weiValue := s₀.executionEnv.weiValue,
                                                }
                              let sharedState₃ := { sharedState₂ with
                                                      memory := memory₃,
                                                      returnData := s₂.toMachineState.H_return,
                                                      H_return := ByteArray.empty,
                                                      executionEnv := executionEnv₃
                                                  }
                              .ok (setStatic (.Ok sharedState₃ varstore) s₀.executionEnv.perm, [⟨1⟩])
                          | .error e => .error e
                          | .ok (s₂, _) =>
                        
                          let memory₃ := s₂.toMachineState.H_return.copySlice 0 s₀Static.toMachineState.memory outOffset.toNat (min outSize.toNat s₂.toMachineState.H_return.size)
                          match s₂ with
                            | .OutOfFuel => .error .OutOfFuel
                            | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
                            | .Ok sharedState₂ _ =>
                              -- Restore ExecutionEnv
                              let executionEnv₃ := { sharedState₂.executionEnv with
                                                    calldata := default,
                                                    code := s₀.executionEnv.code,
                                                    codeOwner := s₀.executionEnv.codeOwner,
                                                    source := s₀.executionEnv.source,
                                                    weiValue := s₀.executionEnv.weiValue,
                                                }
                              let sharedState₃ := { sharedState₂ with
                                                      memory := memory₃,
                                                      returnData := s₂.toMachineState.H_return,
                                                      H_return := ByteArray.empty,
                                                      executionEnv := executionEnv₃
                                                  }
                              .ok (setStatic (.Ok sharedState₃ varstore) s₀.executionEnv.perm, [⟨1⟩])
          | _ => .error .InvalidArguments -- Incorrect number of arguments, this case should be impossible if the Yul code is parsed correctly. Guaranteed by the compiler.
      | .CALLCODE =>
        match args with
          | _ :: address_arg :: value :: inOffset :: inSize :: outOffset :: outSize :: _ =>
            if ¬s₀.executionEnv.perm ∧ value ≠ ⟨0⟩ then throw .StaticModeViolation
            let address := AccountAddress.ofUInt256 address_arg
            let calldata₁ := s₀.toMachineState.memory.readWithPadding inOffset.toNat inSize.toNat
            let accountMap₁Opt := (s₀.sharedState.accountMap.transferBalance .Yul s₀.executionEnv.codeOwner s₀.executionEnv.codeOwner value)
            match accountMap₁Opt with
              | .none =>
                  buildContractCallEmptyReturnState s₀ .none ⟨0⟩ -- Insufficient funds: return 0 to indicate error, with empty return data 
              | .some accountMap₁ =>
                if s₀.executionEnv.depth ≥ 1024
                then
                  buildContractCallEmptyReturnState s₀ accountMap₁ ⟨0⟩ -- Reached depth limit: return 0 to indicate error, with empty return data 
                else
                  match s₀ with
                  | .OutOfFuel => .error .OutOfFuel
                  | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
                  | .Ok sharedState varstore =>
                      match s₀.sharedState.accountMap.get? address with
                        | .none => 
                            buildContractCallEmptyReturnState s₀ accountMap₁ ⟨1⟩ -- No contract at the provided address, return 1 to indicate success, with empty return data. (Like STOP opcode).
                        | .some yulContract =>
                          let executionEnv₁ := { sharedState.executionEnv with
                                                    calldata := calldata₁,
                                                    code := yulContract.code,
                                                    codeOwner := s₀.executionEnv.codeOwner,
                                                    source := s₀.executionEnv.codeOwner,
                                                    weiValue := value
                                                    depth := s₀.executionEnv.depth + 1
                                                }
                          let sharedState₁ := { sharedState with
                                                  executionEnv := executionEnv₁,
                                                  memory := ByteArray.mk #[],
                                                  accountMap := accountMap₁
                                              }
                          let s₁ : State := .Ok sharedState₁ default
                          
                          match k yulContract.code s₁ with
                          | .error (.YulHalt s₂ _) =>
                            let memory₃ := s₂.toMachineState.H_return.copySlice 0 s₀.toMachineState.memory outOffset.toNat (min outSize.toNat s₂.toMachineState.H_return.size)
                            match s₂ with
                              | .OutOfFuel => .error .OutOfFuel
                              | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
                              | .Ok sharedState₂ _ =>
                                -- Restore ExecutionEnv
                                let executionEnv₃ := { sharedState₂.executionEnv with
                                                    calldata := default,
                                                    code := s₀.executionEnv.code,
                                                    codeOwner := s₀.executionEnv.codeOwner,
                                                    source := s₀.executionEnv.source,
                                                    weiValue := s₀.executionEnv.weiValue,
                                                }
                                let sharedState₃ := { sharedState₂ with
                                                        memory := memory₃,
                                                        returnData := s₂.toMachineState.H_return,
                                                        H_return := ByteArray.empty,
                                                        executionEnv := executionEnv₃
                                                    }
                                .ok (.Ok sharedState₃ varstore, [⟨1⟩])

                          | .error e => .error e
                          | .ok (s₂, _) =>                            
                            let memory₃ := s₂.toMachineState.H_return.copySlice 0 s₀.toMachineState.memory outOffset.toNat (min outSize.toNat s₂.toMachineState.H_return.size)
                            match s₂ with
                              | .OutOfFuel => .error .OutOfFuel
                              | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
                              | .Ok sharedState₂ _ =>
                                -- Restore ExecutionEnv
                                let executionEnv₃ := { sharedState₂.executionEnv with
                                                    calldata := default,
                                                    code := s₀.executionEnv.code,
                                                    codeOwner := s₀.executionEnv.codeOwner,
                                                    source := s₀.executionEnv.source,
                                                    weiValue := s₀.executionEnv.weiValue,
                                                }
                                let sharedState₃ := { sharedState₂ with
                                                        memory := memory₃,
                                                        returnData := s₂.toMachineState.H_return,
                                                        H_return := ByteArray.empty,
                                                        executionEnv := executionEnv₃
                                                    }
                                .ok (.Ok sharedState₃ varstore, [⟨1⟩])
          | _ => .error .InvalidArguments -- Incorrect number of arguments, this case should be impossible if the Yul code is parsed correctly. Guaranteed by the compiler.
      | .DELEGATECALL =>
        match args with
          | _ :: address_arg :: inOffset :: inSize :: outOffset :: outSize :: _ =>
            let address := AccountAddress.ofUInt256 address_arg
            let calldata₁ := s₀.toMachineState.memory.readWithPadding inOffset.toNat inSize.toNat
            if s₀.executionEnv.depth ≥ 1024
            then
              buildContractCallEmptyReturnState s₀ .none ⟨0⟩ -- Reached depth limit: return 0 to indicate error, with empty return data 
            else
              match s₀ with
              | .OutOfFuel => .error .OutOfFuel
              | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
              | .Ok sharedState varstore =>
                  match s₀.sharedState.accountMap.get? address with
                    | .none => 
                      buildContractCallEmptyReturnState s₀ .none ⟨1⟩ -- No contract at the provided address, return 1 to indicate success, with empty return data. (Like STOP opcode).
                    | .some yulContract =>
                      let executionEnv₁ := { sharedState.executionEnv with
                                                calldata := calldata₁,
                                                code := yulContract.code,
                                                codeOwner := s₀.executionEnv.codeOwner
                                                depth := s₀.executionEnv.depth + 1
                                            }
                      let sharedState₁ := { sharedState with
                                              executionEnv := executionEnv₁,
                                              memory := ByteArray.mk #[]
                                          }
                      let s₁ : State := .Ok sharedState₁ default
                      
                      match k yulContract.code s₁ with
                        | .error (.YulHalt s₂ _) =>
                        let memory₃ := s₂.toMachineState.H_return.copySlice 0 s₀.toMachineState.memory outOffset.toNat (min outSize.toNat s₂.toMachineState.H_return.size)
                        match s₂ with
                          | .OutOfFuel => .error .OutOfFuel
                          | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
                          | .Ok sharedState₂ _ =>
                            -- Restore ExecutionEnv
                            let executionEnv₃ := { sharedState₂.executionEnv with
                                                    calldata := default,
                                                    code := s₀.executionEnv.code,
                                                    codeOwner := s₀.executionEnv.codeOwner,
                                                    source := s₀.executionEnv.source,
                                                    weiValue := s₀.executionEnv.weiValue,
                                                }
                            let sharedState₃ := { sharedState₂ with
                                                    memory := memory₃,
                                                    returnData := s₂.toMachineState.H_return,
                                                    H_return := ByteArray.empty,
                                                    executionEnv := executionEnv₃
                                                }
                            .ok (.Ok sharedState₃ varstore, [⟨1⟩])
                        | .error e => .error e
                        | .ok (s₂, _) =>                        
                        let memory₃ := s₂.toMachineState.H_return.copySlice 0 s₀.toMachineState.memory outOffset.toNat (min outSize.toNat s₂.toMachineState.H_return.size)
                        match s₂ with
                          | .OutOfFuel => .error .OutOfFuel
                          | .Checkpoint j => .ok (.Checkpoint j, [⟨0⟩])
                          | .Ok sharedState₂ _ =>
                            -- Restore ExecutionEnv
                            let executionEnv₃ := { sharedState₂.executionEnv with
                                                    calldata := default,
                                                    code := s₀.executionEnv.code,
                                                    codeOwner := s₀.executionEnv.codeOwner,
                                                    source := s₀.executionEnv.source,
                                                    weiValue := s₀.executionEnv.weiValue,
                                                }
                            let sharedState₃ := { sharedState₂ with
                                                    memory := memory₃,
                                                    returnData := s₂.toMachineState.H_return,
                                                    H_return := ByteArray.empty,
                                                    executionEnv := executionEnv₃
                                                }
                            .ok (.Ok sharedState₃ varstore, [⟨1⟩])
          | _ => .error .InvalidArguments -- Incorrect number of arguments, this case should be impossible if the Yul code is parsed correctly. Guaranteed by the compiler.
      | _ => match step prim .none s₀ args with
              | .ok (s, lit) => .ok (s, lit.toList)
              | .error e => .error e

/-- The interpreter's `primCall` with fuel `n + 1` is `primCallK` run with the interpreter's own
dispatcher at fuel `n`. -/
theorem primCall_succ_eq_primCallK (n : ℕ) (s : State) (prim : Operation .Yul)
    (args : List Literal) :
    primCall (n + 1) s prim args = primCallK (callDispatcher n) s prim args := by
  rw [primCall.eq_def]
  rfl

theorem primCall_zero (s : State) (prim : Operation .Yul) (args : List Literal) :
    primCall 0 s prim args = .error .OutOfFuel := by
  rw [primCall.eq_def]

end Relational
end Yul
end EvmYul
