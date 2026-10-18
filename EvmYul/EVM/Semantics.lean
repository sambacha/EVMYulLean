module

public import EvmYul.FFI.Primitives
public import Mathlib.Data.BitVec
public import Mathlib.Data.Array.Defs
public import Mathlib.Data.Finmap
public import Mathlib.Data.List.Defs
public import EvmYul.Stack
public import EvmYul.State.AccountMap
public import EvmYul.State.AccountOps
public import EvmYul.State.ExecutionEnv
public import EvmYul.State.Substate
public import EvmYul.State.TransactionOps

public import EvmYul.EVMException
public import EvmYul.EVM.FrameOutcome
public import EvmYul.EVM.Gas.Costs
public import EvmYul.EVM.Gas.Meter
public import EvmYul.EVM.Gas.ForkCost
public import EvmYul.EVM.Gas.Constants
public import EvmYul.EVM.State
public import EvmYul.EVM.StateOps
public import EvmYul.EVMException
public import EvmYul.EVM.Instr
public import EvmYul.EVM.Decode
public import EvmYul.EVM.PrecompiledContracts.Contracts
public import EvmYul.Operations
public import EvmYul.Pretty
public import EvmYul.SharedStateOps
public import EvmYul.Semantics
public import EvmYul.Wheels
public import EvmYul.EllipticCurves
public import EvmYul.UInt256
public import EvmYul.MachineState

/-!
# The EVM interpreter

The exceptional-halt checks, `step`, `X` (the execution loop), `Ξ` (code execution), `Lambda`
(contract creation), `Θ` (message call) and `Υ` (transaction), with gas charged by the cost model of
`EVM/Gas/` (Yellow Paper §6, §8, §9).
-/


public section

open EvmYul.DebuggingAndProfiling

namespace EvmYul

namespace EVM

def BitVec.ofFn {k} (x : Fin k → Bool) : BitVec k :=
  BitVec.ofNat k (natOfBools (Vector.ofFn x))
  where natOfBools (vec : Vector Bool k) : Nat :=
          (·.1) <| vec.toList.foldl (init := (0, 0)) λ (res, i) bit ↦ (res + 2^i * bit.toNat, i + 1)

def byteAt (μ₀ μ₁ : UInt256) : UInt256 :=
  let v₁ : BitVec 256 := BitVec.ofNat 256 μ₁.1
  let vᵣ : BitVec 256 := BitVec.ofFn (λ i => if i >= 248 && μ₀ < ⟨32⟩
                                             then v₁.getLsbD i
                                             else false)
  EvmYul.UInt256.ofNat (BitVec.toNat vᵣ)

def dup (n : ℕ) : Transformer :=
  λ s ↦
  let top := s.stack.take n
  if top.length = n then
    .ok <| s.replaceStackAndIncrPC (top.getLast! :: s.stack)
  else
    .error .StackUnderflow

def swap (n : ℕ) : Transformer :=
  λ s ↦
  let top := s.stack.take (n + 1)
  let bottom := s.stack.drop (n + 1)
  if List.length top = (n + 1) then
    .ok <| s.replaceStackAndIncrPC (top.getLast! :: top.tail!.dropLast ++ [top.head!] ++ bottom)
  else
    .error .StackUnderflow

local instance : MonadLift Option (Except EVM.ExecutionException) :=
  ⟨Option.option (.error .StackUnderflow) .ok⟩

/--
Compile-time switch for the per-instruction trace printed by `X` (handoff MO-8). Off by default.
Flip it to `true` and rebuild to get one line per executed instruction on stderr.
-/
@[expose] def traceInstructions : Bool := false

/-- `true` iff the (optional) jump target is a member of `l`. -/
@[expose] def jumpTargetBelongs (o : Option UInt256) (l : Array UInt256) : Bool :=
  match o with
    | none => false
    | some n => l.contains n

/-- `true` iff the (optional) jump target is **not** a valid jump destination. -/
@[expose] def jumpTargetNotIn (o : Option UInt256) (l : Array UInt256) : Bool := not (jumpTargetBelongs o l)

/-- (159) Operations that modify the state, forbidden in a static context. -/
@[expose] def modifiesState (w : Operation .EVM) (s : Stack UInt256) : Bool :=
  w ∈ [.CREATE, .CREATE2, .SSTORE, .SELFDESTRUCT, .LOG0, .LOG1, .LOG2, .LOG3, .LOG4, .TSTORE] ∨
  (w = .CALL ∧ s[2]? ≠ some ⟨0⟩)

/--
The non-gas exceptional-halting conditions of `Z` (158), together with the two EIP-mandated
`OutOfGass` conditions that are not "cost exceeds gas": the EIP-2200 SSTORE stipend sentry and the
EIP-3860 initcode-size limit. Run by `exceptionalHaltFs` on the state *after* the accounting
transformer `ForkSchedule.chargeOp` has deducted the memory-expansion cost, in this order: bad jump
destination, return-data bounds, stack overflow, static-mode violation, SSTORE sentry, initcode
size.
-/
@[expose] def haltChecks (fs : ForkSchedule) (validJumps : Array UInt256) (w : Operation .EVM)
    (evmState : State) : Except EVM.ExecutionException Unit := do
  let invalidJump := jumpTargetNotIn evmState.stack[0]? validJumps

  if w = .JUMP ∧ invalidJump then
    .error .BadJumpDestination

  if w = .JUMPI ∧ (evmState.stack[1]? ≠ some ⟨0⟩) ∧ invalidJump then
    .error .BadJumpDestination

  if w = .RETURNDATACOPY ∧ (evmState.stack.getD 1 ⟨0⟩).toNat + (evmState.stack.getD 2 ⟨0⟩).toNat > evmState.returnData.size then
    .error .InvalidMemoryAccess

  if evmState.stack.length - (δ w).getD 0 + (α w).getD 0 > 1024 then
    .error .StackOverflow

  if (¬ evmState.executionEnv.perm) ∧ modifiesState w evmState.stack then
    .error .StaticModeViolation

  if fs.sstoreRule = .netMetered ∧ (w = .SSTORE) ∧ evmState.gasAvailable.toNat ≤ fs.Gcallstipend then
    .error .OutOfGass

  match fs.maxInitcodeSize with
  | some limit =>
    if w.isCreate ∧ evmState.stack.getD 2 ⟨0⟩ > .ofNat limit then
      .error .OutOfGass
  | none => pure ()

/--
Exceptional halting `Z` (158) under the gas schedule `fs`, split into its two independent parts:

1. the **accounting transformer** `ForkSchedule.chargeOp` (in `EvmYul/EVM/Gas/ForkCost.lean`): the
   stack guard (`InvalidInstruction`, then `StackUnderflow`), then the pure cost
   `ForkSchedule.costParts` (memory expansion and instruction part, computed only after the guard,
   with `Option`-valued operand reads), the guarded deduction of the memory part, and the
   `OutOfGass` check of the instruction part;
2. the remaining halting conditions `haltChecks`, on the post-memory state.

On success it returns the post-memory state and the instruction cost, which `step` deducts with
`GasMeter.deductPrechecked` (after `call` has computed the forwarded gas from the post-memory gas,
as the 63/64 rule requires).
-/
@[expose] def exceptionalHaltFs (fs : ForkSchedule) (validJumps : Array UInt256) (w : Operation .EVM)
    (evmState : State) : Except EVM.ExecutionException (State × ℕ) := do
  let (evmState, cost₂) ← fs.chargeOp evmState w
  haltChecks fs validJumps w evmState
  pure (evmState, cost₂)

/--
Exceptional halting `Z` (158) as executed by `X`: `exceptionalHaltFs` at the Cancun schedule.
`EvmYul/EVM/Gas/ForkCostBridge.lean` proves that it is equal, for every input, to the previous
definition (`exceptionalHalt_eq_prev`), which evaluated `memoryExpansionCost` and `C'` with `!`
operand reads; the interpreter's behaviour, and hence the conformance results, are unchanged.
-/
@[expose] def exceptionalHalt (validJumps : Array UInt256) (w : Operation .EVM) (evmState : State) :
    Except EVM.ExecutionException (State × ℕ) :=
  exceptionalHaltFs ForkSchedule.cancun validJumps w evmState

/--
Run the precompiled contract at address `p` (YP Appendix E) on world state `σ₁`, gas `g`, substate
`A` and environment `I`, returning the frame outcome, `σ'`, the remaining gas, `A'` and the output.

Addresses other than 1–10 are unreachable through `toExecute` (it only yields `Precompiled` for
addresses in `π`). For them the call fails (`z = false`, empty state ⇒ `σ` and `A` are kept by
(127)/(129) in `Θ`) and all gas is consumed. (This used to be `default`, which for the result monad
of `Θ` is a *successful* result with an empty created-accounts set.)

Factored out of `Θ` so that properties of the ten precompiles can be stated about a function with
variable arguments; `Θ` calls it unchanged (the two definitions are definitionally equal to the
former inline `match`).
-/
@[expose] def precompileDispatch (p : AccountAddress) (σ₁ : AccountMap .EVM) (g : UInt256) (A : Substate)
    (I : ExecutionEnv .EVM) : FrameOutcome × AccountMap .EVM × UInt256 × Substate × ByteArray :=
  match p with
  | 1  => FrameOutcome.ofPrecompile (Ξ_ECREC σ₁ g A I)
  | 2  => FrameOutcome.ofPrecompile (Ξ_SHA256 σ₁ g A I)
  | 3  => FrameOutcome.ofPrecompile (Ξ_RIP160 σ₁ g A I)
  | 4  => FrameOutcome.ofPrecompile (Ξ_ID σ₁ g A I)
  | 5  => FrameOutcome.ofPrecompile (Ξ_EXPMOD σ₁ g A I)
  | 6  => FrameOutcome.ofPrecompile (Ξ_BN_ADD σ₁ g A I)
  | 7  => FrameOutcome.ofPrecompile (Ξ_BN_MUL σ₁ g A I)
  | 8  => FrameOutcome.ofPrecompile (Ξ_SNARKV σ₁ g A I)
  | 9  => FrameOutcome.ofPrecompile (Ξ_BLAKE2_F σ₁ g A I)
  | 10 => FrameOutcome.ofPrecompile (Ξ_PointEval σ₁ g A I)
  | _  => (.exceptionalHalt, ∅, ⟨0⟩, A, .empty)

mutual

@[expose] def call (fuel : Nat)
  (gasCost : Nat)
  (blobVersionedHashes : List ByteArray)
  (gas source recipient t value value' inOffset inSize outOffset outSize : UInt256)
  (permission : Bool)
  (evmState : State)
    :
  Except EVM.ExecutionException (UInt256 × State)
:= do
  match fuel with
    | 0 => .error .OutOfFuel
    | .succ f =>
      let t : AccountAddress := AccountAddress.ofUInt256 t
      let recipient : AccountAddress := AccountAddress.ofUInt256 recipient
      let source : AccountAddress := AccountAddress.ofUInt256 source
      let Iₐ := evmState.executionEnv.codeOwner
      let σ := evmState.accountMap
      let Iₑ := evmState.executionEnv.depth
      let callgas := Ccallgas t recipient value gas σ evmState.toMachineState evmState.substate
      let evmState := {evmState with gasAvailable := GasMeter.deductPrechecked evmState.gasAvailable gasCost}
      -- m[μs[3] . . . (μs[3] + μs[4] − 1)]
      let i := evmState.memory.readWithPadding inOffset.toNat inSize.toNat
      let A' := evmState.addAccessedAccount t |>.substate
      let (cA, σ', g', A', z, o) ← do
        if value ≤ (σ.get? Iₐ |>.option ⟨0⟩ (·.balance)) ∧ Iₑ < 1024 then
          let resultOfΘ ←
            Θ (fuel := f)
              blobVersionedHashes
              (createdAccounts := evmState.createdAccounts)
              (genesisBlockHeader := evmState.genesisBlockHeader)
              (blocks := evmState.blocks)
              (σ  := σ)                                     -- σ in  Θ(σ, ..)
              (σ₀ := evmState.σ₀)
              (A  := A')                                    -- A* in Θ(.., A*, ..)
              (s  := source)
              (o  := evmState.executionEnv.sender)          -- Iₒ in Θ(.., Iₒ, ..)
              (r  := recipient)                             -- t in Θ(.., t, ..)
              (c  := toExecute .EVM σ t)
              (g  := .ofNat callgas)
              (p  := .ofNat evmState.executionEnv.gasPrice) -- Iₚ in Θ(.., Iₚ, ..)
              (v  := value)
              (v' := value')
              (d  := i)
              (e  := Iₑ + 1)
              (H := evmState.executionEnv.header)
              (w  := permission)                            -- I_w in Θ(.., I_W)
          pure resultOfΘ.toTuple
        else
          -- otherwise (σ, CCALLGAS(σ, μ, A), A, 0, ())
          .ok
            (evmState.createdAccounts, evmState.toState.accountMap, .ofNat callgas, A', false, .empty)
      -- n ≡ min({μs[6], ‖o‖})
      let n : UInt256 := min outSize (.ofNat o.size)

      let μ'ₘ := writeBytes o 0 evmState.toMachineState outOffset.toNat n.toNat -- μ′_m[μs[5]  ... (μs[5] + n − 1)] = o[0 ... (n − 1)]
      let μ'ₒ := o -- μ′o = o
      let μ'_g := μ'ₘ.gasAvailable + g' -- Ccall is subtracted in X as part of C

      let codeExecutionFailed   : Bool := !z
      let notEnoughFunds        : Bool := value > (σ.get? evmState.executionEnv.codeOwner |>.elim ⟨0⟩ (·.balance)) -- TODO - Unify condition with CREATE.
      let callDepthLimitReached : Bool := evmState.executionEnv.depth == 1024
      let x : UInt256 := if codeExecutionFailed || notEnoughFunds || callDepthLimitReached then ⟨0⟩ else ⟨1⟩ -- where x = 0 if the code execution for this operation failed, or if μs[2] > σ[Ia]b (not enough funds) or Ie = 1024 (call depth limit reached); x = 1 otherwise.

      -- NB. `MachineState` here does not contain the `Stack` nor the `PC`, thus incomplete.
      let μ'incomplete : MachineState :=
        { μ'ₘ with
            returnData   := μ'ₒ
            gasAvailable := μ'_g
            activeWords :=
              let m : ℕ:= MachineState.M evmState.toMachineState.activeWords.toNat inOffset.toNat inSize.toNat
              .ofNat <| MachineState.M m outOffset.toNat outSize.toNat

        }

      let result : State := { evmState with accountMap := σ', substate := A', createdAccounts := cA }
      let result := {
        result with toMachineState := μ'incomplete
      }
      .ok (x, result)

@[expose] def step (fuel : ℕ) (gasCost : ℕ) (instr : Option (Operation .EVM × Option (UInt256 × Nat)) := .none)
  : EVM.Transformer
:=
  match fuel with
    | 0 => λ _ ↦ .error .OutOfFuel
    | .succ f =>
    λ (evmState : EVM.State) ↦ do
    -- This will normally be called from `Ξ` (or `X`) with `fetchInstr` already having been called.
    -- That said, we sometimes want a `step : EVM.Transformer` and as such, we can decode on demand.
    let (instr, arg) ←
      match instr with
        | .none => fetchInstr evmState.toState.executionEnv evmState.pc
        | .some (instr, arg) => pure (instr, arg)
    let evmState := { evmState with execLength := evmState.execLength + 1 }
    match instr with
      | .CREATE =>
        let evmState := {evmState with gasAvailable := GasMeter.deductPrechecked evmState.gasAvailable gasCost}
        match evmState.stack.pop3 with
          | some ⟨stack, μ₀, μ₁, μ₂⟩ => do
            let i := evmState.memory.readWithPadding μ₁.toNat μ₂.toNat
            let ζ := none
            let I := evmState.executionEnv
            let Iₐ := evmState.executionEnv.codeOwner
            let Iₒ := evmState.executionEnv.sender
            let Iₑ := evmState.executionEnv.depth
            let σ := evmState.accountMap
            let σ_Iₐ : Account .EVM := σ.get? Iₐ |>.getD default
            let σStar := σ.insert Iₐ {σ_Iₐ with nonce := σ_Iₐ.nonce + ⟨1⟩}

            let createResult
                  : Except EVM.ExecutionException
                      (AccountAddress × EVM.State × UInt256 × Bool × ByteArray)
              :=
              if σ_Iₐ.nonce.toNat ≥ 2^64-1 then pure (default, evmState, .ofNat (L evmState.gasAvailable.toNat), False, .empty) else
              if μ₀ ≤ (σ.get? Iₐ |>.option ⟨0⟩ (·.balance)) ∧ Iₑ < 1024 ∧ i.size ≤ 49152 then
                let Λ :=
                  Lambda f
                    evmState.executionEnv.blobVersionedHashes
                    evmState.createdAccounts
                    evmState.genesisBlockHeader
                    evmState.blocks
                    σStar
                    evmState.σ₀
                    evmState.toState.substate
                    Iₐ
                    Iₒ
                    (.ofNat <| L evmState.gasAvailable.toNat)
                    (.ofNat I.gasPrice)
                    μ₀
                    i
                    (.ofNat <| Iₑ + 1)
                    ζ
                    I.header
                    I.perm
                match Λ with
                  | .ok r =>
                    pure
                    ( r.address
                    , { evmState with
                          accountMap := r.accountMap
                          substate := r.substate
                          createdAccounts := r.createdAccounts
                      }
                    , r.gasLeft
                    , r.outcome.isSuccess
                    , r.output
                    )
                  -- Running out of fuel is not an EVM outcome: pass it on, as `Θ` and `Lambda` do
                  -- (review O-2). Previously this catch-all replaced the caller's world state by `∅`.
                  | .error .OutOfFuel => throw .OutOfFuel
                  -- The only other error `Lambda` can raise is a failed address derivation (`L_A`);
                  -- treat it like an exceptional halt of the init code: creation fails, all gas
                  -- handed to it is consumed, and the caller keeps `σ*` (its nonce bump), exactly as
                  -- `Lambda`'s own exceptional-halt branch returns its input state.
                  | .error _ => pure (0, {evmState with accountMap := σStar}, ⟨0⟩, False, .empty)
              else
                pure (0, evmState, .ofNat (L evmState.gasAvailable.toNat), False, .empty)
            let (a, evmState', g', z, o) ← createResult
            let x : UInt256 :=
              let balance := σ.get? Iₐ |>.option ⟨0⟩ (·.balance)
                if z = false ∨ Iₑ = 1024 ∨ μ₀ > balance ∨ i.size > 49152 then ⟨0⟩ else .ofNat a
            let newReturnData : ByteArray := if z then .empty else o
            if (evmState.gasAvailable + g').toNat < L (evmState.gasAvailable.toNat) then
              .error .OutOfGass
            let evmState' :=
              { evmState' with
                  activeWords := .ofNat <| MachineState.M evmState.activeWords.toNat μ₁.toNat μ₂.toNat
                  returnData := newReturnData
                  gasAvailable :=
                    .ofNat <| evmState.gasAvailable.toNat - L (evmState.gasAvailable.toNat) + g'.toNat
              }
            .ok <| evmState'.replaceStackAndIncrPC (stack.push x)
          | _ =>
          .error .StackUnderflow
      | .CREATE2 =>
        -- Exactly equivalent to CREATE except ζ ≡ μₛ[3]
        let evmState := {evmState with gasAvailable := GasMeter.deductPrechecked evmState.gasAvailable gasCost}
        match evmState.stack.pop4 with
          | some ⟨stack, μ₀, μ₁, μ₂, μ₃⟩ => do
            let i := evmState.memory.readWithPadding μ₁.toNat μ₂.toNat
            let ζ := EvmYul.UInt256.toByteArray μ₃
            let I := evmState.executionEnv
            let Iₐ := evmState.executionEnv.codeOwner
            let Iₒ := evmState.executionEnv.sender
            let Iₑ := evmState.executionEnv.depth
            let σ := evmState.accountMap
            let σ_Iₐ : Account .EVM := σ.get? Iₐ |>.getD default
            let σStar := σ.insert Iₐ {σ_Iₐ with nonce := σ_Iₐ.nonce + ⟨1⟩}
            let createResult
                  : Except EVM.ExecutionException
                      (AccountAddress × EVM.State × UInt256 × Bool × ByteArray)
              :=
              if σ_Iₐ.nonce.toNat ≥ 2^64-1 then pure (default, evmState, .ofNat (L evmState.gasAvailable.toNat), False, .empty) else
              if μ₀ ≤ (σ.get? Iₐ |>.option ⟨0⟩ (·.balance)) ∧ Iₑ < 1024 ∧ i.size ≤ 49152 then
                let Λ :=
                  Lambda f
                    evmState.executionEnv.blobVersionedHashes
                    evmState.createdAccounts
                    evmState.genesisBlockHeader
                    evmState.blocks
                    σStar
                    evmState.σ₀
                    evmState.toState.substate
                    Iₐ
                    Iₒ
                    (.ofNat <| L evmState.gasAvailable.toNat)
                    (.ofNat I.gasPrice)
                    μ₀
                    i
                    (.ofNat <| Iₑ + 1)
                    ζ
                    I.header
                    I.perm
                match Λ with
                  | .ok r =>
                    pure
                      ( r.address
                      , { evmState with
                            accountMap := r.accountMap
                            substate := r.substate
                            createdAccounts := r.createdAccounts }
                      , r.gasLeft, r.outcome.isSuccess, r.output)
                  -- Running out of fuel is not an EVM outcome: pass it on, as `Θ` and `Lambda` do
                  -- (review O-2). Previously this catch-all replaced the caller's world state by `∅`.
                  | .error .OutOfFuel => throw .OutOfFuel
                  -- The only other error `Lambda` can raise is a failed address derivation (`L_A`);
                  -- treat it like an exceptional halt of the init code: creation fails, all gas
                  -- handed to it is consumed, and the caller keeps `σ*` (its nonce bump), exactly as
                  -- `Lambda`'s own exceptional-halt branch returns its input state.
                  | .error _ => pure (0, {evmState with accountMap := σStar}, ⟨0⟩, False, .empty)
              else
                pure (0, evmState, .ofNat (L evmState.gasAvailable.toNat), False, .empty)
            let (a, evmState', g', z, o) ← createResult
            let x : UInt256 :=
              let balance := σ.get? Iₐ |>.option ⟨0⟩ (·.balance)
                if z = false ∨ Iₑ = 1024 ∨ μ₀ > balance ∨ i.size > 49152 then ⟨0⟩ else .ofNat a
            let newReturnData : ByteArray := if z then .empty else o
            if (evmState.gasAvailable + g').toNat < L evmState.gasAvailable.toNat then
              .error .OutOfGass
            let evmState' :=
              { evmState' with
                activeWords := .ofNat <| MachineState.M evmState.activeWords.toNat μ₁.toNat μ₂.toNat
                returnData := newReturnData
                gasAvailable := .ofNat <| evmState.gasAvailable.toNat - L (evmState.gasAvailable.toNat) + g'.toNat
              }
            .ok <| evmState'.replaceStackAndIncrPC (stack.push x)
          | _ =>
          .error .StackUnderflow
      | .CALL => do
        -- Names are from the YP, these are:
        -- μ₀ - gas
        -- μ₁ - to
        -- μ₂ - value
        -- μ₃ - inOffset
        -- μ₄ - inSize
        -- μ₅ - outOffsize
        -- μ₆ - outSize
        let (stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆) ← evmState.stack.pop7
        let (x, state') ←
          call f gasCost evmState.executionEnv.blobVersionedHashes μ₀ (.ofNat evmState.executionEnv.codeOwner) μ₁ μ₁ μ₂ μ₂ μ₃ μ₄ μ₅ μ₆ evmState.executionEnv.perm evmState
        let μ'ₛ := stack.push x -- μ′s[0] ≡ x
        let evmState' := state'.replaceStackAndIncrPC μ'ₛ
        .ok evmState'
      | .CALLCODE =>
        do
        -- Names are from the YP, these are:
        -- μ₀ - gas
        -- μ₁ - to
        -- μ₂ - value
        -- μ₃ - inOffset
        -- μ₄ - inSize
        -- μ₅ - outOffsize
        -- μ₆ - outSize
        let (stack, μ₀, μ₁, μ₂, μ₃, μ₄, μ₅, μ₆) ← evmState.stack.pop7
        let (x, state') ←
          call f gasCost evmState.executionEnv.blobVersionedHashes μ₀ (.ofNat evmState.executionEnv.codeOwner) (.ofNat evmState.executionEnv.codeOwner) μ₁ μ₂ μ₂ μ₃ μ₄ μ₅ μ₆ evmState.executionEnv.perm evmState
        let μ'ₛ := stack.push x -- μ′s[0] ≡ x
        let evmState' := state'.replaceStackAndIncrPC μ'ₛ
        .ok evmState'
      | .DELEGATECALL =>
        do
        -- Names are from the YP, these are:
        -- μ₀ - gas
        -- μ₁ - to
        -- μ₃ - inOffset
        -- μ₄ - inSize
        -- μ₅ - outOffsize
        -- μ₆ - outSize
        let (stack, μ₀, μ₁, /-μ₂,-/ μ₃, μ₄, μ₅, μ₆) ← evmState.stack.pop6
        let (x, state') ←
          call f gasCost evmState.executionEnv.blobVersionedHashes μ₀ (.ofNat evmState.executionEnv.source) (.ofNat evmState.executionEnv.codeOwner) μ₁ ⟨0⟩ evmState.executionEnv.weiValue μ₃ μ₄ μ₅ μ₆ evmState.executionEnv.perm evmState
        let μ'ₛ := stack.push x -- μ′s[0] ≡ x
        let evmState' := state'.replaceStackAndIncrPC μ'ₛ
        .ok evmState'
      | .STATICCALL =>
        do
        -- Names are from the YP, these are:
        -- μ₀ - gas
        -- μ₁ - to
        -- μ₂ - value
        -- μ₃ - inOffset
        -- μ₄ - inSize
        -- μ₅ - outOffsize
        -- μ₆ - outSize
        let (stack, μ₀, μ₁, /- μ₂, -/ μ₃, μ₄, μ₅, μ₆) ← evmState.stack.pop6
        let (x, state') ←
          call f gasCost evmState.executionEnv.blobVersionedHashes μ₀ (.ofNat evmState.executionEnv.codeOwner) μ₁ μ₁ ⟨0⟩ ⟨0⟩ μ₃ μ₄ μ₅ μ₆ false evmState
        let μ'ₛ := stack.push x -- μ′s[0] ≡ x
        let evmState' := state'.replaceStackAndIncrPC μ'ₛ
        .ok evmState'
      | instr => EvmYul.step instr arg {evmState with gasAvailable := GasMeter.deductPrechecked evmState.gasAvailable gasCost}

/--
  Iterative progression of `step`
-/
@[expose] def X (fuel : ℕ) (validJumps : Array UInt256) (evmState : State)
  : Except EVM.ExecutionException (ExecutionResult State)
:= do
  match fuel with
    | 0 => .error .OutOfFuel
    | .succ f =>
      let I_b := evmState.toState.executionEnv.code
      let instr@(w, _) := decode I_b evmState.pc |>.getD (.STOP, .none)
      -- Opt-in per-instruction trace (handoff MO-8 / C5). `dbg_trace m; x` is logically `x`, so this
      -- line has no semantic effect; the result feeds the rest of `X`, so the trace really fires
      -- when the flag is set (unlike the former unused `let _ := dbg_trace …` in `EvmYul.step`).
      let evmState := if traceInstructions then dbg_trace w.pretty; evmState else evmState
      let H (μ : MachineState) (w : Operation .EVM) : Option ByteArray :=
        if w ∈ [.RETURN, .REVERT] then
          some <| μ.H_return
        else
          if w ∈ [.STOP, .SELFDESTRUCT] then
            some .empty
          else none
      match exceptionalHalt validJumps w evmState with
        | .error e =>
          .error e
        | some (evmState, cost₂) =>
          let evmState' ← step f cost₂ instr evmState
          -- Maybe we should restructure in a way such that it is more meaningful to compute
          -- gas independently, but the model has not been set up thusly and it seems
          -- that neither really was the YP.
          -- Similarly, we cannot reach a situation in which the stack elements are not available
          -- on the stack because this is guarded above. As such, `C` can be pure here.
          match H evmState'.toMachineState w with -- The YP does this in a weird way.
            | none => X f validJumps evmState'
            | some o =>
              if w == .REVERT then
                /-
                  Requirement (EIP-140): `REVERT` halts like `RETURN` — it charges its memory
                  expansion, reads its output from memory and hands the remaining gas back to the
                  caller — but discards the state changes. So the instruction's own semantics must
                  run (`step` above) before halting, even though the Yellow Paper's definition of
                  `X` does not apply the iterator `O` for `REVERT`; the gas returned is the gas left
                  *after* `REVERT`'s charges. EELS's `revert` instruction does the same.
                -/
                .ok <| .revert evmState'.gasAvailable o
              else
                .ok <| .success evmState' o

/--
  The code execution function
-/
@[expose] def Ξ -- Type `Ξ` using `\GX` or `\Xi`
  (fuel : ℕ)
  (createdAccounts : Std.TreeSet AccountAddress compare)
  (genesisBlockHeader : BlockHeader)
  (blocks : ProcessedBlocks)
  (σ : AccountMap .EVM)
  (σ₀ : AccountMap .EVM)
  (g : UInt256)
  (A : Substate)
  (I : ExecutionEnv .EVM)
    :
  Except
    EVM.ExecutionException
    (ExecutionResult (Std.TreeSet AccountAddress compare × AccountMap .EVM × UInt256 × Substate))
:= do
  match fuel with
    | 0 => .error .OutOfFuel
    | .succ f =>
      let defState : EVM.State := default
      let freshEvmState : EVM.State :=
        { defState with
            accountMap := σ
            σ₀ := σ₀
            executionEnv := I
            substate := A
            createdAccounts := createdAccounts
            gasAvailable := g
            blocks := blocks
            genesisBlockHeader := genesisBlockHeader
        }
      let result ← X f (D_J I.code ⟨0⟩) freshEvmState
      match result with
        | .success evmState' o =>
          let finalGas := evmState'.gasAvailable
          .ok (ExecutionResult.success (evmState'.createdAccounts, evmState'.accountMap, finalGas, evmState'.substate) o)
        | .revert g' o => .ok (ExecutionResult.revert g' o)

@[expose] def Lambda
  (fuel : ℕ)
  (blobVersionedHashes : List ByteArray)
  (createdAccounts : Std.TreeSet AccountAddress compare) -- needed for EIP-6780
  (genesisBlockHeader : BlockHeader)
  (blocks : ProcessedBlocks)
  (σ : AccountMap .EVM)
  (σ₀ : AccountMap .EVM)
  (A : Substate)
  (s : AccountAddress)   -- sender
  (o : AccountAddress)   -- original transactor
  (g : UInt256)          -- available gas
  (p : UInt256)          -- gas price
  (v : UInt256)          -- endowment
  (i : ByteArray)        -- the initialisation EVM code
  (e : UInt256)          -- depth of the message-call/contract-creation stack
  (ζ : Option ByteArray) -- the salt (92)
  (H : BlockHeader)      -- "I_H has no special treatment and is determined from the blockchain"
  (w : Bool)             -- permission to make modifications to the state
  :
  Except EVM.ExecutionException CreateResult
:=
  match fuel with
    | 0 => .error .OutOfFuel
    | .succ f => do

  -- EIP-3860 (includes EIP-170)
  -- https://eips.ethereum.org/EIPS/eip-3860

  let n : UInt256 := (σ.get? s |>.option ⟨0⟩ (·.nonce)) - ⟨1⟩
  let lₐ ← L_A s n ζ i
  let a : AccountAddress := -- (94) (95)
    (ffi.KEC lₐ).extract 12 32 /- 160 bits = 20 bytes -/
      |> fromByteArrayBigEndian |> Fin.ofNat _

  -- A* (97)
  let AStar := A.addAccessedAccount a
  -- σ*
  let existentAccount := σ.getD a default

  /-
    https://eips.ethereum.org/EIPS/eip-7610
    If a contract creation is attempted due to a creation transaction,
    the CREATE opcode, the CREATE2 opcode, or any other reason,
    and the destination address already has either a nonzero nonce,
    a nonzero code length, or non-empty storage, then the creation MUST throw
    as if the first byte in the init code were an invalid opcode.
  -/
  let (i, createdAccounts) :=
    if
      existentAccount.nonce ≠ ⟨0⟩
        || existentAccount.code.size ≠ 0
        || existentAccount.storage != default
    then
      (⟨#[0xfe]⟩, createdAccounts)
    else (i, createdAccounts.insert a)

  let newAccount : Account .EVM :=
    { existentAccount with
        nonce := existentAccount.nonce + ⟨1⟩
        balance := v + existentAccount.balance
    }

  -- If `v` ≠ 0 then the sender must have passed the `INSUFFICIENT_ACCOUNT_FUNDS` check
  let σStar :=
    match σ.get? s with
      | none =>  σ
      | some ac =>
        σ.insert s {ac with balance := ac.balance - v}
          |>.insert a newAccount -- (99)
  -- I
  let exEnv : ExecutionEnv .EVM :=
    { codeOwner := a
    , sender    := o
    , source    := s
    , weiValue  := v
    , calldata := default
    , code      := i
    , gasPrice  := p.toNat
    , header    := H
    , depth     := e.toNat
    , perm      := w
    , blobVersionedHashes := blobVersionedHashes
    }
  match Ξ f createdAccounts genesisBlockHeader blocks σStar σ₀ g AStar exEnv with
    | .error e =>
      if e == .OutOfFuel then throw .OutOfFuel
      .ok { address := a, createdAccounts, accountMap := σ, gasLeft := ⟨0⟩, substate := AStar,
            outcome := .exceptionalHalt, output := .empty }
    | .ok (.revert g' o) =>
      .ok { address := a, createdAccounts, accountMap := σ, gasLeft := g', substate := AStar,
            outcome := .revert, output := o }
    | .ok (.success (createdAccounts', σStarStar, gStarStar, AStarStar) returnedData) =>
      -- The code-deposit cost (113)
      let c := GasConstants.Gcodedeposit * returnedData.size

      let F : Bool := Id.run do -- (118)
        let F₀ : Bool :=
          match σ.get? a with
          | .some ac => ac.code ≠ .empty ∨ ac.nonce ≠ ⟨0⟩
          | .none => false
        let F₂ : Bool := gStarStar.toNat < c
        let MAX_CODE_SIZE := 24576
        let F₃ : Bool := returnedData.size > MAX_CODE_SIZE
        let F₄ : Bool := ¬F₃ && returnedData[0]? = some 0xef
        pure (F₀ ∨ F₂ ∨ F₃ ∨ F₄)

      let σ' : AccountMap .EVM := -- (115)
        if F then σ else
          let newAccount' := σStarStar.getD a default
          σStarStar.insert a {newAccount' with code := returnedData}

      -- (114)
      let g' := if F then 0 else gStarStar.toNat - c

      -- (116)
      let A' := if F then AStar else AStarStar
      -- (117): `z = not F`; a failed code deposit is an exceptional halt.
      let outcome : FrameOutcome := if F then .exceptionalHalt else .success
      .ok { address := a, createdAccounts := createdAccounts', accountMap := σ', gasLeft := .ofNat g',
            substate := A', outcome, output := .empty } -- (93)
 where
  L_A (s : AccountAddress) (n : UInt256) (ζ : Option ByteArray) (i : ByteArray) :
    Option ByteArray
  := -- (96)
    let s := s.toByteArray
    let n := BE n.toNat
    match ζ with
      | none   => RLP <| .𝕃 [.𝔹 s, .𝔹 n]
      | some ζ => .some <| BE 255 ++ s ++ ζ ++ ffi.KEC i

/--
Message cal
`σ`  - evm state
`A`  - accrued substate
`s`  - sender
`o`  - transaction originator
`r`  - recipient
`c`  - the account whose code is to be called, usually the same as `r`
`g`  - available gas
`p`  - effective gas price
`v`  - value
`v'` - value in the execution context
`d`  - input data of the call
`e`  - depth of the message-call / contract-creation stack
`w`  - permissions to make modifications to the stack

NB - This is implemented using the 'boolean' fragment with ==, <=, ||, etc.
     The 'prop' version will come next once we have the comutable one.
-/
@[expose] def Θ (fuel : Nat)
      (blobVersionedHashes : List ByteArray)
      (createdAccounts : Std.TreeSet AccountAddress compare)
      (genesisBlockHeader : BlockHeader)
      (blocks : ProcessedBlocks)
      (σ  : AccountMap .EVM)
      (σ₀  : AccountMap .EVM)
      (A  : Substate)
      (s  : AccountAddress)
      (o  : AccountAddress)
      (r  : AccountAddress)
      (c  : ToExecute .EVM)
      (g  : UInt256)
      (p  : UInt256)
      (v  : UInt256)
      (v' : UInt256)
      (d  : ByteArray)
      (e  : Nat)
      (H : BlockHeader)
      (w  : Bool)
        :
      Except EVM.ExecutionException FrameResult
:=
  match fuel with
    | 0 => .error .OutOfFuel
    | fuel + 1 => do

  -- (124) (125) (126)
  let σ'₁ :=
    match σ.get? r with
      | none =>
        if v != (⟨0⟩ : UInt256) then
          σ.insert r { (default : Account .EVM) with balance := v}
        else
          σ
      | some acc =>
        σ.insert r { acc with balance := acc.balance + v}

  -- If `v` ≠ 0 then the sender must have passed the `INSUFFICIENT_ACCOUNT_FUNDS` check
  let σ₁ :=
    match σ'₁.get? s with
      | none => σ'₁
      | some acc =>
        σ'₁.insert s { acc with balance := acc.balance - v}

  let I : ExecutionEnv .EVM :=
    {
      codeOwner := r        -- Equation (132)
      sender    := o        -- Equation (133)
      gasPrice  := p.toNat  -- Equation (134)
      calldata := d        -- Equation (135)
      source    := s        -- Equation (136)
      weiValue  := v'       -- Equation (137)
      depth     := e        -- Equation (138)
      perm      := w        -- Equation (139)
      -- Note that we don't use an address, but the actual code. Equation (141)-ish.
      code      :=
        match c with
          | ToExecute.Precompiled _ => default
          | ToExecute.Code code => code
      header    := H
      blobVersionedHashes := blobVersionedHashes
    }

  -- Equation (131)
  -- Note that the `c` used here is the actual code, not the address. TODO - Handle precompiled contracts.
  let (createdAccounts, outcome, σ'', g', A'', out) ←
    match c with
      | ToExecute.Precompiled p =>
        -- A precompile creates no accounts, so the set of accounts created in this transaction
        -- (EIP-6780) is passed through unchanged, exactly as the code branch below does on revert
        -- and on exceptional halt (review O-1; this slot used to be `∅`).
        .ok (createdAccounts, precompileDispatch p σ₁ g A I)
      | ToExecute.Code _ =>
        match Ξ fuel createdAccounts genesisBlockHeader blocks σ₁ σ₀ g A I with
          | .error e =>
            if e == .OutOfFuel then throw .OutOfFuel
            pure (createdAccounts, .exceptionalHalt, σ, ⟨0⟩, A, .empty)
          | .ok (.revert g' o) =>
            pure (createdAccounts, .revert, σ, g', A, o)
          | .ok (.success (a, b, c, d) o) =>
            pure (a, .success, b, c, d, o)

  -- Equation (127)
  let σ' := if σ'' == ∅ then σ else σ''

  -- Equation (129)
  let A' := if σ'' == ∅ then A else A''

  -- Equation (119); the success flag `z` is `outcome.isSuccess`.
  .ok { createdAccounts, accountMap := σ', gasLeft := g', substate := A', outcome, output := out }

end



-- Type Υ using \Upsilon or \GU
@[expose] def Υ (fuel : ℕ)
  (σ : AccountMap .EVM)
  (H_f : ℕ)
  (H : BlockHeader)
  (genesisBlockHeader : BlockHeader)
  (blocks : ProcessedBlocks)
  (T : Transaction)
  (S_T : AccountAddress)
  : Except EVM.Exception (AccountMap .EVM × Substate × Bool × UInt256)
:= do
  let g₀ : ℕ := EVM.intrinsicGas T
  -- "here can be no invalid transactions from this point"
  let senderAccount := (σ.get? S_T).get!
  -- The priority fee (67)
  let f :=
    match T with
      | .legacy t | .access t =>
            t.gasPrice - .ofNat H_f
      | .dynamic t | .blob t =>
            min t.maxPriorityFeePerGas (t.maxFeePerGas - .ofNat H_f)
  -- The effective gas price
  let p := -- (66)
    match T with
      | .legacy t | .access t => t.gasPrice
      | .dynamic _ | .blob _ => f + .ofNat H_f
  let senderAccount :=
    { senderAccount with
        /-
          https://eips.ethereum.org/EIPS/eip-4844
          "The actual blob_fee as calculated via calc_blob_fee is deducted from
          the sender balance before transaction execution and burned, and is not
          refunded in case of transaction failure."
        -/
        balance := senderAccount.balance - T.base.gasLimit * p - .ofNat (calcBlobFee H T)  -- (74)
        nonce := senderAccount.nonce + ⟨1⟩ -- (75)
    }
  -- The checkpoint state (73)
  let σ₀ := σ.insert S_T senderAccount
  let accessList := T.getAccessList
  let AStar_K : List (AccountAddress × UInt256) := do -- (78)
    let ⟨Eₐ, Eₛ⟩ ← accessList
    let eₛ ← Eₛ.toList
    pure (Eₐ, eₛ)
  let a := -- (80)
    A0.accessedAccounts.insert S_T
      |>.insert H.beneficiary
      |>.union <| Std.TreeSet.ofList (accessList.map Prod.fst) compare
  -- (81)
  let g := .ofNat <| T.base.gasLimit.toNat - g₀
  let AStarₐ := -- (79)
    match T.base.recipient with
      | some t => a.insert t
      | none => a
  let AStar := -- (77)
    { A0 with accessedAccounts := AStarₐ, accessedStorageKeys := Std.TreeSet.ofList AStar_K Substate.storageKeysCmp}
  let createdAccounts : Std.TreeSet AccountAddress compare := .empty
  let (/- provisional state -/ σ_P, g', A, z) ← -- (76)
    match T.base.recipient with
      | none => do
        match
          Lambda fuel
            T.blobVersionedHashes
            createdAccounts
            genesisBlockHeader
            blocks
            σ₀
            σ₀
            AStar
            S_T
            S_T
            g
            p
            T.base.value
            T.base.data
            ⟨0⟩
            none
            H
            true
        with
          | .ok r => pure (r.accountMap, r.gasLeft, r.substate, r.outcome.isSuccess)
          | .error e => .error <| .ExecutionException e
      | some t =>
        -- Proposition (71) suggests the recipient can be inexistent
        match
          Θ fuel
            T.blobVersionedHashes
            createdAccounts
            genesisBlockHeader
            blocks
            σ₀
            σ₀
            AStar
            S_T
            S_T
            t
            (toExecute .EVM σ₀ t)
            g
            p
            T.base.value
            T.base.value
            T.base.data
            0
            H
            true
        with
          | .ok r => pure (r.accountMap, r.gasLeft, r.substate, r.outcome.isSuccess)
          | .error e => .error <| .ExecutionException e
  -- The amount to be refunded (82)
  -- `g' + min ((T_g - g') / 5) A_r`; see `GasMeter.refundedGas` and its lemmas in `GasLemmas`.
  let gStar := GasMeter.refundedGas T.base.gasLimit g' A.refundBalance
  -- The pre-final state (83)
  let σStar :=
    σ_P.increaseBalance .EVM S_T (gStar * p)

  let beneficiaryFee := (T.base.gasLimit - gStar) * f
  let σStar' :=
    if beneficiaryFee != ⟨0⟩ then
      σStar.increaseBalance .EVM H.beneficiary beneficiaryFee
    else σStar
  let σ' := A.selfDestructSet.foldl Std.TreeMap.erase σStar' -- (87)
  let deadAccounts := A.touchedAccounts.filter (State.dead σStar' ·)
  let σ' := deadAccounts.foldl Std.TreeMap.erase σ' -- (88)
  let σ' := σ'.map λ _ acc ↦ { acc with tstorage := .empty }
  .ok (σ', A, z, T.base.gasLimit - gStar)
end EVM

end EvmYul
