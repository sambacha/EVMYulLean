module

public import EvmYul.EVM.Gas.Termination
public import EvmYul.ProofTags
public section

/-!
# Gas behaviour of `step` outside the spawning instructions

`X_ne_outOfFuel` (in `GasTermination`) needs two facts about the instruction step `EVM.step`, for
the charge `c` that `Z` (`exceptionalHalt`) produced: it must not give back more gas than the
charge allows (`StepGasSoundZ`), and it must not raise `OutOfFuel` when it has more fuel than gas
(`NestedFuelAdequateZ`). This file proves both for every instruction except the six that open a
nested frame (`spawnOps`: CREATE, CREATE2, CALL, CALLCODE, DELEGATECALL, STATICCALL); for those
instructions the facts are exactly the induction hypothesis of a whole-interpreter proof and stay
open (`X_ne_outOfFuel_of_spawn` assumes them only there).

It also **refutes** the earlier charge-free versions `StepGasSound` / `NestedFuelAdequate`, which
an earlier `X_ne_outOfFuel` assumed (so that theorem was vacuous): `not_stepGasSound` and
`not_nestedFuelAdequate`, by concrete CALL executions evaluated in the kernel. `Z` rejects both
witnesses (`exceptionalHalt_callWitness_oog`), which is why the restriction to `Z`-produced
charges is needed and sufficient to exclude them.

## Method

`GasSafe t` says that the transformer `t` either succeeds without changing `gasAvailable`, or
fails with an error other than `OutOfFuel`. It is proved once for each shared helper of
`EvmYul.step` (`execBinOp`, `unaryStateOp`, `log2Op`, …) and once for each instruction that
`EvmYul.step` implements inline (POP, JUMP, SELFDESTRUCT, PUSHn, …). The per-family lemmas
`step_StopArith_gasSafe` … `step_System_gasSafe` then name, for every constructor, the helper it
dispatches to; there is no catch-all case, so a new opcode will not compile here until it is
classified.

## The spawning instructions really are different

`EvmYul.step` has a fall-through case `| .EVM, _ => λ _ ↦ default`, and `default` for
`Except ExecutionException State` is `.ok default`: a *successful* step to the all-zero state.
The six spawning instructions reach this case (`EVM.step` intercepts them before `EvmYul.step`, so
the interpreter never takes it). `evmStep_CREATE_eq_default` pins this behaviour and
`not_gasSafe_CREATE` shows that `GasSafe` fails for it, so the `spawnOps` exclusion in
`evmStep_gasSafe` cannot be dropped.
-/

namespace EvmYul

namespace EVM

open GasMeter

/-- The six instructions that open a nested execution frame. `EVM.step` handles them itself;
every other instruction is delegated to `EvmYul.step`. -/
@[expose] def spawnOps : List (Operation .EVM) :=
  [.CREATE, .CREATE2, .CALL, .CALLCODE, .DELEGATECALL, .STATICCALL]

/-- The outcome of one instruction is gas-safe relative to the gas `g` it started with: success
leaves exactly `g`, failure is not `OutOfFuel`. -/
def GasSafeResult (g : UInt256) : Except ExecutionException State → Prop
  | .ok s' => s'.gasAvailable = g
  | .error e => e ≠ .OutOfFuel

/-- A state transformer is gas-safe if, from every state, its outcome is gas-safe relative to
that state's gas. -/
@[expose] def GasSafe (t : Transformer) : Prop := ∀ s : State, GasSafeResult s.gasAvailable (t s)

theorem GasSafeResult.ok_eq {g : UInt256} {s' : State} (h : GasSafeResult g (.ok s')) :
    s'.gasAvailable = g := h

theorem GasSafeResult.error_ne {g : UInt256} {e : ExecutionException}
    (h : GasSafeResult g (.error e)) : e ≠ .OutOfFuel := h

/-- Close the goals left after splitting a transformer's matches: successful outcomes keep the
gas field by definition, errors are constructors other than `OutOfFuel`. -/
macro "gas_safe_close" : tactic => `(tactic| (
  repeat' split
  all_goals first | exact rfl | (intro h; cases h)))

/-- Unfold a shared helper and close all its branches. -/
macro "gas_safe_tac" t:ident : tactic => `(tactic| (
  intro s
  simp only [$t:ident, Id.run]
  gas_safe_close))

/-- Unfold `EvmYul.step` at a concrete opcode and close all branches. -/
macro "step_inline_tac" : tactic => `(tactic| (
  intro s
  unfold EvmYul.step
  simp only [Id.run]
  gas_safe_close))

/-- The memory and copy operations used by `EvmYul.step` do not touch `gasAvailable`. -/
macro "gas_field_tac" : tactic => `(tactic| (
  intros
  simp only [MachineState.mstore, MachineState.mstore8, MachineState.writeWord, writeBytes,
    MachineState.keccak256, MachineState.mcopy, MachineState.evmReturn, MachineState.evmRevert,
    SharedState.calldatacopy, SharedState.codeCopy, SharedState.extCodeCopy']))

/-! ## The shared helpers of `EvmYul.step` -/

theorem execUnOp_gasSafe (f) : GasSafe (execUnOp f) := by gas_safe_tac execUnOp
theorem execBinOp_gasSafe (f) : GasSafe (execBinOp f) := by gas_safe_tac execBinOp
theorem execTriOp_gasSafe (f) : GasSafe (execTriOp f) := by gas_safe_tac execTriOp
theorem executionEnvOp_gasSafe (f) : GasSafe (executionEnvOp f) := by
  gas_safe_tac executionEnvOp
theorem unaryExecutionEnvOp_gasSafe (f) : GasSafe (unaryExecutionEnvOp f) := by
  gas_safe_tac unaryExecutionEnvOp
theorem machineStateOp_gasSafe (f) : GasSafe (machineStateOp f) := by
  gas_safe_tac machineStateOp
theorem stateOp_gasSafe (f) : GasSafe (stateOp f) := by gas_safe_tac stateOp
theorem unaryStateOp_gasSafe (f) : GasSafe (unaryStateOp f) := by gas_safe_tac unaryStateOp
theorem binaryStateOp_gasSafe (f) : GasSafe (binaryStateOp f) := by gas_safe_tac binaryStateOp
theorem log0Op_gasSafe : GasSafe log0Op := by gas_safe_tac log0Op
theorem log1Op_gasSafe : GasSafe log1Op := by gas_safe_tac log1Op
theorem log2Op_gasSafe : GasSafe log2Op := by gas_safe_tac log2Op
theorem log3Op_gasSafe : GasSafe log3Op := by gas_safe_tac log3Op
theorem log4Op_gasSafe : GasSafe log4Op := by gas_safe_tac log4Op
theorem dup_gasSafe (n) : GasSafe (EvmYul.dup n) := by gas_safe_tac EvmYul.dup
theorem swap_gasSafe (n) : GasSafe (EvmYul.swap n) := by gas_safe_tac EvmYul.swap

theorem binaryMachineStateOp_gasSafe {f : MachineState → UInt256 → UInt256 → MachineState}
    (hf : ∀ m a b, (f m a b).gasAvailable = m.gasAvailable) :
    GasSafe (binaryMachineStateOp f) := by
  intro s; simp only [binaryMachineStateOp, Id.run]
  split
  · exact hf _ _ _
  · intro h; cases h

theorem binaryMachineStateOp'_gasSafe
    {f : MachineState → UInt256 → UInt256 → UInt256 × MachineState}
    (hf : ∀ m a b, (f m a b).2.gasAvailable = m.gasAvailable) :
    GasSafe (binaryMachineStateOp' f) := by
  intro s; simp only [binaryMachineStateOp', Id.run]
  split
  · exact hf _ _ _
  · intro h; cases h

theorem ternaryMachineStateOp_gasSafe
    {f : MachineState → UInt256 → UInt256 → UInt256 → MachineState}
    (hf : ∀ m a b c, (f m a b c).gasAvailable = m.gasAvailable) :
    GasSafe (ternaryMachineStateOp f) := by
  intro s; simp only [ternaryMachineStateOp, Id.run]
  split
  · exact hf _ _ _ _
  · intro h; cases h

theorem ternaryCopyOp_gasSafe
    {f : SharedState .EVM → UInt256 → UInt256 → UInt256 → SharedState .EVM}
    (hf : ∀ m a b c, (f m a b c).gasAvailable = m.gasAvailable) :
    GasSafe (ternaryCopyOp f) := by
  intro s; simp only [ternaryCopyOp, Id.run]
  split
  · exact hf _ _ _ _
  · intro h; cases h

theorem quaternaryCopyOp_gasSafe
    {f : SharedState .EVM → UInt256 → UInt256 → UInt256 → UInt256 → SharedState .EVM}
    (hf : ∀ m a b c d, (f m a b c d).gasAvailable = m.gasAvailable) :
    GasSafe (quaternaryCopyOp f) := by
  intro s; simp only [quaternaryCopyOp, Id.run]
  split
  · exact hf _ _ _ _ _
  · intro h; cases h

/-! ## Every opcode family -/

/-- Every `StopArith` instruction is gas-safe in `EvmYul.step`. -/
theorem step_StopArith_gasSafe (o : Operation.SAOp .EVM) (arg : Option (UInt256 × ℕ)) :
    GasSafe (EvmYul.step (.StopArith o) arg) := by
  cases o with
  | STOP => step_inline_tac
  | ADD => exact execBinOp_gasSafe (UInt256.add)
  | MUL => exact execBinOp_gasSafe (UInt256.mul)
  | SUB => exact execBinOp_gasSafe (UInt256.sub)
  | DIV => exact execBinOp_gasSafe (UInt256.div)
  | SDIV => exact execBinOp_gasSafe (UInt256.sdiv)
  | MOD => exact execBinOp_gasSafe (UInt256.mod)
  | SMOD => exact execBinOp_gasSafe (UInt256.smod)
  | ADDMOD => exact execTriOp_gasSafe (UInt256.addMod)
  | MULMOD => exact execTriOp_gasSafe (UInt256.mulMod)
  | EXP => exact execBinOp_gasSafe (UInt256.exp)
  | SIGNEXTEND => exact execBinOp_gasSafe (UInt256.signextend)

/-- Every `CompBit` instruction is gas-safe in `EvmYul.step`. -/
theorem step_CompBit_gasSafe (o : Operation.CBLOp .EVM) (arg : Option (UInt256 × ℕ)) :
    GasSafe (EvmYul.step (.CompBit o) arg) := by
  cases o with
  | LT => exact execBinOp_gasSafe (UInt256.lt)
  | GT => exact execBinOp_gasSafe (UInt256.gt)
  | SLT => exact execBinOp_gasSafe (UInt256.slt)
  | SGT => exact execBinOp_gasSafe (UInt256.sgt)
  | EQ => exact execBinOp_gasSafe (UInt256.eq)
  | ISZERO => exact execUnOp_gasSafe (UInt256.isZero)
  | AND => exact execBinOp_gasSafe (UInt256.land)
  | OR => exact execBinOp_gasSafe (UInt256.lor)
  | XOR => exact execBinOp_gasSafe (UInt256.xor)
  | NOT => exact execUnOp_gasSafe (UInt256.lnot)
  | BYTE => exact execBinOp_gasSafe (UInt256.byteAt)
  | SHL => exact execBinOp_gasSafe ((flip UInt256.shiftLeft))
  | SHR => exact execBinOp_gasSafe ((flip UInt256.shiftRight))
  | SAR => exact execBinOp_gasSafe (UInt256.sar)

/-- Every `Keccak` instruction is gas-safe in `EvmYul.step`. -/
theorem step_Keccak_gasSafe (o : Operation.KOp .EVM) (arg : Option (UInt256 × ℕ)) :
    GasSafe (EvmYul.step (.Keccak o) arg) := by
  cases o with
  | KECCAK256 =>
    exact binaryMachineStateOp'_gasSafe (f := MachineState.keccak256)
      (by gas_field_tac)

/-- Every `Env` instruction is gas-safe in `EvmYul.step`. -/
theorem step_Env_gasSafe (o : Operation.EOp .EVM) (arg : Option (UInt256 × ℕ)) :
    GasSafe (EvmYul.step (.Env o) arg) := by
  cases o with
  | ADDRESS => exact executionEnvOp_gasSafe ((.ofNat ∘ Fin.val ∘ ExecutionEnv.codeOwner))
  | BALANCE => exact unaryStateOp_gasSafe (EvmYul.State.balance)
  | ORIGIN => exact executionEnvOp_gasSafe ((.ofNat ∘ Fin.val ∘ ExecutionEnv.sender))
  | CALLER => exact executionEnvOp_gasSafe ((.ofNat ∘ Fin.val ∘ ExecutionEnv.source))
  | CALLVALUE => exact executionEnvOp_gasSafe (ExecutionEnv.weiValue)
  | CALLDATALOAD => exact unaryStateOp_gasSafe ((λ s v ↦ (s, EvmYul.State.calldataload s v)))
  | CALLDATASIZE => exact executionEnvOp_gasSafe ((.ofNat ∘ ByteArray.size ∘ ExecutionEnv.calldata))
  | CALLDATACOPY =>
    exact ternaryCopyOp_gasSafe (f := SharedState.calldatacopy)
      (by gas_field_tac)
  | GASPRICE => exact executionEnvOp_gasSafe ((.ofNat ∘ ExecutionEnv.gasPrice))
  | CODESIZE => exact executionEnvOp_gasSafe ((.ofNat ∘ ByteArray.size ∘ ExecutionEnv.code))
  | CODECOPY =>
    exact ternaryCopyOp_gasSafe (f := SharedState.codeCopy)
      (by gas_field_tac)
  | EXTCODESIZE => exact unaryStateOp_gasSafe (EvmYul.State.extCodeSize)
  | EXTCODECOPY =>
    exact quaternaryCopyOp_gasSafe (f := EvmYul.SharedState.extCodeCopy')
      (by gas_field_tac)
  | RETURNDATASIZE => exact machineStateOp_gasSafe (EvmYul.MachineState.returndatasize)
  | RETURNDATACOPY => step_inline_tac
  | EXTCODEHASH => exact unaryStateOp_gasSafe (EvmYul.State.extCodeHash)

/-- Every `Block` instruction is gas-safe in `EvmYul.step`. -/
theorem step_Block_gasSafe (o : Operation.BOp .EVM) (arg : Option (UInt256 × ℕ)) :
    GasSafe (EvmYul.step (.Block o) arg) := by
  cases o with
  | BLOCKHASH => exact unaryStateOp_gasSafe ((λ s v ↦ (s, EvmYul.State.blockHash s v)))
  | COINBASE => exact stateOp_gasSafe ((.ofNat ∘ Fin.val ∘ EvmYul.State.coinBase))
  | TIMESTAMP => exact stateOp_gasSafe (EvmYul.State.timeStamp)
  | NUMBER => exact stateOp_gasSafe (EvmYul.State.number)
  | PREVRANDAO => exact executionEnvOp_gasSafe (EvmYul.prevRandao)
  | GASLIMIT => exact stateOp_gasSafe (EvmYul.State.gasLimit)
  | CHAINID => exact stateOp_gasSafe (EvmYul.State.chainId)
  | SELFBALANCE => exact stateOp_gasSafe (EvmYul.State.selfbalance)
  | BASEFEE => exact executionEnvOp_gasSafe (EvmYul.basefee)
  | BLOBHASH => exact unaryExecutionEnvOp_gasSafe (blobhash)
  | BLOBBASEFEE => exact executionEnvOp_gasSafe (EvmYul.ExecutionEnv.getBlobGasprice)

/-- Every `StackMemFlow` instruction is gas-safe in `EvmYul.step`. -/
theorem step_StackMemFlow_gasSafe (o : Operation.SMSFOp .EVM) (arg : Option (UInt256 × ℕ)) :
    GasSafe (EvmYul.step (.StackMemFlow o) arg) := by
  cases o with
  | POP => step_inline_tac
  | MLOAD => step_inline_tac
  | MSTORE =>
    exact binaryMachineStateOp_gasSafe (f := MachineState.mstore)
      (by gas_field_tac)
  | SLOAD => exact unaryStateOp_gasSafe (EvmYul.State.sload)
  | SSTORE => exact binaryStateOp_gasSafe (EvmYul.State.sstore)
  | MSTORE8 =>
    exact binaryMachineStateOp_gasSafe (f := MachineState.mstore8)
      (by gas_field_tac)
  | JUMP => step_inline_tac
  | JUMPI => step_inline_tac
  | PC => step_inline_tac
  | MSIZE => exact machineStateOp_gasSafe (MachineState.msize)
  | GAS => exact machineStateOp_gasSafe (MachineState.gas)
  | JUMPDEST => step_inline_tac
  | TLOAD => exact unaryStateOp_gasSafe (EvmYul.State.tload)
  | TSTORE => exact binaryStateOp_gasSafe (EvmYul.State.tstore)
  | MCOPY =>
    exact ternaryMachineStateOp_gasSafe (f := MachineState.mcopy)
      (by gas_field_tac)

/-- Every `Push` instruction is gas-safe in `EvmYul.step`. -/
theorem step_Push_gasSafe (o : Operation.POp) (arg : Option (UInt256 × ℕ)) :
    GasSafe (EvmYul.step (.Push o) arg) := by
  cases o with
  | PUSH0 => step_inline_tac
  | PUSH1 => step_inline_tac
  | PUSH2 => step_inline_tac
  | PUSH3 => step_inline_tac
  | PUSH4 => step_inline_tac
  | PUSH5 => step_inline_tac
  | PUSH6 => step_inline_tac
  | PUSH7 => step_inline_tac
  | PUSH8 => step_inline_tac
  | PUSH9 => step_inline_tac
  | PUSH10 => step_inline_tac
  | PUSH11 => step_inline_tac
  | PUSH12 => step_inline_tac
  | PUSH13 => step_inline_tac
  | PUSH14 => step_inline_tac
  | PUSH15 => step_inline_tac
  | PUSH16 => step_inline_tac
  | PUSH17 => step_inline_tac
  | PUSH18 => step_inline_tac
  | PUSH19 => step_inline_tac
  | PUSH20 => step_inline_tac
  | PUSH21 => step_inline_tac
  | PUSH22 => step_inline_tac
  | PUSH23 => step_inline_tac
  | PUSH24 => step_inline_tac
  | PUSH25 => step_inline_tac
  | PUSH26 => step_inline_tac
  | PUSH27 => step_inline_tac
  | PUSH28 => step_inline_tac
  | PUSH29 => step_inline_tac
  | PUSH30 => step_inline_tac
  | PUSH31 => step_inline_tac
  | PUSH32 => step_inline_tac

/-- Every `Dup` instruction is gas-safe in `EvmYul.step`. -/
theorem step_Dup_gasSafe (o : Operation.DOp) (arg : Option (UInt256 × ℕ)) :
    GasSafe (EvmYul.step (.Dup o) arg) := by
  cases o with
  | DUP1 => exact dup_gasSafe _
  | DUP2 => exact dup_gasSafe _
  | DUP3 => exact dup_gasSafe _
  | DUP4 => exact dup_gasSafe _
  | DUP5 => exact dup_gasSafe _
  | DUP6 => exact dup_gasSafe _
  | DUP7 => exact dup_gasSafe _
  | DUP8 => exact dup_gasSafe _
  | DUP9 => exact dup_gasSafe _
  | DUP10 => exact dup_gasSafe _
  | DUP11 => exact dup_gasSafe _
  | DUP12 => exact dup_gasSafe _
  | DUP13 => exact dup_gasSafe _
  | DUP14 => exact dup_gasSafe _
  | DUP15 => exact dup_gasSafe _
  | DUP16 => exact dup_gasSafe _

/-- Every `Exchange` instruction is gas-safe in `EvmYul.step`. -/
theorem step_Exchange_gasSafe (o : Operation.ExOp) (arg : Option (UInt256 × ℕ)) :
    GasSafe (EvmYul.step (.Exchange o) arg) := by
  cases o with
  | SWAP1 => exact swap_gasSafe _
  | SWAP2 => exact swap_gasSafe _
  | SWAP3 => exact swap_gasSafe _
  | SWAP4 => exact swap_gasSafe _
  | SWAP5 => exact swap_gasSafe _
  | SWAP6 => exact swap_gasSafe _
  | SWAP7 => exact swap_gasSafe _
  | SWAP8 => exact swap_gasSafe _
  | SWAP9 => exact swap_gasSafe _
  | SWAP10 => exact swap_gasSafe _
  | SWAP11 => exact swap_gasSafe _
  | SWAP12 => exact swap_gasSafe _
  | SWAP13 => exact swap_gasSafe _
  | SWAP14 => exact swap_gasSafe _
  | SWAP15 => exact swap_gasSafe _
  | SWAP16 => exact swap_gasSafe _

/-- Every `Log` instruction is gas-safe in `EvmYul.step`. -/
theorem step_Log_gasSafe (o : Operation.LOp .EVM) (arg : Option (UInt256 × ℕ)) :
    GasSafe (EvmYul.step (.Log o) arg) := by
  cases o with
  | LOG0 => exact log0Op_gasSafe
  | LOG1 => exact log1Op_gasSafe
  | LOG2 => exact log2Op_gasSafe
  | LOG3 => exact log3Op_gasSafe
  | LOG4 => exact log4Op_gasSafe

/-- Every `System` instruction other than the spawning ones is gas-safe in `EvmYul.step`. -/
theorem step_System_gasSafe (o : Operation.SOp .EVM) (arg : Option (UInt256 × ℕ))
    (hop : Operation.System o ∉ spawnOps) :
    GasSafe (EvmYul.step (.System o) arg) := by
  cases o with
  | CREATE => exact (hop (by decide)).elim
  | CALL => exact (hop (by decide)).elim
  | CALLCODE => exact (hop (by decide)).elim
  | RETURN =>
    exact binaryMachineStateOp_gasSafe (f := MachineState.evmReturn)
      (by gas_field_tac)
  | DELEGATECALL => exact (hop (by decide)).elim
  | CREATE2 => exact (hop (by decide)).elim
  | STATICCALL => exact (hop (by decide)).elim
  | REVERT =>
    exact binaryMachineStateOp_gasSafe (f := MachineState.evmRevert)
      (by gas_field_tac)
  | INVALID => step_inline_tac
  | SELFDESTRUCT => step_inline_tac
/-- **`EvmYul.step` never changes the gas and never runs out of fuel** for any instruction outside
`spawnOps`: it either succeeds with `gasAvailable` unchanged, or fails with an error other than
`OutOfFuel`. -/
theorem evmStep_gasSafe (op : Operation .EVM) (arg : Option (UInt256 × ℕ))
    (hop : op ∉ spawnOps) : GasSafe (EvmYul.step op arg) := by
  cases op with
  | StopArith o => exact step_StopArith_gasSafe o arg
  | CompBit o => exact step_CompBit_gasSafe o arg
  | Keccak o => exact step_Keccak_gasSafe o arg
  | Env o => exact step_Env_gasSafe o arg
  | Block o => exact step_Block_gasSafe o arg
  | StackMemFlow o => exact step_StackMemFlow_gasSafe o arg
  | Push o => exact step_Push_gasSafe o arg
  | Dup o => exact step_Dup_gasSafe o arg
  | Exchange o => exact step_Exchange_gasSafe o arg
  | Log o => exact step_Log_gasSafe o arg
  | System o => exact step_System_gasSafe o arg hop

/-- `EvmYul.step` on CREATE takes the fall-through case and *succeeds* with the all-zero state. -/
@[reviewed_pin EvmYul.EVM.not_gasSafe_CREATE]
theorem evmStep_CREATE_eq_default (arg : Option (UInt256 × ℕ)) (s : State) :
    EvmYul.step (τ := .EVM) .CREATE arg s = .ok default := rfl

/-- The `spawnOps` exclusion in `evmStep_gasSafe` is necessary: CREATE is not gas-safe in
`EvmYul.step` (from a state with gas 1 it "succeeds" with gas 0). -/
theorem not_gasSafe_CREATE (arg : Option (UInt256 × ℕ)) :
    ¬ GasSafe (EvmYul.step (τ := .EVM) .CREATE arg) := by
  intro h
  have h1 := (h { (default : State) with gasAvailable := ⟨1⟩ }).ok_eq
  exact absurd h1 (by decide)

/-! ## The interpreter's `step` -/

/-- **One interpreter step outside `spawnOps`**: with at least one unit of fuel, `EVM.step`
on a decoded instruction either succeeds leaving exactly `gasAvailable - c` (the pre-checked
deduction of the charge `c`), or fails with an error other than `OutOfFuel`. -/
theorem step_some_gasSafe {f c : ℕ} {w : Operation .EVM} {arg : Option (UInt256 × ℕ)}
    (s₁ : State) (hw : w ∉ spawnOps) :
    GasSafeResult (deductPrechecked s₁.gasAvailable c) (step (f + 1) c (some (w, arg)) s₁) := by
  unfold step
  simp only [bind, Except.bind, pure, Except.pure]
  split
  all_goals first
    | (exfalso; apply hw; decide)
    | exact evmStep_gasSafe _ _ hw _

/-- `step` with zero fuel always raises `OutOfFuel`. -/
@[reviewed_pin EvmYul.EVM.Υ_zero_fuel]
theorem step_zero_fuel (c : ℕ) (i : Option (Operation .EVM × Option (UInt256 × Nat)))
    (s : State) : step 0 c i s = .error .OutOfFuel := rfl

/-- `StepGasSoundZ` restricted to the spawning instructions. Proved in `GasNested`
(`spawnStepGasSoundZ`), which needs the nested-frame gas bounds. -/
@[expose] def SpawnStepGasSoundZ : Prop :=
  ∀ (f : ℕ) (vj : Array UInt256) (w : Operation .EVM) (arg : Option (UInt256 × Nat))
    (s s₁ : State) (c : ℕ) (s₂ : State), w ∈ spawnOps →
    exceptionalHalt vj w s = .ok (s₁, c) → step f c (some (w, arg)) s₁ = .ok s₂ →
      s₂.gasAvailable.toNat ≤ (deductPrechecked s₁.gasAvailable c).toNat ∨
        s₂.gasAvailable.toNat < s₁.gasAvailable.toNat

/-- `NestedFuelAdequateZ` restricted to the spawning instructions (the remaining open
obligation). -/
@[expose] def SpawnNestedFuelAdequateZ : Prop :=
  ∀ (f : ℕ) (vj : Array UInt256) (w : Operation .EVM) (arg : Option (UInt256 × Nat))
    (s s₁ : State) (c : ℕ), w ∈ spawnOps →
    exceptionalHalt vj w s = .ok (s₁, c) → s₁.gasAvailable.toNat + 1 < f →
      step f c (some (w, arg)) s₁ ≠ .error .OutOfFuel

/-- `StepGasSoundZ` holds as soon as it holds for the six spawning instructions. -/
theorem stepGasSoundZ_of_spawn (h : SpawnStepGasSoundZ) : StepGasSoundZ := by
  intro f vj w arg s s₁ c s₂ hZ hs
  by_cases hw : w ∈ spawnOps
  · exact h f vj w arg s s₁ c s₂ hw hZ hs
  · cases f with
    | zero => cases hs
    | succ f =>
      have := step_some_gasSafe (f := f) (c := c) (arg := arg) s₁ hw
      rw [hs] at this
      exact Or.inl (le_of_eq (congrArg UInt256.toNat this.ok_eq))

/-- `NestedFuelAdequateZ` holds as soon as it holds for the six spawning instructions. -/
theorem nestedFuelAdequateZ_of_spawn (h : SpawnNestedFuelAdequateZ) : NestedFuelAdequateZ := by
  intro f vj w arg s s₁ c hZ hf
  by_cases hw : w ∈ spawnOps
  · exact h f vj w arg s s₁ c hw hZ hf
  · obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    intro he
    have := step_some_gasSafe (f := f) (c := c) (arg := arg) s₁ hw
    rw [he] at this
    exact this.error_ne rfl

/-- **`X`'s own fuel counter is never exhausted** once the fuel exceeds the gas by 2, assuming
only the two properties for the *spawning* instructions (CREATE, CREATE2, CALL, CALLCODE,
DELEGATECALL, STATICCALL), for charges produced by `Z`. For all other instructions the hypotheses
of `X_ne_outOfFuel` are proved (`step_some_gasSafe`). -/
theorem X_ne_outOfFuel_of_spawn (hS : SpawnStepGasSoundZ) (hN : SpawnNestedFuelAdequateZ) :
    ∀ (f : ℕ) (vj : Array UInt256) (s : State), s.gasAvailable.toNat + 2 < f →
      X f vj s ≠ .error .OutOfFuel :=
  X_ne_outOfFuel (stepGasSoundZ_of_spawn hS) (nestedFuelAdequateZ_of_spawn hN)

/-! ## Refutation of the earlier, charge-free hypotheses

`StepGasSound` and `NestedFuelAdequate` quantify over every charge `c ≤ gas`. A CALL executed with
charge 0 refutes both. The witness state has the code owner's account (balance 0), stack
`[gas 100, to 1, value v, 0, 0, 0, 0]` and gas 0. -/

/-- The CALL witness state (see above). -/
@[expose] def callWitness (value : ℕ) : State :=
  let s0 : State := default
  { s0 with
      accountMap := s0.accountMap.insert s0.executionEnv.codeOwner default
      stack := [.ofNat 100, .ofNat 1, .ofNat value, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩] }

/-- With charge 0, a value-transferring CALL that fails the balance check (value 1 > balance 0)
*raises* the caller's gas from 0 to 2400: the requested 100 plus the 2300 stipend come back,
although nothing was charged. -/
theorem call_charge0_gas_increases :
    ∃ s₂, step 2 0 (some (.CALL, none)) (callWitness 1) = .ok s₂ ∧
      s₂.gasAvailable = .ofNat 2400 := ⟨_, rfl, rfl⟩

/-- With fuel 2, a CALL that passes the balance check reaches `Θ` with fuel 0 and raises
`OutOfFuel`, although the fuel exceeds the gas (0) by 2. -/
@[reviewed_pin EvmYul.EVM.not_nestedFuelAdequate]
theorem call_fuel2_outOfFuel :
    step 2 0 (some (.CALL, none)) (callWitness 0) = .error .OutOfFuel := rfl

/-- **The earlier gas hypothesis is false.** -/
theorem not_stepGasSound : ¬ StepGasSound := by
  intro h
  obtain ⟨s₂, hs, hg⟩ := call_charge0_gas_increases
  have := h 2 0 _ _ s₂ (Nat.zero_le _) hs
  rw [hg] at this
  exact absurd this (by decide)

/-- **The earlier fuel hypothesis is false.** -/
theorem not_nestedFuelAdequate : ¬ NestedFuelAdequate :=
  fun h => h 2 0 _ (callWitness 0) (by decide) call_fuel2_outOfFuel

/-- `Z` rejects both witnesses (out of gas), so the restriction to `Z`-produced charges in
`StepGasSoundZ` / `NestedFuelAdequateZ` excludes them. -/
theorem exceptionalHalt_callWitness_oog (vj : Array UInt256) :
    exceptionalHalt vj .CALL (callWitness 0) = .error .OutOfGass ∧
      exceptionalHalt vj .CALL (callWitness 1) = .error .OutOfGass := ⟨rfl, rfl⟩

end EVM

end EvmYul
