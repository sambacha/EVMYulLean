module

public import EvmYul.Venom.Cfg
public import EvmYul.Venom.Semantics
public import EvmYul.Vyper.Harness

public section

/-!
# The Venom machine interfaces on the project's EVM

Both Venom layers are parametric in their machine: the straight-line semantics in `Prims σ`
(`Semantics.lean`), the control-flow-graph layer in `EvmInterface σ` (`Cfg.lean`). This module gives
each an instance whose state is the project's `EVM.State` and whose behaviour **is** the project's
EVM: nothing is re-implemented.

* `execOp w args s` runs the single EVM instruction `w` on the operand stack `args` (top first):
  first `EVM.exceptionalHalt`, which charges the instruction's full Cancun cost (memory expansion
  and EIP-2929 cold access included) and performs the halting checks, then `EVM.step`, the
  interpreter's own instruction semantics. It returns the stack after the instruction, the new state
  (stack cleared) and the gas charged (`gasAvailable` before minus after).
* `evmPrims : Prims EVM.State` reads the effects, their gas and the terminators' gas off `execOp`.
* `evmInterface : EvmInterface EVM.State` sends every opcode except the copy `assign` to `execOp`.
* `initState` is the state in which `Θ` starts the contract's code in `Vyper.execute` (same world,
  environment, substate and gas), so a Venom run from it can be compared with a `Θ` run.

**What is proved and what is tested.** `compile_correct` holds for every `Prims`, so instantiated at
`evmPrims` it says that compiled code under the EVM's own effects gives the Venom result. That the
assembled *bytes* do the same on `Θ` is checked by the counted differential tests of
`EvmMachineTests.lean` (outcome, output, storage and gas exactly), together with a second route
against the independent reference model `refPrims`.

**Caveat.** `Prims.apply` is total and the Venom semantics has no exceptional-halt outcome. If an
instruction halts exceptionally (out of gas, stack overflow, a write in a static call), `evmPrims`
returns the value `0`, the unchanged state and cost `0`, which no longer follows the EVM; the tests
run with the `Θ` harness's budget of `5·10⁶` gas, far above what their programs need, and compare
with `Θ`, so such a divergence would fail them.
-/

namespace EvmYul.Venom.EvmMachine

open EvmYul.EVM

/-- Fuel for one `EVM.step` call. Only `CREATE`/`CALL`-like instructions use more than one unit,
and none of them is executed here. -/
@[expose] def stepFuel : ℕ := 2

/-- Run the single EVM instruction `w` on operand stack `args` (top first) in state `s`: the
exceptional-halt check, which charges the full cost, then `EVM.step`. Returns the stack after the
instruction, the new state with an empty stack, and the gas charged. `none` on an exceptional halt
or an execution error. -/
@[expose] def execOp (w : Operation .EVM) (args : List UInt256) (s : EVM.State) :
    Option (List UInt256 × EVM.State × ℕ) :=
  match exceptionalHalt #[] w { s with stack := args } with
  | .error _ => none
  | .ok (s₁, cost) =>
    match EVM.step stepFuel cost (some (w, none)) s₁ with
    | .error _ => none
    | .ok s₂ => some (s₂.stack, { s₂ with stack := [] }, s.gasAvailable.toNat - s₂.gasAvailable.toNat)

/-! ## Opcode tables -/

/-- The EVM instruction of a pure operation of the fragment. -/
@[expose] def pureOpEvm : PureOp → Operation .EVM
  | .add => .ADD | .sub => .SUB | .mul => .MUL | .div => .DIV | .mod => .MOD
  | .and => .AND | .or => .OR | .xor => .XOR | .shl => .SHL | .shr => .SHR
  | .lt => .LT | .gt => .GT | .eq => .EQ | .iszero => .ISZERO

/-- The EVM instruction of an effect of the fragment. -/
@[expose] def effEvm : Eff → Operation .EVM
  | .callvalue => .CALLVALUE | .calldatasize => .CALLDATASIZE | .calldataload => .CALLDATALOAD
  | .sload => .SLOAD | .mload => .MLOAD | .sstore => .SSTORE | .mstore => .MSTORE

/-- The EVM instruction of a terminator of the fragment. -/
@[expose] def haltEvm : Halt → Operation .EVM
  | .stop => .STOP | .ret => .RETURN | .revert => .REVERT

/-- The EVM instruction of a CFG opcode; `none` for the copy, φ, `assert` and the control-flow
opcodes, which the CFG semantics handles itself (or rejects). -/
@[expose] def cfgOpEvm : Cfg.Op → Option (Operation .EVM)
  | .add => some .ADD | .sub => some .SUB | .mul => some .MUL | .div => some .DIV
  | .mod => some .MOD | .and => some .AND | .or => some .OR | .xor => some .XOR
  | .shl => some .SHL | .shr => some .SHR | .lt => some .LT | .gt => some .GT | .eq => some .EQ
  | .iszero => some .ISZERO
  | .mload => some .MLOAD | .mstore => some .MSTORE | .sload => some .SLOAD
  | .sstore => some .SSTORE
  | .calldataload => some .CALLDATALOAD | .calldatasize => some .CALLDATASIZE
  | .callvalue => some .CALLVALUE | .codecopy => some .CODECOPY
  | _ => none

/-! ## The straight-line machine -/

/-- The fragment's primitive effects on the project's EVM: value, state and gas of each effect,
and the gas of each terminator (memory expansion of `RETURN`/`REVERT`), all read off `execOp`. -/
@[expose] def evmPrims : Prims EVM.State where
  apply e s vs := match execOp (effEvm e) vs s with
    | some (out, s', _) => (out.headD (word 0), s')
    | none => (word 0, s)
  cost e s vs := match execOp (effEvm e) vs s with
    | some (_, _, g) => g
    | none => 0
  haltCost h s vs := match execOp (haltEvm h) vs s with
    | some (_, _, g) => g
    | none => 0

/-- The state in which `Vyper.execute` has `Θ` start the code: the same world (`Vyper.worldOf`),
environment (contract `0x1000` called by `0x2000` at depth 1 with write permission, call data and
value), empty substate and created-account set, and the harness budget of gas. -/
@[expose] def initState (code : ByteArray) (kvs : List (ℕ × ℕ)) (data : List UInt8) (value : ℕ) :
    EVM.State :=
  let σ := Vyper.worldOf code kvs
  let I : ExecutionEnv .EVM :=
    { codeOwner := Vyper.contractAddr, sender := Vyper.callerAddr, source := Vyper.callerAddr,
      weiValue := .ofNat value, calldata := ⟨data.toArray⟩, code := code, gasPrice := 0,
      header := default, depth := 1, perm := true, blobVersionedHashes := [] }
  let s₀ : EVM.State := default
  { s₀ with accountMap := σ, σ₀ := σ, executionEnv := I, substate := default,
            createdAccounts := ∅, gasAvailable := .ofNat Vyper.budget }

/-- Storage slot `k` of the contract in an EVM state. -/
@[expose] def slotOf (s : EVM.State) (k : ℕ) : ℕ :=
  match s.accountMap.get? Vyper.contractAddr with
  | some a => (a.lookupStorage (.ofNat k)).toNat
  | none => 0

/-- The output bytes of a result over the EVM: memory `[ofs, ofs + len)` for `return`/`revert`. -/
@[expose] def outputOf (f : Final EVM.State) : List UInt8 :=
  match f.data with
  | [o, l] => (f.state.memory.readWithPadding o.toNat l.toNat).toList
  | _ => []

/-! ## The CFG machine -/

/-- A CFG word as an interpreter word. -/
@[expose] def toU (w : Cfg.Word) : UInt256 := .ofNat w.toNat

/-- An interpreter word as a CFG word. -/
@[expose] def toW (u : UInt256) : Cfg.Word := BitVec.ofNat 256 u.toNat

/-- The CFG layer's machine interface on the project's EVM: `assign` copies its operand; every
other machine opcode runs through `execOp` (gas is charged inside the state, in `gasAvailable`);
opcodes without an EVM instruction fault. -/
@[expose] instance evmInterface : Cfg.EvmInterface EVM.State where
  exec op ws s :=
    match op, ws with
    | .assign, [w] => some ([w], s)
    | .assign, _ => none
    | op, ws => do
      let w ← cfgOpEvm op
      let (out, s', _) ← execOp w (ws.map toU) s
      pure (out.map toW, s')

end EvmYul.Venom.EvmMachine
