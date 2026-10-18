module

public import EvmYul.EVM.Gas.Meter
public import EvmYul.EVM.Gas.ForkSchedule
public section

/-!
# The pure, total, fork-parameterised cost function and the accounting transformer

This file splits the Yellow Paper's exceptional-halting function `Z` and its cost `C` into two
independent parts:

* **`ForkSchedule.cost : ForkSchedule → EVM.State → Operation .EVM → Option ℕ`**, a total, pure
  function. It returns `none` exactly when the instruction cannot be priced: the instruction does
  not exist in the fork, or it is invalid (`δ = none`), or its operands are not on the stack
  (`costParts_eq_none_iff`). The stack guard is checked **first**, and every operand is read with
  `stack[i]?` inside `Option`, so there are no `!` reads and the memory-expansion cost is never
  evaluated on a stack that is too short. The result is the memory-expansion cost plus the
  instruction cost (`costParts` returns the two summands separately).
* **The accounting transformer** `ForkSchedule.chargeOp`: it runs the guard, deducts the memory
  part with the guarded `GasMeter.chargeGas`, checks that the instruction part fits (`OutOfGass`
  otherwise) and returns the post-memory state together with the instruction part, which `step`
  deducts with `GasMeter.deductPrechecked`. `ForkSchedule.settleRefund` is the end-of-transaction
  refund rule (YP (82), parameterised by the fork's refund quotient).

**Why the instruction part takes the gas as an argument.** The cost of the CALL family depends on
the gas that is available *after* the memory-expansion charge (EIP-150's 63/64 cap, `Cgascap`).
Full purity in the state is therefore impossible: `instrCost?` takes that gas as an explicit `ℕ`
argument, `costParts` feeds it `gasAvailable − memory cost`, and `chargeOp` deducts the memory part
before checking the instruction part. The order-sensitivity lemmas are in
`EvmYul/EVM/Gas/ForkCostBridge.lean`.

The interpreter's `exceptionalHalt` (in `EvmYul/EVM/Semantics.lean`) is now `chargeOp cancun`
followed by the non-gas halting checks, and `Gas/ForkCostBridge.lean` proves it equal, for every input,
to the previous definition (`exceptionalHalt_eq_prev`).
-/

namespace EvmYul

namespace EVM

open GasConstants InstructionGasGroups

namespace ForkSchedule

/-! ## Opcode availability -/

/-- The fork that introduced an opcode (everything not listed existed at Frontier;
`PREVRANDAO` is the renamed `DIFFICULTY`). -/
@[expose] def introducedIn : Operation .EVM → Fork
  | .DELEGATECALL => .homestead
  | .REVERT | .RETURNDATASIZE | .RETURNDATACOPY | .STATICCALL => .byzantium
  | .SHL | .SHR | .SAR | .EXTCODEHASH | .CREATE2 => .petersburg
  | .CHAINID | .SELFBALANCE => .istanbul
  | .BASEFEE => .london
  | .PUSH0 => .shanghai
  | .TLOAD | .TSTORE | .MCOPY | .BLOBHASH | .BLOBBASEFEE => .cancun
  | _ => .frontier

/-- Whether an opcode exists in the schedule's fork. -/
@[expose] def available (fs : ForkSchedule) (w : Operation .EVM) : Bool :=
  decide (introducedIn w ≤ fs.fork)

/-! ## Cost components -/

/-- YP (328): memory cost of `a` active words, `G_memory · a + ⌊a² / 512⌋`. -/
@[expose] def memCost (fs : ForkSchedule) (a : UInt256) : ℕ :=
  fs.Gmemory * a.toNat + (a.toNat * a.toNat) / 512

/-- Active words after the instruction (YP `μ'ᵢ`), computed from the operands' memory ranges.
Operands are read with `stack[i]?`; `none` only if an operand is missing. -/
@[expose] def newActiveWords? (aw : UInt256) (stk : Stack UInt256) : Operation .EVM → Option UInt256
  | .KECCAK256 => do
    let o ← stk[0]?; let n ← stk[1]?
    pure <| .ofNat <| MachineState.M aw.toNat o.toNat n.toNat
  | .CALLDATACOPY | .CODECOPY | .RETURNDATACOPY => do
    let o ← stk[0]?; let n ← stk[2]?
    pure <| .ofNat <| MachineState.M aw.toNat o.toNat n.toNat
  | .MCOPY => do
    let d ← stk[0]?; let o ← stk[1]?; let n ← stk[2]?
    pure <| .ofNat <| MachineState.M aw.toNat (max d.toNat o.toNat) n.toNat
  | .EXTCODECOPY => do
    let o ← stk[1]?; let n ← stk[3]?
    pure <| .ofNat <| MachineState.M aw.toNat o.toNat n.toNat
  | .MLOAD | .MSTORE => do
    let o ← stk[0]?
    pure <| .ofNat <| MachineState.M aw.toNat o.toNat 32
  | .MSTORE8 => do
    let o ← stk[0]?
    pure <| .ofNat <| MachineState.M aw.toNat o.toNat 1
  | .LOG0 | .LOG1 | .LOG2 | .LOG3 | .LOG4 | .RETURN | .REVERT => do
    let o ← stk[0]?; let n ← stk[1]?
    pure <| .ofNat <| MachineState.M aw.toNat o.toNat n.toNat
  | .CREATE | .CREATE2 => do
    let o ← stk[1]?; let n ← stk[2]?
    pure <| .ofNat <| MachineState.M aw.toNat o.toNat n.toNat
  | .CALL | .CALLCODE => do
    let io ← stk[3]?; let is ← stk[4]?; let oo ← stk[5]?; let os ← stk[6]?
    pure <| .ofNat <| MachineState.M (MachineState.M aw.toNat io.toNat is.toNat) oo.toNat os.toNat
  | .DELEGATECALL | .STATICCALL => do
    let io ← stk[2]?; let is ← stk[3]?; let oo ← stk[4]?; let os ← stk[5]?
    pure <| .ofNat <| MachineState.M (MachineState.M aw.toNat io.toNat is.toNat) oo.toNat os.toNat
  | _ => some aw

/-- Memory-expansion cost of `w` in state `s` (`none` only if an operand is missing). -/
@[expose] def memoryCost? (fs : ForkSchedule) (s : EVM.State) (w : Operation .EVM) : Option ℕ := do
  let a ← newActiveWords? s.toMachineState.activeWords s.stack w
  pure (fs.memCost a - fs.memCost s.toMachineState.activeWords)

/-- Account access: EIP-2929 warm/cold price, or the flat pre-Berlin price `flat`. -/
@[expose] def accessCost (fs : ForkSchedule) (a : AccountAddress) (A : Substate) (flat : ℕ) : ℕ :=
  if fs.eip2929 then
    if A.accessedAccounts.contains a then fs.Gwarmaccess else fs.Gcoldaccountaccess
  else flat

/-- The flat pre-Berlin price of a `W_extaccount` instruction. -/
@[expose] def extAccountFlat (fs : ForkSchedule) (w : Operation .EVM) : ℕ :=
  if w = .BALANCE then fs.Gbalance else if w = .EXTCODEHASH then fs.Gextcodehash else fs.Gextcode

/-- SLOAD of key `k`: warm/cold (EIP-2929) or flat `Gsload`. -/
@[expose] def sloadCost (fs : ForkSchedule) (A : Substate) (I : ExecutionEnv .EVM) (k : UInt256) : ℕ :=
  if fs.eip2929 then
    if A.accessedStorageKeys.contains (I.codeOwner, k) then fs.Gwarmaccess else fs.Gcoldsload
  else fs.Gsload

/-- SSTORE of `v'` at key `k`: the Frontier rule, or EIP-2200 net metering (with EIP-2929 cold
surcharge from Berlin on). `v₀` is the original value (start of transaction), `v` the current. -/
@[expose] def sstoreCost (fs : ForkSchedule) (s : EVM.State) (k v' : UInt256) : ℕ :=
  let Iₐ := s.executionEnv.codeOwner
  let v₀ :=
    match s.σ₀.get? Iₐ with
      | none => ⟨0⟩
      | some acc => acc.storage.getD k ⟨0⟩
  let v := ((s.accountMap.get? Iₐ).getD default).storage.getD k ⟨0⟩
  match fs.sstoreRule with
  | .frontier => if v = ⟨0⟩ ∧ v' ≠ ⟨0⟩ then fs.Gsset else fs.Gsreset
  | .netMetered =>
    let loadComponent :=
      if fs.eip2929 then
        if s.substate.accessedStorageKeys.contains (Iₐ, k) then 0 else fs.Gcoldsload
      else 0
    let noop := if fs.eip2929 then fs.Gwarmaccess else fs.Gsload
    let storeComponent := if v = v' || v₀ ≠ v             then noop else
                          if v ≠ v' && v₀ = v && v₀ = ⟨0⟩ then fs.Gsset else
                                                               fs.Gsreset
    loadComponent + storeComponent

/-- SELFDESTRUCT to beneficiary `r`. -/
@[expose] def selfdestructCost (fs : ForkSchedule) (s : EVM.State) (r : UInt256) : ℕ :=
  let r := AccountAddress.ofUInt256 r
  let c_cold :=
    if fs.eip2929 then
      if s.substate.accessedAccounts.contains r then 0 else fs.Gcoldaccountaccess
    else 0
  let c_new :=
    if fs.selfdestructNewAccount then
      if State.dead s.accountMap r ∧
          (s.accountMap.get? s.executionEnv.codeOwner |>.option ⟨0⟩ (·.balance)) ≠ ⟨0⟩ then
        fs.Gnewaccount
      else 0
    else 0
  fs.Gselfdestruct + c_cold + c_new

/-- `C_EXTRA` of a call to `t` (recipient `r`, value `val`). -/
@[expose] def callExtra (fs : ForkSchedule) (t r : AccountAddress) (val : UInt256) (σ : AccountMap .EVM)
    (A : Substate) : ℕ :=
  fs.accessCost t A fs.Gcall + (if val != ⟨0⟩ then fs.Gcallvalue else 0) +
    (if EvmYul.State.dead σ r && val != ⟨0⟩ then fs.Gnewaccount else 0)

/-- `C_GASCAP`: the gas forwarded (before the stipend), given the gas `gas` available after the
memory charge. With EIP-150 it is capped by "all but one 64th" of what remains after `C_EXTRA`;
before EIP-150 it is the requested `g`. -/
@[expose] def callGasCap (fs : ForkSchedule) (gas : ℕ) (t r : AccountAddress) (val g : UInt256)
    (σ : AccountMap .EVM) (A : Substate) : ℕ :=
  match fs.callGasRetention with
  | none => g.toNat
  | some _ =>
    if gas ≥ fs.callExtra t r val σ A then
      min (fs.allBut (gas - fs.callExtra t r val σ A)) g.toNat
    else g.toNat

/-- `C_CALLGAS`: the gas the callee receives (`C_GASCAP` plus the stipend for value calls). -/
@[expose] def callGas (fs : ForkSchedule) (gas : ℕ) (t r : AccountAddress) (val g : UInt256)
    (σ : AccountMap .EVM) (A : Substate) : ℕ :=
  if val = ⟨0⟩ then fs.callGasCap gas t r val g σ A
  else fs.callGasCap gas t r val g σ A + fs.Gcallstipend

/-- `C_CALL = C_GASCAP + C_EXTRA`. -/
@[expose] def callCost (fs : ForkSchedule) (gas : ℕ) (t r : AccountAddress) (val g : UInt256)
    (σ : AccountMap .EVM) (A : Substate) : ℕ :=
  fs.callGasCap gas t r val g σ A + fs.callExtra t r val σ A

/-- EIP-3860 initcode cost of `x` bytes. -/
@[expose] def initcodeCost (fs : ForkSchedule) (x : ℕ) : ℕ := fs.Ginitcodeword * ((x + 31) / 32)

/-- The instruction part of the cost (YP H.1, third summand), given the gas `gas` available
after the memory-expansion charge. Operands are read with `stack[i]?`; `none` if an operand is
missing or the instruction has no price (INVALID). -/
@[expose] def instrCost? (fs : ForkSchedule) (gas : ℕ) (s : EVM.State) (w : Operation .EVM) : Option ℕ :=
  let stk := s.stack
  let A := s.substate
  let σ := s.accountMap
  let Iₐ := s.executionEnv.codeOwner
  match w with
    | .SSTORE => do let k ← stk[0]?; let v' ← stk[1]?; pure (fs.sstoreCost s k v')
    | .TSTORE => some fs.Gwarmaccess
    | .EXP => do
      let e ← stk[1]?
      pure (if e == ⟨0⟩ then fs.Gexp else fs.Gexp + fs.Gexpbyte * (1 + Nat.log 256 e.toNat))
    | .EXTCODECOPY => do
      let a ← stk[0]?; let n ← stk[3]?
      pure (fs.accessCost (.ofUInt256 a) A fs.Gextcode + fs.Gcopy * ((n.toNat + 31) / 32))
    | .LOG0 => do let n ← stk[1]?; pure (fs.Glog + fs.Glogdata * n.toNat)
    | .LOG1 => do let n ← stk[1]?; pure (fs.Glog + fs.Glogdata * n.toNat + fs.Glogtopic)
    | .LOG2 => do let n ← stk[1]?; pure (fs.Glog + fs.Glogdata * n.toNat + 2 * fs.Glogtopic)
    | .LOG3 => do let n ← stk[1]?; pure (fs.Glog + fs.Glogdata * n.toNat + 3 * fs.Glogtopic)
    | .LOG4 => do let n ← stk[1]?; pure (fs.Glog + fs.Glogdata * n.toNat + 4 * fs.Glogtopic)
    | .SELFDESTRUCT => do let r ← stk[0]?; pure (fs.selfdestructCost s r)
    | .CREATE => do let n ← stk[2]?; pure (fs.Gcreate + fs.initcodeCost n.toNat)
    | .CREATE2 => do
      let n ← stk[2]?
      pure (fs.Gcreate + fs.Gkeccak256word * ((n.toNat + 31) / 32) + fs.initcodeCost n.toNat)
    | .KECCAK256 => do
      let n ← stk[1]?; pure (fs.Gkeccak256 + fs.Gkeccak256word * ((n.toNat + 31) / 32))
    | .JUMPDEST => some fs.Gjumpdest
    | .SLOAD => do let k ← stk[0]?; pure (fs.sloadCost A s.executionEnv k)
    | .TLOAD => some fs.Gwarmaccess
    | .BLOCKHASH => some fs.Gblockhash
    -- The value operand is `stk[2]` for CALL/CALLCODE and 0 for DELEGATECALL/STATICCALL.
    | .CALL => do
      let g ← stk[0]?; let t ← stk[1]?; let v ← stk[2]?
      pure (fs.callCost gas (.ofUInt256 t) (.ofUInt256 t) v g σ A)
    | .CALLCODE => do
      let g ← stk[0]?; let t ← stk[1]?; let v ← stk[2]?
      pure (fs.callCost gas (.ofUInt256 t) Iₐ v g σ A)
    | .DELEGATECALL => do
      let g ← stk[0]?; let t ← stk[1]?
      pure (fs.callCost gas (.ofUInt256 t) Iₐ ⟨0⟩ g σ A)
    | .STATICCALL => do
      let g ← stk[0]?; let t ← stk[1]?
      pure (fs.callCost gas (.ofUInt256 t) (.ofUInt256 t) ⟨0⟩ g σ A)
    | .BLOBHASH => some fs.HASH_OPCODE_GAS
    | w =>
      if w ∈ Wcopy then do let n ← stk[2]?; pure (fs.Gverylow + fs.Gcopy * ((n.toNat + 31) / 32))
      else if w ∈ Wextaccount then do
        let a ← stk[0]?; pure (fs.accessCost (.ofUInt256 a) A (fs.extAccountFlat w))
      else if w ∈ Wzero then some fs.Gzero
      else if w ∈ Wbase then some fs.Gbase
      else if w ∈ Wverylow then some fs.Gverylow
      else if w ∈ Wlow then some fs.Glow
      else if w ∈ Wmid then some fs.Gmid
      else if w ∈ Whigh then some fs.Ghigh
      else none

/-- The stack guard: `w` exists in the fork, is valid, and has all its operands on the stack. -/
@[expose] def guardOk (fs : ForkSchedule) (s : EVM.State) (w : Operation .EVM) : Bool :=
  fs.available w && match δ w with
    | none => false
    | some k => decide (k ≤ s.stack.length)

/-- **The two summands of the cost**: memory expansion and the instruction part, the latter
evaluated with the gas left after the former. `none` iff the guard fails
(`costParts_eq_none_iff`). -/
@[expose] def costParts (fs : ForkSchedule) (s : EVM.State) (w : Operation .EVM) : Option (ℕ × ℕ) :=
  if fs.guardOk s w then do
    let m ← fs.memoryCost? s w
    let c ← fs.instrCost? (s.gasAvailable.toNat - m) s w
    pure (m, c)
  else none

/-- **The cost of executing `w` in state `s` under schedule `fs`**: total and pure; `none` iff
the instruction cannot execute regardless of gas (unknown in the fork, invalid, or stack
underflow). -/
@[expose] def cost (fs : ForkSchedule) (s : EVM.State) (w : Operation .EVM) : Option ℕ :=
  (fs.costParts s w).map fun p => p.1 + p.2

/-! ## The accounting transformer -/

/-- The guard as an exception: `InvalidInstruction` (unknown in the fork or `δ = none`) before
`StackUnderflow`. -/
@[expose] def checkGuard (fs : ForkSchedule) (s : EVM.State) (w : Operation .EVM) :
    Except ExecutionException Unit :=
  if !fs.available w || δ w == none then .error .InvalidInstruction
  else if s.stack.length < (δ w).getD 0 then .error .StackUnderflow
  else .ok ()

/-- **Accounting transformer.** Guard, deduct the memory-expansion cost with the guarded
`chargeGas`, check that the instruction cost fits, and return the post-memory state with the
instruction cost (deducted afterwards by `step` with `deductPrechecked`, after the call-gas
computation that needs the post-memory gas). -/
@[expose] def chargeOp (fs : ForkSchedule) (s : EVM.State) (w : Operation .EVM) :
    Except ExecutionException (EVM.State × ℕ) := do
  fs.checkGuard s w
  match fs.costParts s w with
  | none => .error .StackUnderflow
  | some (m, c) =>
    let g ← GasMeter.chargeGas s.gasAvailable m
    let s := { s with gasAvailable := g }
    if s.gasAvailable.toNat < c then .error .OutOfGass
    pure (s, c)

/-- End-of-transaction refund (YP (82), EIP-3529 / pre-London): the sender gets back the gas left
`gasLeft` plus `min(⌊(gasLimit − gasLeft) / refundQuotient⌋, refundCounter)`. -/
@[expose] def settleRefund (fs : ForkSchedule) (gasLimit gasLeft refundCounter : ℕ) : ℕ :=
  gasLeft + min ((gasLimit - gasLeft) / fs.refundQuotient) refundCounter

end ForkSchedule

end EVM

end EvmYul
