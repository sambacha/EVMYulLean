module

public import EvmYul.EVM.Gas.Costs
public import EvmYul.EVMException
public import EvmYul.EVM.Instr

public section

/-!
# Gas meter hardening

Supporting definitions for the gas model in `EvmYul/EVM/Gas/Costs.lean`. They address issues S2, S3 and S5
of the gas analysis:

* `feeGroup` classifies **every** EVM operation into a fee group. It is written without a wildcard
  arm, so adding a new opcode to `Operation` is a compile error here until the opcode is classified.
  This is the exhaustiveness guarantee missing from the `0` fallthrough of `C'` (S2). The
  theorems in `EvmYul/EVM/Gas/Lemmas.lean` prove that `C'` agrees with this classification.
* `chargeGas` is the single guarded deduction combinator: it fails with `OutOfGass` exactly when the
  cost exceeds the available gas, and otherwise subtracts without wrap-around (S3). `X` uses it for
  the memory-expansion charge (S5).
* `gasSub` is the proof-carrying subtraction: it can only be called with a proof that the cost fits.
* `refundedGas` is the EIP-3529 refund formula (YP (82)) exactly as used by `Υ`.
-/

namespace EvmYul

namespace EVM

namespace GasMeter

open GasConstants

@[expose] section

/--
Fee groups of YP Appendix G / H.1. Static groups have a state-independent cost. Dynamic groups
read the stack, the substate or the account map.
-/
inductive FeeGroup where
  /-- `W_zero`: STOP, RETURN, REVERT. -/
  | zero
  /-- `W_base`. -/
  | base
  /-- `W_verylow` (including PUSH1..32, DUP, SWAP). -/
  | verylow
  /-- `W_low`. -/
  | low
  /-- `W_mid`. -/
  | mid
  /-- `W_high`. -/
  | high
  /-- JUMPDEST: `G_jumpdest`. -/
  | jumpdest
  /-- BLOCKHASH: `G_blockhash`. -/
  | blockhash
  /-- BLOBHASH: `HASH_OPCODE_GAS`. -/
  | blobhash
  /-- TLOAD / TSTORE: `G_warmaccess`. -/
  | transient
  /-- `W_copy`: `G_verylow + G_copy * ⌈μₛ[2] / 32⌉`. -/
  | copy
  /-- `W_extaccount`: `C_access`. -/
  | extAccount
  /-- EXP. -/
  | exp
  /-- EXTCODECOPY. -/
  | extcodecopy
  /-- LOG0..LOG4. -/
  | log
  /-- KECCAK256. -/
  | keccak
  /-- CREATE / CREATE2. -/
  | create
  /-- SLOAD. -/
  | sload
  /-- SSTORE. -/
  | sstore
  /-- CALL, CALLCODE, DELEGATECALL, STATICCALL. -/
  | call
  /-- SELFDESTRUCT. -/
  | selfdestruct
  /-- INVALID: not an executable instruction (`δ = none`). -/
  | invalid
  deriving DecidableEq, Repr

end

/--
Static cost of a fee group, or `none` for groups whose cost depends on the state.
-/
@[expose] def FeeGroup.staticCost? : FeeGroup → Option ℕ
  | .zero      => some Gzero
  | .base      => some Gbase
  | .verylow   => some Gverylow
  | .low       => some Glow
  | .mid       => some Gmid
  | .high      => some Ghigh
  | .jumpdest  => some Gjumpdest
  | .blockhash => some Gblockhash
  | .blobhash  => some HASH_OPCODE_GAS
  | .transient => some Gwarmaccess
  | .copy | .extAccount | .exp | .extcodecopy | .log | .keccak | .create
  | .sload | .sstore | .call | .selfdestruct | .invalid => none

/--
Total fee classification of every EVM operation. **No wildcard arms**: Lean's exhaustiveness check
makes a newly added opcode a compile error here until it has been classified.
-/
@[expose] def feeGroup : Operation .EVM → FeeGroup
  | .StopArith op =>
    match op with
    | .STOP => .zero
    | .ADD => .verylow
    | .MUL => .low
    | .SUB => .verylow
    | .DIV => .low
    | .SDIV => .low
    | .MOD => .low
    | .SMOD => .low
    | .ADDMOD => .mid
    | .MULMOD => .mid
    | .EXP => .exp
    | .SIGNEXTEND => .low
  | .CompBit op =>
    match op with
    | .LT => .verylow
    | .GT => .verylow
    | .SLT => .verylow
    | .SGT => .verylow
    | .EQ => .verylow
    | .ISZERO => .verylow
    | .AND => .verylow
    | .OR => .verylow
    | .XOR => .verylow
    | .NOT => .verylow
    | .BYTE => .verylow
    | .SHL => .verylow
    | .SHR => .verylow
    | .SAR => .verylow
  | .Keccak op =>
    match op with
    | .KECCAK256 => .keccak
  | .Env op =>
    match op with
    | .ADDRESS => .base
    | .BALANCE => .extAccount
    | .ORIGIN => .base
    | .CALLER => .base
    | .CALLVALUE => .base
    | .CALLDATALOAD => .verylow
    | .CALLDATASIZE => .base
    | .CALLDATACOPY => .copy
    | .GASPRICE => .base
    | .CODESIZE => .base
    | .CODECOPY => .copy
    | .EXTCODESIZE => .extAccount
    | .EXTCODECOPY => .extcodecopy
    | .RETURNDATASIZE => .base
    | .RETURNDATACOPY => .copy
    | .EXTCODEHASH => .extAccount
  | .Block op =>
    match op with
    | .BLOCKHASH => .blockhash
    | .COINBASE => .base
    | .TIMESTAMP => .base
    | .NUMBER => .base
    | .PREVRANDAO => .base
    | .GASLIMIT => .base
    | .CHAINID => .base
    | .SELFBALANCE => .low
    | .BASEFEE => .base
    | .BLOBHASH => .blobhash
    | .BLOBBASEFEE => .base
  | .StackMemFlow op =>
    match op with
    | .POP => .base
    | .MLOAD => .verylow
    | .MSTORE => .verylow
    | .SLOAD => .sload
    | .SSTORE => .sstore
    | .MSTORE8 => .verylow
    | .JUMP => .mid
    | .JUMPI => .high
    | .PC => .base
    | .MSIZE => .base
    | .GAS => .base
    | .JUMPDEST => .jumpdest
    | .TLOAD => .transient
    | .TSTORE => .transient
    | .MCOPY => .copy
  | .Push op =>
    match op with
    | .PUSH0 => .base
    | .PUSH1 | .PUSH2 | .PUSH3 | .PUSH4 | .PUSH5 | .PUSH6 | .PUSH7 | .PUSH8
    | .PUSH9 | .PUSH10 | .PUSH11 | .PUSH12 | .PUSH13 | .PUSH14 | .PUSH15 | .PUSH16
    | .PUSH17 | .PUSH18 | .PUSH19 | .PUSH20 | .PUSH21 | .PUSH22 | .PUSH23 | .PUSH24
    | .PUSH25 | .PUSH26 | .PUSH27 | .PUSH28 | .PUSH29 | .PUSH30 | .PUSH31 | .PUSH32 => .verylow
  | .Dup op =>
    match op with
    | .DUP1 | .DUP2 | .DUP3 | .DUP4 | .DUP5 | .DUP6 | .DUP7 | .DUP8
    | .DUP9 | .DUP10 | .DUP11 | .DUP12 | .DUP13 | .DUP14 | .DUP15 | .DUP16 => .verylow
  | .Exchange op =>
    match op with
    | .SWAP1 | .SWAP2 | .SWAP3 | .SWAP4 | .SWAP5 | .SWAP6 | .SWAP7 | .SWAP8
    | .SWAP9 | .SWAP10 | .SWAP11 | .SWAP12 | .SWAP13 | .SWAP14 | .SWAP15 | .SWAP16 => .verylow
  | .Log op =>
    match op with
    | .LOG0 | .LOG1 | .LOG2 | .LOG3 | .LOG4 => .log
  | .System op =>
    match op with
    | .CREATE => .create
    | .CALL => .call
    | .CALLCODE => .call
    | .RETURN => .zero
    | .DELEGATECALL => .call
    | .CREATE2 => .create
    | .STATICCALL => .call
    | .REVERT => .zero
    | .INVALID => .invalid
    | .SELFDESTRUCT => .selfdestruct

/--
Guarded gas deduction: `OutOfGass` exactly when `c` exceeds the available gas, otherwise the
difference. On the success path the subtraction never wraps (see `chargeGas_ok_iff`).
-/
@[expose] def chargeGas (g : UInt256) (c : ℕ) : Except ExecutionException UInt256 :=
  if g.toNat < c then .error .OutOfGass else .ok (g - .ofNat c)

/--
Deduction of an instruction cost that `X` has **already** checked to fit: `exceptionalHalt` returns
`cost₂` only after testing `gasAvailable.toNat < cost₂` (raising `OutOfGass` otherwise), and
`step` / `call` then deduct it with this function. It is the only place in the interpreter that
subtracts from `gasAvailable` without a guard; the build-time lint in
`Audits/RawGasLint.lean` rejects any other raw subtraction (handoff PO-4).
`deductPrechecked_eq_gasSub` shows it is the exact difference whenever the pre-check held.
-/
@[expose] def deductPrechecked (g : UInt256) (c : ℕ) : UInt256 := g - .ofNat c

/--
Proof-carrying gas subtraction. It can only be called with a proof `h` that the cost fits into the
available gas, and it returns the remaining gas together with a certificate, derived from `h`,
that remaining gas plus cost is exactly the gas before the deduction (no wrap-around). Use `.val`
for the remaining gas.
-/
@[expose] def gasSub (g : UInt256) (c : ℕ) (h : c ≤ g.toNat) : {r : UInt256 // r.toNat + c = g.toNat} :=
  ⟨⟨⟨g.toNat - c, lt_of_le_of_lt (Nat.sub_le _ _) g.val.isLt⟩⟩, Nat.sub_add_cancel h⟩

/--
YP (82), EIP-3529: gas returned to the sender, `g* = g' + min(⌊(T_g − g')/5⌋, A_r)`.
-/
@[expose] def refundedGas (gasLimit gasLeft refundBalance : UInt256) : UInt256 :=
  gasLeft + min ((gasLimit - gasLeft) / ⟨5⟩) refundBalance

/--
The machine state after the memory-expansion charge `m` has been deducted. This is the state on
which `X` evaluates `C'`, and so `Cgascap` (issue S4). It is used to state the S4 lemmas.
-/
@[expose] def afterMemoryCharge (μ : MachineState) (m : ℕ) : MachineState :=
  { μ with gasAvailable := μ.gasAvailable - UInt256.ofNat m }

/--
Fuel added on top of the gas limit by `transactionFuel` for the frames' bookkeeping recursion
(`Υ` → `Θ`/`Lambda` → `Ξ` → `X`, and nested CALL/CREATE frames).
-/
@[expose] def fuelOverhead : ℕ := 2 ^ 14

/--
Fuel for executing a transaction (handoff C13 / CE-9). The conformance runner used to pass the
sender's balance as fuel, which is `0` for a zero-balance sender on a zero-fee chain, and `Υ 0 …`
fails with `OutOfFuel` for **every** transaction (`Υ_zero_fuel`). This takes the maximum of the old
choice and `gasLimit + fuelOverhead`, so it is never smaller than before (no test that passed can
newly run out of fuel) and it no longer depends on the sender's balance.
-/
@[expose] def transactionFuel (T : Transaction) (senderBalance : UInt256) : ℕ :=
  max senderBalance.toNat (T.base.gasLimit.toNat + fuelOverhead)

end GasMeter

end EVM

end EvmYul
