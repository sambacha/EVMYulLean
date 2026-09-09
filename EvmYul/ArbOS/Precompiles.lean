import Batteries.Data.RBMap

import EvmYul.ArbOS.Abi
import EvmYul.ArbOS.AddressAlias
import EvmYul.ArbOS.State

/-!
# ArbOS system contracts

Arbitrum exposes chain functionality through *system contracts* at fixed addresses
(`0x64 … 0x72`, `0xC8`).  They are reached by ordinary `CALL`s, so the model treats them
as a chain-specific precompile registry rather than as branches inside the interpreter
(RFC §13, §18).

Three rules shape this module.

1. **No silent defaults.**  An address that is a system contract but that the model does
   not implement returns `ExecutionException.unavailableFeature`; a method that is not
   implemented returns `ExecutionException.unsupportedMethod`.  Neither ever returns zero.
2. **Selectors are checked, not asserted.**  The constants below are cross-checked
   against `Keccak-256` of the method signature by `Tests.ArbOS.SelectorTests`.
3. **Nothing is invented.**  Values that ArbOS derives from state the model does not
   carry (block-hash history, aggregator statistics, …) are reported as unsupported, and
   gas usage — which this milestone does not price — is `none` rather than `0`.
-/

namespace EvmYul

namespace ArbOS

open Batteries (RBMap)

/-- How faithfully a system contract or method is modelled. -/
inductive SupportLevel where
  /-- Behaviour is derived from modelled state and believed faithful. -/
  | modeled
  /-- Present, but some methods return modelled-but-incomplete data. -/
  | modeledWithStub
  /-- Recognised address, deliberately not implemented; calls fail explicitly. -/
  | unsupported
  deriving DecidableEq, Repr, BEq, Inhabited

/-- The context of a call into an ArbOS system contract. -/
structure CallContext where
  /-- `msg.sender` as observed by the system contract. -/
  caller   : AccountAddress
  /-- The system contract being called. -/
  address  : AccountAddress
  /-- `msg.value`. -/
  value    : UInt256
  /-- Full calldata, including the 4-byte selector. -/
  calldata : ByteArray
  /-- Gas supplied to the call. -/
  gas      : UInt256
  /-- The L2 chain id of the active chain profile. -/
  chainId  : UInt256
  deriving Repr, BEq, Inhabited

/--
The result of a system-contract call.

`gasUsed = none` records that this milestone does not price ArbOS system calls; it is
deliberately not `some 0`, which would assert that such calls are free.
-/
structure CallResult where
  returnData : ByteArray
  state      : State
  gasUsed    : Option UInt256 := none
  deriving Repr, Inhabited

/-- The signature of a system-contract implementation. -/
abbrev CallFn := State → CallContext → Except ExecutionException CallResult

/-- An entry of the chain's system-contract registry. -/
structure SystemContract where
  address : AccountAddress
  name    : String
  support : SupportLevel
  call    : CallFn

/-- A system contract that is recognised but not implemented. -/
def unavailable (addr : AccountAddress) (name : String) : SystemContract where
  address := addr
  name := name
  support := .unsupported
  call := fun _ _ => .error (.unavailableFeature addr.val name)

/-! ## Addresses -/

def ArbSysAddress          : AccountAddress := 0x64
def ArbInfoAddress         : AccountAddress := 0x65
def ArbAddressTableAddress : AccountAddress := 0x66
def ArbFunctionTableAddress: AccountAddress := 0x68
def ArbOwnerPublicAddress  : AccountAddress := 0x6B
def ArbGasInfoAddress      : AccountAddress := 0x6C
def ArbAggregatorAddress   : AccountAddress := 0x6D
def ArbRetryableTxAddress  : AccountAddress := 0x6E
def ArbStatisticsAddress   : AccountAddress := 0x6F
def ArbOwnerAddress        : AccountAddress := 0x70
def ArbWasmAddress         : AccountAddress := 0x71
def ArbWasmCacheAddress    : AccountAddress := 0x72
def NodeInterfaceAddress   : AccountAddress := 0xC8

/-! ## ArbSys (0x64) -/

namespace ArbSys

/-- `arbBlockNumber()` -/
def arbBlockNumberSelector : UInt32 := 0xa3b1b31d
/-- `arbBlockHash(uint256)` -/
def arbBlockHashSelector : UInt32 := 0x2b407a82
/-- `arbChainID()` -/
def arbChainIDSelector : UInt32 := 0xd127f54a
/-- `arbOSVersion()` -/
def arbOSVersionSelector : UInt32 := 0x051038f2
/-- `isTopLevelCall()` -/
def isTopLevelCallSelector : UInt32 := 0x08bd624c
/-- `mapL1SenderContractAddressToL2Alias(address,address)` -/
def mapL1SenderSelector : UInt32 := 0x4dbbd506
/-- `wasMyCallersAddressAliased()` -/
def wasMyCallersAddressAliasedSelector : UInt32 := 0x175a260b
/-- `myCallersAddressWithoutAliasing()` -/
def myCallersAddressWithoutAliasingSelector : UInt32 := 0xd74523b3
/-- `withdrawEth(address)` -/
def withdrawEthSelector : UInt32 := 0x25e16063
/-- `sendTxToL1(address,bytes)` -/
def sendTxToL1Selector : UInt32 := 0x928c169a

/--
`ArbSys.arbOSVersion()` reports `55 + <internal ArbOS version>`; the offset is Nitro's
historical numbering convention and is named here rather than being buried in the
dispatcher, so that it can be revisited per protocol version.
-/
def arbOSVersionAbiOffset : Nat := 55

/-- The methods of `ArbSys` that this model implements. -/
inductive Method where
  | arbBlockNumber
  | arbChainID
  | arbOSVersion
  | isTopLevelCall
  | mapL1SenderContractAddressToL2Alias
  | wasMyCallersAddressAliased
  | myCallersAddressWithoutAliasing
  | withdrawEth
  | sendTxToL1
  deriving DecidableEq, Repr, BEq, Inhabited

/-- Selector → modelled method.  Unknown selectors are rejected by the caller. -/
def methodOfSelector (s : UInt32) : Option Method :=
  if s == arbBlockNumberSelector then some .arbBlockNumber
  else if s == arbChainIDSelector then some .arbChainID
  else if s == arbOSVersionSelector then some .arbOSVersion
  else if s == isTopLevelCallSelector then some .isTopLevelCall
  else if s == mapL1SenderSelector then some .mapL1SenderContractAddressToL2Alias
  else if s == wasMyCallersAddressAliasedSelector then some .wasMyCallersAddressAliased
  else if s == myCallersAddressWithoutAliasingSelector then
    some .myCallersAddressWithoutAliasing
  else if s == withdrawEthSelector then some .withdrawEth
  else if s == sendTxToL1Selector then some .sendTxToL1
  else none

/-- `ArbSys` dispatch: calldata → decode → state effect → returndata. -/
def call : CallFn := fun st ctx => do
  let some sel := ABI.selector ctx.calldata
    | .error .invalidCalldata
  let args := ABI.arguments ctx.calldata
  let some m := methodOfSelector sel
    | .error (.unsupportedMethod ctx.address.val sel)
  match m with
    | .arbBlockNumber =>
      .ok { returnData := ABI.encodeWord st.l2BlockNumber, state := st }
    | .arbChainID =>
      .ok { returnData := ABI.encodeWord ctx.chainId, state := st }
    | .arbOSVersion =>
      .ok { returnData := ABI.encodeWord (.ofNat (arbOSVersionAbiOffset + st.version.major))
          , state := st }
    | .isTopLevelCall =>
      .ok { returnData := ABI.encodeBool st.topLevelCall, state := st }
    | .wasMyCallersAddressAliased =>
      .ok { returnData := ABI.encodeBool st.callerAliased, state := st }
    | .myCallersAddressWithoutAliasing =>
      let caller := if st.callerAliased then undoAddressAlias ctx.caller else ctx.caller
      .ok { returnData := ABI.encodeAddress caller, state := st }
    | .mapL1SenderContractAddressToL2Alias =>
      let some sender := ABI.decodeAddress args 0
        | .error .invalidCalldata
      .ok { returnData := ABI.encodeAddress (applyAddressAlias sender), state := st }
    | .withdrawEth =>
      let some dest := ABI.decodeAddress args 0
        | .error .invalidCalldata
      let (st', msg) := st.pushL2ToL1 ctx.caller dest ctx.value .empty
      .ok { returnData := ABI.encodeWord msg.index, state := st' }
    | .sendTxToL1 =>
      let some dest := ABI.decodeAddress args 0
        | .error .invalidCalldata
      let some payload := ABI.decodeBytes args 1
        | .error .invalidCalldata
      let (st', msg) := st.pushL2ToL1 ctx.caller dest ctx.value payload
      .ok { returnData := ABI.encodeWord msg.index, state := st' }

end ArbSys

/-! ## ArbGasInfo (0x6C) -/

namespace ArbGasInfo

/-- `getPricesInWei()` -/
def getPricesInWeiSelector : UInt32 := 0x41b247a8
/-- `getL1BaseFeeEstimate()` -/
def getL1BaseFeeEstimateSelector : UInt32 := 0xf5d6ded7
/-- `getMinimumGasPrice()` -/
def getMinimumGasPriceSelector : UInt32 := 0xf918379a
/-- `getCurrentTxL1GasFees()` -/
def getCurrentTxL1GasFeesSelector : UInt32 := 0xc6f7de0e

/-- The methods of `ArbGasInfo` that this model implements. -/
inductive Method where
  | getPricesInWei
  | getL1BaseFeeEstimate
  | getMinimumGasPrice
  | getCurrentTxL1GasFees
  deriving DecidableEq, Repr, BEq, Inhabited

def methodOfSelector (s : UInt32) : Option Method :=
  if s == getPricesInWeiSelector then some .getPricesInWei
  else if s == getL1BaseFeeEstimateSelector then some .getL1BaseFeeEstimate
  else if s == getMinimumGasPriceSelector then some .getMinimumGasPrice
  else if s == getCurrentTxL1GasFeesSelector then some .getCurrentTxL1GasFees
  else none

/--
`getPricesInWei()` returns
`(perL2Tx, perL1CalldataByte, perStorageAllocation, perArbGasBase, perArbGasCongestion,
perArbGasTotal)`; every component is a projection of `GasState`, so the model cannot
report a price it does not hold.
-/
def pricesInWei (g : GasState) : List UInt256 :=
  [ g.perL2Tx
  , g.perL1CalldataByte
  , g.perStorageAllocation
  , g.l2BaseFee
  , g.perArbGasCongestion
  , g.perArbGasTotal ]

def call : CallFn := fun st ctx => do
  let some sel := ABI.selector ctx.calldata
    | .error .invalidCalldata
  let some m := methodOfSelector sel
    | .error (.unsupportedMethod ctx.address.val sel)
  match m with
    | .getPricesInWei =>
      .ok { returnData := ABI.encodeWords (pricesInWei st.gas), state := st }
    | .getL1BaseFeeEstimate =>
      .ok { returnData := ABI.encodeWord st.gas.l1BaseFeeEstimate, state := st }
    | .getMinimumGasPrice =>
      .ok { returnData := ABI.encodeWord st.gas.minimumGasPrice, state := st }
    | .getCurrentTxL1GasFees =>
      .ok { returnData := ABI.encodeWord st.gas.l1DataFee, state := st }

end ArbGasInfo

/-! ## Registry -/

/-- A registry of system contracts, keyed by address. -/
abbrev Registry := RBMap AccountAddress SystemContract compare

def Registry.ofList (cs : List SystemContract) : Registry :=
  cs.foldl (fun acc c => acc.insert c.address c) (RBMap.empty)

def Registry.lookup (r : Registry) (a : AccountAddress) : Option SystemContract :=
  r.find? a

/--
The ArbOS 61 system-contract surface.

Everything Robinhood Chain exposes is listed; entries that this milestone does not model
are present with `SupportLevel.unsupported` so that a call to them fails explicitly
instead of falling through to "no code at this address, return success with empty data".
-/
def arbOS61SystemContracts : Registry :=
  Registry.ofList
    [ { address := ArbSysAddress, name := "ArbSys", support := .modeledWithStub
      , call := ArbSys.call }
    , { address := ArbGasInfoAddress, name := "ArbGasInfo", support := .modeledWithStub
      , call := ArbGasInfo.call }
    , unavailable ArbInfoAddress "ArbInfo"
    , unavailable ArbAddressTableAddress "ArbAddressTable"
    , unavailable ArbFunctionTableAddress "ArbFunctionTable"
    , unavailable ArbOwnerPublicAddress "ArbOwnerPublic"
    , unavailable ArbAggregatorAddress "ArbAggregator"
    , unavailable ArbRetryableTxAddress "ArbRetryableTx"
    , unavailable ArbStatisticsAddress "ArbStatistics"
    , unavailable ArbOwnerAddress "ArbOwner"
    , unavailable ArbWasmAddress "ArbWasm"
    , unavailable ArbWasmCacheAddress "ArbWasmCache"
    , unavailable NodeInterfaceAddress "NodeInterface" ]

/-! ## Invariants -/

section Invariants

variable (st : State) (ctx : CallContext)

/-- RFC §20.4: `ArbSys.arbBlockNumber` is exactly the modelled L2 block height. -/
theorem arbBlockNumber_eq_l2BlockNumber
    (h : ABI.selector ctx.calldata = some ArbSys.arbBlockNumberSelector) :
    ArbSys.call st ctx = .ok { returnData := ABI.encodeWord st.l2BlockNumber, state := st } := by
  simp [ArbSys.call, h, ArbSys.methodOfSelector, ArbSys.arbBlockNumberSelector]

/--
RFC §20.5 (context separation): changing the L2 block height changes
`ArbSys.arbBlockNumber` and nothing else in the ArbOS state.
-/
theorem arbBlockNumber_tracks_l2BlockNumber (n : UInt256)
    (h : ABI.selector ctx.calldata = some ArbSys.arbBlockNumberSelector) :
    ArbSys.call { st with l2BlockNumber := n } ctx =
      .ok { returnData := ABI.encodeWord n, state := { st with l2BlockNumber := n } } :=
  arbBlockNumber_eq_l2BlockNumber _ ctx h

/-- RFC §20.7: `ArbSys.arbBlockNumber` is a pure read; it does not mutate ArbOS state. -/
theorem arbBlockNumber_no_state_effect
    (h : ABI.selector ctx.calldata = some ArbSys.arbBlockNumberSelector) :
    (ArbSys.call st ctx).map CallResult.state = .ok st := by
  simp [arbBlockNumber_eq_l2BlockNumber st ctx h, Except.map]

/-- An unmodelled `ArbSys` selector fails explicitly rather than returning a value. -/
theorem arbSys_unsupported_selector (s : UInt32)
    (hs : ArbSys.methodOfSelector s = none)
    (h : ABI.selector ctx.calldata = some s) :
    ArbSys.call st ctx = .error (.unsupportedMethod ctx.address.val s) := by
  simp [ArbSys.call, h, hs]

/-- Calldata shorter than a selector is rejected. -/
theorem arbSys_short_calldata (h : ABI.selector ctx.calldata = none) :
    ArbSys.call st ctx = .error .invalidCalldata := by
  simp [ArbSys.call, h]

/-- Every registered-but-unimplemented system contract fails explicitly. -/
theorem unavailable_call_error (a : AccountAddress) (n : String) :
    (unavailable a n).call st ctx = .error (.unavailableFeature a.val n) := rfl

/-- RFC §20.9: reading the fee state never changes it, so no fee can be charged twice. -/
theorem arbGasInfo_no_state_effect
    (h : (ABI.selector ctx.calldata).bind ArbGasInfo.methodOfSelector ≠ none) :
    (ArbGasInfo.call st ctx).map CallResult.state = .ok st := by
  rcases hsel : ABI.selector ctx.calldata with _ | s
  · simp [hsel] at h
  · rcases hm : ArbGasInfo.methodOfSelector s with _ | m
    · simp [hsel, hm] at h
    · cases m <;> simp [ArbGasInfo.call, hsel, hm, Except.map]

end Invariants

end ArbOS

end EvmYul
