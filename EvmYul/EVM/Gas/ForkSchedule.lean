module

public import Mathlib.Order.Basic

public section

/-!
# Fork-indexed gas schedules (Frontier → Cancun / Prague / Osaka)

`ForkSchedule` is the single source of truth for every gas price and every gas-relevant protocol
parameter of the EVM. It replaces the flat list of constants that used to live in
`EvmYul/EVM/Gas/Constants.lean`: those names are now *defined* as projections of
`ForkSchedule.cancun` (the fork the interpreter implements), so the executable interpreter sees
exactly the same numbers as before, by definitional unfolding.

Each named fork is a flat literal record (flat, so that projections such as `cancun.Gbase` reduce
in one step). `EvmYul/EVM/Gas/ForkSchedulePins.lean` pins them twice, by `rfl`: `<fork>_def` restates
every field literally, and `<fork>_eq_prev` states that each fork is the previous one updated with
exactly the fields changed by its EIPs. An accidental edit of any value is a build failure.

Besides prices, a schedule carries the *rule switches* that changed how a price is computed:

* `callGasRetention` (EIP-150): `some 64` for "all but one 64th", `none` before Tangerine Whistle
  (the requested call gas is charged and forwarded as is);
* `eip2929` (Berlin): warm/cold account and storage access instead of flat access prices;
* `sstoreRule`: the Frontier rule, or EIP-2200 net metering (Istanbul);
* `selfdestructNewAccount` (EIP-150): SELFDESTRUCT pays `Gnewaccount` when it creates an account;
* `refundQuotient` (EIP-3529): the refund cap divisor, 2 before London and 5 from London on;
* `maxInitcodeSize` (EIP-3860), `maxCodeSize` (EIP-170), `txDataFloorPerToken` (EIP-7623),
  `txGasLimitCap` (EIP-7825), `perEmptyAccountCost` (EIP-7702) are recorded as data.

`Fork.introduces` records which fork introduced each opcode-family; `ForkSchedule.cost` (in
`EvmYul/EVM/Gas/ForkCost.lean`) treats an opcode as invalid in a fork that predates it.

Scope note: the per-opcode cost function (`Gas/ForkCost.lean`) reproduces the Berlin-and-later dynamic
rules exactly (these are the only ones the interpreter executes, and the Cancun instance is proved
equal to the interpreter's `C'`). For pre-Berlin forks it uses the flat access prices, the
EIP-150 switch, the Frontier/EIP-2200 SSTORE rules and the per-fork constants recorded here; the
pre-EIP-161 "new account" rule for CALL and the short-lived EIP-1283 (Constantinople) SSTORE rule
are **not** modelled (Constantinople is represented by Petersburg, which removed EIP-1283).
Prague's EIP-7702 delegated-code access charge and Osaka's CLZ opcode (EIP-7939) concern features
the interpreter does not implement; precompile pricing (e.g. EIP-7883) is outside the gas model.
-/

namespace EvmYul

namespace EVM

@[expose] section

/-- The hard forks with a distinct gas schedule, in chronological order. Constantinople is
represented by Petersburg (Constantinople's EIP-1283 was removed before it activated on mainnet). -/
inductive Fork where
  | frontier
  | homestead
  | tangerineWhistle
  | spuriousDragon
  | byzantium
  | petersburg
  | istanbul
  | berlin
  | london
  | shanghai
  | cancun
  | prague
  | osaka
  deriving DecidableEq, Repr

end

namespace Fork

/-- Chronological index of a fork. -/
@[expose] def toNat : Fork → ℕ
  | frontier => 0
  | homestead => 1
  | tangerineWhistle => 2
  | spuriousDragon => 3
  | byzantium => 4
  | petersburg => 5
  | istanbul => 6
  | berlin => 7
  | london => 8
  | shanghai => 9
  | cancun => 10
  | prague => 11
  | osaka => 12

@[expose] instance : LE Fork := ⟨fun a b => a.toNat ≤ b.toNat⟩

@[expose] instance (a b : Fork) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.toNat ≤ b.toNat))

/-- All forks, in chronological order. -/
@[expose] def all : List Fork :=
  [frontier, homestead, tangerineWhistle, spuriousDragon, byzantium, petersburg, istanbul, berlin,
    london, shanghai, cancun, prague, osaka]

theorem mem_all (f : Fork) : f ∈ all := by cases f <;> decide

theorem toNat_injective : Function.Injective toNat := by
  intro a b h; cases a <;> cases b <;> first | rfl | (simp [toNat] at h)

end Fork

@[expose] section

/-- How SSTORE is priced. -/
inductive SstoreRule where
  /-- Frontier–Petersburg: `Gsset` when a zero slot becomes non-zero, `Gsreset` otherwise. -/
  | frontier
  /-- EIP-2200 (Istanbul) net gas metering, with EIP-2929 warm/cold pricing from Berlin on. -/
  | netMetered
  deriving DecidableEq, Repr

end

@[expose] section

/-- A complete gas schedule: every price of the Yellow Paper's Appendix G and every rule switch
that changed between forks. -/
structure ForkSchedule where
  /-- The fork this schedule belongs to (determines opcode availability). -/
  fork : Fork
  /-- Nothing is paid for operations of the set `W_zero` (STOP, RETURN, REVERT). -/
  Gzero : ℕ
  /-- Amount of gas to pay for a JUMPDEST operation. -/
  Gjumpdest : ℕ
  /-- Amount of gas to pay for operations of the set `W_base`. -/
  Gbase : ℕ
  /-- Amount of gas to pay for operations of the set `W_verylow`. -/
  Gverylow : ℕ
  /-- Amount of gas to pay for operations of the set `W_low`. -/
  Glow : ℕ
  /-- Amount of gas to pay for operations of the set `W_mid`. -/
  Gmid : ℕ
  /-- Amount of gas to pay for operations of the set `W_high`. -/
  Ghigh : ℕ
  /-- Cost of a warm account or storage access (EIP-2929); also the TLOAD/TSTORE price. -/
  Gwarmaccess : ℕ
  /-- Cost of warming up an account with the access list (EIP-2930). -/
  Gaccesslistaddress : ℕ
  /-- Cost of warming up a storage slot with the access list (EIP-2930). -/
  Gaccessliststorage : ℕ
  /-- Cost of a cold account access (EIP-2929). -/
  Gcoldaccountaccess : ℕ
  /-- Cost of a cold storage access (EIP-2929). -/
  Gcoldsload : ℕ
  /-- Paid for an SSTORE that sets a storage value to non-zero from (original) zero. -/
  Gsset : ℕ
  /-- Paid for an SSTORE that changes an original non-zero storage value. -/
  Gsreset : ℕ
  /-- Refund given (added to the refund counter) when a storage value is set to zero from
  non-zero. -/
  Rsclear : ℕ
  /-- Refund for a SELFDESTRUCT (removed by EIP-3529). -/
  Rselfdestruct : ℕ
  /-- Amount of gas to pay for a SELFDESTRUCT operation. -/
  Gselfdestruct : ℕ
  /-- Paid for a CREATE or CREATE2 operation. -/
  Gcreate : ℕ
  /-- Paid per byte for a CREATE operation to succeed in placing code into the state. -/
  Gcodedeposit : ℕ
  /-- Paid per 32-byte word of initcode by CREATE, CREATE2 and creation transactions (EIP-3860).
  -/
  Ginitcodeword : ℕ
  /-- Paid for a non-zero value transfer as part of a CALL or CALLCODE operation. -/
  Gcallvalue : ℕ
  /-- Stipend given to the callee of a value-transferring call (part of `Gcallvalue`). -/
  Gcallstipend : ℕ
  /-- Paid for a CALL or SELFDESTRUCT operation that creates an account. -/
  Gnewaccount : ℕ
  /-- Base payment for an EXP operation. -/
  Gexp : ℕ
  /-- Payment per byte of the exponent of an EXP operation. -/
  Gexpbyte : ℕ
  /-- Paid for every additional 32-byte word when expanding memory (linear part of `Cₘ`). -/
  Gmemory : ℕ
  /-- Paid by every contract-creating transaction. -/
  Gtxcreate : ℕ
  /-- Paid for every zero byte of transaction data. -/
  Gtxdatazero : ℕ
  /-- Paid for every non-zero byte of transaction data. -/
  Gtxdatanonzero : ℕ
  /-- Paid for every transaction (the intrinsic base cost). -/
  Gtransaction : ℕ
  /-- Base payment for a LOG operation. -/
  Glog : ℕ
  /-- Paid for each byte of a LOG operation's data. -/
  Glogdata : ℕ
  /-- Paid for each topic of a LOG operation. -/
  Glogtopic : ℕ
  /-- Base payment for a KECCAK256 operation. -/
  Gkeccak256 : ℕ
  /-- Paid for each 32-byte word (rounded up) of KECCAK256 input; also per word of CREATE2
  initcode hashing. -/
  Gkeccak256word : ℕ
  /-- Payment per 32-byte word (rounded up) copied by the `*COPY` operations. -/
  Gcopy : ℕ
  /-- Payment for a BLOCKHASH operation. -/
  Gblockhash : ℕ
  /-- Payment for a BLOBHASH operation (EIP-4844). -/
  HASH_OPCODE_GAS : ℕ
  /-- Flat SLOAD price before EIP-2929 (Frontier 50, EIP-150 200, EIP-1884 800); also the
  "no-op" price of EIP-2200 net metering before Berlin. Ignored when `eip2929`. -/
  Gsload : ℕ
  /-- Flat BALANCE price before EIP-2929 (Frontier 20, EIP-150 400, EIP-1884 700). Ignored when
  `eip2929`. -/
  Gbalance : ℕ
  /-- Flat EXTCODESIZE / EXTCODECOPY base price before EIP-2929 (Frontier 20, EIP-150 700).
  Ignored when `eip2929`. -/
  Gextcode : ℕ
  /-- Flat EXTCODEHASH price before EIP-2929 (EIP-1052 400, EIP-1884 700). Ignored when
  `eip2929`. -/
  Gextcodehash : ℕ
  /-- Flat CALL-family base price before EIP-2929 (Frontier 40, EIP-150 700). Ignored when
  `eip2929`. -/
  Gcall : ℕ
  /-- EIP-150 call-gas retention divisor: `some 64` forwards at most "all but one 64th";
  `none` (before Tangerine Whistle) charges and forwards the requested gas unchanged. -/
  callGasRetention : Option ℕ
  /-- EIP-2929 warm/cold access pricing (Berlin and later). -/
  eip2929 : Bool
  /-- The SSTORE pricing rule. -/
  sstoreRule : SstoreRule
  /-- EIP-150: SELFDESTRUCT pays `Gnewaccount` when it sends value to a dead account. -/
  selfdestructNewAccount : Bool
  /-- Refund cap divisor: the refund is at most `⌊gas used / refundQuotient⌋` (2 before London,
  5 since EIP-3529). -/
  refundQuotient : ℕ
  /-- Maximum deployed code size (EIP-170), if any. -/
  maxCodeSize : Option ℕ
  /-- Maximum initcode size (EIP-3860), if any. -/
  maxInitcodeSize : Option ℕ
  /-- Calldata floor price per token (EIP-7623), if any. -/
  txDataFloorPerToken : Option ℕ
  /-- Per-transaction gas-limit cap (EIP-7825), if any. -/
  txGasLimitCap : Option ℕ
  /-- EIP-7702 cost of an authorization targeting an empty account, if set-code transactions
  exist. -/
  perEmptyAccountCost : Option ℕ
  deriving DecidableEq, Repr

end

namespace ForkSchedule

/-- Frontier (2015). -/
@[expose, reducible] def frontier : ForkSchedule :=
    { fork := .frontier, Gzero := 0, Gjumpdest := 1, Gbase := 2, Gverylow := 3, Glow := 5,
      Gmid := 8, Ghigh := 10, Gwarmaccess := 0, Gaccesslistaddress := 0, Gaccessliststorage := 0,
      Gcoldaccountaccess := 0, Gcoldsload := 0, Gsset := 20000, Gsreset := 5000, Rsclear := 15000,
      Rselfdestruct := 24000, Gselfdestruct := 0, Gcreate := 32000, Gcodedeposit := 200,
      Ginitcodeword := 0, Gcallvalue := 9000, Gcallstipend := 2300, Gnewaccount := 25000,
      Gexp := 10, Gexpbyte := 10, Gmemory := 3, Gtxcreate := 0, Gtxdatazero := 4,
      Gtxdatanonzero := 68, Gtransaction := 21000, Glog := 375, Glogdata := 8, Glogtopic := 375,
      Gkeccak256 := 30, Gkeccak256word := 6, Gcopy := 3, Gblockhash := 20, HASH_OPCODE_GAS := 0,
      Gsload := 50, Gbalance := 20, Gextcode := 20, Gextcodehash := 0, Gcall := 40,
      callGasRetention := none, eip2929 := false, sstoreRule := .frontier,
      selfdestructNewAccount := false, refundQuotient := 2, maxCodeSize := none,
      maxInitcodeSize := none, txDataFloorPerToken := none, txGasLimitCap := none,
      perEmptyAccountCost := none }

/-- Homestead: EIP-2 (contract-creating transactions pay `Gtxcreate = 32000`). -/
@[expose, reducible] def homestead : ForkSchedule :=
    { fork := .homestead, Gzero := 0, Gjumpdest := 1, Gbase := 2, Gverylow := 3, Glow := 5,
      Gmid := 8, Ghigh := 10, Gwarmaccess := 0, Gaccesslistaddress := 0, Gaccessliststorage := 0,
      Gcoldaccountaccess := 0, Gcoldsload := 0, Gsset := 20000, Gsreset := 5000, Rsclear := 15000,
      Rselfdestruct := 24000, Gselfdestruct := 0, Gcreate := 32000, Gcodedeposit := 200,
      Ginitcodeword := 0, Gcallvalue := 9000, Gcallstipend := 2300, Gnewaccount := 25000,
      Gexp := 10, Gexpbyte := 10, Gmemory := 3, Gtxcreate := 32000, Gtxdatazero := 4,
      Gtxdatanonzero := 68, Gtransaction := 21000, Glog := 375, Glogdata := 8, Glogtopic := 375,
      Gkeccak256 := 30, Gkeccak256word := 6, Gcopy := 3, Gblockhash := 20, HASH_OPCODE_GAS := 0,
      Gsload := 50, Gbalance := 20, Gextcode := 20, Gextcodehash := 0, Gcall := 40,
      callGasRetention := none, eip2929 := false, sstoreRule := .frontier,
      selfdestructNewAccount := false, refundQuotient := 2, maxCodeSize := none,
      maxInitcodeSize := none, txDataFloorPerToken := none, txGasLimitCap := none,
      perEmptyAccountCost := none }

/-- Tangerine Whistle: EIP-150 (IO-heavy repricing and the 63/64 call-gas rule). -/
@[expose, reducible] def tangerineWhistle : ForkSchedule :=
    { fork := .tangerineWhistle, Gzero := 0, Gjumpdest := 1, Gbase := 2, Gverylow := 3, Glow := 5,
      Gmid := 8, Ghigh := 10, Gwarmaccess := 0, Gaccesslistaddress := 0, Gaccessliststorage := 0,
      Gcoldaccountaccess := 0, Gcoldsload := 0, Gsset := 20000, Gsreset := 5000, Rsclear := 15000,
      Rselfdestruct := 24000, Gselfdestruct := 5000, Gcreate := 32000, Gcodedeposit := 200,
      Ginitcodeword := 0, Gcallvalue := 9000, Gcallstipend := 2300, Gnewaccount := 25000,
      Gexp := 10, Gexpbyte := 10, Gmemory := 3, Gtxcreate := 32000, Gtxdatazero := 4,
      Gtxdatanonzero := 68, Gtransaction := 21000, Glog := 375, Glogdata := 8, Glogtopic := 375,
      Gkeccak256 := 30, Gkeccak256word := 6, Gcopy := 3, Gblockhash := 20, HASH_OPCODE_GAS := 0,
      Gsload := 200, Gbalance := 400, Gextcode := 700, Gextcodehash := 0, Gcall := 700,
      callGasRetention := some 64, eip2929 := false, sstoreRule := .frontier,
      selfdestructNewAccount := true, refundQuotient := 2, maxCodeSize := none,
      maxInitcodeSize := none, txDataFloorPerToken := none, txGasLimitCap := none,
      perEmptyAccountCost := none }

/-- Spurious Dragon: EIP-160 (EXP byte price) and EIP-170 (code size limit). -/
@[expose, reducible] def spuriousDragon : ForkSchedule :=
    { fork := .spuriousDragon, Gzero := 0, Gjumpdest := 1, Gbase := 2, Gverylow := 3, Glow := 5,
      Gmid := 8, Ghigh := 10, Gwarmaccess := 0, Gaccesslistaddress := 0, Gaccessliststorage := 0,
      Gcoldaccountaccess := 0, Gcoldsload := 0, Gsset := 20000, Gsreset := 5000, Rsclear := 15000,
      Rselfdestruct := 24000, Gselfdestruct := 5000, Gcreate := 32000, Gcodedeposit := 200,
      Ginitcodeword := 0, Gcallvalue := 9000, Gcallstipend := 2300, Gnewaccount := 25000,
      Gexp := 10, Gexpbyte := 50, Gmemory := 3, Gtxcreate := 32000, Gtxdatazero := 4,
      Gtxdatanonzero := 68, Gtransaction := 21000, Glog := 375, Glogdata := 8, Glogtopic := 375,
      Gkeccak256 := 30, Gkeccak256word := 6, Gcopy := 3, Gblockhash := 20, HASH_OPCODE_GAS := 0,
      Gsload := 200, Gbalance := 400, Gextcode := 700, Gextcodehash := 0, Gcall := 700,
      callGasRetention := some 64, eip2929 := false, sstoreRule := .frontier,
      selfdestructNewAccount := true, refundQuotient := 2, maxCodeSize := some 24576,
      maxInitcodeSize := none, txDataFloorPerToken := none, txGasLimitCap := none,
      perEmptyAccountCost := none }

/-- Byzantium: no price changes (REVERT, RETURNDATA*, STATICCALL are introduced). -/
@[expose, reducible] def byzantium : ForkSchedule :=
    { fork := .byzantium, Gzero := 0, Gjumpdest := 1, Gbase := 2, Gverylow := 3, Glow := 5,
      Gmid := 8, Ghigh := 10, Gwarmaccess := 0, Gaccesslistaddress := 0, Gaccessliststorage := 0,
      Gcoldaccountaccess := 0, Gcoldsload := 0, Gsset := 20000, Gsreset := 5000, Rsclear := 15000,
      Rselfdestruct := 24000, Gselfdestruct := 5000, Gcreate := 32000, Gcodedeposit := 200,
      Ginitcodeword := 0, Gcallvalue := 9000, Gcallstipend := 2300, Gnewaccount := 25000,
      Gexp := 10, Gexpbyte := 50, Gmemory := 3, Gtxcreate := 32000, Gtxdatazero := 4,
      Gtxdatanonzero := 68, Gtransaction := 21000, Glog := 375, Glogdata := 8, Glogtopic := 375,
      Gkeccak256 := 30, Gkeccak256word := 6, Gcopy := 3, Gblockhash := 20, HASH_OPCODE_GAS := 0,
      Gsload := 200, Gbalance := 400, Gextcode := 700, Gextcodehash := 0, Gcall := 700,
      callGasRetention := some 64, eip2929 := false, sstoreRule := .frontier,
      selfdestructNewAccount := true, refundQuotient := 2, maxCodeSize := some 24576,
      maxInitcodeSize := none, txDataFloorPerToken := none, txGasLimitCap := none,
      perEmptyAccountCost := none }

/-- Petersburg (= Constantinople without EIP-1283): EIP-1052 EXTCODEHASH at 400. -/
@[expose, reducible] def petersburg : ForkSchedule :=
    { fork := .petersburg, Gzero := 0, Gjumpdest := 1, Gbase := 2, Gverylow := 3, Glow := 5,
      Gmid := 8, Ghigh := 10, Gwarmaccess := 0, Gaccesslistaddress := 0, Gaccessliststorage := 0,
      Gcoldaccountaccess := 0, Gcoldsload := 0, Gsset := 20000, Gsreset := 5000, Rsclear := 15000,
      Rselfdestruct := 24000, Gselfdestruct := 5000, Gcreate := 32000, Gcodedeposit := 200,
      Ginitcodeword := 0, Gcallvalue := 9000, Gcallstipend := 2300, Gnewaccount := 25000,
      Gexp := 10, Gexpbyte := 50, Gmemory := 3, Gtxcreate := 32000, Gtxdatazero := 4,
      Gtxdatanonzero := 68, Gtransaction := 21000, Glog := 375, Glogdata := 8, Glogtopic := 375,
      Gkeccak256 := 30, Gkeccak256word := 6, Gcopy := 3, Gblockhash := 20, HASH_OPCODE_GAS := 0,
      Gsload := 200, Gbalance := 400, Gextcode := 700, Gextcodehash := 400, Gcall := 700,
      callGasRetention := some 64, eip2929 := false, sstoreRule := .frontier,
      selfdestructNewAccount := true, refundQuotient := 2, maxCodeSize := some 24576,
      maxInitcodeSize := none, txDataFloorPerToken := none, txGasLimitCap := none,
      perEmptyAccountCost := none }

/-- Istanbul: EIP-1884 (SLOAD 800, BALANCE 700, EXTCODEHASH 700), EIP-2028 (non-zero calldata
16) and EIP-2200 (net-metered SSTORE). -/
@[expose, reducible] def istanbul : ForkSchedule :=
    { fork := .istanbul, Gzero := 0, Gjumpdest := 1, Gbase := 2, Gverylow := 3, Glow := 5,
      Gmid := 8, Ghigh := 10, Gwarmaccess := 0, Gaccesslistaddress := 0, Gaccessliststorage := 0,
      Gcoldaccountaccess := 0, Gcoldsload := 0, Gsset := 20000, Gsreset := 5000, Rsclear := 15000,
      Rselfdestruct := 24000, Gselfdestruct := 5000, Gcreate := 32000, Gcodedeposit := 200,
      Ginitcodeword := 0, Gcallvalue := 9000, Gcallstipend := 2300, Gnewaccount := 25000,
      Gexp := 10, Gexpbyte := 50, Gmemory := 3, Gtxcreate := 32000, Gtxdatazero := 4,
      Gtxdatanonzero := 16, Gtransaction := 21000, Glog := 375, Glogdata := 8, Glogtopic := 375,
      Gkeccak256 := 30, Gkeccak256word := 6, Gcopy := 3, Gblockhash := 20, HASH_OPCODE_GAS := 0,
      Gsload := 800, Gbalance := 700, Gextcode := 700, Gextcodehash := 700, Gcall := 700,
      callGasRetention := some 64, eip2929 := false, sstoreRule := .netMetered,
      selfdestructNewAccount := true, refundQuotient := 2, maxCodeSize := some 24576,
      maxInitcodeSize := none, txDataFloorPerToken := none, txGasLimitCap := none,
      perEmptyAccountCost := none }

/-- Berlin: EIP-2929 (warm/cold access, `Gsreset = 5000 − 2100`) and EIP-2930 (access lists). -/
@[expose, reducible] def berlin : ForkSchedule :=
    { fork := .berlin, Gzero := 0, Gjumpdest := 1, Gbase := 2, Gverylow := 3, Glow := 5,
      Gmid := 8, Ghigh := 10, Gwarmaccess := 100, Gaccesslistaddress := 2400,
      Gaccessliststorage := 1900, Gcoldaccountaccess := 2600, Gcoldsload := 2100, Gsset := 20000,
      Gsreset := 2900, Rsclear := 15000, Rselfdestruct := 24000, Gselfdestruct := 5000,
      Gcreate := 32000, Gcodedeposit := 200, Ginitcodeword := 0, Gcallvalue := 9000,
      Gcallstipend := 2300, Gnewaccount := 25000, Gexp := 10, Gexpbyte := 50, Gmemory := 3,
      Gtxcreate := 32000, Gtxdatazero := 4, Gtxdatanonzero := 16, Gtransaction := 21000,
      Glog := 375, Glogdata := 8, Glogtopic := 375, Gkeccak256 := 30, Gkeccak256word := 6,
      Gcopy := 3, Gblockhash := 20, HASH_OPCODE_GAS := 0, Gsload := 800, Gbalance := 700,
      Gextcode := 700, Gextcodehash := 700, Gcall := 700, callGasRetention := some 64,
      eip2929 := true, sstoreRule := .netMetered, selfdestructNewAccount := true,
      refundQuotient := 2, maxCodeSize := some 24576, maxInitcodeSize := none,
      txDataFloorPerToken := none, txGasLimitCap := none, perEmptyAccountCost := none }

/-- London: EIP-3529 (refund cap `⌊used/5⌋`, `Rsclear = 4800`, no SELFDESTRUCT refund). -/
@[expose, reducible] def london : ForkSchedule :=
    { fork := .london, Gzero := 0, Gjumpdest := 1, Gbase := 2, Gverylow := 3, Glow := 5,
      Gmid := 8, Ghigh := 10, Gwarmaccess := 100, Gaccesslistaddress := 2400,
      Gaccessliststorage := 1900, Gcoldaccountaccess := 2600, Gcoldsload := 2100, Gsset := 20000,
      Gsreset := 2900, Rsclear := 4800, Rselfdestruct := 0, Gselfdestruct := 5000,
      Gcreate := 32000, Gcodedeposit := 200, Ginitcodeword := 0, Gcallvalue := 9000,
      Gcallstipend := 2300, Gnewaccount := 25000, Gexp := 10, Gexpbyte := 50, Gmemory := 3,
      Gtxcreate := 32000, Gtxdatazero := 4, Gtxdatanonzero := 16, Gtransaction := 21000,
      Glog := 375, Glogdata := 8, Glogtopic := 375, Gkeccak256 := 30, Gkeccak256word := 6,
      Gcopy := 3, Gblockhash := 20, HASH_OPCODE_GAS := 0, Gsload := 800, Gbalance := 700,
      Gextcode := 700, Gextcodehash := 700, Gcall := 700, callGasRetention := some 64,
      eip2929 := true, sstoreRule := .netMetered, selfdestructNewAccount := true,
      refundQuotient := 5, maxCodeSize := some 24576, maxInitcodeSize := none,
      txDataFloorPerToken := none, txGasLimitCap := none, perEmptyAccountCost := none }

/-- Shanghai: EIP-3860 (initcode metering and limit); PUSH0 (EIP-3855) is introduced. -/
@[expose, reducible] def shanghai : ForkSchedule :=
    { fork := .shanghai, Gzero := 0, Gjumpdest := 1, Gbase := 2, Gverylow := 3, Glow := 5,
      Gmid := 8, Ghigh := 10, Gwarmaccess := 100, Gaccesslistaddress := 2400,
      Gaccessliststorage := 1900, Gcoldaccountaccess := 2600, Gcoldsload := 2100, Gsset := 20000,
      Gsreset := 2900, Rsclear := 4800, Rselfdestruct := 0, Gselfdestruct := 5000,
      Gcreate := 32000, Gcodedeposit := 200, Ginitcodeword := 2, Gcallvalue := 9000,
      Gcallstipend := 2300, Gnewaccount := 25000, Gexp := 10, Gexpbyte := 50, Gmemory := 3,
      Gtxcreate := 32000, Gtxdatazero := 4, Gtxdatanonzero := 16, Gtransaction := 21000,
      Glog := 375, Glogdata := 8, Glogtopic := 375, Gkeccak256 := 30, Gkeccak256word := 6,
      Gcopy := 3, Gblockhash := 20, HASH_OPCODE_GAS := 0, Gsload := 800, Gbalance := 700,
      Gextcode := 700, Gextcodehash := 700, Gcall := 700, callGasRetention := some 64,
      eip2929 := true, sstoreRule := .netMetered, selfdestructNewAccount := true,
      refundQuotient := 5, maxCodeSize := some 24576, maxInitcodeSize := some 49152,
      txDataFloorPerToken := none, txGasLimitCap := none, perEmptyAccountCost := none }

/-- Cancun: EIP-4844 (`HASH_OPCODE_GAS = 3`); TLOAD/TSTORE (EIP-1153), MCOPY (EIP-5656) and
BLOBBASEFEE (EIP-7516) are introduced. This is the fork the interpreter implements. -/
@[expose, reducible] def cancun : ForkSchedule :=
    { fork := .cancun, Gzero := 0, Gjumpdest := 1, Gbase := 2, Gverylow := 3, Glow := 5,
      Gmid := 8, Ghigh := 10, Gwarmaccess := 100, Gaccesslistaddress := 2400,
      Gaccessliststorage := 1900, Gcoldaccountaccess := 2600, Gcoldsload := 2100, Gsset := 20000,
      Gsreset := 2900, Rsclear := 4800, Rselfdestruct := 0, Gselfdestruct := 5000,
      Gcreate := 32000, Gcodedeposit := 200, Ginitcodeword := 2, Gcallvalue := 9000,
      Gcallstipend := 2300, Gnewaccount := 25000, Gexp := 10, Gexpbyte := 50, Gmemory := 3,
      Gtxcreate := 32000, Gtxdatazero := 4, Gtxdatanonzero := 16, Gtransaction := 21000,
      Glog := 375, Glogdata := 8, Glogtopic := 375, Gkeccak256 := 30, Gkeccak256word := 6,
      Gcopy := 3, Gblockhash := 20, HASH_OPCODE_GAS := 3, Gsload := 800, Gbalance := 700,
      Gextcode := 700, Gextcodehash := 700, Gcall := 700, callGasRetention := some 64,
      eip2929 := true, sstoreRule := .netMetered, selfdestructNewAccount := true,
      refundQuotient := 5, maxCodeSize := some 24576, maxInitcodeSize := some 49152,
      txDataFloorPerToken := none, txGasLimitCap := none, perEmptyAccountCost := none }

/-- Prague: EIP-7623 (calldata floor of 10 per token) and EIP-7702 (set-code transactions,
25000 per empty-account authorization). -/
@[expose, reducible] def prague : ForkSchedule :=
    { fork := .prague, Gzero := 0, Gjumpdest := 1, Gbase := 2, Gverylow := 3, Glow := 5,
      Gmid := 8, Ghigh := 10, Gwarmaccess := 100, Gaccesslistaddress := 2400,
      Gaccessliststorage := 1900, Gcoldaccountaccess := 2600, Gcoldsload := 2100, Gsset := 20000,
      Gsreset := 2900, Rsclear := 4800, Rselfdestruct := 0, Gselfdestruct := 5000,
      Gcreate := 32000, Gcodedeposit := 200, Ginitcodeword := 2, Gcallvalue := 9000,
      Gcallstipend := 2300, Gnewaccount := 25000, Gexp := 10, Gexpbyte := 50, Gmemory := 3,
      Gtxcreate := 32000, Gtxdatazero := 4, Gtxdatanonzero := 16, Gtransaction := 21000,
      Glog := 375, Glogdata := 8, Glogtopic := 375, Gkeccak256 := 30, Gkeccak256word := 6,
      Gcopy := 3, Gblockhash := 20, HASH_OPCODE_GAS := 3, Gsload := 800, Gbalance := 700,
      Gextcode := 700, Gextcodehash := 700, Gcall := 700, callGasRetention := some 64,
      eip2929 := true, sstoreRule := .netMetered, selfdestructNewAccount := true,
      refundQuotient := 5, maxCodeSize := some 24576, maxInitcodeSize := some 49152,
      txDataFloorPerToken := some 10, txGasLimitCap := none,
      perEmptyAccountCost := some 25000 }

/-- Osaka: EIP-7825 (transaction gas-limit cap `2^24`). -/
@[expose, reducible] def osaka : ForkSchedule :=
    { fork := .osaka, Gzero := 0, Gjumpdest := 1, Gbase := 2, Gverylow := 3, Glow := 5, Gmid := 8,
      Ghigh := 10, Gwarmaccess := 100, Gaccesslistaddress := 2400, Gaccessliststorage := 1900,
      Gcoldaccountaccess := 2600, Gcoldsload := 2100, Gsset := 20000, Gsreset := 2900,
      Rsclear := 4800, Rselfdestruct := 0, Gselfdestruct := 5000, Gcreate := 32000,
      Gcodedeposit := 200, Ginitcodeword := 2, Gcallvalue := 9000, Gcallstipend := 2300,
      Gnewaccount := 25000, Gexp := 10, Gexpbyte := 50, Gmemory := 3, Gtxcreate := 32000,
      Gtxdatazero := 4, Gtxdatanonzero := 16, Gtransaction := 21000, Glog := 375, Glogdata := 8,
      Glogtopic := 375, Gkeccak256 := 30, Gkeccak256word := 6, Gcopy := 3, Gblockhash := 20,
      HASH_OPCODE_GAS := 3, Gsload := 800, Gbalance := 700, Gextcode := 700, Gextcodehash := 700,
      Gcall := 700, callGasRetention := some 64, eip2929 := true, sstoreRule := .netMetered,
      selfdestructNewAccount := true, refundQuotient := 5, maxCodeSize := some 24576,
      maxInitcodeSize := some 49152, txDataFloorPerToken := some 10,
      txGasLimitCap := some 16777216, perEmptyAccountCost := some 25000 }

/-- The schedule of each fork. -/
@[expose] def ofFork : Fork → ForkSchedule
  | .frontier => frontier
  | .homestead => homestead
  | .tangerineWhistle => tangerineWhistle
  | .spuriousDragon => spuriousDragon
  | .byzantium => byzantium
  | .petersburg => petersburg
  | .istanbul => istanbul
  | .berlin => berlin
  | .london => london
  | .shanghai => shanghai
  | .cancun => cancun
  | .prague => prague
  | .osaka => osaka

theorem ofFork_fork (f : Fork) : (ofFork f).fork = f := by cases f <;> rfl

/-- "All but one `d`-th" of `n` under the schedule's EIP-150 rule (`L` of the Yellow Paper when
`callGasRetention = some 64`); the identity before EIP-150. -/
@[expose] def allBut (fs : ForkSchedule) (n : ℕ) : ℕ :=
  match fs.callGasRetention with
  | some d => n - n / d
  | none => n

end ForkSchedule

end EVM

end EvmYul
