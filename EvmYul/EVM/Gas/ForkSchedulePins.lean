module

public import EvmYul.EVM.Gas.ForkSchedule
public import EvmYul.ProofTags
public section

/-!
# Pins: every named fork, field by field

Two independent families of `rfl` lemmas lock the schedules of `EvmYul/EVM/Gas/ForkSchedule.lean`:

* `<fork>_def` states the full record of one named fork as literal values;
* `<fork>_eq_prev` states that a fork is the previous fork updated with exactly the fields changed
  by its EIPs (and nothing else). This is the EIP-by-EIP reading of the table.

Editing any value of any fork breaks at least one of these theorems.
-/

namespace EvmYul.EVM.ForkSchedule

/-- Frontier (YP Appendix G as of 2015). Every field of `frontier` pinned to its EIP value. -/
@[reviewed_rfl "the fork's full schedule, by definition (golden pin of the fork table; the cost theorems of `ForkCostLemmas` reason about it)"]
theorem frontier_def : frontier =
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
      perEmptyAccountCost := none } := rfl

/-- Homestead: EIP-2 sets `Gtxcreate = 32000`. Every field of `homestead` pinned to its
EIP value. -/
@[reviewed_rfl "the fork's full schedule, by definition (golden pin of the fork table; the cost theorems of `ForkCostLemmas` reason about it)"]
theorem homestead_def : homestead =
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
      perEmptyAccountCost := none } := rfl

/-- Tangerine Whistle, EIP-150: SLOAD 200, BALANCE 400, EXTCODE* 700, CALL 700, SELFDESTRUCT 5000
(+25000 for a new account), call gas "all but one 64th". Every field of `tangerineWhistle`
pinned to its EIP value. -/
@[reviewed_rfl "the fork's full schedule, by definition (golden pin of the fork table; the cost theorems of `ForkCostLemmas` reason about it)"]
theorem tangerineWhistle_def : tangerineWhistle =
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
      perEmptyAccountCost := none } := rfl

/-- Spurious Dragon: EIP-160 `Gexpbyte = 50`, EIP-170 code size limit 24576. Every field of
`spuriousDragon` pinned to its EIP value. -/
@[reviewed_rfl "the fork's full schedule, by definition (golden pin of the fork table; the cost theorems of `ForkCostLemmas` reason about it)"]
theorem spuriousDragon_def : spuriousDragon =
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
      perEmptyAccountCost := none } := rfl

/-- Byzantium: no price changes. Every field of `byzantium` pinned to its EIP value. -/
@[reviewed_rfl "the fork's full schedule, by definition (golden pin of the fork table; the cost theorems of `ForkCostLemmas` reason about it)"]
theorem byzantium_def : byzantium =
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
      perEmptyAccountCost := none } := rfl

/-- Petersburg: EIP-1052 EXTCODEHASH 400. Every field of `petersburg` pinned to its EIP value. -/
@[reviewed_rfl "the fork's full schedule, by definition (golden pin of the fork table; the cost theorems of `ForkCostLemmas` reason about it)"]
theorem petersburg_def : petersburg =
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
      perEmptyAccountCost := none } := rfl

/-- Istanbul: EIP-1884 (SLOAD 800, BALANCE 700, EXTCODEHASH 700), EIP-2028 (non-zero calldata 16),
EIP-2200 (net-metered SSTORE). Every field of `istanbul` pinned to its EIP value. -/
@[reviewed_rfl "the fork's full schedule, by definition (golden pin of the fork table; the cost theorems of `ForkCostLemmas` reason about it)"]
theorem istanbul_def : istanbul =
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
      perEmptyAccountCost := none } := rfl

/-- Berlin: EIP-2929 (warm 100, cold account 2600, cold slot 2100, `Gsreset = 2900`), EIP-2930 (2400
/ 1900). Every field of `berlin` pinned to its EIP value. -/
@[reviewed_rfl "the fork's full schedule, by definition (golden pin of the fork table; the cost theorems of `ForkCostLemmas` reason about it)"]
theorem berlin_def : berlin =
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
      txDataFloorPerToken := none, txGasLimitCap := none, perEmptyAccountCost := none } := rfl

/-- London: EIP-3529 (`Rsclear = 4800`, no SELFDESTRUCT refund, refund quotient 5). Every field of
`london` pinned to its EIP value. -/
@[reviewed_rfl "the fork's full schedule, by definition (golden pin of the fork table; the cost theorems of `ForkCostLemmas` reason about it)"]
theorem london_def : london =
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
      txDataFloorPerToken := none, txGasLimitCap := none, perEmptyAccountCost := none } := rfl

/-- Shanghai: EIP-3860 (`Ginitcodeword = 2`, initcode limit 49152). Every field of `shanghai` pinned
to its EIP value. -/
@[reviewed_rfl "the fork's full schedule, by definition (golden pin of the fork table; the cost theorems of `ForkCostLemmas` reason about it)"]
theorem shanghai_def : shanghai =
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
      txDataFloorPerToken := none, txGasLimitCap := none, perEmptyAccountCost := none } := rfl

/-- Cancun: EIP-4844 `HASH_OPCODE_GAS = 3`. Every field of `cancun` pinned to its EIP value. -/
@[reviewed_rfl "the fork's full schedule, by definition (golden pin of the fork table; the cost theorems of `ForkCostLemmas` reason about it)"]
theorem cancun_def : cancun =
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
      txDataFloorPerToken := none, txGasLimitCap := none, perEmptyAccountCost := none } := rfl

/-- Prague: EIP-7623 floor 10 per calldata token, EIP-7702 25000 per empty-account authorization.
Every field of `prague` pinned to its EIP value. -/
@[reviewed_rfl "the fork's full schedule, by definition (golden pin of the fork table; the cost theorems of `ForkCostLemmas` reason about it)"]
theorem prague_def : prague =
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
      perEmptyAccountCost := some 25000 } := rfl

/-- Osaka: EIP-7825 transaction gas-limit cap `2^24 = 16777216`. Every field of `osaka` pinned to
its EIP value. -/
@[reviewed_rfl "the fork's full schedule, by definition (golden pin of the fork table; the cost theorems of `ForkCostLemmas` reason about it)"]
theorem osaka_def : osaka =
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
      txGasLimitCap := some 16777216, perEmptyAccountCost := some 25000 } := rfl


/-! ## Each fork is the previous one plus exactly the gas changes of its EIPs -/

/-- Delta pin. Homestead: EIP-2 (contract-creating transactions pay `Gtxcreate = 32000`). -/
@[reviewed_rfl "the fork's EIP-by-EIP relation to the previous fork, by definition (second, independent family of fork-table pins)"]
theorem homestead_eq_prev : homestead =
    { frontier with fork := .homestead, Gtxcreate := 32000 } := rfl

/-- Delta pin. Tangerine Whistle: EIP-150 (IO-heavy repricing and the 63/64 call-gas rule). -/
@[reviewed_rfl "the fork's EIP-by-EIP relation to the previous fork, by definition (second, independent family of fork-table pins)"]
theorem tangerineWhistle_eq_prev : tangerineWhistle =
    { homestead with
      fork := .tangerineWhistle
      Gsload := 200, Gbalance := 400, Gextcode := 700, Gcall := 700, Gselfdestruct := 5000
      selfdestructNewAccount := true, callGasRetention := some 64 } := rfl

/-- Delta pin. Spurious Dragon: EIP-160 (EXP byte price) and EIP-170 (code size limit). -/
@[reviewed_rfl "the fork's EIP-by-EIP relation to the previous fork, by definition (second, independent family of fork-table pins)"]
theorem spuriousDragon_eq_prev : spuriousDragon =
    { tangerineWhistle with fork := .spuriousDragon, Gexpbyte := 50, maxCodeSize := some 24576 } :=
  rfl

/-- Delta pin. Byzantium: no price changes (REVERT, RETURNDATA*, STATICCALL are introduced). -/
@[reviewed_rfl "the fork's EIP-by-EIP relation to the previous fork, by definition (second, independent family of fork-table pins)"]
theorem byzantium_eq_prev : byzantium =
    { spuriousDragon with fork := .byzantium } := rfl

/-- Delta pin. Petersburg (= Constantinople without EIP-1283): EIP-1052 EXTCODEHASH at 400. -/
@[reviewed_rfl "the fork's EIP-by-EIP relation to the previous fork, by definition (second, independent family of fork-table pins)"]
theorem petersburg_eq_prev : petersburg =
    { byzantium with fork := .petersburg, Gextcodehash := 400 } := rfl

/-- Delta pin. Istanbul: EIP-1884 (SLOAD 800, BALANCE 700, EXTCODEHASH 700), EIP-2028 (non-zero
calldata
16) and EIP-2200 (net-metered SSTORE). -/
@[reviewed_rfl "the fork's EIP-by-EIP relation to the previous fork, by definition (second, independent family of fork-table pins)"]
theorem istanbul_eq_prev : istanbul =
    { petersburg with
      fork := .istanbul
      Gsload := 800, Gbalance := 700, Gextcodehash := 700, Gtxdatanonzero := 16
      sstoreRule := .netMetered } := rfl

/-- Delta pin. Berlin: EIP-2929 (warm/cold access, `Gsreset = 5000 − 2100`) and EIP-2930 (access
lists). -/
@[reviewed_rfl "the fork's EIP-by-EIP relation to the previous fork, by definition (second, independent family of fork-table pins)"]
theorem berlin_eq_prev : berlin =
    { istanbul with
      fork := .berlin
      Gwarmaccess := 100, Gcoldaccountaccess := 2600, Gcoldsload := 2100, Gsreset := 2900
      Gaccesslistaddress := 2400, Gaccessliststorage := 1900, eip2929 := true } := rfl

/-- Delta pin. London: EIP-3529 (refund cap `⌊used/5⌋`, `Rsclear = 4800`, no SELFDESTRUCT refund).
-/
@[reviewed_rfl "the fork's EIP-by-EIP relation to the previous fork, by definition (second, independent family of fork-table pins)"]
theorem london_eq_prev : london =
    { berlin with fork := .london, Rsclear := 4800, Rselfdestruct := 0, refundQuotient := 5 } := rfl

/-- Delta pin. Shanghai: EIP-3860 (initcode metering and limit); PUSH0 (EIP-3855) is introduced. -/
@[reviewed_rfl "the fork's EIP-by-EIP relation to the previous fork, by definition (second, independent family of fork-table pins)"]
theorem shanghai_eq_prev : shanghai =
    { london with fork := .shanghai, Ginitcodeword := 2, maxInitcodeSize := some 49152 } := rfl

/-- Delta pin. Cancun: EIP-4844 (`HASH_OPCODE_GAS = 3`); TLOAD/TSTORE (EIP-1153), MCOPY (EIP-5656)
and
BLOBBASEFEE (EIP-7516) are introduced. This is the fork the interpreter implements. -/
@[reviewed_rfl "the fork's EIP-by-EIP relation to the previous fork, by definition (second, independent family of fork-table pins)"]
theorem cancun_eq_prev : cancun =
    { shanghai with fork := .cancun, HASH_OPCODE_GAS := 3 } := rfl

/-- Delta pin. Prague: EIP-7623 (calldata floor of 10 per token) and EIP-7702 (set-code
transactions, 25000 per empty-account authorization). -/
@[reviewed_rfl "the fork's EIP-by-EIP relation to the previous fork, by definition (second, independent family of fork-table pins)"]
theorem prague_eq_prev : prague =
    { cancun with
        fork := .prague, txDataFloorPerToken := some 10, perEmptyAccountCost := some 25000 } := rfl

/-- Delta pin. Osaka: EIP-7825 (transaction gas-limit cap `2^24`). -/
@[reviewed_rfl "the fork's EIP-by-EIP relation to the previous fork, by definition (second, independent family of fork-table pins)"]
theorem osaka_eq_prev : osaka =
    { prague with fork := .osaka, txGasLimitCap := some 16777216 } := rfl

end EvmYul.EVM.ForkSchedule
