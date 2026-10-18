module

public import EvmYul.EVM.Gas.Classification
public section

/-!
# Fee-schedule types (handoff WP-6, MO-10, PO-12) and the opcode/price parity theorem (PO-1)

As the handoff prescribes, this ships **types only**: a `Hardfork` index with a single inhabitant
(Cancun, the fork the model implements) and a `FeeSchedule` record holding every constant of
`GasConstants`. `C'` is **not** refactored to dispatch through the record: it is
conformance-critical and the conformance corpus cannot be re-run here. Instead, the record is tied
to `C'` by proof:

* `FeeSchedule.cancun_eq`: the Cancun schedule holds exactly the values of `GasConstants` (and these
  values are pinned numerically by `cancun_values`).
* `FeeSchedule.staticCost_cancun`: its static-cost table is the one of `FeeGroup.staticCost?`.
* `C'_eq_schedule_staticCost`: for every opcode with a static fee group, `C'` charges exactly the
  schedule's price, in every state.

PO-12 ("total and decidable per fork index"): `Hardfork.schedule` is a total function, and
`Hardfork`, `FeeSchedule` have decidable equality.

PO-1 ("handled-by-step ↔ priced-by-C'"): `X` lets an instruction reach `step` only if `δ w ≠ none`
(otherwise `exceptionalHalt` raises `InvalidInstruction`). `opcode_price_parity` proves that these
are exactly the opcodes with a fee classification, and that each of them except STOP/RETURN/REVERT
costs at least 1 gas in every state. Adding an opcode without classifying it is a compile error in
`feeGroup` (no wildcard arm).
-/

namespace EvmYul

namespace EVM

open GasMeter GasConstants InstructionGasGroups

@[expose] section

/-- Hard forks with a fee schedule. One inhabitant: the model implements Cancun. -/
inductive Hardfork where
  | cancun
  deriving DecidableEq, Repr

end

/-- All hard forks (for exhaustive checks). -/
def Hardfork.all : List Hardfork := [.cancun]

theorem Hardfork.mem_all (f : Hardfork) : f ∈ Hardfork.all := by cases f; decide

@[expose] section

/-- Every named fee-schedule constant of the Yellow Paper, Appendix G (plus EIP-4844's
`HASH_OPCODE_GAS`). -/
structure FeeSchedule where
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
  non-zero (EIP-3529). -/
  Rsclear : ℕ
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
  /-- Paid for every non-zero byte of transaction data (EIP-2028). -/
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
  deriving DecidableEq, Repr

end

namespace FeeSchedule

/-- The Cancun schedule, read from `GasConstants` (the constants `C'` uses). -/
@[expose] def cancun : FeeSchedule where
  Gzero := GasConstants.Gzero
  Gjumpdest := GasConstants.Gjumpdest
  Gbase := GasConstants.Gbase
  Gverylow := GasConstants.Gverylow
  Glow := GasConstants.Glow
  Gmid := GasConstants.Gmid
  Ghigh := GasConstants.Ghigh
  Gwarmaccess := GasConstants.Gwarmaccess
  Gaccesslistaddress := GasConstants.Gaccesslistaddress
  Gaccessliststorage := GasConstants.Gaccessliststorage
  Gcoldaccountaccess := GasConstants.Gcoldaccountaccess
  Gcoldsload := GasConstants.Gcoldsload
  Gsset := GasConstants.Gsset
  Gsreset := GasConstants.Gsreset
  Rsclear := GasConstants.Rsclear
  Gselfdestruct := GasConstants.Gselfdestruct
  Gcreate := GasConstants.Gcreate
  Gcodedeposit := GasConstants.Gcodedeposit
  Ginitcodeword := GasConstants.Ginitcodeword
  Gcallvalue := GasConstants.Gcallvalue
  Gcallstipend := GasConstants.Gcallstipend
  Gnewaccount := GasConstants.Gnewaccount
  Gexp := GasConstants.Gexp
  Gexpbyte := GasConstants.Gexpbyte
  Gmemory := GasConstants.Gmemory
  Gtxcreate := GasConstants.Gtxcreate
  Gtxdatazero := GasConstants.Gtxdatazero
  Gtxdatanonzero := GasConstants.Gtxdatanonzero
  Gtransaction := GasConstants.Gtransaction
  Glog := GasConstants.Glog
  Glogdata := GasConstants.Glogdata
  Glogtopic := GasConstants.Glogtopic
  Gkeccak256 := GasConstants.Gkeccak256
  Gkeccak256word := GasConstants.Gkeccak256word
  Gcopy := GasConstants.Gcopy
  Gblockhash := GasConstants.Gblockhash
  HASH_OPCODE_GAS := GasConstants.HASH_OPCODE_GAS

/-- Numeric pin of the Cancun schedule (YP Appendix G, EIP-2929, EIP-3529, EIP-3860, EIP-4844).
Any edit to a constant in `GasConstants` breaks this theorem. -/
theorem cancun_values : cancun =
    { Gzero := 0, Gjumpdest := 1, Gbase := 2, Gverylow := 3, Glow := 5, Gmid := 8, Ghigh := 10,
      Gwarmaccess := 100, Gaccesslistaddress := 2400, Gaccessliststorage := 1900,
      Gcoldaccountaccess := 2600, Gcoldsload := 2100, Gsset := 20000, Gsreset := 2900,
      Rsclear := 4800, Gselfdestruct := 5000, Gcreate := 32000, Gcodedeposit := 200,
      Ginitcodeword := 2, Gcallvalue := 9000, Gcallstipend := 2300, Gnewaccount := 25000,
      Gexp := 10, Gexpbyte := 50, Gmemory := 3, Gtxcreate := 32000, Gtxdatazero := 4,
      Gtxdatanonzero := 16, Gtransaction := 21000, Glog := 375, Glogdata := 8, Glogtopic := 375,
      Gkeccak256 := 30, Gkeccak256word := 6, Gcopy := 3, Gblockhash := 20,
      HASH_OPCODE_GAS := 3 } := by
  decide

/-- Static cost of a fee group under a schedule (`none` for state-dependent groups). -/
def staticCost (fs : FeeSchedule) : FeeGroup → Option ℕ
  | .zero      => some fs.Gzero
  | .base      => some fs.Gbase
  | .verylow   => some fs.Gverylow
  | .low       => some fs.Glow
  | .mid       => some fs.Gmid
  | .high      => some fs.Ghigh
  | .jumpdest  => some fs.Gjumpdest
  | .blockhash => some fs.Gblockhash
  | .blobhash  => some fs.HASH_OPCODE_GAS
  | .transient => some fs.Gwarmaccess
  | .copy | .extAccount | .exp | .extcodecopy | .log | .keccak | .create
  | .sload | .sstore | .call | .selfdestruct | .invalid => none

/-- The Cancun schedule's static-cost table is the one `feeGroup`/`C'` use. -/
theorem staticCost_cancun : cancun.staticCost = FeeGroup.staticCost? := by
  funext g; cases g <;> rfl

end FeeSchedule

/-- The fee schedule of a hard fork (total, PO-12). -/
@[expose] def Hardfork.schedule : Hardfork → FeeSchedule
  | .cancun => .cancun

/-- For every opcode with a static fee group, `C'` charges exactly the Cancun schedule's price, in
every state. -/
theorem C'_eq_schedule_staticCost (s : EVM.State) (w : Operation .EVM) {c : ℕ}
    (h : Hardfork.cancun.schedule.staticCost (feeGroup w) = some c) : C' s w = c :=
  C'_eq_staticCost s w (by rw [← FeeSchedule.staticCost_cancun]; exact h)

/--
**PO-1 parity.** An opcode reaches `step` (`δ w ≠ none`) iff it has a fee classification, and every
such opcode except STOP/RETURN/REVERT costs at least 1 gas in every state.
-/
theorem opcode_price_parity (s : EVM.State) (w : Operation .EVM) :
    (δ w ≠ none ↔ feeGroup w ≠ .invalid) ∧ (δ w ≠ none → w ∉ Wzero → 0 < C' s w) :=
  ⟨not_congr (feeGroup_invalid_iff w).symm, C'_pos_of_valid s w⟩

end EVM

end EvmYul
