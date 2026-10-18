module

public import EvmYul.UInt256
public import EvmYul.EVM.Gas.ForkSchedule
public section

/-!
# Fee schedule constants (Yellow Paper, Appendix G)

The named gas prices used by the interpreter. They are no longer independent literals: each one is
the corresponding field of `EvmYul.EVM.ForkSchedule.cancun` (see `EvmYul/EVM/Gas/ForkSchedule.lean`),
the Cancun instance of the fork-indexed schedule, so it unfolds definitionally to the same number as
before. `ForkSchedule.cancun_def` and `FeeSchedule.cancun_values` pin the values numerically.
-/

namespace GasConstants

section FeeSchedule

/-- Nothing is paid for operations of the set `W_zero` (STOP, RETURN, REVERT). -/
@[expose] def Gzero : ℕ              := EvmYul.EVM.ForkSchedule.cancun.Gzero
/-- Amount of gas to pay for a JUMPDEST operation. -/
@[expose] def Gjumpdest : ℕ          := EvmYul.EVM.ForkSchedule.cancun.Gjumpdest
/-- Amount of gas to pay for operations of the set `W_base`. -/
@[expose] def Gbase : ℕ              := EvmYul.EVM.ForkSchedule.cancun.Gbase
/-- Amount of gas to pay for operations of the set `W_verylow`. -/
@[expose] def Gverylow : ℕ           := EvmYul.EVM.ForkSchedule.cancun.Gverylow
/-- Amount of gas to pay for operations of the set `W_low`. -/
@[expose] def Glow : ℕ               := EvmYul.EVM.ForkSchedule.cancun.Glow
/-- Amount of gas to pay for operations of the set `W_mid`. -/
@[expose] def Gmid : ℕ               := EvmYul.EVM.ForkSchedule.cancun.Gmid
/-- Amount of gas to pay for operations of the set `W_high`. -/
@[expose] def Ghigh : ℕ              := EvmYul.EVM.ForkSchedule.cancun.Ghigh
/-- Cost of a warm account or storage access (EIP-2929); also the TLOAD/TSTORE price. -/
@[expose] def Gwarmaccess : ℕ        := EvmYul.EVM.ForkSchedule.cancun.Gwarmaccess
/-- Cost of warming up an account with the access list (EIP-2930). -/
@[expose] def Gaccesslistaddress : ℕ := EvmYul.EVM.ForkSchedule.cancun.Gaccesslistaddress
/-- Cost of warming up a storage slot with the access list (EIP-2930). -/
@[expose] def Gaccessliststorage : ℕ := EvmYul.EVM.ForkSchedule.cancun.Gaccessliststorage
/-- Cost of a cold account access (EIP-2929). -/
@[expose] def Gcoldaccountaccess : ℕ := EvmYul.EVM.ForkSchedule.cancun.Gcoldaccountaccess
/-- Cost of a cold storage access (EIP-2929). -/
@[expose] def Gcoldsload : ℕ         := EvmYul.EVM.ForkSchedule.cancun.Gcoldsload
/-- Paid for an SSTORE that sets a storage value to non-zero from (original) zero. -/
@[expose] def Gsset : ℕ              := EvmYul.EVM.ForkSchedule.cancun.Gsset
/-- Paid for an SSTORE that changes an original non-zero storage value. -/
@[expose] def Gsreset : ℕ            := EvmYul.EVM.ForkSchedule.cancun.Gsreset
/-- Refund given (added to the refund counter) when a storage value is set to zero from
non-zero (EIP-3529). -/
@[expose] def Rsclear : ℕ            := EvmYul.EVM.ForkSchedule.cancun.Rsclear
/-- Amount of gas to pay for a SELFDESTRUCT operation. -/
@[expose] def Gselfdestruct : ℕ      := EvmYul.EVM.ForkSchedule.cancun.Gselfdestruct
/-- Paid for a CREATE or CREATE2 operation. -/
@[expose] def Gcreate : ℕ            := EvmYul.EVM.ForkSchedule.cancun.Gcreate
/-- Paid per byte for a CREATE operation to succeed in placing code into the state. -/
@[expose] def Gcodedeposit : ℕ       := EvmYul.EVM.ForkSchedule.cancun.Gcodedeposit
/-- Paid per 32-byte word of initcode by CREATE, CREATE2 and creation transactions (EIP-3860). -/
@[expose] def Ginitcodeword : ℕ      := EvmYul.EVM.ForkSchedule.cancun.Ginitcodeword
/-- Paid for a non-zero value transfer as part of a CALL or CALLCODE operation. -/
@[expose] def Gcallvalue : ℕ         := EvmYul.EVM.ForkSchedule.cancun.Gcallvalue
/-- Stipend given to the callee of a value-transferring call (part of `Gcallvalue`). -/
@[expose] def Gcallstipend : ℕ       := EvmYul.EVM.ForkSchedule.cancun.Gcallstipend
/-- Paid for a CALL or SELFDESTRUCT operation that creates an account. -/
@[expose] def Gnewaccount : ℕ        := EvmYul.EVM.ForkSchedule.cancun.Gnewaccount
/-- Base payment for an EXP operation. -/
@[expose] def Gexp : ℕ               := EvmYul.EVM.ForkSchedule.cancun.Gexp
/-- Payment per byte of the exponent of an EXP operation. -/
@[expose] def Gexpbyte : ℕ           := EvmYul.EVM.ForkSchedule.cancun.Gexpbyte
/-- Paid for every additional 32-byte word when expanding memory (linear part of `Cₘ`). -/
@[expose] def Gmemory : ℕ            := EvmYul.EVM.ForkSchedule.cancun.Gmemory
/-- Paid by every contract-creating transaction. -/
@[expose] def Gtxcreate : ℕ          := EvmYul.EVM.ForkSchedule.cancun.Gtxcreate
/-- Paid for every zero byte of transaction data. -/
@[expose] def Gtxdatazero : ℕ        := EvmYul.EVM.ForkSchedule.cancun.Gtxdatazero
/-- Paid for every non-zero byte of transaction data (EIP-2028). -/
@[expose] def Gtxdatanonzero : ℕ     := EvmYul.EVM.ForkSchedule.cancun.Gtxdatanonzero
/-- Paid for every transaction (the intrinsic base cost). -/
@[expose] def Gtransaction : ℕ       := EvmYul.EVM.ForkSchedule.cancun.Gtransaction
/-- Base payment for a LOG operation. -/
@[expose] def Glog : ℕ               := EvmYul.EVM.ForkSchedule.cancun.Glog
/-- Paid for each byte of a LOG operation's data. -/
@[expose] def Glogdata : ℕ           := EvmYul.EVM.ForkSchedule.cancun.Glogdata
/-- Paid for each topic of a LOG operation. -/
@[expose] def Glogtopic : ℕ          := EvmYul.EVM.ForkSchedule.cancun.Glogtopic
/-- Base payment for a KECCAK256 operation. -/
@[expose] def Gkeccak256 : ℕ         := EvmYul.EVM.ForkSchedule.cancun.Gkeccak256
/-- Paid for each 32-byte word (rounded up) of KECCAK256 input; also per word of CREATE2
initcode hashing. -/
@[expose] def Gkeccak256word : ℕ     := EvmYul.EVM.ForkSchedule.cancun.Gkeccak256word
/-- Payment per 32-byte word (rounded up) copied by the `*COPY` operations. -/
@[expose] def Gcopy : ℕ              := EvmYul.EVM.ForkSchedule.cancun.Gcopy
/-- Payment for a BLOCKHASH operation. -/
@[expose] def Gblockhash : ℕ         := EvmYul.EVM.ForkSchedule.cancun.Gblockhash
/-- Payment for a BLOBHASH operation (EIP-4844). -/
@[expose] def HASH_OPCODE_GAS : ℕ    := EvmYul.EVM.ForkSchedule.cancun.HASH_OPCODE_GAS

end FeeSchedule

end GasConstants
