module

public import EvmYul.EVM.Gas.ForkCost
public import EvmYul.ProofTags
public section

/-!
# The Cancun instance of `ForkSchedule.cost` is the interpreter's cost

For every instruction whose operands are on the stack:

* `instrCost?_cancun`: `ForkSchedule.cancun.instrCost?`, evaluated with the state's own gas, is
  `some (C' s w)`: the `Option`-reading, fork-parameterised instruction cost agrees with the
  interpreter's `!`-reading `C'` (YP H.1);
* `memoryCost?_cancun`: `ForkSchedule.cancun.memoryCost?` is `some (memoryExpansionCost s w)`;
* `instrCost?_isSome`, `memoryCost?_isSome`: for **every** schedule the `Option` is `some` as soon
  as the operands are on the stack and the instruction is valid, so `none` never arises from the
  cost computation itself (`costParts_eq_none_iff`: `none` iff the stack guard fails).

The proofs go opcode family by opcode family (one lemma per `Operation` constructor).
-/

namespace EvmYul

namespace EVM

open InstructionGasGroups

namespace ForkSchedule

/-- `get!` is `get?` with the default value (the panic message is logically `default`). -/
@[reviewed_generic "tree map `get!` as `getD`"]
theorem get!_eq_getD_get? {α β : Type} {cmp : α → α → Ordering} [Std.TransCmp cmp] [Inhabited β]
    (m : Std.TreeMap α β cmp) (k : α) : m.get! k = (m.get? k).getD default := by
  rw [Std.TreeMap.get!_eq_getElem!, Std.TreeMap.getElem!_eq_getD_default,
    Std.TreeMap.getD_eq_getD_getElem?, Std.TreeMap.get?_eq_getElem?]

/-- Every opcode of the interpreter exists in Cancun. -/
theorem available_cancun (w : Operation .EVM) : cancun.available w = true := by
  rcases w with op|op|op|op|op|op|op|op|op|op|op <;> cases op <;> rfl

/-- The instruction cost does not read `gasAvailable` from the state (only the explicit gas). -/
@[reviewed_rfl "the cost function reads the gas only through its `gas` argument"]
theorem instrCost?_gasAvailable (fs : ForkSchedule) (n : ℕ) (s : EVM.State) (g : UInt256)
    (w : Operation .EVM) :
    fs.instrCost? n { s with gasAvailable := g } w = fs.instrCost? n s w := rfl

/-- The memory cost does not read `gasAvailable`. -/
@[reviewed_rfl "the cost function reads the gas only through its `gas` argument"]
theorem memoryCost?_gasAvailable (fs : ForkSchedule) (s : EVM.State) (g : UInt256)
    (w : Operation .EVM) :
    fs.memoryCost? { s with gasAvailable := g } w = fs.memoryCost? s w := rfl

attribute [local simp] GasConstants.Gzero GasConstants.Gjumpdest GasConstants.Gbase
  GasConstants.Gverylow GasConstants.Glow GasConstants.Gmid GasConstants.Ghigh
  GasConstants.Gwarmaccess GasConstants.Gcoldaccountaccess GasConstants.Gcoldsload
  GasConstants.Gsset GasConstants.Gsreset GasConstants.Gselfdestruct GasConstants.Gcreate
  GasConstants.Ginitcodeword GasConstants.Gcallvalue GasConstants.Gcallstipend
  GasConstants.Gnewaccount GasConstants.Gexp GasConstants.Gexpbyte GasConstants.Gmemory
  GasConstants.Glog GasConstants.Glogdata GasConstants.Glogtopic GasConstants.Gkeccak256
  GasConstants.Gkeccak256word GasConstants.Gcopy GasConstants.Gblockhash
  GasConstants.HASH_OPCODE_GAS

/-- Agreement of one opcode case of `instrCost?_cancun`. -/
macro "cost_agree" : tactic => `(tactic| (
  simp (disch := omega) only [instrCost?, C', sstoreCost, Csstore, selfdestructCost,
    Cselfdestruct, sloadCost, Csload, List.getElem?_eq_getElem, getElem!_pos, get!_eq_getD_get?]
  try simp (config := {decide := true}) [callCost, Ccall, callGasCap, Cgascap, callExtra, Cextra,
    accessCost, Caccess, Cxfer, Cnew, allBut, L, extAccountFlat, initcodeCost, R, Ctstore, Ctload]
  try rfl))

/-- One opcode case of `instrCost?_cancun` for a `W_verylow` instruction (PUSH, DUP, SWAP): both
sides fall through `W_copy`, `W_extaccount`, `W_zero`, `W_base` to `W_verylow`. -/
macro "verylow_agree" : tactic => `(tactic| (
  simp only [instrCost?, C']
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_pos (by decide)]
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide),
    if_pos (by decide)]
  rfl))

/-- One opcode case of `memoryCost?_cancun`. -/
macro "mem_agree" : tactic => `(tactic| (
  simp (disch := omega) only [memoryCost?, newActiveWords?, memoryExpansionCost,
    memoryExpansionCost.μᵢ', List.getElem?_eq_getElem, getElem!_pos, Option.bind_some,
    Option.pure_def, Option.bind_eq_bind]
  try simp [memCost, Cₘ, Cₘ.QuadraticCeofficient]))

/-- `isSome` of one opcode case of `instrCost?` for an arbitrary schedule. -/
macro "cost_some" : tactic => `(tactic| (
  simp (disch := omega) only [instrCost?, List.getElem?_eq_getElem]
  try simp (config := {decide := true})))

/-- `isSome` of one opcode case of `memoryCost?`. -/
macro "mem_some" : tactic => `(tactic| (
  simp (disch := omega) only [memoryCost?, newActiveWords?, List.getElem?_eq_getElem]
  try simp))

/-- `instrCost?_cancun` for the StopArith family. -/
theorem instrCost?_cancun_stopArith (s : EVM.State) (op : Operation.SAOp .EVM) {k : ℕ}
    (hδ : δ (.StopArith op) = some k) (hk : k ≤ s.stack.length) :
    cancun.instrCost? s.gasAvailable.toNat s (.StopArith op) = some (C' s (.StopArith op)) := by
  cases op <;> simp only [δ, Option.some.injEq] at hδ <;> subst hδ <;> cost_agree

/-- `memoryCost?_cancun` for the StopArith family. -/
theorem memoryCost?_cancun_stopArith (s : EVM.State) (op : Operation.SAOp .EVM) {k : ℕ}
    (hδ : δ (.StopArith op) = some k) (hk : k ≤ s.stack.length) :
    cancun.memoryCost? s (.StopArith op) = some (memoryExpansionCost s (.StopArith op)) := by
  cases op <;> simp only [δ, Option.some.injEq] at hδ <;> subst hδ <;> mem_agree

/-- `instrCost?_isSome` for the StopArith family. -/
theorem instrCost?_isSome_stopArith (fs : ForkSchedule) (g : ℕ) (s : EVM.State)
    (op : Operation.SAOp .EVM) {k : ℕ}
    (hδ : δ (.StopArith op) = some k) (hk : k ≤ s.stack.length) :
    (fs.instrCost? g s (.StopArith op)).isSome := by
  cases op <;> simp only [δ, Option.some.injEq] at hδ <;> subst hδ <;> cost_some

/-- `memoryCost?_isSome` for the StopArith family. -/
theorem memoryCost?_isSome_stopArith (fs : ForkSchedule) (s : EVM.State)
    (op : Operation.SAOp .EVM) {k : ℕ}
    (hδ : δ (.StopArith op) = some k) (hk : k ≤ s.stack.length) :
    (fs.memoryCost? s (.StopArith op)).isSome := by
  cases op <;> simp only [δ, Option.some.injEq] at hδ <;> subst hδ <;> mem_some

/-- `instrCost?_cancun` for the CompBit family. -/
theorem instrCost?_cancun_compBit (s : EVM.State) (op : Operation.CBLOp .EVM) {k : ℕ}
    (hδ : δ (.CompBit op) = some k) (hk : k ≤ s.stack.length) :
    cancun.instrCost? s.gasAvailable.toNat s (.CompBit op) = some (C' s (.CompBit op)) := by
  cases op <;> simp only [δ, Option.some.injEq] at hδ <;> subst hδ <;> cost_agree

/-- `memoryCost?_cancun` for the CompBit family. -/
theorem memoryCost?_cancun_compBit (s : EVM.State) (op : Operation.CBLOp .EVM) {k : ℕ}
    (hδ : δ (.CompBit op) = some k) (hk : k ≤ s.stack.length) :
    cancun.memoryCost? s (.CompBit op) = some (memoryExpansionCost s (.CompBit op)) := by
  cases op <;> simp only [δ, Option.some.injEq] at hδ <;> subst hδ <;> mem_agree

/-- `instrCost?_isSome` for the CompBit family. -/
theorem instrCost?_isSome_compBit (fs : ForkSchedule) (g : ℕ) (s : EVM.State)
    (op : Operation.CBLOp .EVM) {k : ℕ}
    (hδ : δ (.CompBit op) = some k) (hk : k ≤ s.stack.length) :
    (fs.instrCost? g s (.CompBit op)).isSome := by
  cases op <;> simp only [δ, Option.some.injEq] at hδ <;> subst hδ <;> cost_some

/-- `memoryCost?_isSome` for the CompBit family. -/
theorem memoryCost?_isSome_compBit (fs : ForkSchedule) (s : EVM.State)
    (op : Operation.CBLOp .EVM) {k : ℕ}
    (hδ : δ (.CompBit op) = some k) (hk : k ≤ s.stack.length) :
    (fs.memoryCost? s (.CompBit op)).isSome := by
  cases op <;> simp only [δ, Option.some.injEq] at hδ <;> subst hδ <;> mem_some

/-- `instrCost?_cancun` for the Keccak family. -/
theorem instrCost?_cancun_keccak (s : EVM.State) (op : Operation.KOp .EVM) {k : ℕ}
    (hδ : δ (.Keccak op) = some k) (hk : k ≤ s.stack.length) :
    cancun.instrCost? s.gasAvailable.toNat s (.Keccak op) = some (C' s (.Keccak op)) := by
  cases op; simp only [δ, Option.some.injEq] at hδ; subst hδ; cost_agree

/-- `memoryCost?_cancun` for the Keccak family. -/
theorem memoryCost?_cancun_keccak (s : EVM.State) (op : Operation.KOp .EVM) {k : ℕ}
    (hδ : δ (.Keccak op) = some k) (hk : k ≤ s.stack.length) :
    cancun.memoryCost? s (.Keccak op) = some (memoryExpansionCost s (.Keccak op)) := by
  cases op; simp only [δ, Option.some.injEq] at hδ; subst hδ; mem_agree

/-- `instrCost?_isSome` for the Keccak family. -/
theorem instrCost?_isSome_keccak (fs : ForkSchedule) (g : ℕ) (s : EVM.State)
    (op : Operation.KOp .EVM) {k : ℕ}
    (hδ : δ (.Keccak op) = some k) (hk : k ≤ s.stack.length) :
    (fs.instrCost? g s (.Keccak op)).isSome := by
  cases op; simp only [δ, Option.some.injEq] at hδ; subst hδ; cost_some

/-- `memoryCost?_isSome` for the Keccak family. -/
theorem memoryCost?_isSome_keccak (fs : ForkSchedule) (s : EVM.State)
    (op : Operation.KOp .EVM) {k : ℕ}
    (hδ : δ (.Keccak op) = some k) (hk : k ≤ s.stack.length) :
    (fs.memoryCost? s (.Keccak op)).isSome := by
  cases op; simp only [δ, Option.some.injEq] at hδ; subst hδ; mem_some

/-- `instrCost?_cancun` for the Env family. -/
theorem instrCost?_cancun_env (s : EVM.State) (op : Operation.EOp .EVM) {k : ℕ}
    (hδ : δ (.Env op) = some k) (hk : k ≤ s.stack.length) :
    cancun.instrCost? s.gasAvailable.toNat s (.Env op) = some (C' s (.Env op)) := by
  cases op <;> simp only [δ, Option.some.injEq] at hδ <;> subst hδ <;> cost_agree

/-- `memoryCost?_cancun` for the Env family. -/
theorem memoryCost?_cancun_env (s : EVM.State) (op : Operation.EOp .EVM) {k : ℕ}
    (hδ : δ (.Env op) = some k) (hk : k ≤ s.stack.length) :
    cancun.memoryCost? s (.Env op) = some (memoryExpansionCost s (.Env op)) := by
  cases op <;> simp only [δ, Option.some.injEq] at hδ <;> subst hδ <;> mem_agree

/-- `instrCost?_isSome` for the Env family. -/
theorem instrCost?_isSome_env (fs : ForkSchedule) (g : ℕ) (s : EVM.State)
    (op : Operation.EOp .EVM) {k : ℕ}
    (hδ : δ (.Env op) = some k) (hk : k ≤ s.stack.length) :
    (fs.instrCost? g s (.Env op)).isSome := by
  cases op <;> simp only [δ, Option.some.injEq] at hδ <;> subst hδ <;> cost_some

/-- `memoryCost?_isSome` for the Env family. -/
theorem memoryCost?_isSome_env (fs : ForkSchedule) (s : EVM.State) (op : Operation.EOp .EVM) {k : ℕ}
    (hδ : δ (.Env op) = some k) (hk : k ≤ s.stack.length) :
    (fs.memoryCost? s (.Env op)).isSome := by
  cases op <;> simp only [δ, Option.some.injEq] at hδ <;> subst hδ <;> mem_some

/-- `instrCost?_cancun` for the Block family. -/
theorem instrCost?_cancun_block (s : EVM.State) (op : Operation.BOp .EVM) {k : ℕ}
    (hδ : δ (.Block op) = some k) (hk : k ≤ s.stack.length) :
    cancun.instrCost? s.gasAvailable.toNat s (.Block op) = some (C' s (.Block op)) := by
  cases op <;> simp only [δ, Option.some.injEq] at hδ <;> subst hδ <;> cost_agree

/-- `memoryCost?_cancun` for the Block family. -/
theorem memoryCost?_cancun_block (s : EVM.State) (op : Operation.BOp .EVM) {k : ℕ}
    (hδ : δ (.Block op) = some k) (hk : k ≤ s.stack.length) :
    cancun.memoryCost? s (.Block op) = some (memoryExpansionCost s (.Block op)) := by
  cases op <;> simp only [δ, Option.some.injEq] at hδ <;> subst hδ <;> mem_agree

/-- `instrCost?_isSome` for the Block family. -/
theorem instrCost?_isSome_block (fs : ForkSchedule) (g : ℕ) (s : EVM.State)
    (op : Operation.BOp .EVM) {k : ℕ}
    (hδ : δ (.Block op) = some k) (hk : k ≤ s.stack.length) :
    (fs.instrCost? g s (.Block op)).isSome := by
  cases op <;> simp only [δ, Option.some.injEq] at hδ <;> subst hδ <;> cost_some

/-- `memoryCost?_isSome` for the Block family. -/
theorem memoryCost?_isSome_block (fs : ForkSchedule) (s : EVM.State)
    (op : Operation.BOp .EVM) {k : ℕ}
    (hδ : δ (.Block op) = some k) (hk : k ≤ s.stack.length) :
    (fs.memoryCost? s (.Block op)).isSome := by
  cases op <;> simp only [δ, Option.some.injEq] at hδ <;> subst hδ <;> mem_some

/-- `instrCost?_cancun` for the StackMemFlow family. -/
theorem instrCost?_cancun_stackMemFlow (s : EVM.State) (op : Operation.SMSFOp .EVM) {k : ℕ}
    (hδ : δ (.StackMemFlow op) = some k) (hk : k ≤ s.stack.length) :
    cancun.instrCost? s.gasAvailable.toNat s (.StackMemFlow op) =
      some (C' s (.StackMemFlow op)) := by
  cases op <;> simp only [δ, Option.some.injEq] at hδ <;> subst hδ <;> cost_agree

/-- `memoryCost?_cancun` for the StackMemFlow family. -/
theorem memoryCost?_cancun_stackMemFlow (s : EVM.State) (op : Operation.SMSFOp .EVM) {k : ℕ}
    (hδ : δ (.StackMemFlow op) = some k) (hk : k ≤ s.stack.length) :
    cancun.memoryCost? s (.StackMemFlow op) = some (memoryExpansionCost s (.StackMemFlow op)) := by
  cases op <;> simp only [δ, Option.some.injEq] at hδ <;> subst hδ <;> mem_agree

/-- `instrCost?_isSome` for the StackMemFlow family. -/
theorem instrCost?_isSome_stackMemFlow (fs : ForkSchedule) (g : ℕ) (s : EVM.State)
    (op : Operation.SMSFOp .EVM) {k : ℕ}
    (hδ : δ (.StackMemFlow op) = some k) (hk : k ≤ s.stack.length) :
    (fs.instrCost? g s (.StackMemFlow op)).isSome := by
  cases op <;> simp only [δ, Option.some.injEq] at hδ <;> subst hδ <;> cost_some

/-- `memoryCost?_isSome` for the StackMemFlow family. -/
theorem memoryCost?_isSome_stackMemFlow (fs : ForkSchedule) (s : EVM.State)
    (op : Operation.SMSFOp .EVM) {k : ℕ}
    (hδ : δ (.StackMemFlow op) = some k) (hk : k ≤ s.stack.length) :
    (fs.memoryCost? s (.StackMemFlow op)).isSome := by
  cases op <;> simp only [δ, Option.some.injEq] at hδ <;> subst hδ <;> mem_some

/-- `instrCost?_cancun` for the Push family. -/
theorem instrCost?_cancun_push (s : EVM.State) (op : Operation.POp) {k : ℕ}
    (hδ : δ (.Push op) = some k) (hk : k ≤ s.stack.length) :
    cancun.instrCost? s.gasAvailable.toNat s (.Push op) = some (C' s (.Push op)) := by
  cases op <;> simp only [δ, Option.some.injEq] at hδ <;> subst hδ <;>
    first | verylow_agree | cost_agree

/-- `memoryCost?_cancun` for the Push family. -/
theorem memoryCost?_cancun_push (s : EVM.State) (op : Operation.POp) {k : ℕ}
    (hδ : δ (.Push op) = some k) (hk : k ≤ s.stack.length) :
    cancun.memoryCost? s (.Push op) = some (memoryExpansionCost s (.Push op)) := by
  cases op <;> simp only [δ, Option.some.injEq] at hδ <;> subst hδ <;> mem_agree

/-- `instrCost?_isSome` for the Push family. -/
theorem instrCost?_isSome_push (fs : ForkSchedule) (g : ℕ) (s : EVM.State)
    (op : Operation.POp) {k : ℕ}
    (hδ : δ (.Push op) = some k) (hk : k ≤ s.stack.length) :
    (fs.instrCost? g s (.Push op)).isSome := by
  cases op <;> simp only [δ, Option.some.injEq] at hδ <;> subst hδ <;> cost_some

/-- `memoryCost?_isSome` for the Push family. -/
theorem memoryCost?_isSome_push (fs : ForkSchedule) (s : EVM.State) (op : Operation.POp) {k : ℕ}
    (hδ : δ (.Push op) = some k) (hk : k ≤ s.stack.length) :
    (fs.memoryCost? s (.Push op)).isSome := by
  cases op <;> simp only [δ, Option.some.injEq] at hδ <;> subst hδ <;> mem_some

/-- `instrCost?_cancun` for the Dup family. -/
theorem instrCost?_cancun_dup (s : EVM.State) (op : Operation.DOp) {k : ℕ}
    (hδ : δ (.Dup op) = some k) (hk : k ≤ s.stack.length) :
    cancun.instrCost? s.gasAvailable.toNat s (.Dup op) = some (C' s (.Dup op)) := by
  cases op <;> simp only [δ, Option.some.injEq] at hδ <;> subst hδ <;> verylow_agree

/-- `memoryCost?_cancun` for the Dup family. -/
theorem memoryCost?_cancun_dup (s : EVM.State) (op : Operation.DOp) {k : ℕ}
    (hδ : δ (.Dup op) = some k) (hk : k ≤ s.stack.length) :
    cancun.memoryCost? s (.Dup op) = some (memoryExpansionCost s (.Dup op)) := by
  cases op <;> simp only [δ, Option.some.injEq] at hδ <;> subst hδ <;> mem_agree

/-- `instrCost?_isSome` for the Dup family. -/
theorem instrCost?_isSome_dup (fs : ForkSchedule) (g : ℕ) (s : EVM.State)
    (op : Operation.DOp) {k : ℕ}
    (hδ : δ (.Dup op) = some k) (hk : k ≤ s.stack.length) :
    (fs.instrCost? g s (.Dup op)).isSome := by
  cases op <;> simp only [δ, Option.some.injEq] at hδ <;> subst hδ <;> cost_some

/-- `memoryCost?_isSome` for the Dup family. -/
theorem memoryCost?_isSome_dup (fs : ForkSchedule) (s : EVM.State) (op : Operation.DOp) {k : ℕ}
    (hδ : δ (.Dup op) = some k) (hk : k ≤ s.stack.length) :
    (fs.memoryCost? s (.Dup op)).isSome := by
  cases op <;> simp only [δ, Option.some.injEq] at hδ <;> subst hδ <;> mem_some

/-- `instrCost?_cancun` for the Exchange family. -/
theorem instrCost?_cancun_exchange (s : EVM.State) (op : Operation.ExOp) {k : ℕ}
    (hδ : δ (.Exchange op) = some k) (hk : k ≤ s.stack.length) :
    cancun.instrCost? s.gasAvailable.toNat s (.Exchange op) = some (C' s (.Exchange op)) := by
  cases op <;> simp only [δ, Option.some.injEq] at hδ <;> subst hδ <;> verylow_agree

/-- `memoryCost?_cancun` for the Exchange family. -/
theorem memoryCost?_cancun_exchange (s : EVM.State) (op : Operation.ExOp) {k : ℕ}
    (hδ : δ (.Exchange op) = some k) (hk : k ≤ s.stack.length) :
    cancun.memoryCost? s (.Exchange op) = some (memoryExpansionCost s (.Exchange op)) := by
  cases op <;> simp only [δ, Option.some.injEq] at hδ <;> subst hδ <;> mem_agree

/-- `instrCost?_isSome` for the Exchange family. -/
theorem instrCost?_isSome_exchange (fs : ForkSchedule) (g : ℕ) (s : EVM.State)
    (op : Operation.ExOp) {k : ℕ}
    (hδ : δ (.Exchange op) = some k) (hk : k ≤ s.stack.length) :
    (fs.instrCost? g s (.Exchange op)).isSome := by
  cases op <;> simp only [δ, Option.some.injEq] at hδ <;> subst hδ <;> cost_some

/-- `memoryCost?_isSome` for the Exchange family. -/
theorem memoryCost?_isSome_exchange (fs : ForkSchedule) (s : EVM.State)
    (op : Operation.ExOp) {k : ℕ}
    (hδ : δ (.Exchange op) = some k) (hk : k ≤ s.stack.length) :
    (fs.memoryCost? s (.Exchange op)).isSome := by
  cases op <;> simp only [δ, Option.some.injEq] at hδ <;> subst hδ <;> mem_some

/-- `instrCost?_cancun` for the Log family. -/
theorem instrCost?_cancun_log (s : EVM.State) (op : Operation.LOp .EVM) {k : ℕ}
    (hδ : δ (.Log op) = some k) (hk : k ≤ s.stack.length) :
    cancun.instrCost? s.gasAvailable.toNat s (.Log op) = some (C' s (.Log op)) := by
  cases op <;> simp only [δ, Option.some.injEq] at hδ <;> subst hδ <;> cost_agree

/-- `memoryCost?_cancun` for the Log family. -/
theorem memoryCost?_cancun_log (s : EVM.State) (op : Operation.LOp .EVM) {k : ℕ}
    (hδ : δ (.Log op) = some k) (hk : k ≤ s.stack.length) :
    cancun.memoryCost? s (.Log op) = some (memoryExpansionCost s (.Log op)) := by
  cases op <;> simp only [δ, Option.some.injEq] at hδ <;> subst hδ <;> mem_agree

/-- `instrCost?_isSome` for the Log family. -/
theorem instrCost?_isSome_log (fs : ForkSchedule) (g : ℕ) (s : EVM.State)
    (op : Operation.LOp .EVM) {k : ℕ}
    (hδ : δ (.Log op) = some k) (hk : k ≤ s.stack.length) :
    (fs.instrCost? g s (.Log op)).isSome := by
  cases op <;> simp only [δ, Option.some.injEq] at hδ <;> subst hδ <;> cost_some

/-- `memoryCost?_isSome` for the Log family. -/
theorem memoryCost?_isSome_log (fs : ForkSchedule) (s : EVM.State) (op : Operation.LOp .EVM) {k : ℕ}
    (hδ : δ (.Log op) = some k) (hk : k ≤ s.stack.length) :
    (fs.memoryCost? s (.Log op)).isSome := by
  cases op <;> simp only [δ, Option.some.injEq] at hδ <;> subst hδ <;> mem_some

/-- `instrCost?_cancun` for the System family. -/
theorem instrCost?_cancun_system (s : EVM.State) (op : Operation.SOp .EVM) {k : ℕ}
    (hδ : δ (.System op) = some k) (hk : k ≤ s.stack.length) :
    cancun.instrCost? s.gasAvailable.toNat s (.System op) = some (C' s (.System op)) := by
  cases op <;> simp only [δ, Option.some.injEq, reduceCtorEq] at hδ <;> subst hδ <;> cost_agree

/-- `memoryCost?_cancun` for the System family. -/
theorem memoryCost?_cancun_system (s : EVM.State) (op : Operation.SOp .EVM) {k : ℕ}
    (hδ : δ (.System op) = some k) (hk : k ≤ s.stack.length) :
    cancun.memoryCost? s (.System op) = some (memoryExpansionCost s (.System op)) := by
  cases op <;> simp only [δ, Option.some.injEq, reduceCtorEq] at hδ <;> subst hδ <;> mem_agree

/-- `instrCost?_isSome` for the System family. -/
theorem instrCost?_isSome_system (fs : ForkSchedule) (g : ℕ) (s : EVM.State)
    (op : Operation.SOp .EVM) {k : ℕ}
    (hδ : δ (.System op) = some k) (hk : k ≤ s.stack.length) :
    (fs.instrCost? g s (.System op)).isSome := by
  cases op <;> simp only [δ, Option.some.injEq, reduceCtorEq] at hδ <;> subst hδ <;> cost_some

/-- `memoryCost?_isSome` for the System family. -/
theorem memoryCost?_isSome_system (fs : ForkSchedule) (s : EVM.State)
    (op : Operation.SOp .EVM) {k : ℕ}
    (hδ : δ (.System op) = some k) (hk : k ≤ s.stack.length) :
    (fs.memoryCost? s (.System op)).isSome := by
  cases op <;> simp only [δ, Option.some.injEq, reduceCtorEq] at hδ <;> subst hδ <;> mem_some

/-- **Agreement with `C'`**: for an instruction whose operands are on the stack, the Cancun
instruction cost (evaluated with the state's gas) is the interpreter's `C'`. -/
theorem instrCost?_cancun (s : EVM.State) (w : Operation .EVM) {k : ℕ}
    (hδ : δ w = some k) (hk : k ≤ s.stack.length) :
    cancun.instrCost? s.gasAvailable.toNat s w = some (C' s w) := by
  cases w with
  | StopArith op => exact instrCost?_cancun_stopArith s op hδ hk
  | CompBit op => exact instrCost?_cancun_compBit s op hδ hk
  | Keccak op => exact instrCost?_cancun_keccak s op hδ hk
  | Env op => exact instrCost?_cancun_env s op hδ hk
  | Block op => exact instrCost?_cancun_block s op hδ hk
  | StackMemFlow op => exact instrCost?_cancun_stackMemFlow s op hδ hk
  | Push op => exact instrCost?_cancun_push s op hδ hk
  | Dup op => exact instrCost?_cancun_dup s op hδ hk
  | Exchange op => exact instrCost?_cancun_exchange s op hδ hk
  | Log op => exact instrCost?_cancun_log s op hδ hk
  | System op => exact instrCost?_cancun_system s op hδ hk

/-- **Agreement with `memoryExpansionCost`** for an instruction whose operands are on the stack. -/
theorem memoryCost?_cancun (s : EVM.State) (w : Operation .EVM) {k : ℕ}
    (hδ : δ w = some k) (hk : k ≤ s.stack.length) :
    cancun.memoryCost? s w = some (memoryExpansionCost s w) := by
  cases w with
  | StopArith op => exact memoryCost?_cancun_stopArith s op hδ hk
  | CompBit op => exact memoryCost?_cancun_compBit s op hδ hk
  | Keccak op => exact memoryCost?_cancun_keccak s op hδ hk
  | Env op => exact memoryCost?_cancun_env s op hδ hk
  | Block op => exact memoryCost?_cancun_block s op hδ hk
  | StackMemFlow op => exact memoryCost?_cancun_stackMemFlow s op hδ hk
  | Push op => exact memoryCost?_cancun_push s op hδ hk
  | Dup op => exact memoryCost?_cancun_dup s op hδ hk
  | Exchange op => exact memoryCost?_cancun_exchange s op hδ hk
  | Log op => exact memoryCost?_cancun_log s op hδ hk
  | System op => exact memoryCost?_cancun_system s op hδ hk

/-- For every schedule, the instruction cost of a valid instruction with its operands on the stack
is defined. -/
theorem instrCost?_isSome (fs : ForkSchedule) (g : ℕ) (s : EVM.State) (w : Operation .EVM) {k : ℕ}
    (hδ : δ w = some k) (hk : k ≤ s.stack.length) :
    (fs.instrCost? g s w).isSome := by
  cases w with
  | StopArith op => exact instrCost?_isSome_stopArith fs g s op hδ hk
  | CompBit op => exact instrCost?_isSome_compBit fs g s op hδ hk
  | Keccak op => exact instrCost?_isSome_keccak fs g s op hδ hk
  | Env op => exact instrCost?_isSome_env fs g s op hδ hk
  | Block op => exact instrCost?_isSome_block fs g s op hδ hk
  | StackMemFlow op => exact instrCost?_isSome_stackMemFlow fs g s op hδ hk
  | Push op => exact instrCost?_isSome_push fs g s op hδ hk
  | Dup op => exact instrCost?_isSome_dup fs g s op hδ hk
  | Exchange op => exact instrCost?_isSome_exchange fs g s op hδ hk
  | Log op => exact instrCost?_isSome_log fs g s op hδ hk
  | System op => exact instrCost?_isSome_system fs g s op hδ hk

/-- For every schedule, the memory cost of a valid instruction with its operands on the stack is
defined. -/
theorem memoryCost?_isSome (fs : ForkSchedule) (s : EVM.State) (w : Operation .EVM) {k : ℕ}
    (hδ : δ w = some k) (hk : k ≤ s.stack.length) :
    (fs.memoryCost? s w).isSome := by
  cases w with
  | StopArith op => exact memoryCost?_isSome_stopArith fs s op hδ hk
  | CompBit op => exact memoryCost?_isSome_compBit fs s op hδ hk
  | Keccak op => exact memoryCost?_isSome_keccak fs s op hδ hk
  | Env op => exact memoryCost?_isSome_env fs s op hδ hk
  | Block op => exact memoryCost?_isSome_block fs s op hδ hk
  | StackMemFlow op => exact memoryCost?_isSome_stackMemFlow fs s op hδ hk
  | Push op => exact memoryCost?_isSome_push fs s op hδ hk
  | Dup op => exact memoryCost?_isSome_dup fs s op hδ hk
  | Exchange op => exact memoryCost?_isSome_exchange fs s op hδ hk
  | Log op => exact memoryCost?_isSome_log fs s op hδ hk
  | System op => exact memoryCost?_isSome_system fs s op hδ hk

end ForkSchedule

end EVM

end EvmYul
