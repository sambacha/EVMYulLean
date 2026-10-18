module

public import EvmYul.EVM.Gas.ForkCostLemmas
public section

/-!
# Every non-halting instruction costs gas, in every named fork

`minCost fs w` is a state-independent lower bound of the instruction cost (`instrCost?_ge_minCost`).
Under the decidable condition `PositivePrices fs` (checked for all 13 named forks by `decide` in
`positivePrices_ofFork`), `minCost fs w` is positive for every opcode that exists in the fork and is
not one of the halting instructions STOP, RETURN, REVERT, SELFDESTRUCT, INVALID
(`minCost_pos`). Hence `instrCost?_pos`: **a non-halting instruction is never free.** SELFDESTRUCT
must be excluded: it is free in Frontier and Homestead (`Gselfdestruct = 0`), see
`frontier_selfdestruct_free`.
-/

namespace EvmYul

namespace EVM

open GasMeter InstructionGasGroups

namespace ForkSchedule

/-- The instructions that end the current frame (they need not cost gas). -/
@[expose] def halting (w : Operation .EVM) : Bool :=
  w == .STOP || w == .RETURN || w == .REVERT || w == .SELFDESTRUCT || w == .INVALID

/-- The cheapest possible account access: warm/cold minimum, or the flat price. -/
def accessFloor (fs : ForkSchedule) (flat : ℕ) : ℕ :=
  if fs.eip2929 then min fs.Gwarmaccess fs.Gcoldaccountaccess else flat

/-- The cheapest possible SLOAD. -/
def sloadFloor (fs : ForkSchedule) : ℕ :=
  if fs.eip2929 then min fs.Gwarmaccess fs.Gcoldsload else fs.Gsload

/-- The cheapest possible SSTORE. -/
def sstoreFloor (fs : ForkSchedule) : ℕ :=
  match fs.sstoreRule with
  | .frontier => min fs.Gsset fs.Gsreset
  | .netMetered => min (if fs.eip2929 then fs.Gwarmaccess else fs.Gsload) (min fs.Gsset fs.Gsreset)

/-- A state-independent lower bound of the instruction cost of `w` under `fs`. -/
def minCost (fs : ForkSchedule) (w : Operation .EVM) : ℕ :=
  match feeGroup w with
  | .zero => fs.Gzero
  | .base => fs.Gbase
  | .verylow => fs.Gverylow
  | .low => fs.Glow
  | .mid => fs.Gmid
  | .high => fs.Ghigh
  | .jumpdest => fs.Gjumpdest
  | .blockhash => fs.Gblockhash
  | .blobhash => fs.HASH_OPCODE_GAS
  | .transient => fs.Gwarmaccess
  | .copy => fs.Gverylow
  | .extAccount => fs.accessFloor (fs.extAccountFlat w)
  | .exp => fs.Gexp
  | .extcodecopy => fs.accessFloor fs.Gextcode
  | .log => fs.Glog
  | .keccak => fs.Gkeccak256
  | .create => fs.Gcreate
  | .sload => fs.sloadFloor
  | .sstore => fs.sstoreFloor
  | .call => fs.accessFloor fs.Gcall
  | .selfdestruct => fs.Gselfdestruct
  | .invalid => 0

/-- Decidable sufficient condition for "every non-halting instruction costs gas". -/
@[expose] def PositivePrices (fs : ForkSchedule) : Prop :=
  0 < fs.Gjumpdest ∧ 0 < fs.Gbase ∧ 0 < fs.Gverylow ∧ 0 < fs.Glow ∧ 0 < fs.Gmid ∧
  0 < fs.Ghigh ∧ 0 < fs.Gexp ∧ 0 < fs.Glog ∧ 0 < fs.Gkeccak256 ∧ 0 < fs.Gcreate ∧
  0 < fs.Gblockhash ∧ 0 < fs.Gsset ∧ 0 < fs.Gsreset ∧
  (fs.eip2929 = true → 0 < fs.Gwarmaccess ∧ 0 < fs.Gcoldaccountaccess ∧ 0 < fs.Gcoldsload) ∧
  (fs.eip2929 = false → 0 < fs.Gsload ∧ 0 < fs.Gbalance ∧ 0 < fs.Gextcode ∧ 0 < fs.Gcall) ∧
  (fs.available .EXTCODEHASH = true → fs.eip2929 = false → 0 < fs.Gextcodehash) ∧
  (fs.available .BLOBHASH = true → 0 < fs.HASH_OPCODE_GAS) ∧
  (fs.available .TLOAD = true → 0 < fs.Gwarmaccess)

@[expose] instance (fs : ForkSchedule) : Decidable fs.PositivePrices := by
  unfold PositivePrices; infer_instance

/-- All 13 named forks satisfy `PositivePrices`. -/
theorem positivePrices_ofFork (f : Fork) : (ofFork f).PositivePrices := by
  cases f <;> decide

/-! ## Lower bounds of the cost components -/

theorem accessFloor_le (fs : ForkSchedule) (a : AccountAddress) (A : Substate) (flat : ℕ) :
    fs.accessFloor flat ≤ fs.accessCost a A flat := by
  unfold accessFloor accessCost; split_ifs <;> omega

theorem sloadFloor_le (fs : ForkSchedule) (A : Substate) (I : ExecutionEnv .EVM) (k : UInt256) :
    fs.sloadFloor ≤ fs.sloadCost A I k := by
  unfold sloadFloor sloadCost; split_ifs <;> omega

theorem sstoreFloor_le (fs : ForkSchedule) (s : EVM.State) (k v' : UInt256) :
    fs.sstoreFloor ≤ fs.sstoreCost s k v' := by
  unfold sstoreFloor sstoreCost
  cases fs.sstoreRule <;> dsimp only <;> split_ifs <;> omega

theorem selfdestruct_ge (fs : ForkSchedule) (s : EVM.State) (r : UInt256) :
    fs.Gselfdestruct ≤ fs.selfdestructCost s r := by
  unfold selfdestructCost; simp only; omega

theorem callCost_ge (fs : ForkSchedule) (gas : ℕ) (t r : AccountAddress) (val g : UInt256)
    (σ : AccountMap .EVM) (A : Substate) :
    fs.accessFloor fs.Gcall ≤ fs.callCost gas t r val g σ A := by
  have := accessFloor_le fs t A fs.Gcall
  unfold callCost callExtra; omega

set_option hygiene false in
/-- Lower bound of one opcode case of `instrCost?_ge_minCost` (non-hygienic: uses `h`). -/
macro "min_le_case" : tactic => `(tactic| first
  | (simp only [minCost, feeGroup]; exact Nat.zero_le _)
  | (simp only [instrCost?] at h
     repeat (rw [if_neg (by decide)] at h)
     rw [if_pos (by decide)] at h
     simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
       Option.some.injEq] at h
     simp only [minCost, feeGroup]
     first
       | (cases h; exact le_refl _)
       | (obtain ⟨_, -, rfl⟩ := h; first | omega | exact accessFloor_le ..))
  | (simp only [instrCost?, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
       Option.some.injEq] at h
     simp only [minCost, feeGroup]
     first
       | (cases h; exact le_refl _)
       | (obtain ⟨_, -, rfl⟩ := h; first
           | exact sstoreFloor_le ..
           | exact sloadFloor_le ..
           | exact selfdestruct_ge ..
           | (split <;> omega)
           | omega)
       | (obtain ⟨_, -, _, -, rfl⟩ := h; first
           | exact sstoreFloor_le ..
           | exact le_trans (accessFloor_le ..) (Nat.le_add_right _ _)
           | exact callCost_ge ..
           | omega)
       | (obtain ⟨_, -, _, -, _, -, rfl⟩ := h; exact callCost_ge ..)))

/-- `instrCost?_ge_minCost` for the StopArith family. -/
theorem instrCost?_ge_minCost_stopArith (fs : ForkSchedule) (g : ℕ) (s : EVM.State)
    (op : Operation.SAOp .EVM) {c : ℕ} (h : fs.instrCost? g s (.StopArith op) = some c) :
    fs.minCost (.StopArith op) ≤ c := by
  cases op <;> min_le_case

/-- `instrCost?_ge_minCost` for the CompBit family. -/
theorem instrCost?_ge_minCost_compBit (fs : ForkSchedule) (g : ℕ) (s : EVM.State)
    (op : Operation.CBLOp .EVM) {c : ℕ} (h : fs.instrCost? g s (.CompBit op) = some c) :
    fs.minCost (.CompBit op) ≤ c := by
  cases op <;> min_le_case

/-- `instrCost?_ge_minCost` for the Keccak family. -/
theorem instrCost?_ge_minCost_keccak (fs : ForkSchedule) (g : ℕ) (s : EVM.State)
    (op : Operation.KOp .EVM) {c : ℕ} (h : fs.instrCost? g s (.Keccak op) = some c) :
    fs.minCost (.Keccak op) ≤ c := by
  cases op; min_le_case

/-- `instrCost?_ge_minCost` for the Env family. -/
theorem instrCost?_ge_minCost_env (fs : ForkSchedule) (g : ℕ) (s : EVM.State)
    (op : Operation.EOp .EVM) {c : ℕ} (h : fs.instrCost? g s (.Env op) = some c) :
    fs.minCost (.Env op) ≤ c := by
  cases op <;> min_le_case

/-- `instrCost?_ge_minCost` for the Block family. -/
theorem instrCost?_ge_minCost_block (fs : ForkSchedule) (g : ℕ) (s : EVM.State)
    (op : Operation.BOp .EVM) {c : ℕ} (h : fs.instrCost? g s (.Block op) = some c) :
    fs.minCost (.Block op) ≤ c := by
  cases op <;> min_le_case

/-- `instrCost?_ge_minCost` for the StackMemFlow family. -/
theorem instrCost?_ge_minCost_stackMemFlow (fs : ForkSchedule) (g : ℕ) (s : EVM.State)
    (op : Operation.SMSFOp .EVM) {c : ℕ} (h : fs.instrCost? g s (.StackMemFlow op) = some c) :
    fs.minCost (.StackMemFlow op) ≤ c := by
  cases op <;> min_le_case

/-- `instrCost?_ge_minCost` for the Push family. -/
theorem instrCost?_ge_minCost_push (fs : ForkSchedule) (g : ℕ) (s : EVM.State)
    (op : Operation.POp) {c : ℕ} (h : fs.instrCost? g s (.Push op) = some c) :
    fs.minCost (.Push op) ≤ c := by
  cases op <;> min_le_case

/-- `instrCost?_ge_minCost` for the Dup family. -/
theorem instrCost?_ge_minCost_dup (fs : ForkSchedule) (g : ℕ) (s : EVM.State)
    (op : Operation.DOp) {c : ℕ} (h : fs.instrCost? g s (.Dup op) = some c) :
    fs.minCost (.Dup op) ≤ c := by
  cases op <;> min_le_case

/-- `instrCost?_ge_minCost` for the Exchange family. -/
theorem instrCost?_ge_minCost_exchange (fs : ForkSchedule) (g : ℕ) (s : EVM.State)
    (op : Operation.ExOp) {c : ℕ} (h : fs.instrCost? g s (.Exchange op) = some c) :
    fs.minCost (.Exchange op) ≤ c := by
  cases op <;> min_le_case

/-- `instrCost?_ge_minCost` for the Log family. -/
theorem instrCost?_ge_minCost_log (fs : ForkSchedule) (g : ℕ) (s : EVM.State)
    (op : Operation.LOp .EVM) {c : ℕ} (h : fs.instrCost? g s (.Log op) = some c) :
    fs.minCost (.Log op) ≤ c := by
  cases op <;> min_le_case

/-- `instrCost?_ge_minCost` for the System family. -/
theorem instrCost?_ge_minCost_system (fs : ForkSchedule) (g : ℕ) (s : EVM.State)
    (op : Operation.SOp .EVM) {c : ℕ} (h : fs.instrCost? g s (.System op) = some c) :
    fs.minCost (.System op) ≤ c := by
  cases op <;> min_le_case

/-- **`minCost` is a lower bound of the instruction cost**, for every schedule, state and gas. -/
theorem instrCost?_ge_minCost (fs : ForkSchedule) (g : ℕ) (s : EVM.State) (w : Operation .EVM)
    {c : ℕ} (h : fs.instrCost? g s w = some c) : fs.minCost w ≤ c := by
  cases w with
  | StopArith op => exact instrCost?_ge_minCost_stopArith fs g s op h
  | CompBit op => exact instrCost?_ge_minCost_compBit fs g s op h
  | Keccak op => exact instrCost?_ge_minCost_keccak fs g s op h
  | Env op => exact instrCost?_ge_minCost_env fs g s op h
  | Block op => exact instrCost?_ge_minCost_block fs g s op h
  | StackMemFlow op => exact instrCost?_ge_minCost_stackMemFlow fs g s op h
  | Push op => exact instrCost?_ge_minCost_push fs g s op h
  | Dup op => exact instrCost?_ge_minCost_dup fs g s op h
  | Exchange op => exact instrCost?_ge_minCost_exchange fs g s op h
  | Log op => exact instrCost?_ge_minCost_log fs g s op h
  | System op => exact instrCost?_ge_minCost_system fs g s op h

/-- **`minCost` is positive** for every non-halting opcode of the fork, under `PositivePrices`. -/
theorem minCost_pos {fs : ForkSchedule} (hP : fs.PositivePrices) {w : Operation .EVM}
    (ha : fs.available w = true) (hw : halting w = false) : 0 < fs.minCost w := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hA, hB, hX, hBl, hT⟩ := hP
  rcases w with op|op|op|op|op|op|op|op|op|op|op <;> cases op <;>
    simp only [halting, minCost, feeGroup] at hw ⊢ <;>
    first
    | assumption
    | (simp at hw; done)
    | exact hBl ha
    | exact hT ha
    | (try have hX' := hX ha
       simp only [accessFloor, extAccountFlat, sloadFloor, sstoreFloor] at ⊢
       cases he : fs.eip2929 <;> cases hr : fs.sstoreRule <;> simp_all)

/-- **A non-halting instruction is never free**: in a schedule with positive prices, every
instruction cost of an available non-halting opcode is positive, whatever the state and gas. -/
theorem instrCost?_pos {fs : ForkSchedule} (hP : fs.PositivePrices) {g : ℕ} {s : EVM.State}
    {w : Operation .EVM} (ha : fs.available w = true) (hw : halting w = false) {c : ℕ}
    (h : fs.instrCost? g s w = some c) : 0 < c :=
  Nat.lt_of_lt_of_le (minCost_pos hP ha hw) (instrCost?_ge_minCost fs g s w h)

/-- In Frontier SELFDESTRUCT is free (`Gselfdestruct = 0`, no cold or new-account surcharge), which
is why halting instructions are excluded from `instrCost?_pos`. -/
theorem frontier_selfdestruct_free (g : ℕ) (s : EVM.State) (r : UInt256)
    (stk : List UInt256) (hs : s.stack = r :: stk) :
    frontier.instrCost? g s .SELFDESTRUCT = some 0 := by
  simp [instrCost?, hs, selfdestructCost]

end ForkSchedule

end EVM

end EvmYul
