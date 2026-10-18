module

public import EvmYul.EVM.Semantics
public import EvmYul.Vyper.Fixture

public section

/-!
# Running compiled Vyper contracts on this project's EVM (V1 harness)

The fixtures in `EvmYul/Vyper/Fixtures.lean` are runtime bytecode produced by real Vyper compilers.
This module executes them on the project's message-call semantics `Θ` (the same entry point as
`NestedTests.runΘ` and `LoweringTests.gasUsed`) with ABI-encoded calldata, an initial storage,
and a call value, and reports what a user of the contract would observe: how the frame ended, the
gas it consumed, the return data and the storage afterwards.

Proof obligations discharged here (the harness is test infrastructure, so what it feeds the EVM
must be right *by proof*, not by another test):

* `fromBytesBigEndian_word`: the 32-byte ABI word of `n` decodes, with the project's own big-endian
  decoder (the one `CALLDATALOAD` uses), to `n mod 2^256`; `word_length`: it is 32 bytes.
* `calldata_size`: a call with `k` arguments is `4 + 32 k` bytes, so Vyper's `calldatasize` guard
  sees a well-formed call.
* `uInt256OfByteArray_word`: the word read back as a `UInt256` is `UInt256.ofNat n`.
* `allUpTo_iff`: the exhaustive sweep `allUpTo b p` is exactly `∀ n ≤ b, p n`, so a passing sweep
  over `[0, bound]` *is* the universally quantified statement (TESTING.md F1, F3).
-/

namespace EvmYul.Vyper

open EVM

/-! ## Hex and ABI encoding -/

/-- Value of one lower-case or upper-case hex digit. -/
def hexDigit? (c : Char) : Option ℕ :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- Decode a list of hex digits, two per byte; `none` on an odd length or a non-hex character. -/
def hexBytes? : List Char → Option (List UInt8)
  | [] => some []
  | [_] => none
  | a :: b :: rest => do
    let hi ← hexDigit? a
    let lo ← hexDigit? b
    let tl ← hexBytes? rest
    pure ((16 * hi + lo).toUInt8 :: tl)

/-- Decode a hex string (no `0x`) into bytes. -/
def ofHex? (s : String) : Option ByteArray := (hexBytes? s.toList).map fun l => ⟨l.toArray⟩

/-- Lower-case hex rendering, the inverse direction (used for the D2 round-trip check). -/
def hexOf (b : ByteArray) : String :=
  String.join <| b.toList.map fun x =>
    let d (k : ℕ) : Char := if k < 10 then Char.ofNat (48 + k) else Char.ofNat (87 + k)
    String.ofList [d (x.toNat / 16), d (x.toNat % 16)]

/-- The `k` low-order bytes of `n`, big-endian. -/
def bytesBE : ℕ → ℕ → List UInt8
  | 0, _ => []
  | k + 1, n => bytesBE k (n / 256) ++ [UInt8.ofNat (n % 256)]

/-- The 32-byte ABI encoding of a `uint256` argument (`n mod 2^256`). -/
@[expose] def word (n : ℕ) : List UInt8 := bytesBE 32 n

/-- ABI calldata: 4-byte selector, then one 32-byte word per argument. -/
def calldata (sel : ℕ) (args : List ℕ) : ByteArray :=
  ⟨(bytesBE 4 sel ++ args.flatMap word).toArray⟩

theorem bytesBE_length (k n : ℕ) : (bytesBE k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [bytesBE, ih]

theorem word_length (n : ℕ) : (word n).length = 32 := bytesBE_length 32 n

theorem calldata_size (sel : ℕ) (args : List ℕ) :
    (calldata sel args).size = 4 + 32 * args.length := by
  simp only [calldata, ByteArray.size, List.size_toArray, List.length_append, bytesBE_length]
  congr 1
  induction args with
  | nil => rfl
  | cons a as ih => simp [List.flatMap_cons, word_length, ih, Nat.mul_succ, Nat.add_comm]

/-- The project's little-endian decoder on a reversed big-endian encoding. -/
theorem fromBytes'_reverse_bytesBE (k n : ℕ) :
    fromBytes' (bytesBE k n).reverse = n % 256 ^ k := by
  induction k generalizing n with
  | zero => simp [bytesBE, fromBytes', Nat.mod_one]
  | succ k ih =>
    simp only [bytesBE, List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, fromBytes', ih]
    have h : (UInt8.ofNat (n % 256)).toFin.val = n % 256 := by
      simp [UInt8.ofNat, UInt8.toFin, Nat.mod_mod_of_dvd]
    rw [h, show 256 ^ (k + 1) = 256 * 256 ^ k from pow_succ' 256 k, Nat.mod_mul]
    norm_num

theorem fromBytesBigEndian_word (n : ℕ) : fromBytesBigEndian (word n) = n % 2 ^ 256 := by
  simp only [fromBytesBigEndian, Function.comp, word, fromBytes'_reverse_bytesBE]
  norm_num

theorem uInt256OfByteArray_word (n : ℕ) :
    uInt256OfByteArray ⟨(word n).toArray⟩ = UInt256.ofNat n := by
  have := fromBytesBigEndian_word n
  simp only [fromBytesBigEndian, Function.comp] at this
  simp only [uInt256OfByteArray, this]
  apply UInt256.ext
  simp only [UInt256.ofNat, Id.run]
  apply Fin.ext
  simp [Fin.val_natCast, UInt256.size]

/-! ## The exhaustive sweep -/

/-- `p n` for every `n ≤ b` (the executable form of a bounded `∀`). -/
def allUpTo (b : ℕ) (p : ℕ → Bool) : Bool := (List.range (b + 1)).all p

theorem allUpTo_iff (b : ℕ) (p : ℕ → Bool) : allUpTo b p = true ↔ ∀ n ≤ b, p n = true := by
  simp [allUpTo, List.all_eq_true, List.mem_range, Nat.lt_succ_iff]

/-! ## Executing a call on `Θ` -/

/-- Address of the contract under test. -/
def contractAddr : AccountAddress := Fin.ofNat _ 0x1000

/-- Address of the caller (sender and origin). -/
def callerAddr : AccountAddress := Fin.ofNat _ 0x2000

/-- Gas given to every measured call (well above every estimate in the corpus). -/
def budget : ℕ := 5000000

/-- A storage map from `(slot, value)` pairs. -/
def storageOf (kvs : List (ℕ × ℕ)) : Storage :=
  kvs.foldl (fun s (k, v) => if v = 0 then s else s.insert (.ofNat k) (.ofNat v)) ∅

/-- The world before the call: the contract with its code and storage, a funded caller. -/
def worldOf (code : ByteArray) (kvs : List (ℕ × ℕ)) : AccountMap .EVM :=
  ((∅ : AccountMap .EVM).insert contractAddr
      { (default : Account .EVM) with code, storage := storageOf kvs }).insert callerAddr
    { (default : Account .EVM) with balance := .ofNat (2 ^ 128) }

/-- What a caller observes after one message call. -/
structure Run where
  /-- How the frame ended. -/
  outcome : FrameOutcome
  /-- Gas handed back by the frame (`Θ_gasLeft_le`: at most `budget`). -/
  gasLeft : ℕ
  /-- Gas consumed by execution (`budget − gasLeft`; intrinsic transaction gas not included). -/
  gasUsed : ℕ
  /-- Return data (`RETURN` or `REVERT` payload). -/
  output : ByteArray
  /-- World state after the frame. -/
  world : AccountMap .EVM

/-- Storage slot `k` of the contract after the call. -/
def Run.slot (r : Run) (k : ℕ) : ℕ :=
  match r.world.get? contractAddr with
  | some a => (a.lookupStorage (.ofNat k)).toNat
  | none => 0

/-- Did the call succeed? -/
def Run.ok (r : Run) : Bool := r.outcome == .success

/-- Run `code` with storage `kvs`, calldata `data` and call value `value` on `Θ`, with fuel
`budget + 5` (enough by `Θ_ne_outOfFuel`). `none` only if `Θ` itself errors. -/
def execute (code : ByteArray) (kvs : List (ℕ × ℕ)) (data : ByteArray) (value : ℕ := 0) :
    Option Run :=
  let σ := worldOf code kvs
  match Θ (budget + 5) [] .empty default ∅ σ σ default callerAddr callerAddr contractAddr
      (.Code code) (.ofNat budget) ⟨0⟩ (.ofNat value) (.ofNat value) data 1 default true with
  | .ok r => some { outcome := r.outcome, gasLeft := r.gasLeft.toNat,
                    gasUsed := budget - r.gasLeft.toNat,
                    output := r.output, world := r.accountMap }
  | .error _ => none

/-! ## Reading a cell -/

/-- The runtime bytecode of a cell (`none` if the hex is malformed). -/
def Cell.code? (c : Cell) : Option ByteArray := ofHex? c.runtimeHex

/-- Selector of an ABI signature in this cell. -/
def Cell.selector? (c : Cell) (sig : String) : Option ℕ := c.selectors.lookup sig

/-- Vyper's gas estimate for a function of this cell. -/
def Cell.estimate? (c : Cell) (fn : String) : Option ℕ := c.gasEstimates.lookup fn

/-- Storage slot of a variable of this cell. -/
def Cell.slot? (c : Cell) (v : String) : Option ℕ := c.storageSlots.lookup v

/-- Call function `sig` of cell `c` with arguments `args`, from storage `kvs`. -/
def Cell.call? (c : Cell) (sig : String) (args : List ℕ) (kvs : List (ℕ × ℕ)) (value : ℕ := 0) :
    Option Run := do
  let code ← c.code?
  let sel ← c.selector? sig
  execute code kvs (calldata sel args) value

/-! ## K16 as a statement, and the sweep that establishes it (TESTING.md F3)

`EstimateSound c sig fn kvs b` is conjecture K16 restricted to one fixture: every successful call of
`sig` with an argument `n ≤ b`, from storage `kvs`, consumes at most Vyper's estimate for `fn`. The
build evaluates the Boolean sweep `allUpTo b (gasWithin …)`; `estimateSound_of_sweep` proves that a
passing sweep *is* the statement, so the test and the claim cannot drift apart. -/

/-- One point of the K16 sweep: the call ran (no `Θ` error), and if it succeeded its gas is within
the estimate. A missing estimate or selector is a failure, not a pass. -/
def gasWithin (c : Cell) (sig fn : String) (kvs : List (ℕ × ℕ)) (n : ℕ) : Bool :=
  match c.call? sig [n] kvs, c.estimate? fn with
  | some r, some e => !r.ok || decide (r.gasUsed ≤ e)
  | _, _ => false

/-- K16 for one fixture, one function, arguments `n ≤ b`. -/
@[expose] def EstimateSound (c : Cell) (sig fn : String) (kvs : List (ℕ × ℕ)) (b : ℕ) : Prop :=
  ∀ n ≤ b, ∀ r e, c.call? sig [n] kvs = some r → c.estimate? fn = some e → r.ok = true →
    r.gasUsed ≤ e

theorem estimateSound_of_sweep {c : Cell} {sig fn : String} {kvs : List (ℕ × ℕ)} {b : ℕ}
    (h : allUpTo b (gasWithin c sig fn kvs) = true) : EstimateSound c sig fn kvs b := by
  intro n hn r e hr he hok
  have := (allUpTo_iff b _).mp h n hn
  simp only [gasWithin, hr, he, hok, Bool.not_true, Bool.false_or, decide_eq_true_eq] at this
  exact this

/-- Conversely, a failing sweep point with a successful run is a concrete K16 counterexample. -/
theorem not_estimateSound_of_witness {c : Cell} {sig fn : String} {kvs : List (ℕ × ℕ)} {b n : ℕ}
    {r : Run} {e : ℕ} (hn : n ≤ b) (hr : c.call? sig [n] kvs = some r) (he : c.estimate? fn = some e)
    (hok : r.ok = true) (hgt : e < r.gasUsed) : ¬ EstimateSound c sig fn kvs b :=
  fun h => absurd (h n hn r e hr he hok) (by omega)

end EvmYul.Vyper
