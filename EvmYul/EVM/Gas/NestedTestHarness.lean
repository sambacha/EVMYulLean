module

public import EvmYul.EVM.Gas.StepFrameTestHarness
public meta import EvmYul.EVM.Gas.StepFrameTestHarness
public import EvmYul.EVM.Gas.NestedFuel
public meta import EvmYul.EVM.Gas.NestedFuel
@[expose] public meta section

/-!
# Test harness of `NestedTests`

The definitions that `NestedTests.lean` runs and that other test files reuse: generators, observers,
runners, mutants and the lemmas about them. They used to live in the test file itself, which made
other test files import a test file as a fixture library; `GUIDELINES.md` Rule 3 keeps shared
fixtures in a harness module instead (layout check L10). Every declaration keeps its name and
namespace.
-/

namespace EvmYul

namespace EVM

namespace NestedTests

open GasMeter Plausible StepFrameTests
open EvmYul.Testing.EvmFixtures

/-! ## Callee programs -/

def progSTOP : ByteArray := ⟨#[0x00]⟩

/-- `JUMPDEST; PUSH1 0; JUMP` — loops until out of gas. -/
def progLoop : ByteArray := ⟨#[0x5b, 0x60, 0x00, 0x56]⟩

/-- `PUSH1 32; PUSH1 0; RETURN`. -/
def progReturn : ByteArray := ⟨#[0x60, 0x20, 0x60, 0x00, 0xf3]⟩

/-- `PUSH1 0; PUSH1 0; REVERT`. -/
def progRevert : ByteArray := ⟨#[0x60, 0x00, 0x60, 0x00, 0xfd]⟩

/-- `PUSH1 1; PUSH1 0; SSTORE; STOP`. -/
def progSstore : ByteArray := ⟨#[0x60, 0x01, 0x60, 0x00, 0x55, 0x00]⟩

/-- `CALL(GAS, ADDRESS, 0, 0, 0, 0, 0); STOP` — calls itself until depth or gas runs out. -/
def progRecurse : ByteArray :=
  ⟨#[0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0x30, 0x5a, 0xf1, 0x00]⟩

/-- `CREATE(0, 0, 0); STOP` — a nested creation with empty init code. -/
def progCreate : ByteArray := ⟨#[0x60, 0x00, 0x60, 0x00, 0x60, 0x00, 0xf0, 0x00]⟩

def programs : List ByteArray :=
  [progSTOP, progLoop, progReturn, progRevert, progSstore, progRecurse, progCreate]

def prog (k : Fin 7) : ByteArray := programs.getD k.val progSTOP

/-- The callee address used throughout. -/
def callee : AccountAddress := Fin.ofNat _ 0x1000

/-- An account map with the callee holding `code` (and some balance for CREATE). -/
def calleeMap (code : ByteArray) : AccountMap .EVM :=
  (∅ : AccountMap .EVM).insert callee { (default : Account .EVM) with code, balance := u 10 }

/-- Run `Θ` on `callee` running `code`, with gas `g` and fuel `fuel`. -/
def runΘ (fuel : ℕ) (code : ByteArray) (g : ℕ) : Except ExecutionException FrameResult :=
  let σ := calleeMap code
  Θ fuel [] .empty default ∅ σ σ default (Fin.ofNat _ 0x2000) (Fin.ofNat _ 0x2000) callee
    (.Code code) (u g) ⟨0⟩ ⟨0⟩ ⟨0⟩ .empty 1 default true

/-- `Θ_ne_outOfFuel` and `Θ_gasLeft_le`, executed (fuel `g + 5`). -/
def θSpec (code : ByteArray) (g : ℕ) : Bool :=
  match runΘ (g + 5) code g with
  | .error e => !(e == .OutOfFuel)
  | .ok r => decide (r.gasLeft.toNat ≤ g)

def θGasLeft? (code : ByteArray) (g : ℕ) : Option ℕ :=
  match runΘ (g + 5) code g with
  | .ok r => some r.gasLeft.toNat
  | .error _ => none

/-! ## A CALL step into a code-running callee -/

/-- Caller state: balance `bal`, gas `g`, the callee installed with `code`, and a CALL stack
(requested gas `gReq`, value `val`, empty memory ranges). -/
def callState (code : ByteArray) (gReq val bal g : ℕ) : EVM.State :=
  let s0 := withGas (withStack [u gReq, u callee.val, u val, u 0, u 0, u 0, u 0]) g
  let acct : Account .EVM := { (default : Account .EVM) with balance := u bal }
  { s0 with accountMap := (calleeMap code).insert s0.executionEnv.codeOwner acct }

/-- `Z`, then the CALL step with fuel `gas + 2`: no `OutOfFuel`, and the gas strictly drops
(`step_CALL_gas_lt`). Samples rejected by `Z` pass trivially (see the coverage check). -/
def callSpec (k : Fin 7) (gReq val bal g : ℕ) : Bool :=
  let s := callState (prog k) (gReq % 300000) (val % 3) (bal % 3) (30000 + g % 400000)
  match exceptionalHalt #[] .CALL s with
  | .error _ => true
  | .ok (s₁, c) =>
    match step (s₁.gasAvailable.toNat + 2) c (some (.CALL, none)) s₁ with
    | .error e => !(e == .OutOfFuel)
    | .ok s₂ => decide (s₂.gasAvailable.toNat < s₁.gasAvailable.toNat)

/-- The caller's gas after the CALL step (`none` if `Z` or the step failed). -/
def callGasAfter? (code : ByteArray) (gReq val bal g : ℕ) : Option ℕ :=
  let s := callState code gReq val bal g
  match exceptionalHalt #[] .CALL s with
  | .error _ => none
  | .ok (s₁, c) =>
    match step (s₁.gasAvailable.toNat + 2) c (some (.CALL, none)) s₁ with
    | .error _ => none
    | .ok s₂ => some s₂.gasAvailable.toNat

/-- Gas the callee program `k` burned, measured against the same CALL into a STOP callee (which
hands everything back). Positive means the callee ran code that used gas. -/
def callBurn? (k : Fin 7) (gReq g : ℕ) : Option ℕ := do
  let a ← callGasAfter? progSTOP gReq 0 0 g
  let b ← callGasAfter? (prog k) gReq 0 0 g
  pure (a - b)

/-- Mutant: "the callee's consumption is not charged to the caller" (every callee costs the
caller exactly what a STOP callee costs). -/
def callNoBurn (k : Fin 7) (gReq g : ℕ) : Bool :=
  match callBurn? k (gReq % 300000) (30000 + g % 400000) with
  | some b => b == 0
  | none => true

/-! ## A whole transaction (`Υ`) -/

def sender : AccountAddress := Fin.ofNat _ 0x3000

/-- `Υ` on a legacy transaction to `callee` running `code`, gas limit `21000 + gl`, with `fuel`. -/
def runΥ (fuel : ℕ) (code : ByteArray) (gl : ℕ) :
    Except EVM.Exception (AccountMap .EVM × Substate × Bool × UInt256) :=
  let σ := (calleeMap code).insert sender { (default : Account .EVM) with balance := u 0 }
  let T : Transaction :=
    .legacy { nonce := ⟨0⟩, gasLimit := u (21000 + gl), recipient := some callee, value := ⟨0⟩,
              r := .empty, s := .empty, data := .empty, gasPrice := ⟨0⟩, w := ⟨0⟩ }
  Υ fuel σ 0 default default ∅ T sender

def txOf (gl : ℕ) : Transaction :=
  .legacy { nonce := ⟨0⟩, gasLimit := u (21000 + gl), recipient := some callee, value := ⟨0⟩,
            r := .empty, s := .empty, data := .empty, gasPrice := ⟨0⟩, w := ⟨0⟩ }

def isOutOfFuel {α : Type} : Except EVM.Exception α → Bool
  | .error (.ExecutionException .OutOfFuel) => true
  | _ => false

/-- `Υ_transactionFuel_ne_outOfFuel`, executed (zero sender balance, as in CE-9). -/
def υSpec (k : Fin 7) (gl : ℕ) : Bool :=
  !isOutOfFuel (runΥ (transactionFuel (txOf (gl % 60000)) ⟨0⟩) (prog k) (gl % 60000))

/-! ## 3. Coverage -/

/-- Grid samples (7 programs × 4 requested gases × 3 caller gases) whose CALL burned more than the
bare charge, i.e. ran callee code that used gas. -/
def callCoverage : ℕ := Id.run do
  let mut n := 0
  for k in List.finRange 7 do
    for gReq in [100, 5000, 50000, 250000] do
      for g in [60000, 200000, 400000] do
        if (callBurn? k gReq g).any (· > 0) then n := n + 1
  return n

instance : Shrinkable (Fin 7) := ⟨fun _ => []⟩

instance : Arbitrary (Fin 7) where
  arbitrary := do
    let n ← Gen.choose Nat 0 6 (by decide)
    pure ⟨n.val, by omega⟩

end NestedTests

end EVM

end EvmYul
