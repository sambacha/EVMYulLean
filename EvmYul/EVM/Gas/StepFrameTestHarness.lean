module

public import EvmYul.Testing.EvmFixtures
public meta import EvmYul.Testing.EvmFixtures
public import EvmYul.EVM.Gas.StepFrame
public meta import EvmYul.EVM.Gas.StepFrame
@[expose] public meta section

/-!
# Test harness of `StepFrameTests`

The definitions that `StepFrameTests.lean` runs and that other test files reuse: generators,
observers, runners, mutants and the lemmas about them. They used to live in the test file itself,
which made other test files import a test file as a fixture library; `GUIDELINES.md` Rule 3 keeps
shared fixtures in a harness module instead (layout check L10). Every declaration keeps its name and
namespace.
-/

namespace EvmYul

namespace EVM

namespace StepFrameTests

open GasMeter Plausible EvmYul.Testing.EvmFixtures

/-- Executable mirror of `GasSafeResult`. -/
def gasSafeB (g : UInt256) : Except ExecutionException State → Bool
  | .ok s' => s'.gasAvailable == g
  | .error e => !(e == .OutOfFuel)

/-- Seventeen small operands (enough for DUP16/SWAP16) and gas `g`. -/
def smallState (a b c : ℕ) (g : ℕ) : EVM.State :=
  let xs := [a, b, c].map (fun n => u (n % 4096))
  withGas (withOwnerAccount (withStack (List.flatten (List.replicate 6 xs)))) g

/-! ## 2. Property tests -/

/-- `evmStep_gasSafe`, executed. -/
def evmStepSpec (o : AnyOp) (a b c g : ℕ) (pushArg : Bool) : Bool :=
  let w := o.op
  let s := smallState a b c g
  let arg := if pushArg then some (u a, 1) else none
  w ∈ spawnOps || gasSafeB s.gasAvailable (EvmYul.step w arg s)

/-- `step_some_gasSafe`, executed: the interpreter's step deducts exactly the (fitting) charge. -/
def stepSpec (o : AnyOp) (a b c g k : ℕ) : Bool :=
  let w := o.op
  let s := smallState a b c g
  let charge := k % (g + 1)
  w ∈ spawnOps ||
    gasSafeB (deductPrechecked s.gasAvailable charge) (step 1 charge (some (w, none)) s)

/-! ### The spawning instructions (regression mirror of proved theorems)

`SpawnStepGasSoundZ` and `SpawnNestedFuelAdequateZ` are proved in `GasNested`. These checks execute random
CREATE/CREATE2/CALL/CALLCODE/DELEGATECALL/STATICCALL instructions whose charge `c` comes from `Z`
(`exceptionalHalt`), with fuel `gas + 2`, and check both. Callees are non-precompile addresses
without code, so nested frames return at once. -/

/-- The six spawning instructions, indexed. -/
def spawnOp (k : Fin 6) : Operation .EVM := spawnOps.getD k.val .CALL

/-- A state for spawning instruction `w`: owner balance `bal`, gas `g`, and operands
(requested gas `gReq`, callee `0x1000 + toN`, value `val`, empty memory ranges). -/
def spawnState (w : Operation .EVM) (gReq toN val bal g : ℕ) : EVM.State :=
  let s0 := withGas (withStack []) g
  let acct : Account .EVM := { (default : Account .EVM) with balance := u bal }
  let s0 := { s0 with accountMap := s0.accountMap.insert s0.executionEnv.codeOwner acct }
  let stack : List UInt256 :=
    if w == .CREATE then [u val, u 0, u 0]
    else if w == .CREATE2 then [u val, u 0, u 0, u toN]
    else if w == .DELEGATECALL || w == .STATICCALL then
      [u gReq, u (0x1000 + toN), u 0, u 0, u 0, u 0]
    else [u gReq, u (0x1000 + toN), u val, u 0, u 0, u 0, u 0]
  { s0 with stack := stack }

/-- Run `Z`, then the step with fuel `gas + 2` (the bound of `NestedFuelAdequateZ`). With
`useZ = false` the charge is replaced by 0 (the refuted, charge-free hypotheses). -/
def spawnSpec (useZ : Bool) (k : Fin 6) (gReq toN val bal g : ℕ) : Bool :=
  let w := spawnOp k
  let s := spawnState w (gReq * 997 % 200000) (toN % 64) (val % 3) (bal % 3)
    (30000 + g * 7919 % 2000000)
  match exceptionalHalt #[] w s with
  | .error _ => true
  | .ok (s₁, c₀) =>
    let c := if useZ then c₀ else 0
    match step (s₁.gasAvailable.toNat + 2) c (some (w, none)) s₁ with
    | .error e => !(e == .OutOfFuel)
    | .ok s₂ =>
      decide (s₂.gasAvailable.toNat ≤ (deductPrechecked s₁.gasAvailable c).toNat) ||
        decide (s₂.gasAvailable.toNat < s₁.gasAvailable.toNat)

/-- Coverage: the sample passes `Z`, so `spawnSpec` really executes the step. -/
def spawnReached (k : Fin 6) (gReq toN val bal g : ℕ) : Bool :=
  let w := spawnOp k
  let s := spawnState w (gReq * 997 % 200000) (toN % 64) (val % 3) (bal % 3)
    (30000 + g * 7919 % 2000000)
  match exceptionalHalt #[] w s with
  | .error _ => false
  | .ok _ => true

/-- Number of passing-`Z` samples on a fixed grid of 6 × 5 × 3 × 3 × 5 inputs. -/
def spawnCoverage : ℕ := Id.run do
  let mut n := 0
  for k in List.finRange 6 do
    for gReq in [0, 1, 50, 300, 1000] do
      for val in [0, 1, 2] do
        for bal in [0, 1, 2] do
          for g in [0, 3, 40, 200, 999] do
            if spawnReached k gReq 7 val bal g then n := n + 1
  return n

/-- Grid samples (same grid as `spawnCoverage`) on which `spawnSpec true` fails. -/
def spawnGridFailures : List (Fin 6 × ℕ × ℕ × ℕ × ℕ) := Id.run do
  let mut bad := []
  for k in List.finRange 6 do
    for gReq in [0, 1, 50, 300, 1000] do
      for val in [0, 1, 2] do
        for bal in [0, 1, 2] do
          for g in [0, 3, 40, 200, 999] do
            unless spawnSpec true k gReq 7 val bal g do bad := (k, gReq, val, bal, g) :: bad
  return bad

instance : Shrinkable (Fin 6) := ⟨fun _ => []⟩

instance : Arbitrary (Fin 6) where
  arbitrary := do
    let n ← Gen.choose Nat 0 5 (by decide)
    pure ⟨n.val, by omega⟩

end StepFrameTests

end EVM

end EvmYul
