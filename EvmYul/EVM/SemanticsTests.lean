module

public import EvmYul.EVM.Semantics
public meta import EvmYul.EVM.Semantics
public import EvmYul.Testing.EvmFixtures
public meta import EvmYul.Testing.EvmFixtures
@[expose] public meta section

/-!
# Executable regression tests for review findings O-1, O-2 and O-4

These run **during `lake build EvmYulGasTests`**. That is possible only because padding is now pure
Lean (`ByteArray.zeroesPure`, O-4): before, any path through `ByteArray.readWithPadding` called the
FFI primitive `memset_zero`, which the elaborator cannot execute, so interpreter tests needed a
separate executable. The paths exercised here (identity precompile, `call` into it, CREATE/CREATE2
with no fuel left for `Lambda`, SELFDESTRUCT) touch no other FFI or Python helper.

1. **Unit tests** (named checks, each must be `true`), including the end-to-end EIP-6780 scenario
   from the review: a contract created in this transaction calls precompile `0x04` and then
   SELFDESTRUCTs; it must land in the self-destruct set.
2. **Property tests** (Plausible, 300 random inputs, fixed seed), mirroring
   `Θ_precompile_preserves_createdAccounts`, `call_precompile_preserves_createdAccounts` and
   `create_outOfFuel_propagates` / `create2_outOfFuel_propagates`.
3. **Mutation tests**: each property is re-run against a re-implementation of the *old* behaviour
   (precompile result set replaced by `∅`; CREATE's `OutOfFuel` replaced by an empty world state),
   and Plausible must find a counterexample. This shows the properties can detect the bugs they
   guard against, i.e. they are not vacuous.
-/

namespace EvmYul.EVM.SemanticsTests

open Batteries Plausible EvmYul.Testing.EvmFixtures

/-- A created-accounts set from a list of small address numbers. -/
def mkSet (xs : List ℕ) : Std.TreeSet AccountAddress compare :=
  Std.TreeSet.ofList (xs.map (Fin.ofNat _)) compare

/-- Set equality, by sorted contents. -/
def sameSet (a b : Std.TreeSet AccountAddress compare) : Bool := a.toList == b.toList

/-- Run `Θ` on the identity precompile with created-accounts set `cA`, input bytes `bs` and gas `g`;
returns the created-accounts set of the result, if any. -/
def thetaId (cA : Std.TreeSet AccountAddress compare) (bs : List ℕ) (g : ℕ) :
    Option (Std.TreeSet AccountAddress compare) :=
  match Θ 3 [] cA default default ∅ ∅ default 1 1 4 (.Precompiled 4) (u g) (u 1) (u 0) (u 0)
      ⟨(bs.map (·.toUInt8)).toArray⟩ 0 default true with
  | .ok r => some r.createdAccounts
  | .error _ => none

/-- Outcome of the same identity-precompile call (O-3, `FrameOutcome`). -/
def thetaIdOutcome (bs : List ℕ) (g : ℕ) : Option FrameOutcome :=
  match Θ 3 [] ∅ default default ∅ ∅ default 1 1 4 (.Precompiled 4) (u g) (u 1) (u 0) (u 0)
      ⟨(bs.map (·.toUInt8)).toArray⟩ 0 default true with
  | .ok r => some r.outcome
  | .error _ => none

/-- Mutant for O-3: rebuilding an outcome from the old `Bool` flag by the tempting rule
"`false` means revert" (the old tuple could not tell revert from exceptional halt). -/
def thetaIdOutcomeFromBool (bs : List ℕ) (g : ℕ) : Option FrameOutcome :=
  (thetaIdOutcome bs g).map fun o => if o.isSuccess then .success else .revert

/-- A state that runs CALL to the identity precompile: owner balance `bal`, gas `g`, value `val`,
input `inSize` bytes of memory, created-accounts set `cA`. -/
def callIdState (cA : Std.TreeSet AccountAddress compare) (bal val inSize g : ℕ) : EVM.State :=
  let s0 := withGas (withStack [u 5000, u 4, u val, u 0, u inSize, u 0, u 32]) g
  let acct : Account .EVM := { (default : Account .EVM) with balance := u bal }
  { s0 with accountMap := s0.accountMap.insert s0.executionEnv.codeOwner acct
            createdAccounts := cA }

/-- Created-accounts set after `EVM.step` executes that CALL (charge 0, fuel 10). -/
def callIdCreated (cA : Std.TreeSet AccountAddress compare) (bal val inSize g : ℕ) :
    Option (Std.TreeSet AccountAddress compare) :=
  match step 10 0 (some (.CALL, none)) (callIdState cA bal val inSize g) with
  | .ok s => some s.createdAccounts
  | .error _ => none

/-- A non-empty world state (the owner's account, with balance `bal`) whose stack is `stk`. -/
def createState (stk : List UInt256) (bal : ℕ) : EVM.State :=
  let s0 := withGas (withStack stk) 100000
  let acct : Account .EVM := { (default : Account .EVM) with balance := u bal }
  { s0 with accountMap := s0.accountMap.insert s0.executionEnv.codeOwner acct }

/-- Executable mirror of O-2's corrected behaviour: with fuel 1 (none left for `Lambda`) a CREATE
or CREATE2 either fails with an error, or (when `Lambda` is not reached) succeeds **without**
emptying the non-empty world state. The old code returned `.ok` with `accountMap = ∅`. -/
def noWipe : Except ExecutionException EVM.State → Bool
  | .ok s => !s.accountMap.isEmpty
  | .error _ => true

/-- CREATE (`k = false`) or CREATE2 (`k = true`) with endowment `v`, init code at memory `[off,
off + len)`, owner balance `bal`, run with fuel 1. -/
def createStep (k : Bool) (v off len bal : ℕ) : Except ExecutionException EVM.State :=
  let stk := if k then [u v, u off, u len, u 7] else [u v, u off, u len]
  step 1 0 (some (if k then .CREATE2 else .CREATE, none)) (createState stk bal)

/-- The **old** behaviour, re-implemented for the mutation tests: `OutOfFuel` from `Lambda` was
turned into a successful step with an empty world state. -/
def oldCreateCatchAll (s : EVM.State) : Except ExecutionException EVM.State →
    Except ExecutionException EVM.State
  | .error .OutOfFuel => .ok { s with accountMap := ∅ }
  | r => r

/-! ## 1. Unit tests -/

/-- Named unit checks; each must evaluate to `true`. -/
def unitChecks : List (String × Bool) :=
  [ ("Θ identity precompile with enough gas: outcome success",
      thetaIdOutcome [1, 2, 3] 100000 == some .success),
    ("Θ identity precompile out of gas: outcome exceptionalHalt (not revert)",
      thetaIdOutcome [1, 2, 3] 0 == some .exceptionalHalt),
    ("Θ identity precompile keeps {0x77}",
      (thetaId (mkSet [0x77]) [1, 2, 3] 100000).any (sameSet · (mkSet [0x77]))),
    ("Θ identity precompile keeps a 3-element set, even when out of gas",
      (thetaId (mkSet [5, 6, 7]) [1, 2, 3] 0).any (sameSet · (mkSet [5, 6, 7]))),
    ("CALL 0x04 keeps the caller's created-accounts set",
      (callIdCreated (mkSet [0x77, 0x78]) 10 0 3 100000).any (sameSet · (mkSet [0x77, 0x78]))),
    ("CALL 0x04 refused for lack of balance keeps the set",
      (callIdCreated (mkSet [0x77]) 0 5 3 100000).any (sameSet · (mkSet [0x77]))),
    ("CREATE with no fuel for Lambda is OutOfFuel",
      match createStep false 0 0 0 10 with
      | .error .OutOfFuel => true
      | _ => false),
    ("CREATE2 with no fuel for Lambda is OutOfFuel",
      match createStep true 0 0 0 10 with
      | .error .OutOfFuel => true
      | _ => false),
    ("CREATE whose endowment exceeds the balance does not reach Lambda: ok, world state kept",
      match createStep false 11 0 0 10 with
      | .ok s => !s.accountMap.isEmpty
      | .error _ => false),
    ("readWithPadding pads with zeroes (pure Lean)",
      (ByteArray.readWithPadding ⟨#[1, 2]⟩ 1 4).data == #[2, 0, 0, 0]),
    ("readWithPadding of length 0 is empty",
      (ByteArray.readWithPadding ⟨#[1, 2]⟩ 5 0).size == 0) ]

/-- End-to-end EIP-6780 scenario from the review (O-1): the code owner was created in this
transaction; it CALLs precompile `0x04` and then SELFDESTRUCTs. Returns whether the owner ends up in
the self-destruct set. `wipe = true` replays the **old** bug by emptying the created-accounts set
after the CALL, as the old precompile branch of `Θ` did. -/
def createCallSelfdestruct (wipe : Bool) : Bool :=
  let s := callIdState ∅ 10 0 3 100000
  let owner := s.executionEnv.codeOwner
  let s := { s with createdAccounts := mkSet [] |>.insert owner }
  match step 10 0 (some (.CALL, none)) s with
  | .error _ => false
  | .ok s₁ =>
    let s₁ := if wipe then { s₁ with createdAccounts := ∅ } else s₁
    match step 10 0 (some (.SELFDESTRUCT, none)) s₁ with
    | .error _ => false
    | .ok s₂ => s₂.substate.selfDestructSet.contains owner

/-! ## 2. Property and mutation tests -/

/-- Run every check; throws on the first failure. -/
def runAll : IO Unit := do
  for (name, ok) in unitChecks do
    unless ok do throw <| IO.userError s!"unit check failed: {name}"
  IO.println s!"{unitChecks.length} unit checks passed"
  unless createCallSelfdestruct false do
    throw <| IO.userError "CREATE → CALL 0x04 → SELFDESTRUCT: owner not in the self-destruct set"
  if createCallSelfdestruct true then
    throw <| IO.userError "scenario cannot detect the old bug (wiped set still self-destructs)"
  IO.println "EIP-6780 scenario: deleted after a precompile call; the old bug would keep it"
  -- O-1, `Θ` level (mirrors `Θ_precompile_preserves_createdAccounts` and `Θ_precompile_ok`).
  expectHolds "Θ identity precompile: succeeds and returns the incoming created-accounts set"
    (∀ xs bs : List ℕ, ∀ g : ℕ,
      ((thetaId (mkSet xs) bs (g % 2000)).any (sameSet · (mkSet xs))) = true)
  -- O-1, opcode level (mirrors `call_precompile_preserves_createdAccounts`).
  expectHolds "CALL 0x04: the caller's created-accounts set is unchanged"
    (∀ xs : List ℕ, ∀ bal val n g : ℕ,
      ((callIdCreated (mkSet xs) (bal % 3) (val % 3) (n % 64) (30000 + g)).any
        (sameSet · (mkSet xs))) = true)
  -- O-2 (mirrors `create_outOfFuel_propagates` / `create2_outOfFuel_propagates`).
  expectHolds "CREATE/CREATE2 with fuel 1 never empty a non-empty world state"
    (∀ k : Bool, ∀ v off len bal : ℕ,
      noWipe (createStep k (v % 4) (off % 100) (len % 100) (bal % 4)) = true)
  expectHolds "CREATE/CREATE2 reaching Lambda with fuel 1 report OutOfFuel"
    (∀ k : Bool, ∀ off len bal : ℕ,
      (match createStep k 0 (off % 100) (len % 100) (bal % 4) with
        | .error .OutOfFuel => true
        | _ => false) = true)
  -- O-3 (mirrors `Θ_precompile_outcome_ne_revert`).
  expectHolds "Θ identity precompile: the outcome is never revert"
    (∀ bs : List ℕ, ∀ g : ℕ, (thetaIdOutcome bs (g % 2000) != some .revert) = true)
  IO.println "5 property suites passed (300 inputs each)"
  -- Mutation tests: the same properties against the old behaviour.
  expectRefuted "mutant (old O-1): precompile returns ∅ as the created-accounts set"
    (∀ xs bs : List ℕ, ∀ g : ℕ,
      (((thetaId (mkSet xs) bs (g % 2000)).map fun _ => (∅ : Std.TreeSet AccountAddress compare)).any
        (sameSet · (mkSet xs))) = true)
  expectRefuted "mutant (O-3): outcome rebuilt from the old Bool, false read as revert"
    (∀ bs : List ℕ, ∀ g : ℕ, (thetaIdOutcomeFromBool bs (g % 2000) != some .revert) = true)
  expectRefuted "mutant (old O-2): OutOfFuel inside CREATE empties the world state"
    (∀ k : Bool, ∀ v off len bal : ℕ,
      noWipe (oldCreateCatchAll (createState [] 0)
        (createStep k (v % 4) (off % 100) (len % 100) (bal % 4))) = true)

#eval runAll

end EvmYul.EVM.SemanticsTests
