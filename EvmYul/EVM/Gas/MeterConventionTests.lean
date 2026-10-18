module

public import EvmYul.EVM.Gas.Laws
public meta import EvmYul.EVM.Gas.Laws
public import EvmYul.EVM.Gas.HaltOrder
public meta import EvmYul.EVM.Gas.HaltOrder
public import EvmYul.EVM.Gas.Atomicity
public meta import EvmYul.EVM.Gas.Atomicity
public import EvmYul.EVM.Gas.CallReadings
public meta import EvmYul.EVM.Gas.CallReadings
public import EvmYul.Testing.EvmFixtures
public meta import EvmYul.Testing.EvmFixtures
@[expose] public meta section

/-!
# Tests that apply the project testing conventions (`TESTING.md`) to the gas meter

Built by `lake build EvmYulGasTests`; every check runs during elaboration and any failure fails the
build. Each section names the guideline of `TESTING.md` it implements. All checks here are
**deterministic** (exhaustive sweeps over finite, boundary-heavy domains, or Plausible with the
fixed seed of `EvmFixtures.cfg`), so a failure is never a flake (E3).

The final section prints the suite's *detection surface* (G2): the coverage counts, the
mutation-adequacy score per module and the standing caveats.
-/

namespace EvmYul

namespace EVM

namespace MeterConventionTests

open GasConstants GasMeter Plausible Plausible.Decorations
open EvmYul.Testing.EvmFixtures

/-! ## Fixtures -/

/-- The test state: the given stack (top first), the given gas, an account for the owner, and a
non-static frame. -/
def mkState (xs : List UInt256) (g : UInt256) : EVM.State :=
  let s := withOwnerAccount { (withStack xs) with
    toMachineState := { (default : MachineState) with gasAvailable := g } }
  -- a non-static frame, so state-modifying opcodes reach their gas checks
  { s with executionEnv := { s.executionEnv with perm := true } }

/-- `2^256 − 1`, the largest gas value. -/
def maxU : UInt256 := u (UInt256.size - 1)

/-- Throw a build error unless `b`. -/
def check (name : String) (b : Bool) : IO Unit :=
  unless b do throw <| IO.userError s!"[{name}] FAILED"

/-- Operand count of `w` (0 for INVALID). -/
def arity (w : Operation .EVM) : ℕ := (δ w).getD 0

/-- Memory cost plus `C'` of `w` on stack `xs`, evaluated with the maximal gas (for the CALL
family `C'` depends on the gas; elsewhere it does not). -/
def chargeAt (w : Operation .EVM) (xs : List UInt256) (g : UInt256) : ℕ :=
  let s := mkState xs g
  let m := memoryExpansionCost s w
  m + C' { s with gasAvailable := s.gasAvailable - .ofNat m } w

/-! ## F1 + A2: exhaustive, boundary-heavy sweep of `exceptionalHalt`

Domain: every decoded opcode × stack lengths `{0, δ−1, δ, 17}` × stack values `{0, 1, 2^256−1}` ×
gas `{0, c−1, c, c+1, 2^256−1}` where `c` is the opcode's charge on that stack. The finite domain is
covered completely (F1), so no opcode-specific branch depends on random sampling (see B5 below:
Plausible's uniform opcode generator hits a *given* opcode in 300 draws only with probability
≈ 0.69). -/

/-- Outcome region of one sample. -/
inductive Region where
  | invalid | underflow | oog | ok | laterError
  deriving DecidableEq, Repr, Inhabited

/-- One sweep sample: opcode, stack, gas. -/
structure Sample where
  w : Operation .EVM
  xs : List UInt256
  g : UInt256

/-- The sweep domain. -/
def sweep : List Sample := Id.run do
  let mut out := []
  for w in decodedOps do
    let d := arity w
    for n in [0, d - 1, d, 17].eraseDups do
      for v in [u 0, u 1, maxU] do
        let xs := List.replicate n v
        -- the charge is only evaluated on operand-complete stacks (no defaulted reads)
        let c := if d ≤ n then chargeAt w xs maxU else 0
        let gs := [0, c - 1, c, c + 1, UInt256.size - 1].filter (· < UInt256.size)
        for g in gs.eraseDups do
          out := ⟨w, xs, u g⟩ :: out
  return out

/-- Independent (first-tier) oracle for the region, from `δ`, the stack length and the charge. -/
def expectedRegion (smp : Sample) : Option Region :=
  if δ smp.w = none then some .invalid
  else if smp.xs.length < arity smp.w then some .underflow
  else if smp.g.toNat < chargeAt smp.w smp.xs smp.g then some .oog
  else none -- `ok` or one of the later, operand-dependent checks

/-- The region `exceptionalHalt` actually lands in. -/
def actualRegion (smp : Sample) : Region :=
  match exceptionalHalt #[] smp.w (mkState smp.xs smp.g) with
  | .ok _ => .ok
  | .error .InvalidInstruction => .invalid
  | .error .StackUnderflow => .underflow
  | .error .OutOfGass =>
    if smp.g.toNat < chargeAt smp.w smp.xs smp.g then .oog else .laterError
  | .error _ => .laterError

/-- A sample passes iff it lands in the oracle's region and satisfies the shared `HaltLaw`. -/
def samplePasses (smp : Sample) : Bool :=
  decide (HaltLaw #[] smp.w (mkState smp.xs smp.g)) &&
    match expectedRegion smp with
    | some r => actualRegion smp == r
    | none => actualRegion smp == .ok || actualRegion smp == .laterError

/-- Interesting antecedent indices for the law "insufficient gas ⇒ `OutOfGass`" (A2): gas does not
cover the charge **and** a later check would also fire (here: JUMP/JUMPI to an invalid target, or
a static-mode / stack-overflow / initcode condition), so the law's priority claim is actually
exercised rather than holding because nothing else could fail. -/
def oogAndLaterWouldFire (smp : Sample) : Bool :=
  expectedRegion smp == some .oog &&
    (smp.w == .JUMP || (smp.w == .JUMPI && smp.xs.getD 1 (u 0) != u 0) ||
      (smp.w.isCreate && decide (smp.xs.getD 2 (u 0) > ⟨49152⟩)))

/-- Count of samples in each region, in the order invalid, underflow, oog, ok, laterError. -/
def regionCounts (ss : List Sample) : List ℕ :=
  [.invalid, .underflow, .oog, .ok, .laterError].map fun r =>
    (ss.filter fun smp => actualRegion smp == r).length

#eval show IO Unit from do
  let ss := sweep
  let bad := ss.filter (!samplePasses ·)
  check s!"F1 sweep: {bad.length} failing samples, first: {(bad.head?.map fun (smp : Sample) => smp.w.pretty)}"
    bad.isEmpty
  let cs := regionCounts ss
  let interesting := (ss.filter oogAndLaterWouldFire).length
  IO.println s!"F1/A2 exceptionalHalt sweep: total={ss.length} invalid={cs[0]!} underflow={cs[1]!} \
    oog={cs[2]!} ok={cs[3]!} laterError={cs[4]!} oog∧later-check-would-fire={interesting}"
  -- A2: every region is populated, and the priority law has interesting antecedent indices.
  check "A2: every outcome region is exercised" (cs.all (· > 0))
  check "A2: OOG-priority law has non-trivial antecedent indices" (interesting ≥ 10)

/-! ## A1: a ∀∃ law with a two-tier oracle

Law: *for every valid instruction with its operands present, there is an amount of gas with which
it does not run out of gas*, **unless** its charge is at least `2^256` or it is a CREATE whose
initcode exceeds the 49152-byte limit (which are out of gas for every gas value).

The universal part is the adversarial sweep above (it includes `2^256 − 1` operands, so it reaches
the states where no witness exists). The solver `solveGas` is deliberately simple and may be
incomplete; only the checker must be sound (`gasWitness_sound`). -/

/-- Second tier, the checker: with gas `g`, `exceptionalHalt` does not raise `OutOfGass`. -/
def gasWitnessOk (w : Operation .EVM) (xs : List UInt256) (g : UInt256) : Bool :=
  match exceptionalHalt #[] w (mkState xs g) with
  | .error .OutOfGass => false
  | _ => true

/-- Soundness of the checker (the only property the test relies on). -/
theorem gasWitness_sound {w : Operation .EVM} {xs : List UInt256} {g : UInt256}
    (h : gasWitnessOk w xs g = true) :
    ∃ g : UInt256, exceptionalHalt #[] w (mkState xs g) ≠ .error .OutOfGass := by
  refine ⟨g, fun he => ?_⟩
  simp [gasWitnessOk, he] at h

/-- First tier, the solver: try the charge, the SSTORE stipend floor and the maximum. -/
def solveGas (w : Operation .EVM) (xs : List UInt256) : Option UInt256 :=
  let c := chargeAt w xs maxU
  let cands := [c, max c (Gcallstipend + 1), UInt256.size - 1].filter (· < UInt256.size)
  (cands.map u).find? (gasWitnessOk w xs)

/-- The independent reason why no witness can exist. -/
def provablyUnpayable (w : Operation .EVM) (xs : List UInt256) : Bool :=
  decide (UInt256.size ≤ chargeAt w xs maxU) ||
    (w.isCreate && decide (xs.getD 2 (u 0) > ⟨49152⟩))

#eval show IO Unit from do
  let univ := sweep.filter fun (smp : Sample) =>
    decide (δ smp.w ≠ none) && decide (arity smp.w ≤ smp.xs.length)
  let univ := (univ.map fun (smp : Sample) => (smp.w, smp.xs)).eraseDups
  let solved := univ.filter fun (w, xs) => (solveGas w xs).isSome
  let unsolved := univ.filter fun (w, xs) => (solveGas w xs).isNone
  let unexplained := unsolved.filter fun (w, xs) => !provablyUnpayable w xs
  IO.println s!"A1 ∀∃ gas-witness law: universal={univ.length} solved={solved.length} \
    unsolved={unsolved.length} (all provably unpayable: {unexplained.isEmpty})"
  check "A1: every unsolved state is provably unpayable" unexplained.isEmpty
  -- Non-vacuity of the universal generator: it does reach states where ∃ fails.
  check "A1: the universal generator reaches unpayable states" (unsolved.length > 0)
  -- ... and the solver is not trivial: it needs the SSTORE stipend floor at least once.
  check "A1: solver uses the stipend floor (charge alone is not a witness for SSTORE)"
    (univ.any fun (w, xs) => w == Operation.SSTORE && !gasWitnessOk w xs (u (chargeAt w xs maxU)) &&
      (solveGas w xs).isSome)

/-! ## A4: conjunct liveness of `HaltLaw`

`HaltLaw` on success is `fit ∧ exact-deduction ∧ cost = C' s'`. For each conjunct we plant a mutant
of `exceptionalHalt` that violates it, on states chosen by a targeted generator (C1/B5), and require
that conjunct to be the **only** one that kills the mutant on at least one state: no conjunct is
implied by the other two on the sample. -/

/-- The three conjuncts of `HaltLaw` for a claimed successful result `(s', k)`. -/
def haltConjuncts (w : Operation .EVM) (s : EVM.State) (s' : EVM.State) (k : ℕ) : List Bool :=
  let m := memoryExpansionCost s w
  [decide (m + k ≤ s.gasAvailable.toNat),
   (deductPrechecked s'.gasAvailable k).toNat == s.gasAvailable.toNat - (m + k),
   k == C' s' w]

/-- Mutant 1: the `OutOfGass` guard after `C'` is removed. -/
def mutNoGuard (w : Operation .EVM) (s : EVM.State) : Option (EVM.State × ℕ) :=
  match exceptionalHalt #[] w s with
  | .error .OutOfGass =>
    let m := memoryExpansionCost s w
    if m ≤ s.gasAvailable.toNat then
      let s' := { s with gasAvailable := s.gasAvailable - .ofNat m }
      some (s', C' s' w)
    else none
  | _ => none

/-- Mutant 2: the memory cost is deducted twice. -/
def mutDoubleMem (w : Operation .EVM) (s : EVM.State) : Option (EVM.State × ℕ) :=
  match exceptionalHalt #[] w s with
  | .ok (s', k) =>
    some ({ s' with gasAvailable := s'.gasAvailable - .ofNat (memoryExpansionCost s w) }, k)
  | _ => none

/-- Mutant 3: `C'` is evaluated on the pre-memory state (the S4 / MO-4 alternative reading). -/
def mutPreMemCost (w : Operation .EVM) (s : EVM.State) : Option (EVM.State × ℕ) :=
  match exceptionalHalt #[] w s with
  | .ok (s', _) => some (s', C' s w)
  | _ => none

/-- Targeted generator: CALL-family states with a huge requested gas and gas just below / at /
above `C_extra` (where `C_GASCAP` switches branch and `C'` can exceed `2^256`), plus memory-touching
operations with real memory growth. -/
def targeted : List (Operation .EVM × List UInt256 × UInt256) := Id.run do
  let mut out := []
  for w in [Operation.CALL, .CALLCODE, .DELEGATECALL, .STATICCALL] do
    for req in [u 0, u 1, u 5000, maxU, u (UInt256.size - 2600)] do
      for g in [0, 99, 100, 2599, 2600, 2601, 9000, 12000, 40000, 1000000] do
        -- out-size 64 at offset 0 (stack positions differ by family) forces memory growth
        let xs := if w == .CALL || w == .CALLCODE then [req, u 0, u 0, u 0, u 0, u 0, u 64]
                  else [req, u 0, u 0, u 0, u 0, u 64]
        out := (w, xs, u g) :: (w, List.replicate 7 req |>.set 1 (u 0), u g) ::
          (w, req :: List.replicate 6 (u 0), u g) :: out
  for w in [Operation.MSTORE, .MLOAD, .KECCAK256, .CALLDATACOPY, .LOG1, .MCOPY] do
    for g in [0, 3, 6, 9, 12, 30, 40, 100] do
      out := (w, [u 0, u 64, u 64, u 0], u g) :: out
  return out

/-- For a mutant, the conjunct indices that are the *unique* killer on some targeted state. -/
def uniqueKillers (mutant : Operation .EVM → EVM.State → Option (EVM.State × ℕ)) : List ℕ :=
  (targeted.filterMap fun (w, xs, g) =>
    let s := mkState xs g
    match mutant w s with
    | some (s', k) =>
      let cs := haltConjuncts w s s' k
      match cs.findIdx? (!·), (cs.filter (!·)).length with
      | some i, 1 => some i
      | _, _ => none
    | none => none).eraseDups

#eval show IO Unit from do
  let k1 := uniqueKillers mutNoGuard
  let k2 := uniqueKillers mutDoubleMem
  let k3 := uniqueKillers mutPreMemCost
  let all := (k1 ++ k2 ++ k3).eraseDups
  IO.println s!"A4 HaltLaw conjunct liveness: unique killers noGuard={k1} doubleMem={k2} \
    preMemCost={k3}; targeted states={targeted.length}"
  check "A4: conjunct 0 (fit) is not implied by the others" (all.contains 0)
  check "A4: conjunct 1 (exact deduction) is not implied by the others" (all.contains 1)
  check "A4: conjunct 2 (cost = C' after memory) is not implied by the others" (all.contains 2)

-- The state on which only the `fit` conjunct kills the missing-guard mutant: a call whose
-- requested gas is `2^256 − 1` with `2599 < C_extra = 2600` gas left, so `C' = 2^256 + 2599` wraps
-- to `2599` under `ofNat` and the deduction *looks* exact. This is why the explicit fit test in
-- `HaltLaw` (and the `gasAvailable < cost₂` guard in `chargeAndCheck`) is load-bearing.
#guard
  let s := mkState [maxU, u 0, u 0, u 0, u 0, u 0] (u 2599)
  match mutNoGuard .STATICCALL s with
  | some (s', k) => haltConjuncts .STATICCALL s s' k == [false, true, true]
  | none => false

/-! ## B1: the `2^256` wall (the integer analogue of the floating-point threshold rule)

Gas is exact integer arithmetic, so B1's float neighbours become the neighbours of the `2^256`
wrap-around: the property is checked at `t − 1`, `t`, `t + 1` for each threshold `t`, never by an
offset that wraps back onto `t`. -/

#eval show IO Unit from do
  let size := UInt256.size
  for g in [u 0, u 1, maxU, u (size - 2)] do
    for c in [g.toNat, g.toNat + 1, size - 1, size, size + 1, 2 * size, 2 * size + g.toNat] do
      check s!"B1: ChargeLaw at g={g.toNat}, c={c}" (decide (ChargeLaw g c))
      -- `ofNat c` wraps for `c ≥ 2^256`; the charge must still fail.
      if size ≤ c then check s!"B1: no wrap-around charge at c={c}" (isOOG (chargeGas g c))
  -- the wrapped value really is small: an unguarded deduction would subtract almost nothing
  check "B1: ofNat (2^256 + 1) = 1" ((u (size + 1)).toNat == 1)

/-! ## C3: replay is a congruence (chunking, reordering, padding) on the full observable

`chargeAll` returns the full observable result (`Except` with the exact remaining gas). Checked
exhaustively on small cost lists; the theorems `chargeAll_append`, `chargeAll_perm`,
`chargeAll_append_zeros` prove the same laws for all inputs. -/

/-- All lists over `{0, 1, 2, 7}` of length at most 3. -/
def smallLists : List (List ℕ) :=
  [[]] ++ ([0, 1, 2, 7].map fun a => [a]) ++
  ([0, 1, 2, 7].flatMap fun a => [0, 1, 2, 7].map fun b => [a, b]) ++
  ([0, 1, 2, 7].flatMap fun a => [0, 1, 2, 7].flatMap fun b => [0, 1, 2, 7].map fun c => [a, b, c])

/-- Equality of two charge results on the full observable. -/
def sameResult (a b : Except ExecutionException UInt256) : Bool :=
  match a, b with
  | .ok x, .ok y => x == y
  | .error e, .error e' => e == e'
  | _, _ => false

#eval show IO Unit from do
  let gs := [u 0, u 1, u 3, u 9, u 20, maxU]
  let mut n := 0
  for g in gs do
    for xs in smallLists do
      for ys in smallLists do
        n := n + 1
        check "C3: chunking" (sameResult (chargeAll g (xs ++ ys)) ((chargeAll g xs).bind
          (chargeAll · ys)))
        check "C3: reordering" (sameResult (chargeAll g (xs ++ ys)) (chargeAll g (ys ++ xs)))
      check "C3: no-op padding" (sameResult (chargeAll g (xs ++ [0, 0])) (chargeAll g xs))
  IO.println s!"C3 replay congruences: {n} (g, xs, ys) triples, horizon (max run length) = 6"

example := @chargeAll_append
example := @chargeAll_perm
example := @chargeAll_append_zeros

/-! ## C4: the model rejects bad input instead of clamping it -/

-- Over-spending is *rejected* (error), not clamped to 0 gas.
#guard isOOG (chargeGas (u 5) 6)
#guard (match exceptionalHalt #[] .INVALID (mkState [] maxU) with
  | .error .InvalidInstruction => true | _ => false)
-- Too few operands is rejected even with unlimited gas.
#guard (match exceptionalHalt #[] .ADD (mkState [u 1] maxU) with
  | .error .StackUnderflow => true | _ => false)
-- Initcode above the EIP-3860 limit is rejected even with unlimited gas (not truncated).
#guard (match exceptionalHalt #[] .CREATE (mkState [u 0, u 0, u 49153] maxU) with
  | .error .OutOfGass => true | _ => false)
-- ... while the same CREATE at the limit is accepted (the rejection is not a blanket one).
#guard (match exceptionalHalt #[] .CREATE (mkState [u 0, u 0, u 49152] maxU) with
  | .ok _ => true | _ => false)
-- An unpriced cost (≥ 2^256) is rejected, not wrapped.
#guard isOOG (chargeGas maxU UInt256.size)

/-! ## D1: independent derivations (a second mathematical route to the same quantity) -/

/-- Intrinsic data cost counted by a different route: number of zero / non-zero bytes. -/
def dataCostByCount (data : List UInt8) : ℕ :=
  Gtxdatazero * (data.filter (· == 0)).length + Gtxdatanonzero * (data.filter (· != 0)).length

#eval show IO Unit from do
  for n in [0, 1, 2, 5, 31, 32, 33, 64, 100] do
    for pat in [fun _ => (0 : UInt8), fun _ => 1, fun i => if i % 3 == 0 then 0 else 0xff] do
      let data := (List.range n).map pat
      check s!"D1: intrinsic data cost, n={n}"
        (intrinsicGas (legacyTx (some default) data) == Gtransaction + dataCostByCount data)
  -- 63/64 rule: `n − ⌊n/64⌋` against `⌈63n/64⌉` (also proved: `L_eq_ceil`)
  for n in (List.range 300) ++ [UInt256.size - 1, UInt256.size] do
    check s!"D1: L {n}" (L n == (63 * n + 63) / 64)

example := L_eq_ceil

/-! ## D2: the `UInt256` ↔ `ℕ` Galois round trip, probed at the boundary -/

#eval show IO Unit from do
  let size := UInt256.size
  for n in [0, 1, size - 2, size - 1, size, size + 1, 2 * size - 1] do
    check s!"D2: toNat (ofNat {n}) ≤ {n}" (decide ((u n).toNat ≤ n))
    check s!"D2: exact iff below 2^256 ({n})" (((u n).toNat == n) == decide (n < size))
  for a in [u 0, u 1, maxU] do
    check "D2: ofNat ∘ toNat = id" (u a.toNat == a)

example := ofNat_toNat
example := toNat_ofNat_le

/-! ## D3: differential test against the previous version (golden corpus)

Expected outcomes recorded from the **pre-refactor** body (`exceptionalHaltLegacy`) for the
operand-complete region. Entries whose expectation changed on purpose carry `GOLDEN-CHANGE` with
the justification; any other change in behaviour fails here and must be reviewed. -/

/-- Golden outcome: `some (gasLeftAfterMemory, cost₂)` or `none` with the error tag. -/
def golden : List (Operation .EVM × List ℕ × ℕ × Option (ℕ × ℕ) × String) :=
  [ (.ADD, [1, 2], 10, some (10, 3), ""),
    (.ADD, [1, 2], 2, none, "OutOfGass"),
    (.MSTORE, [0, 5], 100, some (97, 3), ""),
    (.MSTORE, [0, 5], 6, some (3, 3), ""),
    (.MSTORE, [0, 5], 5, none, "OutOfGass"),
    (.MSTORE8, [31, 1], 7, some (4, 3), ""),
    (.KECCAK256, [0, 64], 1000, some (994, 42), ""),
    (.EXP, [2, 0], 10, some (10, 10), ""),
    (.EXP, [2, 256], 110, some (110, 110), ""),
    (.SLOAD, [5], 2100, some (2100, 2100), ""),
    (.SLOAD, [5], 2099, none, "OutOfGass"),
    (.BALANCE, [7], 2600, some (2600, 2600), ""),
    (.JUMP, [5], 7, none, "OutOfGass"),
    (.JUMP, [5], 8, none, "BadJumpDestination"),
    (.LOG2, [0, 32, 1, 2], 2000, some (1997, 1381), ""),
    (.CREATE, [0, 0, 49153], 1000000, none, "OutOfGass"),
    (.SSTORE, [1, 1], 2300, none, "OutOfGass"),
    (.SSTORE, [1, 1], 30000, some (30000, 22100), ""),
    -- GOLDEN-CHANGE (GasHaltOrder.lean): the legacy order said OutOfGass; operand errors now come
    -- first, as in EELS. Proved invisible to every caller (`exceptionalHalt_ok_iff_legacy`,
    -- `exceptionalHalt_ne_outOfFuel`).
    (.ADD, [], 2, none, "StackUnderflow") ]

/-- The tag of an error, as recorded in the corpus. -/
def tagName : ExecutionException → String
  | .OutOfGass => "OutOfGass"
  | .StackUnderflow => "StackUnderflow"
  | .BadJumpDestination => "BadJumpDestination"
  | .InvalidInstruction => "InvalidInstruction"
  | .StaticModeViolation => "StaticModeViolation"
  | _ => "other"

#eval show IO Unit from do
  for (w, xs, g, exp, tag) in golden do
    let got := match exceptionalHalt #[] w (mkState (xs.map u) (u g)) with
      | .ok (s', k) => (some (s'.gasAvailable.toNat, k), "")
      | .error e => (none, tagName e)
    check s!"D3 golden: {w.pretty} {xs} gas={g}: got {got.1} {got.2}" (got == (exp, tag))
  IO.println s!"D3 golden corpus: {golden.length} entries, 1 GOLDEN-CHANGE"

/-! ## E1: mutation adequacy per module (canary-mutant contract)

Planted mutants of the functions under test, each run against the *same* checkers the suite uses.
`MA = detected / planted` is reported per module; the build fails unless every module has `MA = 1`
or the undetected mutant is listed in `justifiedNeutral` with a reason. -/

/-- Checker for a deduction function, against the independent ℕ oracle, on boundary inputs. -/
def chargeChecker (impl : UInt256 → ℕ → Except ExecutionException UInt256) : Bool :=
  [u 0, u 1, u 2, u 100, maxU].all fun g =>
    [0, 1, 2, 3, 99, 100, 101, UInt256.size - 1, UInt256.size].all fun c =>
      match impl g c with
      | .ok g' => decide (c ≤ g.toNat) && g'.toNat == g.toNat - c
      | .error e => decide (g.toNat < c) && e == .OutOfGass

/-- Checker for the refund formula, against `g' + min(⌊(T_g − g')/5⌋, A_r)` computed in ℕ. -/
def refundChecker (impl : UInt256 → UInt256 → UInt256 → UInt256) : Bool :=
  [(100000, 0), (100000, 40000), (21000, 21000), (50, 0), (5, 1)].all fun (gl, gl') =>
    [0, 1, 4000, 100000].all fun r =>
      (impl (u gl) (u gl') (u r)).toNat == gl' + min ((gl - gl') / 5) r

/-- Checker for the 63/64 rule: `L n ≤ n`, `63 n ≤ 64 L n`, and the ceiling form. -/
def lChecker (impl : ℕ → ℕ) : Bool :=
  ((List.range 200) ++ [6400, 1000000]).all fun n =>
    decide (impl n ≤ n) && decide (63 * n ≤ 64 * impl n) && impl n == (63 * n + 63) / 64

/-- Checker for the memory cost: the YP closed form `3a + ⌊a²/512⌋` at boundary word counts. -/
def memChecker (impl : UInt256 → ℕ) : Bool :=
  [0, 1, 2, 22, 23, 32, 724, 725, 1024, 100000].all fun a =>
    impl (u a) == 3 * a + a * a / 512

/-- Checker for `exceptionalHalt`-like functions: the sweep oracle plus `HaltLaw`'s conjuncts. -/
def haltChecker (impl : Array UInt256 → Operation .EVM → EVM.State →
    Except ExecutionException (EVM.State × ℕ)) : Bool :=
  (sweep ++ targeted.map fun (w, xs, g) => (⟨w, xs, g⟩ : Sample)).all fun smp =>
    let s := mkState smp.xs smp.g
    match impl #[] smp.w s with
    | .ok (s', k) => (haltConjuncts smp.w s s' k).all id && (expectedRegion smp).isNone
    | .error e =>
      match expectedRegion smp with
      | some .invalid => e == ExecutionException.InvalidInstruction
      | some .underflow => e == ExecutionException.StackUnderflow
      | some .oog => e == ExecutionException.OutOfGass
      | _ => true

/-- Opcodes whose legacy charge reads no operand: a static fee group and no memory range. -/
def staticNoMemory (w : Operation .EVM) : Bool :=
  (feeGroup w).staticCost?.isSome &&
    !([Operation.MLOAD, .MSTORE, .MSTORE8, .RETURN, .REVERT].contains w)

/-- A mutant: name, module, and whether the suite's checker rejects it. -/
structure Mutant where
  name : String
  module : String
  detected : Bool

/-- The catalogue of planted mutants. -/
def mutants : List Mutant :=
  [ ⟨"chargeGas: guard `≤` (OOG at equality)", "GasMeter",
      !chargeChecker fun g c => if g.toNat ≤ c then .error .OutOfGass else .ok (g - .ofNat c)⟩,
    ⟨"chargeGas: no guard (raw subtraction)", "GasMeter",
      !chargeChecker fun g c => .ok (g - .ofNat c)⟩,
    ⟨"chargeGas: clamp to 0 instead of failing", "GasMeter",
      !chargeChecker fun g c => if g.toNat < c then .ok (u 0) else .ok (g - .ofNat c)⟩,
    ⟨"chargeGas: off by one", "GasMeter",
      !chargeChecker fun g c => if g.toNat < c then .error .OutOfGass else .ok (g - .ofNat (c + 1))⟩,
    ⟨"refundedGas: quotient 2 (pre-London)", "GasMeter",
      !refundChecker fun gl g' r => g' + min ((gl - g') / ⟨2⟩) r⟩,
    ⟨"refundedGas: max instead of min", "GasMeter",
      !refundChecker fun gl g' r => g' + max ((gl - g') / ⟨5⟩) r⟩,
    ⟨"L: all but one 32nd", "Gas", !lChecker fun n => n - n / 32⟩,
    ⟨"L: off by one", "Gas", !lChecker fun n => n - n / 64 - 1⟩,
    ⟨"Cₘ: no quadratic term", "Gas", !memChecker fun a => 3 * a.toNat⟩,
    ⟨"Cₘ: quadratic divisor 256", "Gas", !memChecker fun a => 3 * a.toNat + a.toNat ^ 2 / 256⟩,
    ⟨"exceptionalHalt: no OOG guard after C'", "Semantics",
      !haltChecker fun vj w s => match mutNoGuard w s with
        | some r => .ok r | none => exceptionalHalt vj w s⟩,
    ⟨"exceptionalHalt: memory cost deducted twice", "Semantics",
      !haltChecker fun vj w s => match mutDoubleMem w s with
        | some r => .ok r | none => exceptionalHalt vj w s⟩,
    ⟨"exceptionalHalt: C' on the pre-memory state", "Semantics",
      !haltChecker fun vj w s => match mutPreMemCost w s with
        | some r => .ok r | none => exceptionalHalt vj w s⟩,
    ⟨"exceptionalHalt: legacy order (gas before operands)", "Semantics",
      !haltChecker fun vj w s =>
        -- the legacy body is only run where it cannot read missing operands: everywhere on
        -- operand-complete stacks, and on short stacks for statically priced, memory-free opcodes
        if s.stack.length < arity w ∧ !(staticNoMemory w) then exceptionalHalt vj w s
        else exceptionalHaltLegacy vj w s⟩,
    -- order-2 spot check (E1 conjecture): two faults that might mask each other
    ⟨"order-2: guard `≤` + subtract c−1", "GasMeter",
      !chargeChecker fun g c =>
        if g.toNat ≤ c then .error .OutOfGass else .ok (g - .ofNat (c - 1))⟩ ]

/-- Undetected mutants that are semantically neutral, with the reason (none at present). -/
def justifiedNeutral : List (String × String) := []

#eval show IO Unit from do
  let mods := (mutants.map fun (m : Mutant) => m.module).eraseDups
  let mut lines := #[]
  for m in mods do
    let ms := mutants.filter fun (x : Mutant) => x.module == m
    let d := (ms.filter fun (x : Mutant) => x.detected).length
    lines := lines.push s!"{m}: MA = {d}/{ms.length}"
  IO.println s!"E1 mutation adequacy per module: {String.intercalate ", " lines.toList}"
  for m in mutants do
    unless m.detected || justifiedNeutral.any (·.1 == m.name) do
      throw <| IO.userError s!"E1: undetected, unjustified mutant [{m.module}] {m.name}"

/-! ## E2 / E3: shrinking keeps preconditions; randomized tests are reproducible -/

/-- Run a property with the suite's fixed-seed configuration; the counterexample, if any. -/
def counterexample (p : Prop) (p' : Decorations.DecorationsOf p := by mk_decorations)
    [Testable p'] : IO (Option (List String)) := do
  match ← Testable.checkIO p' cfg with
  | .failure _ xs _ => pure (some xs)
  | _ => pure none

#eval show IO Unit from do
  -- E2: the (shrunk) counterexample of a guarded property still satisfies its guard. Plausible
  -- records a satisfied guard as `guard: …`; a shrink step through the precondition would be
  -- discarded, never reported.
  let some xs ← counterexample
      (∀ g m e q : ℕ, g < m + e → CallReadings.modelCallCharge g m e q = some q)
    | throw <| IO.userError "E2: expected a counterexample"
  check s!"E2: shrunk counterexample keeps its precondition: {xs}"
    (xs.any fun x => x.startsWith "guard:")
  -- E3: same seed, same verdict, same counterexample (no flaky randomized test).
  let ys ← counterexample
      (∀ g m e q : ℕ, g < m + e → CallReadings.modelCallCharge g m e q = some q)
  check "E3: randomized test is reproducible" (ys == some xs)

/-! ## F2: lawfulness of the monad the meter runs in, tested through the interpreter -/

example : LawfulMonad (Except ExecutionException) := inferInstance

#eval show IO Unit from do
  -- associativity with a branching continuation (reads the remaining gas, then charges)
  let f (g : UInt256) := chargeGas g 3
  let k (g : UInt256) := if g.toNat % 2 == 0 then chargeGas g 1 else chargeGas g 2
  for g in [u 0, u 2, u 3, u 4, u 5, u 6, maxU] do
    check "F2: associativity" (sameResult ((chargeGas g 1 >>= f) >>= k)
      (chargeGas g 1 >>= fun x => f x >>= k))
    check "F2: left identity" (sameResult (pure g >>= f) (f g))
    check "F2: right identity" (sameResult (chargeGas g 1 >>= pure) (chargeGas g 1))

/-! ## F3: the tested statement is the proved statement

`ChargeLaw` and `HaltLaw` are single definitions: `chargeLaw_holds` / `haltLaw_holds` prove them,
and the checks below (and the F1 sweep, which uses `HaltLaw`) decide the very same propositions. -/

example := chargeLaw_holds
example := haltLaw_holds

#eval check "F3: ChargeLaw decided on boundary inputs"
  ([u 0, u 1, maxU].all fun g => [0, 1, UInt256.size - 1, UInt256.size].all fun c =>
    decide (ChargeLaw g c))

/-! ## B5: computed detection probabilities for the randomized tests -/

/-- Probability that `n` independent draws hit an event of probability `p` at least once. -/
def hitProb (p : ℚ) (n : ℕ) : ℚ := 1 - (1 - p) ^ n

#eval show IO Unit from do
  let n := cfg.numInst
  -- a CALL-family opcode (4 of 256 bytes) under the uniform `AnyOp` generator
  let pCall := hitProb (4 / 256) n
  -- one *specific* opcode (1 of 256 bytes)
  let pOne := hitProb (1 / 256) n
  check "B5: CALL family hit with probability ≥ 0.99 in one run" (pCall ≥ 99 / 100)
  check "B5: a specific opcode is a coin flip under Plausible (hence the exhaustive sweep)"
    (pOne < 3 / 4)
  IO.println s!"B5 detection budget (n = {n}): P[hit CALL family] ≈ {(pCall * 1000).floor}/1000, \
    P[hit a given opcode] ≈ {(pOne * 1000).floor}/1000 ⇒ per-opcode branches are covered by the \
    F1 sweep, not by sampling"

/-! ## G2: detection surface

Printed on every build. Standing caveat (D1 conjecture / closing remark of `TESTING.md`): every
check above is internal to the model's specification. Agreement with the external world is only
established by the `ethereum/tests` conformance run (`lake exe conform`, CI `conformance` job). -/

#eval IO.println "G2 detection surface: see the F1/A2, A1, A4, C3, D3, E1 and B5 lines above; the \
  audit of axioms and the lints are in GasAxioms / GasLint. CAVEAT: all checks are relative to the \
  specification; the specification itself is validated only by the external conformance corpus."

end MeterConventionTests

end EVM

end EvmYul
