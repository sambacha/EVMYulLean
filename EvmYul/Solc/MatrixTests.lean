module

public import EvmYul.Solc.MatrixTestHarness
public meta import EvmYul.Solc.MatrixTestHarness
@[expose] public meta section

/-!
# Real solc output against the Yul model (`docs/SOLC_VYPER_PLAN.md`, Steps 3–4)

Every cell of `EvmYul/Solc/Fixtures.lean` is bytecode that a pinned solc binary emitted for a
program of `tools/solc/corpus/` (`--strict-assembly`; 0.8.13, 0.8.20, 0.8.21, 0.8.24, 0.8.26,
0.8.30 and the latest 0.8.37; optimizer off and on; plus the experimental SSA-CFG code generator of
the latest). `EvmYul/Solc/Corpus.lean` is the same source text read by the project's Yul parser.
This file runs the bytecode on `Θ`, the source on the Yul interpreter and on the Yul gas meter, and
checks the claims of conjecture K13 against what the compilers really emit. It is built by
`lake build EvmYulGasTests`; any failed check fails the build.

* **§0 Matrix and provenance.** The cells are exactly *lock file × corpus × columns*, read from
  `tools/solc/solc-matrix.lock` and `tools/solc/corpus/` at build time; binary and source hashes
  match (editing a program without regenerating fails the build, offline); the hex round-trips; the
  EVM target follows the lock file; the SSA-CFG column exists for the latest compiler only.
* **§1 Behaviour, three ways.** On every sweep point the compiled code (on `Θ`), the Yul interpreter
  and the Yul gas meter all produce the storage of the closed-form reference model.
* **§2 The floor laws (K14, K15) and the inlining refutation (R3).** With the storage remainder
  taken out, compiled gas is at least the model's gas on every sweep point of every unoptimized
  cell (K14), and of every optimized cell whose calls survive (K15). Where the optimizer inlines the
  call (`call_inline`), the compiled code is **cheaper** than the model on every point: the
  executable counterpart of the Lean theorem `inlining_breaks_floor`.
* **§3 Lowering families and per-construct overheads (K13(c), R1, R2).** The `if` lowering of every
  cell classifies into a known family (unknown shapes fail the build) and the version → family
  table is pinned. The measured `if` overheads (skip 22/14/13, taken 22/26/14 gas) are pinned per
  family; each is at least the model's branch price (L1), and the optimized skip path has a gap of
  only **2** over the price, which refutes the "gap ≥ 3" rule of `LoweringTests.floorHolds` (L3,
  kept as a regression witness). Loop iterations cost a constant amount per family. Golden gas.
* **§4 Preservation, executed.** `runF_costMono` on the corpus: random cost models `c ≤ c'` give
  the same result and no less gas; with the call price lowered (an inlining model) the inequality
  fails on call programs (canary).
* **§5 Property tests (counted).** Random 256-bit inputs; each property has a canary that must be
  refuted.
* **§6 Mutation tests.** A `JUMPI` turned into `JUMP`, swapped compiler versions, a model whose
  branch price exceeds the measured overhead, and a py-evm record off by one gas are each caught.
* **§7 Independent EVM.** Every run recorded on py-evm when the fixtures were generated agrees with
  `Θ` exactly: success, execution gas, storage slots 0 and 1.
-/

namespace EvmYul.Solc.MatrixTests

open EvmYul.Solc EvmYul.Yul Gas Plausible Plausible.Decorations GasConstants
open EvmYul.Testing.EvmFixtures
open EvmYul.Vyper (hexOf Run)

/-- All checks; throws on the first failing section. -/
def runAll : IO Unit := do
  -- §0 Matrix and provenance
  let lock ← readLock
  let corpus ← readCorpus
  let expected := lock.flatMap fun (v, _, _, extra) => corpus.flatMap fun (k, _) =>
    [(v, false, Codegen.legacy, k), (v, true, Codegen.legacy, k)] ++
    (if extra == "ssa" then [(v, false, Codegen.ssaCfg, k)] else [])
  let actual := fixtures.map fun c => (c.solc, c.optimize, c.codegen, c.program)
  failIf "§0 matrix" <|
    (expected.filter (!actual.contains ·)).map (fun e => s!"missing cell {repr e}") ++
    (actual.filter (!expected.contains ·)).map (fun e => s!"cell not in lock × corpus {repr e}") ++
    (if actual.length == actual.eraseDups.length then [] else ["duplicate cells"]) ++
    (if lock.getLast?.map (·.1) == some pinnedLatest then [] else
      ["pinnedLatest is not the last lock entry"]) ++
    (if lock.map (·.1) == pinnedVersions then [] else ["pinnedVersions differs from the lock"]) ++
    (if corpus.map (·.1) |>.all corpusNames.contains then [] else
      ["a corpus file has no parsed program in Corpus.lean (rerun the generator)"]) ++
    (if corpusNames.length == corpus.length then [] else ["Corpus.lean lists a removed program"])
  failIf "§0 provenance" <| fixtures.flatMap fun c =>
    (match lock.find? (·.1 == c.solc) with
     | some (_, sha, evm, _) =>
       (if sha == c.binarySha256 then [] else [s!"{c.name}: binary sha256 differs from the lock"]) ++
       (if evm == c.evmVersion then [] else [s!"{c.name}: EVM target differs from the lock"])
     | none => [s!"{c.name}: compiler not in the lock file"]) ++
    (if corpus.lookup c.program == some c.sourceSha256 then [] else
      [s!"{c.name}: compiled from a different source than tools/solc/corpus/{c.program}.yul \
        (rerun the generator)"]) ++
    (if corpusSha256.lookup c.program == some c.sourceSha256 then [] else
      [s!"{c.name}: source hash differs from the generated corpus table"]) ++
    (match c.code? with
     | some b => if hexOf b == c.runtimeHex then [] else [s!"{c.name}: hex does not round-trip"]
     | none => [s!"{c.name}: bytecode hex does not decode"]) ++
    (if c.codegen == .ssaCfg && c.solc != pinnedLatest then
      [s!"{c.name}: SSA-CFG column on a compiler other than the latest"] else [])
  IO.println s!"§0 matrix: {fixtures.length} cells = {lock.length} pinned solc × {corpus.length} \
    corpus programs × (optimizer off/on) + SSA-CFG on {pinnedLatest}; binary and source hashes, \
    EVM targets and hex round trip checked on every cell"
  -- §1 Behaviour, three ways
  let mut points := 0
  for c in fixtures do
    failIf s!"§1 behaviour {c.name}" ((sweep c.program).filterMap (behaviourDiff c))
    points := points + (sweep c.program).length
  IO.println s!"§1 behaviour: {points} runs; on each, the compiled code on Θ, the Yul interpreter \
    and the Yul gas meter (all on the parsed source) leave exactly the reference storage"
  -- §2 Floor laws K14 / K15 and the inlining refutation R3
  let mut k14 := 0
  let mut k15 := 0
  let mut minGap : Option ℤ := none
  for c in fixtures do
    let gs := gapsWith cancunFn c
    if floorApplies c then
      failIf s!"§2 floor law {c.name}" <| gs.filterMap fun (a, g) =>
        match g with
        | some g => if 0 ≤ g then none else some s!"{a}: compiled gas below the model by {-g}"
        | none => some s!"{a}: no gap (run failed)"
      if c.optimize then k15 := k15 + gs.length else k14 := k14 + gs.length
      for (_, g) in gs do
        if let some g := g then minGap := some (min g (minGap.getD g))
    else
      failIf s!"§2 R3 inlining witness {c.name}" <| gs.filterMap fun (a, g) =>
        match g with
        | some g => if g < 0 then none else some s!"{a}: expected the inlined code to undercut \
            the model, gap {g}"
        | none => some s!"{a}: no gap (run failed)"
  let inl := (cellsOf "call_inline").filter (·.optimize)
  failIf "§2 R3: the optimizer inlines call_inline in every optimized cell" <|
    inl.filterMap fun c => if (c.code?.map callSurvives) == some false then none else some c.name
  let inlGaps := inl.map fun c => ((gapsWith cancunFn c).head?.bind (·.2))
  IO.println s!"§2 K14: {k14} sweep points of unoptimized cells, K15: {k15} of optimized cells \
    whose calls survive; compiled gas − storage remainder ≥ model gas on all (smallest gap \
    {minGap}). R3: on all {inl.length} optimized call_inline cells the call is inlined and the \
    compiled code undercuts the model (gaps {inlGaps.eraseDups}); Lean: inlining_breaks_floor"
  -- §3 Families and per-construct overheads
  let ifCells := fixtures.filter fun c => c.program == "if_const" || c.program == "if_store"
  failIf "§3 classification" <| ifCells.filterMap fun c =>
    match c.code?.bind classifyIf, familyTable.lookup (c.solc, c.optimize, c.codegen) with
    | some f, some f' => if f == f' then none else
        some s!"{c.name}: family {repr f}, pinned {repr f'}"
    | none, _ => some s!"{c.name}: unknown if-lowering shape (a new compiler form; classify it)"
    | _, none => some s!"{c.name}: no pinned family"
  let consts := cellsOf "if_const"
  failIf "§3 if overheads" <| consts.filterMap fun c =>
    match c.code?.bind classifyIf with
    | some f =>
      let (sk, tk) := overheadTable f
      if skipOverhead c == some sk && takenOverhead c == some tk then none
      else some s!"{c.name}: overheads skip {skipOverhead c}, taken {takenOverhead c}; pinned \
        {sk}, {tk} for {repr f}"
    | none => some s!"{c.name}: unclassified"
  -- L1: every measured if overhead is at least the model's branch price.
  failIf "§3 L1 floor" <| consts.filterMap fun c =>
    if (skipOverhead c).any (cancun.branch ≤ ·) && (takenOverhead c).any (cancun.branch ≤ ·)
    then none else some c.name
  -- L3: the smallest gap over the branch price is 2 (optimized skip): the "gap ≥ 3" rule fails.
  let skipGaps := consts.filterMap fun c => (skipOverhead c).map (· - cancun.branch)
  unless skipGaps.min? == some 2 do
    throw <| IO.userError s!"§3 L3: smallest if-skip gap over the branch price is {skipGaps.min?}, \
      expected 2 (R2)"
  unless consts.any (fun c => c.optimize && skipOverhead c == some 13) do
    throw <| IO.userError "§3 L3: the optimized 13-gas skip path (R2) is gone"
  IO.println s!"§3 families: {ifCells.length} if-cells classified (≤0.8.20 noopt: inline+ISZERO, \
    ≥0.8.21 noopt and SSA-CFG: out of line, optimized: duplicated STOP); if overheads skip/taken \
    22/22, 14/26, 13/14 per family, all ≥ the model's branch price {cancun.branch} (L1); smallest \
    gap 2 on the optimized skip path, so the 'gap ≥ 3' rule of LoweringTests.floorHolds is refuted \
    (L3, R2)"
  -- Loops: constant cost per iteration, pinned per column, above the model's.
  failIf "§3 loop iterations" <| (cellsOf "for_sum").filterMap fun c =>
    let steps := (List.range 18).map fun n => do
      let a ← c.run? [n + 2]
      let b ← c.run? [n + 1]
      pure (a.gasUsed - b.gasUsed)
    match iterTable.lookup (c.solc, c.optimize, c.codegen) with
    | some k =>
      if steps.all (· == some k) && iterGas c == some k && modelIter < k then none
      else some s!"{c.name}: iteration gas {steps.eraseDups}, pinned {k}, model {modelIter}"
    | none => some s!"{c.name}: no pinned iteration gas"
  failIf "§3 golden gas" <| fixtures.filterMap fun c =>
    match golden.lookup (cellKey c) with
    | some g => if (c.run? (probe c.program)).map (·.gasUsed) == some g then none
        else some s!"{c.name}: gas {(c.run? (probe c.program)).map (·.gasUsed)}, golden {g}"
    | none => none
  -- Provenance (TESTING.md D1): every pinned number above equals the same quantity computed from
  -- the py-evm records, an EVM independent of this project, so no pinned value rests on `Θ` alone;
  -- and the specified fresh-`SSTORE` price the overheads subtract is what `Θ` charges.
  failIf "§3 provenance: golden = py-evm at the probe" <| fixtures.filterMap fun c =>
    match golden.lookup (cellKey c) with
    | some g => if oracleGasAt c (probe c.program) == some g then none
        else some s!"{c.name}: py-evm {oracleGasAt c (probe c.program)} at \
          {probe c.program}, golden {g}"
    | none => none
  failIf "§3 provenance: if overheads from py-evm" <| consts.filterMap fun c =>
    match c.code?.bind classifyIf with
    | some f =>
      let (sk, tk) := overheadTable f
      if skipOverheadWith (oracleGasAt c) c == some sk &&
          takenOverheadWith (oracleGasAt c) c == some tk
      then none else some s!"{c.name}: py-evm overheads differ from the pinned {sk}, {tk}"
    | none => some s!"{c.name}: unclassified"
  failIf "§3 provenance: iteration gas from py-evm" <| (cellsOf "for_sum").filterMap fun c =>
    if iterGasWith (oracleGasAt c) == iterTable.lookup (c.solc, c.optimize, c.codegen) then none
    else some s!"{c.name}: py-evm iteration gas {iterGasWith (oracleGasAt c)}"
  unless sstoreFreshGas? == some sstoreFreshSpec do
    throw <| IO.userError s!"§3 Θ charges {sstoreFreshGas?} for a fresh nonzero SSTORE, the EIPs \
      {sstoreFreshSpec}"
  IO.println s!"§3 provenance: every golden value, if overhead and iteration gas equals the same \
    quantity on the py-evm records; Θ's fresh nonzero SSTORE = G_coldsload + G_sset = \
    {sstoreFreshSpec}"
  IO.println s!"§3 loops: for_sum costs a constant 65/59 (≤0.8.20), 62/59 (≥0.8.21), 53 (SSA-CFG) \
    gas per iteration on every trip count 1 … 19, against the model's {modelIter}; \
    {(fixtures.filter fun c => (golden.lookup (cellKey c)).isSome).length} golden gas values match"
  -- §4 Preservation, executed (random increments; `above_le` proves `cancunFn ≤ above …`)
  matrixHolds "runF_costMono on the corpus: c ≤ c' gives the same storage and no less gas"
    60 (∀ di db dc k : ℕ, ∀ x : UInt256,
      let m' := above (di % 50) (db % 50) (dc % 50)
      corpusNames.all fun p =>
        monoAt cancunFn m' p (if p == "call_inline" then [x.toNat, k] else
          if p == "if_store" || p == "if_const" then [x.toNat] else [k % 12]))
  expectRefuted "canary: an inlining model (call price 0) is above cancunFn on call programs"
    (∀ k : ℕ, monoAt cancunFn (inlined cancunFn) "call_rec" [k % 12])
  IO.println "§4 preservation: runF_costMono executed on all corpus programs with random price \
    increments; the inlining model breaks it (canary)"
  -- §5 Property tests
  matrixHolds "if_store: every cell stores x on Θ, as the Yul interpreter does (random 256-bit x)"
    150 (∀ x : UInt256, (cellsOf "if_store").all fun c => (behaviourDiff c [x.toNat]).isNone)
  expectRefuted "canary: if_store stores x + 1"
    (∀ x : UInt256, (cellsOf "if_store").all fun c =>
      (c.run? [x.toNat]).any fun r => r.slot 0 == (x.toNat + 1) % W)
  matrixHolds "if_store: gas does not depend on x ≠ 0 (random 256-bit x, every cell)"
    150 (∀ x : UInt256, x.toNat ≠ 0 → (cellsOf "if_store").all fun c =>
      ((c.run? [x.toNat]).map (·.gasUsed)) == ((c.run? [1]).map (·.gasUsed)))
  expectRefuted "canary: if_store gas does not depend on x at all (x = 0 skips the store)"
    (∀ x : UInt256, (cellsOf "if_store").all fun c =>
      ((c.run? [x.toNat % 2]).map (·.gasUsed)) == ((c.run? [1]).map (·.gasUsed)))
  matrixHolds "call_inline: three-way agreement on random 256-bit a, b"
    150 (∀ a b : UInt256, (cellsOf "call_inline").all fun c =>
      (behaviourDiff c [a.toNat, b.toNat]).isNone)
  expectRefuted "canary: call_inline computes a + a² + 1 without wrapping"
    (∀ a : UInt256, (cellsOf "call_inline").all fun c =>
      (c.run? [a.toNat, 0]).any fun r => r.slot 0 == a.toNat + a.toNat * a.toNat + 1)
  matrixHolds "loops and recursion: three-way agreement and the floor law (random n ≤ 15)"
    40 (∀ n : ℕ, ["for_sum", "call_rec", "nested_call"].all fun p => (cellsOf p).all fun c =>
      (behaviourDiff c [n % 16]).isNone &&
      (!floorApplies c || match corpusContract p with
        | some q => (gap? c q [n % 16]).any (0 ≤ ·)
        | none => false))
  -- §6 Mutation tests
  let mut killed := 0
  -- (a) JUMPI → JUMP in every if-cell: classification or behaviour must catch it.
  for c in ifCells do
    let some hex' := replaceFirst c.runtimeHex "57" "56" | throw <| IO.userError s!"{c.name}: no 57"
    let c' := { c with runtimeHex := hex' }
    let caught := (c'.code?.bind classifyIf) != familyTable.lookup (c.solc, c.optimize, c.codegen)
      || boundary.any fun x => (behaviourDiff c' [x]).isSome
    unless caught do throw <| IO.userError s!"§6 mutant survived: JUMPI→JUMP in {c.name}"
    killed := killed + 1
  -- (b) Swapped versions: the golden table must catch the relabelled cells.
  for (v, v') in [("0.8.20", "0.8.21"), ("0.8.13", "0.8.37")] do
    let swapped := fixtures.filter (fun c => c.solc == v && !c.optimize && c.codegen == .legacy)
      |>.map fun c => { c with solc := v' }
    let caught := swapped.any fun c =>
      (golden.lookup (cellKey c)).any (fun g => (c.run? (probe c.program)).map (·.gasUsed) != some g)
      || ((c.program == "if_const" || c.program == "if_store") &&
          (c.code?.bind classifyIf) != familyTable.lookup (c.solc, c.optimize, c.codegen))
    unless caught do throw <| IO.userError s!"§6 mutant survived: {v} cells relabelled {v'}"
    killed := killed + 1
  -- (c) A model whose branch price exceeds the measured overhead violates K14 somewhere.
  let tooDear : FnCostModel := { cancunFn with branch := 40 }
  unless fixtures.any (fun c => floorApplies c &&
      (gapsWith tooDear c).any fun (_, g) => g.any (· < 0)) do
    throw <| IO.userError "§6 mutant survived: a 40-gas branch price passes the floor law"
  killed := killed + 1
  -- (d) A py-evm record off by one gas is detected.
  for c in fixtures.take 6 do
    let some code := c.code? | throw <| IO.userError s!"{c.name}: bad hex"
    let some p := c.oracle.head? | throw <| IO.userError s!"{c.name}: no oracle point"
    unless (oracleDiff code c { p with gasUsed := p.gasUsed + 1 }).isSome do
      throw <| IO.userError s!"§6 mutant survived: py-evm gas + 1 on {c.name}"
    killed := killed + 1
  IO.println s!"§6 mutation: {killed} mutants killed (JUMPI→JUMP in every if-cell, swapped \
    versions, a too-dear branch price, py-evm records off by one), 0 survived"
  -- §7 Independent EVM
  let mut agree := 0
  for c in fixtures do
    let some code := c.code? | throw <| IO.userError s!"{c.name}: bad hex"
    failIf s!"§7 py-evm {c.name}" (c.oracle.filterMap (oracleDiff code c))
    agree := agree + c.oracle.length
  IO.println s!"§7 independent EVM: Θ and py-evm agree exactly (success, execution gas, storage \
    slots 0 and 1) on all {agree} recorded runs of the {fixtures.length} cells"

#eval runAll

end EvmYul.Solc.MatrixTests
