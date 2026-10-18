module

public import EvmYul.FFI.Primitives
public meta import EvmYul.FFI.Primitives
public import EvmYul.Venom.ThetaTestHarness
public meta import EvmYul.Venom.ThetaTestHarness
public import EvmYul.Venom.LoweringCheckTestHarness
public meta import EvmYul.Venom.LoweringCheckTestHarness
public import EvmYul.Testing.Counted
public meta import EvmYul.Testing.Counted
public import Plausible
public meta import Plausible

@[expose] public meta section

/-!
# Venom fragment on `Θ`: differential, real-compiler and mutation tests

`compile_correct` proves that the compiled `Asm` code behaves exactly like the Venom semantics, gas
included, for every interpretation of the primitive effects. What it does **not** cover is checked
here, on the project's EVM `Θ` (this module is an FFI test root, so `Θ` runs during the build):

1. **§1 Real Vyper output (Step 3 falsification).** The two straight-line paths of `store.vy` that
   `vyper 0.4.3 -f bb_runtime --experimental-codegen` prints (`set` and `bump`, recorded in
   `docs/VENOM_PLAN.md` §3) are written in the fragment, with literals inlined and the `djmp`
   selector dispatch replaced by the bucket's own selector `assert`. Compiled by this compiler they
   agree with the **real Vyper 0.4.3 Venom bytecode** of the fixture cell on outcome and storage, for
   boundary arguments, initial storage, call value, a foreign selector and truncated call data.
2. **§2 Differential property (counted).** Random programs of the fragment (every pure operation,
   all effects, `assert`, the three terminators; literals biased to 256-bit boundaries; memory
   offsets up to 2048 so the quadratic memory cost matters): the assembled code on `Θ` agrees with
   the Venom semantics over the reference model on outcome, output bytes, storage slots `0…7`
   and **gas exactly**, storage gas included (EIP-2929 cold/warm slots, EIP-2200 `SSTORE` from the
   original value). The outcome mix and the share of programs that touch storage, and that touch a
   slot twice (the warm path), are printed (A2).
3. **§3 Per-operation route (D1).** Each pure operation, defined on ℕ in `Syntax.lean`, against the
   interpreter on random boundary-biased 256-bit operands.
4. **§4 Canaries (E1).** A compiler that pushes operands in list order, a memory cost without the
   quadratic term, an `assert` that ignores its condition, and three wrong storage-gas models (no
   cold surcharge, `SSTORE` priced from the current value instead of the original, `SLOAD` not
   warming its slot) must each be refuted; the stack-depth limit of the scheme is checked as a rule
   (a program compiles exactly when its deepest operand is within `DUP16`'s reach), over a range
   of depths rather than at the single boundary point.
5. **§5 Stack code with `SWAP`/`POP` on `Θ` (`assembleS`).** `validateLowering_sound` is about the
   model `runSAsm`; here the *bytes* of checked schedules run on `Θ`. Unit checks: the `SWAP1`
   schedule of `subProg`, and `POP` schedules of `deepProg d` for `d` = 16, 40, 100 (which the
   proved compiler cannot compile). Counted properties: the `SWAP1` scheduler and `PUSH`/`POP`
   padding on random programs agree with the Venom semantics on outcome, output and storage and with
   `runSAsm refPrims` on gas exactly; and `Θ`'s gas satisfies the three proved laws of
   `validateLowering_gas` (lower, upper, exact without `assert`), with the regions where the upper
   bound is strict counted (A2). Canaries (E1): `SWAPk` encoded one too high, and the exact law
   without its `assert`-free hypothesis.
-/

namespace EvmYul.Venom.ThetaTests

open EvmYul.Venom Plausible Plausible.Decorations GasConstants

/-! ## §1 Real Vyper output: `store.vy` -/

/-- My compiled program and the real Vyper bytecode agree on outcome and slot 0. -/
def sameAsVyper (p : Program) (sig : String) (args : List ℕ) (kvs : List (ℕ × ℕ)) (value : ℕ)
    (truncate : Bool := false) (selOverride : Option ℕ := none) : Bool :=
  match storeVenom, compile p with
  | some cell, some c =>
    match cell.code?, cell.selector? sig with
    | some vcode, some sel =>
      let data := (Vyper.calldata (selOverride.getD sel) args).toList
      let data := if truncate then data.take 20 else data
      match onTheta (assemble c) kvs data value, onTheta vcode kvs data value with
      | some r₁, some r₂ => r₁.outcome == r₂.outcome && r₁.slot 0 == r₂.slot 0
      | _, _ => false
    | _, _ => false
  | _, _ => false

/-- Boundary arguments. -/
def boundary : List ℕ := [0, 1, 2, 2 ^ 128, 2 ^ 255, 2 ^ 256 - 2, 2 ^ 256 - 1]

/-- §1 sweep: every combination of argument, initial slot 0 and call value, plus a foreign
selector and truncated call data, for `set` and `bump`. Returns the number of compared runs. -/
def storeSweep : Option ℕ := Id.run do
  let mut n := 0
  for (p, sig) in [(setProg, "set(uint256)"), (bumpProg, "bump(uint256)")] do
    for a in boundary do
      for x0 in [0, 5, 2 ^ 256 - 1] do
        for value in [0, 1] do
          unless sameAsVyper p sig [a] [(0, x0)] value do return none
          n := n + 1
      unless sameAsVyper p sig [a] [(0, 7)] 0 (truncate := true) do return none
      unless sameAsVyper p sig [a] [(0, 7)] 0 (selOverride := some 0x12345678) do return none
      n := n + 2
  return some n

/-! ## §2 Random programs -/

/-- The §2 law on decoded inputs. -/
def law (xs : List (ℕ × ℕ × ℕ × ℕ)) (t : ℕ) (kv : List (ℕ × ℕ)) (cd : List ℕ) (v : ℕ) : Bool :=
  agrees (decodeProg xs t) (mkKvs kv) (mkData cd) (v % 3)

/-- The §2b law: storage-heavy programs agree on `Θ` and in the model, gas included. -/
def storageLaw (P : Prims Ref) (ops : List (ℕ × ℕ × ℕ)) (a b c : ℕ) : Bool :=
  match compile (decodeStorageProg ops) with
  | some code => agreesWith P code (decodeStorageProg ops) (mkPoolKvs a b c) [] 0
  | none => false

/-- Does the program write a slot after it was already changed (a dirty-slot write)? Computed on
the reference model; printed as coverage of §2b. -/
def writesDirtySlot (p : Program) (kvs : List (ℕ × ℕ)) : Bool := Id.run do
  let mut s := Ref.init kvs [] 0
  for i in p do
    match i with
    | .eff _ .sstore [.lit k, .lit v] =>
      if s.storage k.toNat ≠ s.original k.toNat ∧ s.storage k.toNat ≠ v.toNat then return true
      s := (refApply .sstore s [k, v]).2
    | _ => pure ()
  return false

/-! ## §3 Per-operation route -/

/-- `%0 = o a b; mstore 0, %0; return 0, 32` on `Θ` returns `o.eval₂ a b`. -/
def opRoute (o : PureOp) (a b : ℕ) : Bool :=
  let p : Program := [.pure 0 o (if o.arity = 1 then [L a] else [L a, L b]),
    .eff none .mstore [L 0, V 0], .halt .ret [L 0, L 32]]
  match compile p with
  | some c =>
    match onTheta (assemble c) [] [] 0 with
    | some r => r.output.toList == bytes32 (o.eval₂ (a % 2 ^ 256) (b % 2 ^ 256))
    | none => false
  | none => false

/-! ## §4 Mutants -/

/-- Mutant compiler: operands pushed in list order (operand 0 ends at the bottom). -/
def compileArgsInOrder (p : Program) : Option (List Asm) :=
  compile (p.map fun
    | .pure d o args => .pure d o args.reverse
    | .eff d e args => .eff d e args.reverse
    | .halt h args => .halt h args.reverse
    | i => i)

/-- Mutant reference: memory cost without the quadratic term. -/
def linearPrims : Prims Ref :=
  { refPrims with
    cost := fun e s vs => match e with
      | .mload | .mstore =>
        Gverylow + Gmemory * (wordsAfter s.words (vs.getD 0 default).toNat 32 - s.words)
      | _ => refCost e s vs }

/-- Mutant reference: every slot already warm (no EIP-2929 cold surcharge). -/
def allWarmPrims : Prims Ref :=
  { refPrims with
    cost := fun e s vs => match e with
      | .sload => Gwarmaccess
      | .sstore => s.sstoreCost (vs.getD 0 default).toNat (vs.getD 1 default).toNat
      | _ => refCost e s vs }

/-- Mutant reference: `SSTORE` priced from the current value only (pre-EIP-2200 reading: every
change costs `G_sset` from zero and `G_sreset` otherwise, dirty or not). -/
def noOriginalPrims : Prims Ref :=
  { refPrims with
    cost := fun e s vs => match e with
      | .sstore =>
        let a := (vs.getD 0 default).toNat
        let new := (vs.getD 1 default).toNat
        s.coldCost a + (if s.storage a = new then Gwarmaccess
                        else if s.storage a = 0 then Gsset else Gsreset)
      | _ => refCost e s vs }

/-- Mutant reference: `SLOAD` does not add its slot to the accessed set. -/
def sloadColdPrims : Prims Ref :=
  { refPrims with
    apply := fun e s vs => match e with
      | .sload => (word (s.storage (vs.getD 0 default).toNat), s)
      | _ => refApply e s vs }

/-- Slots accessed by the program, in order (its storage operands are literals). -/
def slotsOf (p : Program) : List ℕ :=
  p.filterMap fun
    | .eff _ .sload [.lit k] | .eff _ .sstore [.lit k, _] => some k.toNat
    | _ => none

/-- Does the program access some slot twice (so the warm-slot price is exercised)? -/
def touchesSlotTwice (p : Program) : Bool := (slotsOf p).length != (slotsOf p).eraseDups.length

/-- Mutant assembler input: every `assert` dropped from the code (the condition is still pushed
and popped by nothing, so the check is skipped). -/
def dropAsserts (c : List Asm) : List Asm := c.filter (· != .assertJ)

/-- A program whose deepest operand needs `DUP(d + 1)`: `d` variables are defined after `%0`, and
`%0` is the size operand of `return`, which is pushed first (operands go last-first), so no
temporary lies above it when it is loaded. -/
def depthProg (d : ℕ) : Program :=
  (List.range (d + 1)).map (fun i => .pure i .add [L i, L 1]) ++ [.halt .ret [L 0, V 0]]

/-! ## Running -/

/-- Seeded configuration (`TESTING.md` E3). -/
def cfg : Configuration := { numInst := 300, maxSize := 30, randomSeed := some 20261010,
                             quiet := true }

/-- Unit checks; each must be `true`. -/
def unitChecks : List (String × Bool) :=
  [("store.vy set: compiled fragment = real Vyper 0.4.3 Venom bytecode, set(5) from 0",
      sameAsVyper setProg "set(uint256)" [5] [] 0),
   ("store.vy bump: overflow from 2^256 - 1 reverts in both",
      sameAsVyper bumpProg "bump(uint256)" [1] [(0, 2 ^ 256 - 1)] 0),
   ("the comparison discriminates: the set fragment differs from Vyper's bump on bump(3) from 4",
      !(match storeVenom, compile setProg with
        | some cell, some c =>
          match cell.code?, cell.selector? "bump(uint256)" with
          | some vcode, some sel =>
            let data := (Vyper.calldata sel [3]).toList
            (match onTheta (assemble c) [(0, 4)] data 0, onTheta vcode [(0, 4)] data 0 with
             | some r₁, some r₂ => r₁.outcome == r₂.outcome && r₁.slot 0 == r₂.slot 0
             | _, _ => true)
          | _, _ => true
        | _, _ => true)),
   ("sub is a − b with a = μₛ[0]: 10 − 3 = 7", opRoute .sub 10 3),
   ("shr 224, x takes the shift first", opRoute .shr 224 (2 ^ 255)),
   -- The rule, not one point: an operand `k` slots deep is loaded with `DUPk`, and the EVM has
   -- `DUP1 … DUP16` only (no SWAP/POP scheduling here), so `depthProg d` (deepest operand at
   -- `DUP(d + 1)`) compiles exactly when `d + 1 ≤ 16`, for every `d` checked.
   ("compiles iff the deepest operand is within DUP16's reach (d < 40)",
      (List.range 40).all fun d => (compile (depthProg d)).isSome == decide (d + 1 ≤ 16)),
   ("the assert revert block sits at the end of the code",
      (match compile setProg with
       | some c => (assemble c).toList.drop (c.map asmSize).sum == revertBlock
       | none => false))]

/-- Fail the build on a counterexample or on too few valid inputs (counts printed). -/
def expectHolds (name : String) (p : Prop)
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] : IO Unit :=
  discard <| EvmYul.CountedTesting.holdsCore cfg name p' (EvmYul.CountedTesting.defaultMinValid cfg)

/-- Mutation test: fail the build unless a counterexample is found (counts printed). -/
def expectRefuted (name : String) (p : Prop)
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] : IO Unit :=
  discard <| EvmYul.CountedTesting.refutedCore cfg name p'

/-! ## §5 Stack code with `SWAP`/`POP` on `Θ` -/

/-- `Θ` on the bytes `asm c` agrees with the Venom result of `p` (outcome, output, storage) and with
the stack model `runSAsm refPrims c` on gas. -/
def agreesS (c : List SAsm) (p : Program) (kvs : List (ℕ × ℕ)) (data : List UInt8) (value : ℕ)
    (asm : List SAsm → ByteArray := assembleS) : Bool :=
  let s₀ := Ref.init kvs data value
  match run refPrims p Store.empty s₀ 0, runSAsm refPrims c [] s₀ 0 with
  | some f, some f' =>
    match onTheta (asm c) kvs data value with
    | some r =>
      r.outcome == f.outcome.frame && r.output.toList == f.output &&
        (List.range 8).all (fun k => r.slot k == expectedSlot f kvs k) && r.gasUsed == f'.gas
    | none => false
  | _, _ => false

/-- The `SWAP1` schedule of a decoded program (operands loaded in list order, fixed by `SWAP1`). -/
def swapSched (p : Program) : Option (List SAsm) := LoweringCheckTests.lowerWith false true [] p

/-- §5a: the `SWAP1` schedule is accepted by the checker and its bytes agree on `Θ`. -/
def swapLaw (xs : List (ℕ × ℕ × ℕ × ℕ)) (t : ℕ) (kv : List (ℕ × ℕ)) (cd : List ℕ) : Bool :=
  let p := decodeProg xs t
  match swapSched p with
  | some c => validateLowering p c [] && agreesS c p (mkKvs kv) (mkData cd) 0
  | none => false

/-- A decoded program with its `assert`s removed. -/
def withoutAsserts (p : Program) : Program := p.filter fun | .assert _ => false | _ => true

/-- §5b: compiled code padded with `PUSH`/`POP` pairs agrees on `Θ` and costs exactly
`W_verylow + W_base` per pair more than the Venom semantics. The programs have no `assert`: a
failing `assert` before a pair skips it, so the exact count needs the hypothesis of the exact law of
`validateLowering_gas` (the first version of this property omitted it and was refuted on
`assert 0`). -/
def padLaw (xs : List (ℕ × ℕ × ℕ × ℕ)) (t : ℕ) (pos : List ℕ) : Bool :=
  let p := withoutAsserts (decodeProg xs t)
  match compile p with
  | some c =>
    let (c', m) := LoweringCheckTests.pad pos (c.map Asm.toSAsm)
    validateLowering p c' [] && agreesS c' p [] [] 0 &&
      (match run refPrims p Store.empty (Ref.init [] [] 0) 0, onTheta (assembleS c') [] [] 0 with
       | some f, some r => r.gasUsed == f.gas + m * (Gverylow + Gbase)
       | _, _ => false)
  | none => false

/-- The gas used on `Θ` by the `SWAP1` schedule and by the Venom semantics of a decoded program. -/
def thetaGasPair (p : Program) (c : List SAsm) : Option (ℕ × ℕ) :=
  match onTheta (assembleS c) [] [] 0, run refPrims p Store.empty (Ref.init [] [] 0) 0 with
  | some r, some f => some (r.gasUsed, f.gas)
  | _, _ => none

/-- §5c: `Θ`'s gas for the `SWAP1` schedule satisfies the laws of `validateLowering_gas`; with
`exactAlways` the exact law is also demanded for programs with `assert` (the canary). -/
def gasLaw (exactAlways : Bool) (xs : List (ℕ × ℕ × ℕ × ℕ)) (t : ℕ) : Bool :=
  let p := decodeProg xs t
  match swapSched p with
  | some c =>
    match thetaGasPair p c with
    | some (gc, gp) =>
      decide (gp ≤ gc + loadGas p) && decide (gc ≤ gp + shuffleGas c) &&
        (!(exactAlways || assertFree p) || gc + loadGas p == gp + shuffleGas c)
    | none => false
  | none => false

/-- Mutant encoder: `SWAPk` emitted as `0x90 + k` (that is, `SWAP(k+1)`). -/
def encodeSHigh (r : ℕ) : SAsm → List UInt8
  | .swap k => [UInt8.ofNat (0x90 + k)]
  | a => encodeS r a

/-- Mutant assembler built on `encodeSHigh`. -/
def assembleSHigh (c : List SAsm) : ByteArray :=
  let r := (c.map asmSizeS).sum
  ⟨(c.flatMap (encodeSHigh r) ++ revertBlock).toArray⟩

/-- §5 unit checks; each must be `true`. -/
def stackUnitChecks : List (String × Bool) :=
  [("SWAP1 schedule of subProg: accepted, and its bytes agree on Θ (gas = runSAsm)",
      validateLowering LoweringCheckTests.subProg LoweringCheckTests.subSwapped [] &&
        agreesS LoweringCheckTests.subSwapped LoweringCheckTests.subProg [] (mkData [1, 2, 3]) 0),
   ("the same code without its SWAP1 disagrees with the Venom semantics on Θ",
      !agreesS LoweringCheckTests.subUnswapped LoweringCheckTests.subProg [] (mkData [1, 2, 3]) 0),
   ("POP schedules of deepProg 16/40/100: not compilable, accepted, and correct on Θ",
      [16, 40, 100].all fun d =>
        (compile (LoweringCheckTests.deepProg d)).isNone &&
          validateLowering (LoweringCheckTests.deepProg d) (LoweringCheckTests.deepPopped d) [] &&
          agreesS (LoweringCheckTests.deepPopped d) (LoweringCheckTests.deepProg d) [] [] 0),
   ("POP opcode is 0x50 and SWAP1 is 0x90 in the emitted bytes",
      (assembleS [.push (word 1), .push (word 2), .swap 1, .pop, .halt .stop]).toList.drop 66 ==
        [0x90, 0x50, 0x00] ++ revertBlock),
   ("assembleS on embedded Asm is assemble (assembleS_embed, evaluated on setProg)",
      (compile setProg).any fun c => (assembleS (c.map Asm.toSAsm)).toList == (assemble c).toList)]

/-- Run everything; throws on the first failure. -/
def runAll : IO Unit := do
  for (name, ok) in unitChecks do
    unless ok do throw <| IO.userError s!"unit check failed: {name}"
  IO.println s!"Venom on Θ: {unitChecks.length} unit checks passed"
  match storeSweep with
  | some n => IO.println s!"§1 store.vy: {n} runs, compiled Venom fragment = real Vyper 0.4.3 \
      Venom bytecode (outcome and storage) on every one"
  | none => throw <| IO.userError "§1 store.vy: the compiled fragment and Vyper's bytecode disagree"
  -- §2
  expectHolds "§2 Θ(assemble(compile p)) = Venom semantics (outcome, output, storage, gas)"
    (∀ (xs : List (ℕ × ℕ × ℕ × ℕ)) (t : ℕ) (kv : List (ℕ × ℕ)) (cd : List ℕ) (v : ℕ),
      law xs t kv cd v = true)
  let gen := (List.range 300).map fun i =>
    decodeProg ((List.range (i % 25)).map fun j => (mix (i * 31 + j) % 10, mix (i + j) % 97,
      mix (j * 7 + i) % 101, mix (i * j + 3) % 89)) i
  let outs := gen.filterMap fun p => (run refPrims p Store.empty (Ref.init [] [] 0) 0).map (·.outcome)
  let cnt (o : Outcome) := (outs.filter (· == o)).length
  let lens := gen.map List.length
  let quad := (gen.filter fun p => match run refPrims p Store.empty (Ref.init [] [] 0) 0 with
    | some f => f.state.words > 22
    | none => false).length
  IO.println s!"§2 coverage of the decoder (300 programs): stopped {cnt .stopped}, returned \
    {cnt .returned}, reverted {cnt .reverted}; touching storage \
    {(gen.filter (!storageFree ·)).length}, a slot twice (warm path) \
    {(gen.filter touchesSlotTwice).length}; memory past 22 words (quadratic cost term non-zero) \
    {quad}; longest program {lens.foldl max 0} instructions"
  -- §2b
  expectHolds "§2b storage-heavy programs: Θ = Venom semantics, EIP-2929/2200 storage gas exact"
    (∀ (ops : List (ℕ × ℕ × ℕ)) (a b c : ℕ), storageLaw refPrims ops a b c = true)
  let sgen := (List.range 300).map fun i =>
    ((List.range (i % 12)).map fun j =>
        (mix (i * 13 + j) % 7, mix (i + 5 * j) % 11, mix (i * j + j) % 13),
     mkPoolKvs (mix i) (mix (i + 1)) (mix (i + 2)))
  IO.println s!"§2b coverage (300 programs): writing a dirty slot \
    {(sgen.filter fun (ops, kvs) => writesDirtySlot (decodeStorageProg ops) kvs).length}"
  -- §3
  for o in pureOps do
    expectHolds s!"§3 {repr o} on Θ = the ℕ definition (boundary-biased 256-bit operands)"
      (∀ (c a b : ℕ), opRoute o (mkLit c a) (mkLit (c + 1) b) = true)
  -- §4
  expectRefuted "§4 canary: operands pushed in list order"
    (∀ (xs : List (ℕ × ℕ × ℕ × ℕ)) (t : ℕ),
      (match compileArgsInOrder (decodeProg xs t) with
       | some c => agreesWith refPrims c (decodeProg xs t) [] [] 0
       | none => false) = true)
  expectRefuted "§4 canary: memory cost without the quadratic term"
    (∀ (xs : List (ℕ × ℕ × ℕ × ℕ)) (t : ℕ),
      (match compile (decodeProg xs t) with
       | some c => agreesWith linearPrims c (decodeProg xs t) [] [] 0
       | none => false) = true)
  expectRefuted "§4 canary: asserts dropped from the code"
    (∀ (xs : List (ℕ × ℕ × ℕ × ℕ)) (t : ℕ),
      (match compile (decodeProg xs t) with
       | some c => agreesWith refPrims (dropAsserts c) (decodeProg xs t) [] [] 0
       | none => false) = true)
  expectRefuted "§4 canary: storage gas, no cold surcharge (every slot warm)"
    (∀ (ops : List (ℕ × ℕ × ℕ)) (a b c : ℕ), storageLaw allWarmPrims ops a b c = true)
  expectRefuted "§4 canary: storage gas, SSTORE priced from the current value, not the original"
    (∀ (ops : List (ℕ × ℕ × ℕ)) (a b c : ℕ), storageLaw noOriginalPrims ops a b c = true)
  expectRefuted "§4 canary: storage gas, SLOAD does not warm its slot"
    (∀ (ops : List (ℕ × ℕ × ℕ)) (a b c : ℕ), storageLaw sloadColdPrims ops a b c = true)
  -- §5
  for (name, ok) in stackUnitChecks do
    unless ok do throw <| IO.userError s!"§5 unit check failed: {name}"
  IO.println s!"§5 stack code on Θ: {stackUnitChecks.length} unit checks passed"
  expectHolds "§5a SWAP1 schedules: accepted, Θ = Venom (outcome, output, storage), gas = runSAsm"
    (∀ (xs : List (ℕ × ℕ × ℕ × ℕ)) (t : ℕ) (kv : List (ℕ × ℕ)) (cd : List ℕ),
      (swapSched (decodeProg xs t)).isSome = true → swapLaw xs t kv cd = true)
  expectHolds "§5b PUSH/POP padding on Θ: accepted, same result, gas + 5 per pair"
    (∀ (xs : List (ℕ × ℕ × ℕ × ℕ)) (t : ℕ) (pos : List ℕ),
      (compile (withoutAsserts (decodeProg xs t))).isSome = true → padLaw xs t pos = true)
  expectHolds "§5c Θ gas of SWAP1 schedules obeys validateLowering_gas (lower, upper, exact)"
    (∀ (xs : List (ℕ × ℕ × ℕ × ℕ)) (t : ℕ),
      (swapSched (decodeProg xs t)).isSome = true → gasLaw false xs t = true)
  let sgen := (List.range 300).map fun i =>
    decodeProg ((List.range (i % 25)).map fun j => (mix (i * 31 + j) % 10, mix (i + j) % 97,
      mix (j * 7 + i) % 101, mix (i * j + 3) % 89)) i
  let pairs := sgen.filterMap fun p => (swapSched p).bind fun c =>
    (thetaGasPair p c).map fun (gc, gp) => (p, c, gc, gp)
  let exact := (pairs.filter fun (p, _, _, _) => assertFree p).length
  let strict := (pairs.filter fun (p, c, gc, gp) => gc < gp + shuffleGas c ∧
    gc + loadGas p ≠ gp + shuffleGas c).length
  let swapped := (pairs.filter fun (_, c, _, _) => c.contains (.swap 1)).length
  IO.println s!"§5c coverage (300 programs): scheduled {pairs.length}, with a SWAP {swapped}, \
    assert-free (exact law applies) {exact}, upper bound strict and not exact (an assert cut the run \
    short) {strict}"
  unless exact ≥ 10 ∧ strict ≥ 10 ∧ swapped ≥ 100 do
    throw <| IO.userError "§5c coverage: a region is empty or too small (A2)"
  expectRefuted "§5 canary: SWAPk encoded as 0x90 + k"
    (∀ (xs : List (ℕ × ℕ × ℕ × ℕ)) (t : ℕ),
      (match swapSched (decodeProg xs t) with
       | some c => agreesS c (decodeProg xs t) [] [] 0 (asm := assembleSHigh)
       | none => true) = true)
  expectRefuted "§5 canary: the exact gas law also holds for programs with assert"
    (∀ (xs : List (ℕ × ℕ × ℕ × ℕ)) (t : ℕ),
      (swapSched (decodeProg xs t)).isSome = true → gasLaw true xs t = true)
  IO.println "Venom on Θ: standing caveat (D1): the fragment and the reference model are written \
    from the Vyper output and the Yellow Paper; a shared misreading of either passes these tests"

#eval runAll

end EvmYul.Venom.ThetaTests
