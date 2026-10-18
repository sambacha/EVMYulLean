module

public import EvmYul.FFI.Primitives
public meta import EvmYul.FFI.Primitives
public import EvmYul.Venom.EvmMachine
public meta import EvmYul.Venom.EvmMachine
public import EvmYul.Venom.ThetaTestHarness
public meta import EvmYul.Venom.ThetaTestHarness
public import EvmYul.Testing.Counted
public meta import EvmYul.Testing.Counted
public import Plausible
public meta import Plausible

@[expose] public meta section

/-!
# Tests of the EVM-backed machine interfaces

`EvmMachine.lean` defines `evmPrims` and `evmInterface` through the project's own `exceptionalHalt`
and `EVM.step`. These tests check that the Venom layers, run on them, predict the project's EVM
`Θ` (this module is an FFI test root, so `Θ` and the interpreter's memory primitives run during the
build). Each section names the `TESTING.md` rule it applies.

1. **§1 Per-operation route (D1).** For every pure operation, `execOp` on two boundary-biased
   256-bit operands leaves exactly the ℕ definition `PureOp.eval₂` on the stack and charges exactly
   the fragment's price `PureOp.gas`; the CFG interface's arithmetic agrees with `BitVec` arithmetic
   (a third route).
2. **§2 Venom over the EVM = `Θ` (counted, A2).** For random fragment programs, the Venom semantics
   run on `evmPrims` from `initState` agrees with `Θ` on the assembled compiled code on outcome,
   output bytes, storage slots `0…7` and **gas exactly**. With `compile_correct` at `evmPrims` this
   closes the loop from the Venom semantics over the project's EVM to the bytes on `Θ`.
3. **§3 Two models agree (D1).** `evmPrims` and the reference model `refPrims` (written separately
   from the Yellow Paper and the EIPs) give the same outcome, data, gas and storage.
4. **§4 The CFG layer on the EVM.** Loops with φs, `assert` and the EVM `return` run under
   `evmInterface`: concrete business values (a sum over a loop, a selector check that reverts on a
   foreign selector, a storage write that survives) are asserted exactly.
5. **§5 Canaries (E1).** An executor that hands the operands over reversed, one that reports no gas,
   and a CFG `assert` that never reverts must each be refuted.
-/

namespace EvmYul.Venom.EvmMachineTests

open EvmYul.Venom EvmYul.Venom.EvmMachine EvmYul.Venom.ThetaTests Plausible Plausible.Decorations
open GasConstants

/-! ## §1 Per-operation route -/

/-- `execOp` of a pure operation on `a = μₛ[0]`, `b = μₛ[1]` leaves `eval₂ a b` and costs `gas`. -/
def opLaw (o : PureOp) (a b : ℕ) : Bool :=
  let args := if o.arity = 1 then [word a] else [word a, word b]
  match execOp (pureOpEvm o) args (initState .empty [] [] 0) with
  | some (out, _, g) => out == [o.eval₂ (a % 2 ^ 256) (b % 2 ^ 256)] && g == o.gas
  | none => false

/-- The CFG interface on `add`/`sub`/`mul`/`and`/`or`/`xor` agrees with `BitVec` arithmetic. -/
def cfgArithLaw (a b : ℕ) : Bool :=
  let x : Cfg.Word := BitVec.ofNat 256 a
  let y : Cfg.Word := BitVec.ofNat 256 b
  let s₀ := initState .empty [] [] 0
  let ex (op : Cfg.Op) := (Cfg.EvmInterface.exec op [x, y] s₀).map (·.1)
  ex .add == some [x + y] && ex .sub == some [x - y] && ex .mul == some [x * y] &&
    ex .and == some [x &&& y] && ex .or == some [x ||| y] && ex .xor == some [x ^^^ y] &&
    ex .lt == some [if x.toNat < y.toNat then 1 else 0] &&
    ex .eq == some [if x = y then 1 else 0]

/-! ## §2 and §3 Straight-line programs -/

/-- Storage slot `k` expected after a run over the EVM: the initial value after a revert. -/
def expectedSlotE (f : Final EVM.State) (kvs : List (ℕ × ℕ)) (k : ℕ) : ℕ :=
  if f.outcome = .reverted then (kvs.lookup k).getD 0 % 2 ^ 256 else slotOf f.state k

/-- §2: the Venom semantics over `P` (an EVM-state machine) agrees with `Θ` on the assembled
compiled code. -/
def thetaLawWith (P : Prims EVM.State) (p : Program) (kvs : List (ℕ × ℕ)) (data : List UInt8)
    (value : ℕ) : Bool :=
  match compile p with
  | none => false
  | some c =>
    let code := assemble c
    match run P p Store.empty (initState code kvs data value) 0, onTheta code kvs data value with
    | some f, some r =>
      r.outcome == f.outcome.frame && r.output.toList == outputOf f &&
        (List.range 8).all (fun k => r.slot k == expectedSlotE f kvs k) && r.gasUsed == f.gas
    | _, _ => false

/-- §2 on decoded inputs. -/
def thetaLaw (xs : List (ℕ × ℕ × ℕ × ℕ)) (t : ℕ) (kv : List (ℕ × ℕ)) (cd : List ℕ) (v : ℕ) : Bool :=
  thetaLawWith evmPrims (decodeProg xs t) (mkKvs kv) (mkData cd) (v % 3)

/-- §3: `evmPrims` and `refPrims` agree (outcome, data, gas, storage slots `0…7`, output). -/
def twoModelsLaw (xs : List (ℕ × ℕ × ℕ × ℕ)) (t : ℕ) (kv : List (ℕ × ℕ)) (cd : List ℕ) : Bool :=
  let p := decodeProg xs t
  let kvs := mkKvs kv
  let data := mkData cd
  match run evmPrims p Store.empty (initState .empty kvs data 0) 0,
        run refPrims p Store.empty (Ref.init kvs data 0) 0 with
  | some f, some f' =>
    f.outcome == f'.outcome && f.data == f'.data && f.gas == f'.gas && outputOf f == f'.output &&
      (List.range 8).all fun k => expectedSlotE f kvs k == expectedSlot f' kvs k
  | _, _ => false

/-! ## §4 The CFG layer on the EVM -/

open Cfg in
/-- Sum `1 + … + n` in a loop with φs, `n` read from call data word 0, stored to slot 0:
```
entry: %n = calldataload 0; jmp @head
head:  %i = phi @entry, %n, @body, %i2 ; %acc = phi @entry, 0, @body, %acc2 ; jnz %i, @body, @exit
body:  %acc2 = add %acc, %i ; %i2 = sub %i, 1 ; jmp @head
exit:  sstore 0, %acc ; stop
```
(`sstore` takes `key, value` in Venom text order.) -/
def sumLoop : Func := { name := "sum", entry := "entry", blocks := [
  { label := "entry", insts := [
      { op := .calldataload, args := [.lit 0], outs := ["n"] },
      { op := .jmp, args := [.lbl "head"], outs := [] } ] },
  { label := "head", insts := [
      { op := .phi, args := [.lbl "entry", .var "n", .lbl "body", .var "i2"], outs := ["i"] },
      { op := .phi, args := [.lbl "entry", .lit 0, .lbl "body", .var "acc2"], outs := ["acc"] },
      { op := .jnz, args := [.var "i", .lbl "body", .lbl "exit"], outs := [] } ] },
  { label := "body", insts := [
      { op := .add, args := [.var "acc", .var "i"], outs := ["acc2"] },
      { op := .sub, args := [.var "i", .lit 1], outs := ["i2"] },
      { op := .jmp, args := [.lbl "head"], outs := [] } ] },
  { label := "exit", insts := [
      { op := .sstore, args := [.lit 0, .var "acc"], outs := [] },
      { op := .stop, args := [], outs := [] } ] } ] }

open Cfg in
/-- The selector check of `store.vy`'s `set(uint256)` bucket, written in the CFG layer: revert unless
the selector is `0x60fe47b1` (`assert`), then store word 1 of the call data to slot 0 and
`return 0, 0` (the EVM `return`). -/
def setBucket : Func := { name := "set", entry := "b", blocks := [
  { label := "b", insts := [
      { op := .calldataload, args := [.lit 0], outs := ["1"] },
      { op := .shr, args := [.lit 224, .var "1"], outs := ["2"] },
      { op := .xor, args := [.lit 0x60fe47b1, .var "2"], outs := ["42"] },
      { op := .iszero, args := [.var "42"], outs := ["8"] },
      { op := .assert, args := [.var "8"], outs := [] },
      { op := .calldataload, args := [.lit 4], outs := ["15"] },
      { op := .sstore, args := [.lit 0, .var "15"], outs := [] },
      { op := .evmReturn, args := [.lit 0, .lit 0], outs := [] } ] } ] }

/-- Run a CFG function under `evmInterface` from `initState` with call data `data`; report how it
ended and storage slot 0 (`none` if it faulted or ran out of fuel). -/
def runCfgEvm (f : Cfg.Func) (data : List UInt8) (fuel : ℕ := 200) : Option (String × ℕ) :=
  match Cfg.runEntry f fuel (initState .empty [] data 0) with
  | .halted s => some ("halted", slotOf s 0)
  | .reverted s => some ("reverted", slotOf s 0)
  | _ => none

/-- Call data of a call with selector `sel` and word arguments `args`. -/
def cd (sel : ℕ) (args : List ℕ) : List UInt8 := (Vyper.calldata sel args).toList

/-- Call data holding one word `n`. -/
def cdWord (n : ℕ) : List UInt8 := Vyper.word n

/-- Gas consumed by a halted CFG run (the EVM charges inside the state). -/
def cfgGas (f : Cfg.Func) (data : List UInt8) : Option ℕ :=
  match Cfg.runEntry f 200 (initState .empty [] data 0) with
  | .halted s => some (Vyper.budget - s.gasAvailable.toNat)
  | _ => none

/-- §4 unit checks; each must be `true`. -/
def cfgUnitChecks : List (String × Bool) :=
  [("sum loop on the EVM: n = 0, 1, 4, 10 store 0, 1, 10, 55",
      [0, 1, 4, 10].all fun n => runCfgEvm sumLoop (cdWord n) == some ("halted", n * (n + 1) / 2)),
   ("sum loop: more iterations cost strictly more EVM gas (4 < 10)",
      match cfgGas sumLoop (cdWord 4), cfgGas sumLoop (cdWord 10) with
      | some g₄, some g₁₀ => g₄ < g₁₀
      | _, _ => false),
   ("sum loop: one cold SSTORE of a non-zero value from zero costs at least G_sset + G_coldsload",
      (cfgGas sumLoop (cdWord 3)).any fun g => g ≥ Gsset + Gcoldsload),
   ("set bucket, matching selector: halts and stores the argument",
      runCfgEvm setBucket (cd 0x60fe47b1 [77]) == some ("halted", 77)),
   ("set bucket, foreign selector: the assert reverts before the store",
      runCfgEvm setBucket (cd 0xb20eb4c4 [77]) == some ("reverted", 0)),
   ("the sum loop runs out of fuel when the fuel is below the iteration count",
      runCfgEvm sumLoop (cdWord 10) (fuel := 5) == none)]

/-! ## §5 Mutants -/

/-- Mutant machine: the effects get their operands reversed. -/
def reversedPrims : Prims EVM.State :=
  { evmPrims with
    apply := fun e s vs => evmPrims.apply e s vs.reverse
    cost := fun e s vs => evmPrims.cost e s vs.reverse }

/-- Mutant machine: the effects report no gas. -/
def freePrims : Prims EVM.State := { evmPrims with cost := fun _ _ _ => 0 }

/-- Mutant CFG machine: `evmInterface`, run by a semantics whose `assert` never reverts (the
`assert` is dropped from every block before running). -/
def dropAssertsCfg (f : Cfg.Func) : Cfg.Func :=
  { f with blocks := f.blocks.map fun b => { b with insts := b.insts.filter (·.op != .assert) } }

/-! ## Running -/

/-- Seeded configuration (`TESTING.md` E3). -/
def cfg : Configuration := { numInst := 300, maxSize := 30, randomSeed := some 20261013,
                             quiet := true }

/-- Fail the build on a counterexample or on too few valid inputs (counts printed). -/
def expectHolds (name : String) (p : Prop)
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] : IO Unit :=
  discard <| EvmYul.CountedTesting.holdsCore cfg name p' (EvmYul.CountedTesting.defaultMinValid cfg)

/-- Mutation test: fail the build unless a counterexample is found (counts printed). -/
def expectRefuted (name : String) (p : Prop)
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] : IO Unit :=
  discard <| EvmYul.CountedTesting.refutedCore cfg name p'

/-- Run everything; throws on the first failure. -/
def runAll : IO Unit := do
  -- §1
  for o in pureOps do
    expectHolds s!"§1 execOp {repr o} = the ℕ definition, gas = PureOp.gas"
      (∀ (c a b : ℕ), opLaw o (mkLit c a) (mkLit (c + 1) b) = true)
  expectHolds "§1 CFG interface arithmetic = BitVec arithmetic"
    (∀ (c a b : ℕ), cfgArithLaw (mkLit c a) (mkLit (c + 1) b) = true)
  -- §2
  expectHolds "§2 Venom semantics on evmPrims = Θ on the assembled code (outcome, output, storage, gas)"
    (∀ (xs : List (ℕ × ℕ × ℕ × ℕ)) (t : ℕ) (kv : List (ℕ × ℕ)) (cd : List ℕ) (v : ℕ),
      thetaLaw xs t kv cd v = true)
  -- A2 coverage of §2/§3: outcomes and effects actually exercised over the EVM machine
  let gen := (List.range 300).map fun i =>
    decodeProg ((List.range (i % 25)).map fun j => (mix (i * 31 + j) % 10, mix (i + j) % 97,
      mix (j * 7 + i) % 101, mix (i * j + 3) % 89)) i
  let outs := gen.filterMap fun p =>
    (run evmPrims p Store.empty (initState .empty [] [] 0) 0).map (·.outcome)
  let cnt (o : Outcome) := (outs.filter (· == o)).length
  IO.println s!"§2 coverage (300 programs on evmPrims): stopped {cnt .stopped}, returned \
    {cnt .returned}, reverted {cnt .reverted}; touching storage {(gen.filter (!storageFree ·)).length}"
  unless cnt .stopped ≥ 10 ∧ cnt .returned ≥ 10 ∧ cnt .reverted ≥ 10 do
    throw <| IO.userError "§2 coverage: an outcome region is empty or too small (A2)"
  for (p, name) in [(setProg, "set"), (bumpProg, "bump")] do
    unless [0, 1, 2 ^ 256 - 1].all (fun a => [0x60fe47b1, 0xb20eb4c4].all fun sel =>
        thetaLawWith evmPrims p [(0, 5)] (cd sel [a]) 0) do
      throw <| IO.userError s!"§2 store.vy {name} fragment: evmPrims and Θ disagree"
  IO.println "§2 store.vy set/bump fragments on evmPrims = Θ for 3 arguments × 2 selectors"
  -- §3
  expectHolds "§3 evmPrims = refPrims (outcome, data, gas, storage, output)"
    (∀ (xs : List (ℕ × ℕ × ℕ × ℕ)) (t : ℕ) (kv : List (ℕ × ℕ)) (cd : List ℕ),
      twoModelsLaw xs t kv cd = true)
  -- §4
  for (name, ok) in cfgUnitChecks do
    unless ok do throw <| IO.userError s!"§4 unit check failed: {name}"
  IO.println s!"§4 CFG layer on the EVM: {cfgUnitChecks.length} unit checks passed"
  expectHolds "§4 sum loop on the EVM stores n(n+1)/2 mod 2^256 for every n ≤ 29"
    (∀ n : ℕ, n < 30 → runCfgEvm sumLoop (cdWord n) == some ("halted", n * (n + 1) / 2))
  -- §5
  expectRefuted "§5 canary: effects get their operands reversed"
    (∀ (xs : List (ℕ × ℕ × ℕ × ℕ)) (t : ℕ),
      thetaLawWith reversedPrims (decodeProg xs t) [] (mkData [1, 2, 3]) 0 = true)
  expectRefuted "§5 canary: effects report no gas"
    (∀ (xs : List (ℕ × ℕ × ℕ × ℕ)) (t : ℕ),
      thetaLawWith freePrims (decodeProg xs t) [] (mkData [1, 2, 3]) 0 = true)
  expectRefuted "§5 canary: a CFG assert that never reverts"
    (∀ sel : ℕ, runCfgEvm (dropAssertsCfg setBucket) (cd (0x60fe47b1 + sel) [5]) ==
      runCfgEvm setBucket (cd (0x60fe47b1 + sel) [5]))

#eval runAll

end EvmYul.Venom.EvmMachineTests
