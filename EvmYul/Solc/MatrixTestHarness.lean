module

public import EvmYul.FFI.Primitives
public meta import EvmYul.FFI.Primitives
public import EvmYul.Solc.Harness
public meta import EvmYul.Solc.Harness
public import EvmYul.Solc.Fixtures
public meta import EvmYul.Solc.Fixtures
public import EvmYul.Solc.Corpus
public meta import EvmYul.Solc.Corpus
public import EvmYul.Testing.EvmFixtures
public meta import EvmYul.Testing.EvmFixtures
@[expose] public meta section

/-!
# Test harness of `MatrixTests`

The definitions that `MatrixTests.lean` runs and that other test files reuse: generators, observers,
runners, mutants and the lemmas about them. They used to live in the test file itself, which made
other test files import a test file as a fixture library; `GUIDELINES.md` Rule 3 keeps shared
fixtures in a harness module instead (layout check L10). Every declaration keeps its name and
namespace.
-/

namespace EvmYul.Solc.MatrixTests

open EvmYul.Solc EvmYul.Yul Gas Plausible Plausible.Decorations GasConstants
open EvmYul.Testing.EvmFixtures
open EvmYul.Vyper (hexOf Run)

/-! ## Helpers -/

/-- Fail with all collected messages (at most ten shown). -/
def failIf (what : String) (errs : List String) : IO Unit :=
  unless errs.isEmpty do
    throw <| IO.userError s!"{what}: {errs.length} failure(s):\n{String.intercalate "\n" (errs.take 10)}"

/-- `2^256`. -/
def W : ℕ := 2 ^ 256

/-- The cells of one corpus program. -/
def cellsOf (p : String) : List Cell := fixtures.filter (·.program == p)

/-- Counted property test with `n` samples (the suite's sweeps are already exhaustive, so the random
tests are kept small enough for the build); fails on a counterexample or too few valid samples. -/
def matrixHolds (name : String) (n : ℕ) (p : Prop)
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] : IO Unit :=
  let c : Configuration := { cfg with numInst := n, randomSeed := some 20261008 }
  discard <| CountedTesting.holdsCore c name p' (CountedTesting.defaultMinValid c)

/-! ## Reference models (closed forms, mod `2^256`) -/

/-- Storage slots `0, 1` the program must leave, from empty storage. -/
def reference : String → List ℕ → Option (List ℕ)
  | "if_store", [x] => some [x % W, 0]
  | "if_const", [x] => some [if x % W = 0 then 0 else 1, 0]
  | "for_sum", [n] => some [(n * (n - 1) / 2 + 1) % W, 0]
  | "call_inline", [a, b] => some [(a + a * a + 1) % W, (b + b * b + 1) % W]
  | "call_rec", [n] => some [(n * (n + 1) / 2 + 1) % W, 0]
  | "nested_call", [n] => some [(n * (n - 1) * (n - 2) / 6 + 1) % W, 0]
  | _, _ => none

/-- Boundary values for 256-bit inputs. -/
def boundary : List ℕ := [0, 1, 2, 3, 255, 256, 2 ^ 128, 2 ^ 255, W - 2, W - 1]

/-- The sweep of each program: every loop/recursion count up to a bound, boundary grids for the
straight-line programs. -/
def sweep : String → List (List ℕ)
  | "if_store" | "if_const" => boundary.map ([·])
  | "for_sum" => (List.range 21).map ([·])
  | "call_inline" => boundary.flatMap fun a => [[a, 0], [a, W - 1], [0, a]]
  | "call_rec" => (List.range 21).map ([·])
  | "nested_call" => (List.range 11).map ([·])
  | _ => []

/-- Fuel for the Yul interpreter (enough for every sweep point). -/
def yulFuel : ℕ := 20000

/-- The three-way behaviour check at one point; `none` if everything agrees. -/
def behaviourDiff (c : Cell) (args : List ℕ) : Option String := do
  let what := s!"{c.name} {args}"
  let some p := corpusContract c.program | some s!"{what}: no parsed corpus program"
  let some ref := reference c.program args | some s!"{what}: no reference model"
  match c.run? args with
  | none => some s!"{what}: Θ error or bad hex"
  | some r =>
    if !r.ok then some s!"{what}: compiled run failed ({repr r.outcome})"
    else if [r.slot 0, r.slot 1] != ref then
      some s!"{what}: compiled storage {[r.slot 0, r.slot 1]}, reference {ref}"
    else if yulSlots p yulFuel args != some ref then
      some s!"{what}: Yul interpreter storage {yulSlots p yulFuel args}, reference {ref}"
    else if (modelRun cancunFn p bigN bigD args).map (·.1) != some ref then
      some s!"{what}: Yul gas meter storage {(modelRun cancunFn p bigN bigD args).map (·.1)}, \
        reference {ref}"
    else none

/-! ## §2 Floor laws -/

/-- Programs with a user-function call. -/
def hasCall (p : String) : Bool := p == "call_inline" || p == "call_rec" || p == "nested_call"

/-- Does the floor law (gap ≥ 0) apply to this cell? Unoptimized cells always (K14); optimized
cells when the program has no call or its call survives (K15). -/
def floorApplies (c : Cell) : Bool :=
  !c.optimize || !hasCall c.program || (c.code?.map callSurvives).getD false

/-- The gaps of a cell over its sweep, with a model `m` (`cancunFn` for the real law). -/
def gapsWith (m : FnCostModel) (c : Cell) : List (List ℕ × Option ℤ) :=
  (sweep c.program).map fun a =>
    (a, match c.run? a, corpusContract c.program with
        | some r, some p =>
          if r.ok then ((modelRun m p bigN bigD a).map fun (_, g) =>
            (r.gasUsed : ℤ) - storageRemainder r - g) else none
        | _, _ => none)

/-! ## §3 Families and overheads -/

/-- The literal `0` costs `PUSH0` (`G_base`) from Shanghai on, `PUSH1 0` (`G_verylow`) before. -/
def pushZero (c : Cell) : ℕ := if c.evmVersion == "london" then Gverylow else Gbase

/-- Execution gas py-evm recorded for cell `c` at `args` (`none` if not recorded or not
successful). -/
def oracleGasAt (c : Cell) (args : List ℕ) : Option ℕ := do
  let p ← c.oracle.find? (·.args == args)
  if p.success then pure p.gasUsed else none

/-- Gas of a successful run of cell `c` at `args` on `Θ`. -/
def thetaGasAt (c : Cell) (args : List ℕ) : Option ℕ := do
  let r ← c.run? args
  if r.ok then pure r.gasUsed else none

/-- Overhead of the `if` when skipped, from a gas source `g` (`Θ` or py-evm): gas of the run with
`x = 0` minus the specified cost of the condition's work (`push 0; CALLDATALOAD`). -/
def skipOverheadWith (g : List ℕ → Option ℕ) (c : Cell) : Option ℕ := do
  let gas ← g [0]
  let w := pushZero c + Gverylow
  if w ≤ gas then pure (gas - w) else none

/-- Overhead of `if_const`'s `if` when taken, from a gas source `g`: gas with `x = 1` minus the
specified cost of the condition's work and the body's work (`PUSH1 1; push 0; SSTORE` of a fresh
nonzero slot, `sstoreFreshSpec`). -/
def takenOverheadWith (g : List ℕ → Option ℕ) (c : Cell) : Option ℕ := do
  let gas ← g [1]
  let w := pushZero c + Gverylow + Gverylow + pushZero c + sstoreFreshSpec
  if w ≤ gas then pure (gas - w) else none

/-- `skipOverheadWith` on `Θ`. -/
def skipOverhead (c : Cell) : Option ℕ := skipOverheadWith (thetaGasAt c) c

/-- `takenOverheadWith` on `Θ`. -/
def takenOverhead (c : Cell) : Option ℕ := takenOverheadWith (thetaGasAt c) c

/-- Pinned version → family table for `if_const` and `if_store` (R1/R2): `(version, optimize,
codegen) ↦ family`. -/
def familyTable : List ((String × Bool × Codegen) × IfFamily) :=
  [(("0.8.13", false, .legacy), .inlineNegated), (("0.8.13", true, .legacy), .duplicatedStop),
   (("0.8.20", false, .legacy), .inlineNegated), (("0.8.20", true, .legacy), .duplicatedStop),
   (("0.8.21", false, .legacy), .outOfLine), (("0.8.21", true, .legacy), .duplicatedStop),
   (("0.8.24", false, .legacy), .outOfLine), (("0.8.24", true, .legacy), .duplicatedStop),
   (("0.8.26", false, .legacy), .outOfLine), (("0.8.26", true, .legacy), .duplicatedStop),
   (("0.8.30", false, .legacy), .outOfLine), (("0.8.30", true, .legacy), .duplicatedStop),
   (("0.8.37", false, .legacy), .outOfLine), (("0.8.37", true, .legacy), .duplicatedStop),
   (("0.8.37", false, .ssaCfg), .outOfLine)]

/-- Pinned `if_const` overheads per family: `(skip, taken)`. These are observations about the
compilers' output (a regression snapshot), computed from a run's gas minus the specified cost of the
condition and the body; each must also follow from the py-evm records (`MatrixTests` §3,
provenance), and the rule they are checked against is L1 (every overhead is at least the model's
branch price). -/
def overheadTable : IfFamily → ℕ × ℕ
  | .inlineNegated => (22, 22)
  | .outOfLine => (14, 26)
  | .duplicatedStop => (13, 14)

/-- One more loop iteration of `for_sum` (`n = 6` minus `n = 5`), from a gas source `g`. -/
def iterGasWith (g : List ℕ → Option ℕ) : Option ℕ := do
  let a ← g [6]
  let b ← g [5]
  if b ≤ a then pure (a - b) else none

/-- `iterGasWith` on `Θ`. -/
def iterGas (c : Cell) : Option ℕ := iterGasWith (thetaGasAt c)

/-- Pinned per-iteration gas of `for_sum`, `(version, optimize, codegen) ↦ gas`: a regression
snapshot whose every value must equal the same difference on the py-evm records (`MatrixTests` §3);
the rule checked is that it is constant in the trip count and above the model's iteration price. -/
def iterTable : List ((String × Bool × Codegen) × ℕ) :=
  [(("0.8.13", false, .legacy), 65), (("0.8.13", true, .legacy), 59),
   (("0.8.20", false, .legacy), 65), (("0.8.20", true, .legacy), 59),
   (("0.8.21", false, .legacy), 62), (("0.8.21", true, .legacy), 59),
   (("0.8.24", false, .legacy), 62), (("0.8.24", true, .legacy), 59),
   (("0.8.26", false, .legacy), 62), (("0.8.26", true, .legacy), 59),
   (("0.8.30", false, .legacy), 62), (("0.8.30", true, .legacy), 59),
   (("0.8.37", false, .legacy), 62), (("0.8.37", true, .legacy), 59),
   (("0.8.37", false, .ssaCfg), 53)]

/-- The Yul model's price for one `for_sum` iteration: `LT`, the branch, two `ADD`s. -/
def modelIter : ℕ := (do
  let a ← modelGas? prog_for_sum [6]
  let b ← modelGas? prog_for_sum [5]
  pure (a - b)).getD 0

/-- The input at which golden gas is taken. Every probe is a call py-evm recorded, so every golden
value has an independent counterpart (`MatrixTests` §3, provenance). -/
def probe : String → List ℕ
  | "call_inline" => [2, 2]
  | "call_rec" | "nested_call" => [3]
  | _ => [0]

/-- Golden gas values at `probe`: a **regression snapshot** (TESTING.md D3), not a source of rules.
Each value must equal the py-evm record at the same input (`oracleGasAt`), so none of them rests on
`Θ` alone. -/
def golden : List ((String × String × Bool × Codegen) × ℕ) :=
  [(("call_inline", "0.8.13", false, .legacy), 44356), (("call_inline", "0.8.13", true, .legacy), 44258),
   (("call_rec", "0.8.13", false, .legacy), 22463), (("call_rec", "0.8.13", true, .legacy), 22382),
   (("for_sum", "0.8.13", false, .legacy), 22157), (("for_sum", "0.8.13", true, .legacy), 22148),
   (("if_store", "0.8.13", false, .legacy), 28), (("if_store", "0.8.13", true, .legacy), 22),
   (("nested_call", "0.8.13", false, .legacy), 22742), (("nested_call", "0.8.13", true, .legacy), 22516),
   (("call_inline", "0.8.20", false, .legacy), 44352), (("call_inline", "0.8.20", true, .legacy), 44256),
   (("call_rec", "0.8.20", false, .legacy), 22453), (("call_rec", "0.8.20", true, .legacy), 22377),
   (("for_sum", "0.8.20", false, .legacy), 22154), (("for_sum", "0.8.20", true, .legacy), 22146),
   (("if_store", "0.8.20", false, .legacy), 27), (("if_store", "0.8.20", true, .legacy), 21),
   (("nested_call", "0.8.20", false, .legacy), 22733), (("nested_call", "0.8.20", true, .legacy), 22515),
   (("call_inline", "0.8.21", false, .legacy), 44310), (("call_inline", "0.8.21", true, .legacy), 44256),
   (("call_rec", "0.8.21", false, .legacy), 22440), (("call_rec", "0.8.21", true, .legacy), 22377),
   (("for_sum", "0.8.21", false, .legacy), 22150), (("for_sum", "0.8.21", true, .legacy), 22146),
   (("if_store", "0.8.21", false, .legacy), 22), (("if_store", "0.8.21", true, .legacy), 21),
   (("nested_call", "0.8.21", false, .legacy), 22606), (("nested_call", "0.8.21", true, .legacy), 22515),
   (("call_inline", "0.8.37", false, .legacy), 44310), (("call_inline", "0.8.37", true, .legacy), 44256),
   (("call_inline", "0.8.37", false, .ssaCfg), 44316),
   (("call_rec", "0.8.37", false, .legacy), 22440), (("call_rec", "0.8.37", true, .legacy), 22377),
   (("call_rec", "0.8.37", false, .ssaCfg), 22393),
   (("for_sum", "0.8.37", false, .legacy), 22150), (("for_sum", "0.8.37", true, .legacy), 22146),
   (("for_sum", "0.8.37", false, .ssaCfg), 22141),
   (("if_store", "0.8.37", false, .legacy), 22), (("if_store", "0.8.37", true, .legacy), 21),
   (("if_store", "0.8.37", false, .ssaCfg), 24),
   (("nested_call", "0.8.37", false, .legacy), 22605), (("nested_call", "0.8.37", true, .legacy), 22509),
   (("nested_call", "0.8.37", false, .ssaCfg), 22609)]

/-- The golden key of a cell. -/
def cellKey (c : Cell) : String × String × Bool × Codegen := (c.program, c.solc, c.optimize, c.codegen)

/-! ## §4 Preservation, executed -/

/-- `GLe` as a Boolean, for metered outcomes observed as `(slots, gas)`. -/
def gleB : Option (List ℕ × ℕ) → Option (List ℕ × ℕ) → Bool
  | none, none => true
  | some (r, g), some (r', g') => r == r' && g ≤ g'
  | _, _ => false

/-- A cost model `c'` above `cancunFn` by the increments `di` (builtins), `db` (branch), `dc`
(call). -/
def above (di db dc : ℕ) : FnCostModel :=
  { prim := fun op => cancunFn.prim op + di, branch := cancunFn.branch + db,
    call := cancunFn.call + dc }

theorem above_le (di db dc : ℕ) : cancunFn.Le (above di db dc) :=
  ⟨fun _ => Nat.le_add_right _ _, Nat.le_add_right _ _, Nat.le_add_right _ _⟩

/-- `runF_costMono` checked on a corpus program at one input, between `m` and `m'`. -/
def monoAt (m m' : FnCostModel) (prog : String) (args : List ℕ) : Bool :=
  match corpusContract prog with
  | some p => gleB (modelRun m p bigN bigD args) (modelRun m' p bigN bigD args)
  | none => false

/-! ## §6 Mutation helpers -/

/-- Replace the first occurrence of `pat` in `s` (`none` if absent). -/
def replaceFirst (s pat rep : String) : Option String :=
  match s.splitOn pat with
  | a :: rest@(_ :: _) => some (a ++ rep ++ pat.intercalate rest)
  | _ => none

/-! ## §7 Independent EVM -/

/-- Replay one py-evm point on `Θ`; `none` if success, gas and both slots agree. -/
def oracleDiff (code : ByteArray) (c : Cell) (p : OraclePoint) : Option String :=
  let what := s!"{c.name} {p.args}"
  match runCode code p.args with
  | none => some s!"{what}: Θ error"
  | some r =>
    if r.ok == p.success && r.gasUsed == p.gasUsed && [r.slot 0, r.slot 1] == p.slots then none
    else some s!"{what}: Θ (ok {r.ok}, gas {r.gasUsed}, slots {[r.slot 0, r.slot 1]}) vs py-evm \
      (ok {p.success}, gas {p.gasUsed}, slots {p.slots})"

/-! ## The suite -/

/-- Parse `tools/solc/solc-matrix.lock`: `(version, sha256, evm target, extra)` per entry. -/
def readLock : IO (List (String × String × String × String)) := do
  let t ← IO.FS.readFile ("tools" / "solc" / "solc-matrix.lock")
  return (t.splitOn "\n").filterMap fun l =>
    match (l.splitOn " ").filter (· ≠ "") with
    | [v, _, sha, evm, extra] => if v.startsWith "#" then none else some (v, sha, evm, extra)
    | _ => none

/-- Corpus programs (file stems) and their sha256, read from `tools/solc/corpus`. -/
def readCorpus : IO (List (String × String)) := do
  let mut out := []
  for e in ← ("tools" / "solc" / "corpus" : System.FilePath).readDir do
    if e.path.extension == some "yul" then
      let bytes ← IO.FS.readBinFile e.path
      let sha ← IO.ofExcept (ffi.SHA256 bytes)
      out := (e.path.fileStem.getD "", hexOf sha) :: out
  return out

end EvmYul.Solc.MatrixTests
