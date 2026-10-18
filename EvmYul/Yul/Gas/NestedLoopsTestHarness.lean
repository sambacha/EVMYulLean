module

public import EvmYul.Yul.Gas.LoopsTestHarness
public meta import EvmYul.Yul.Gas.LoopsTestHarness
public import EvmYul.Yul.Gas.NestedLoops
public meta import EvmYul.Yul.Gas.NestedLoops

@[expose] public meta section

/-!
# Test harness of `NestedLoopsTests`

The definitions that `Gas/NestedLoopsTests.lean` runs and that other test files reuse: generators,
observers, runners, mutants and the lemmas about them. They used to live in the test file itself,
which made other test files import a test file as a fixture library; `GUIDELINES.md` Rule 3 keeps
shared fixtures in a harness module instead (layout check L10). Every declaration keeps its name and
namespace.
-/

namespace EvmYul.Yul.GasTests.NestedLoopsTests

open Plausible Ast Relational Gas LoopsTests
open EvmYul.Testing.EvmFixtures

/-- The outer loop counter. -/
def jc : Identifier := "j"

/-- A third counter, for the three-level unit test. -/
def lc : Identifier := "l"

/-- `lt(x, k)`. -/
def ltc (x : Identifier) (k : ℕ) : Expr := call .LT [.Var x, lit k]

/-- `x := add(x, 1)`. -/
def incr (x : Identifier) : List Stmt := [.Let [x] (some (call .ADD [.Var x, lit 1]))]

/-- `let x := 0`. -/
def zero (x : Identifier) : Stmt := .Let [x] (some (lit 0))

/-- The inner loop over `i`. -/
def innerFor (k₂ : ℕ) (body : List Stmt) : Stmt := .For (ltc ctr k₂) (incr ctr) body

/-- The nested program with an explicit inner body. -/
def nestWith (k₁ k₂ : ℕ) (init : List ℕ) (body : List Stmt) : Stmt :=
  .Block [loopInit init, zero jc,
    .For (ltc jc k₁) (incr jc) [zero ctr, innerFor k₂ body]]

/-- The nested program with a generated inner body. -/
def nestProg (k₁ k₂ : ℕ) (straight : Bool) (init ns : List ℕ) : Stmt :=
  nestWith k₁ k₂ init (lBody straight ns)

/-- Observable result: outcome kind, the four variables and both counters (only for the nested
programs, which define both counters). -/
def obsN : Res → String
  | .ok (.Ok ss st) =>
    s!"ok {(List.range 4).map (fun i => (lookupVar (.Ok ss st) (vr i)).toNat)} \
      i={(lookupVar (.Ok ss st) ctr).toNat} j={(lookupVar (.Ok ss st) jc).toNat}"
  | r => obs r

/-- The metered run with budget `n`, observed. -/
def mObs (n : ℕ) (p : Stmt) : Option (String × ℕ) :=
  (execL cancun n p s0).map fun (r, g) => (obsN r, g)

/-- The interpreter's observable result, `none` when it runs out of fuel. -/
def eObs (fuel : ℕ) (p : Stmt) : Option String :=
  match exec fuel p none s0 with
  | .error .OutOfFuel => none
  | r => some (obsN r)

/-- Fuel that is enough for the test programs. -/
def nestFuel (ns : List ℕ) : ℕ := 4 * ns.length + 300

/-- The largest number of body executions of a single loop entry, for break-free bodies. -/
def maxIters (k₁ k₂ : ℕ) : ℕ := if k₁ = 0 then 0 else max k₁ k₂

/-- Mutant bound: the inner loop is charged once, not once per outer iteration. -/
def onceBound (n k₁ k₂ : ℕ) (body : List Stmt) : ℕ :=
  n * (loopExitGas cancun (ltc jc k₁) + gasB cancun (incr jc)) + loopExitGas cancun (ltc jc k₁) +
    gasLS cancun n (innerFor k₂ body)

/-! ## Unit tests -/

/-- `v0 := add(v0, 2)`. -/
def addBody : List Stmt := [.Let [vr 0] (some (call .ADD [.Var (vr 0), lit 2]))]

/-- Three outer and four inner iterations. -/
def p34 : Stmt := nestWith 3 4 [0, 0, 0, 0] addBody

/-- Three by three. -/
def p33 : Stmt := nestWith 3 3 [0, 0, 0, 0] addBody

/-- An inner loop that breaks at once. -/
def pBreak : Stmt := nestWith 3 4 [0, 0, 0, 0] [.Break]

/-- Three levels, two iterations each. -/
def p222 : Stmt :=
  .Block [loopInit [0, 0, 0, 0], zero jc,
    .For (ltc jc 2) (incr jc) [zero ctr,
      .For (ltc ctr 2) (incr ctr) [zero lc, .For (ltc lc 2) (incr lc) addBody]]]

end EvmYul.Yul.GasTests.NestedLoopsTests
