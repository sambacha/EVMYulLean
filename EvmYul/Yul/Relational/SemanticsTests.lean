module

public import EvmYul.Testing.EvmFixtures
public meta import EvmYul.Testing.EvmFixtures
public import EvmYul.Yul.Relational.Examples
public meta import EvmYul.Yul.Relational.Examples

@[expose] public meta section

/-!
# Regression tests for the relational Yul semantics, the WP layer and well-scopedness

These run **during `lake build EvmYulGasTests`**; any failing check fails the build.

1. **Unit tests** (named checks, each must be `true`): the interpreter on the worked example
   `doubling n` returns exactly what `doubling_exec` predicts; the `switch` quirk
   (`switch_default_error_aborts`) is observable; the scope checker accepts and rejects the
   expected programs. (The undeclared-read behaviour is covered by the theorem
   `ill_scoped_read_defaults_to_zero` rather than by running it: compiled code reports a `PANIC`
   on the out-of-bounds `s[x]!` before returning the default `0`.)
2. **Property tests** (Plausible, fixed seed): for random `n` and random fuel, `exec` on
   `doubling n` either runs out of fuel or ends with `i = n`, `x = 2n` (mirrors `doubling_exec` and
   `doubling_exec_error`); with enough fuel it always terminates (so the first property is not
   vacuous); random let-chains that only read earlier variables pass the scope checker, a read of
   a fresh variable makes them fail, and adding variables to the scope keeps them passing (mirrors
   `checkBlock_mono`).
3. **Mutation tests**: the same properties against a wrong loop body (`x := add(x, 3)`) and
   against a checker that ignores variable scopes; Plausible must find a counterexample.
-/

namespace EvmYul.Yul.RelationalTests

open Plausible EvmYul.Testing.EvmFixtures Ast Relational

/-- The initial state used by the tests: default shared state, empty variable store. -/
def s0 : State := .Ok default ∅

/-- `exec` on `doubling n` with fuel `f`: `none` when out of fuel, `some none` for any other
error, otherwise `some (some (i, x))`. -/
def runDoubling (n f : ℕ) (body : Stmt := dblBody) : Option (Option (ℕ × ℕ)) :=
  let prog : Stmt := .Block [.Let ["i"] (some (.Lit ⟨0⟩)), .Let ["x"] (some (.Lit ⟨0⟩)),
    .For (dblCond (UInt256.ofNat n)) [dblPost] [body]]
  match exec f prog none s0 with
  | .ok s => some (some ((lookupVar s "i").toNat, (lookupVar s "x").toNat))
  | .error .OutOfFuel => none
  | .error _ => some none

/-- What `doubling_exec` / `doubling_exec_error` allow for `exec` on `doubling n`. -/
def allowed (n : ℕ) : Option (Option (ℕ × ℕ)) → Bool
  | none => true
  | some (some (i, x)) => i == n && x == 2 * n
  | some none => false

/-- `allowed` on a run that did not run out of fuel (the antecedent is then visible to the counted
runner through `WhenSome`). -/
def allowedRun (n : ℕ) : Option (ℕ × ℕ) → Bool := fun r => allowed n (some r)

/-- `x := add(x, 3)`: a wrong loop body. -/
def badBody : Stmt := .Let ["x"] (some (.Call (.inl .ADD) [.Var "x", .Lit ⟨3⟩]))

/-- Variable `v k`. -/
def v (k : ℕ) : Identifier := s!"v{k}"

/-- A let-chain `let v0 := 0  let v1 := v_(r₁ % 1) ...`: statement `k` reads a variable declared
earlier (`v (r % k)`), or, when `fresh` holds for its position, the undeclared `v (k + 1000)`. -/
def letChain (rs : List ℕ) (fresh : Option ℕ := none) : List Stmt :=
  .Let [v 0] (some (.Lit ⟨0⟩)) ::
    (rs.zipIdx 1).map fun (r, k) =>
      if fresh = some k then .Let [v k] (some (.Var (v (k + 1000))))
      else .Let [v k] (some (.Call (.inl .ADD) [.Var (v (r % k)), .Lit ⟨1⟩]))

/-- A checker that ignores variable scopes (mutant): only `break`/`continue`/`leave` placement. -/
def checkIgnoringVars (p : List Stmt) : Bool :=
  (checkBlock [] {} (p.map fun
    | .Let vars (some (.Var _)) => .Let vars none
    | st => st)).isSome

/-- Named unit checks; each must evaluate to `true`. -/
def unitChecks : List (String × Bool) :=
  [ ("doubling 0 with fuel 100: i = 0, x = 0", runDoubling 0 100 == some (some (0, 0))),
    ("doubling 7 with fuel 100: i = 7, x = 14", runDoubling 7 100 == some (some (7, 14))),
    ("doubling 30 with fuel 2: out of fuel", runDoubling 30 2 == none),
    ("wrong body is caught: doubling 5 with x += 3 gives x = 15",
      runDoubling 5 100 badBody == some (some (5, 15))),
    ("switch quirk: default stop() aborts a matched empty case",
      match exec 10 switchQuirk none s0 with
      | .error (.YulHalt _ _) => true
      | _ => false),
    ("switch without the erroring default runs the matched case",
      match exec 10 (.Switch (.Lit ⟨1⟩) [(⟨1⟩, [])] []) none s0 with
      | .ok _ => true
      | _ => false),
    ("checker rejects the undeclared read", !decide (WellScoped illScopedRead)),
    ("checker accepts doubling 9", decide (WellScoped (doubling ⟨9⟩))),
    ("checker rejects top-level break", !decide (WellScoped .Break)),
    ("checker rejects top-level leave", !decide (WellScoped .Leave)),
    ("checker accepts break in a loop body",
      decide (WellScoped (.For (.Lit ⟨1⟩) [] [.Break]))),
    ("checker rejects break in a loop post block",
      !decide (WellScoped (.For (.Lit ⟨1⟩) [.Break] []))),
    ("block-local declarations are not visible after the block",
      !decide (WellScoped (.Block [.Block [.Let ["a"] none], .Let ["b"] (some (.Var "a"))]))),
    ("function bodies see parameters and may leave",
      decide (FunctionDefinition.Def ["p"] ["r"]
        [.Let ["r"] (some (.Var "p")), .Leave]).WellScoped),
    ("ScopedStmt.ofStmt? accepts doubling 3", (ScopedStmt.ofStmt? (doubling ⟨3⟩)).isSome),
    ("ScopedStmt.ofStmt? rejects the undeclared read", (ScopedStmt.ofStmt? illScopedRead).isNone)
  ]

/-- Run every check; throws on the first failure. -/
def runAll : IO Unit := do
  for (name, ok) in unitChecks do
    unless ok do throw <| IO.userError s!"unit check failed: {name}"
  IO.println s!"{unitChecks.length} unit checks passed"
  -- Mirrors `doubling_exec` and `doubling_exec_error`.
  expectHolds "exec on doubling n: out of fuel, or i = n and x = 2n"
    (∀ n f : ℕ, CountedTesting.WhenSome (runDoubling (n % 40) (f % 150)) (allowedRun (n % 40)))
  -- Non-vacuity of the property above: with enough fuel the loop terminates.
  expectHolds "exec on doubling n terminates with fuel 4n + 20"
    (∀ n : ℕ, (runDoubling (n % 40) (4 * (n % 40) + 20)).isSome = true)
  expectHolds "let-chains reading earlier variables are well scoped"
    (∀ rs : List ℕ, (checkBlock [] {} (letChain rs)).isSome = true)
  expectHolds "a read of a fresh variable makes a let-chain ill scoped"
    (∀ rs : List ℕ, ∀ k : ℕ,
      (checkBlock [] {} (letChain (0 :: rs) (some (k % (rs.length + 1) + 1)))).isNone = true)
  -- Mirrors `checkBlock_mono`.
  expectHolds "well-scoped code stays well scoped with more variables in scope"
    (∀ rs extra : List ℕ, (checkBlock (extra.map v) {} (letChain rs)).isSome = true)
  IO.println "5 property suites passed"
  -- Mutation tests.
  expectRefuted "mutant: loop body x := add(x, 3)"
    (∀ n f : ℕ, allowed (n % 40) (runDoubling (n % 40) (f % 150) badBody) = true)
  expectRefuted "mutant: checker that ignores variable scopes"
    (∀ rs : List ℕ, ∀ k : ℕ,
      (!checkIgnoringVars (letChain (0 :: rs) (some (k % (rs.length + 1) + 1)))) = true)

#eval runAll

end EvmYul.Yul.RelationalTests
