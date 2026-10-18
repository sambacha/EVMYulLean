module

public import EvmYul.Venom.Category.BridgeTestHarness
public meta import EvmYul.Venom.Category.BridgeTestHarness
public import EvmYul.Venom.Category.Retract
public meta import EvmYul.Venom.Category.Retract
public import EvmYul.Venom.Text
public meta import EvmYul.Venom.Text

@[expose] public meta section

/-!
# Tests of the parse/print retract (D2.1, P2.1)

`Retract.lean` proves the categorical part: a printer with a left-inverse parser is a `Retract` in
the category of partial maps (`printParseRetract`), its normalizer `N = parse ≫ print` is
idempotent (`normalizer_idem`), and two retracts with the same normalizer are isomorphic
(`retractIsoOfSameIdempotent`). The opcode table is a proved instance (`opRetract`). For whole
functions the left-inverse law of `Text.lean` is **not proved**; these tests check it, and the
idempotence of `N` on text with trivia, on random functions. Each section names the `TESTING.md`
rule it applies.

1. **§1 Unit checks.** `i ≫ r = 𝟙` on every opcode, computed through the Kleisli composition;
   `N` of `opRetract` on a known name, an unknown name and an upper-case name; the recorded
   Vyper 0.4.3 output for `store.vy`: printing its parse and parsing again gives the same AST,
   and `N` is idempotent on it.
2. **§2 Random functions (counted, A2).** P2: `parseFunc? (printFunc f) = some f` (compared through
   `Repr`). P3: `N` is idempotent on `printFunc f` with comments, blank lines and trailing blanks
   inserted, and maps it back to `printFunc f` (trivia are quotiented out). The number of inputs
   with φs, parallel slots and inserted trivia is printed and thresholded.
3. **§3 Canaries (E1).** A printer dropping instruction outputs, and one printing upper-case
   opcodes, must each break P2.
-/

namespace EvmYul.Venom.Category.RetractTests

open CategoryTheory EvmYul.Venom.Cfg EvmYul.Venom.Category EvmYul.Venom.Category.BridgeTests
  EvmYul.Venom.Text Plausible Plausible.Decorations

/-- The normalizer `N = parse ≫ print` on function text. -/
def normFunc (t : String) : Option String := (parseFunc? t).map printFunc

/-- P2 for a printer, compared through `Repr`. -/
def roundTrips (pr : Func → String) (f : Func) : Bool :=
  (parseFunc? (pr f)).map reprStr == some (reprStr f)

/-- Insert trivia after each line, chosen by the bits of `k`: a comment, a blank line, trailing
blanks, or nothing. -/
def withTrivia (k : Nat) (t : String) : String :=
  let lines := t.splitOn "\n"
  "\n".intercalate <| (lines.zipIdx).map fun (l, j) =>
    match (k / 4 ^ (j % 16)) % 4 with
    | 0 => l ++ "   ; note " ++ toString j
    | 1 => l ++ "\n"
    | 2 => l ++ "  \t"
    | _ => l

/-- P3 on a text: `N (N t) = N t`, and `N t` is the printed function. -/
def idemOn (f : Func) (k : Nat) : Bool :=
  let t := withTrivia k (printFunc f)
  match normFunc t with
  | some n => normFunc n == some n && n == printFunc f
  | none => false

/-- `i ≫ r` of the opcode retract, computed through the Kleisli composition. -/
def opRoundTrip (o : Op) : Option Op := (opRetract.i ≫ opRetract.r) o

/-- The normalizer of the opcode retract. -/
def normOp (s : String) : Option String := normalizer opRetract s

/-- §1 unit checks. -/
def unitChecks (store : Func) (storeText : String) : List (String × Bool) :=
  [("opRetract: i ≫ r = 𝟙 on every opcode",
      allOps.all fun o => opRoundTrip o == some o),
   ("opRetract: N is the identity on \"add\" and undefined on \"frobnicate\" and \"ADD\"",
      normOp "add" == some "add" &&
      normOp "frobnicate" == none &&
      normOp "ADD" == none),
   ("store.vy: parse ≫ print ≫ parse gives the parsed AST", roundTrips printFunc store),
   ("store.vy: N is idempotent on the recorded text",
      match normFunc storeText with
      | some n => normFunc n == some n
      | none => false)]

/-- **Canary**: drop the outputs of every instruction. -/
def printNoOuts (f : Func) : String :=
  printFunc { f with blocks := f.blocks.map fun b =>
    { b with insts := b.insts.map fun i => { i with outs := [] } } }

/-- **Canary**: upper-case opcode names. -/
def printUpper (f : Func) : String :=
  "\n".intercalate <| (printFunc f).splitOn "\n" |>.map fun l =>
    match l.splitOn " = " with
    | [lhs, rhs] => lhs ++ " = " ++ rhs.toUpper
    | _ => l

/-- Run everything; throws on the first failure. -/
def runAll : IO Unit := do
  let text ← IO.FS.readFile "docs/research/venom/store_bb_runtime_0.4.3.txt"
  let some store := parseFunc? text | throw <| IO.userError "§1: the store.vy fixture does not parse"
  -- §1
  let checks := unitChecks store text
  for (name, ok) in checks do
    unless ok do throw <| IO.userError s!"§1 unit check failed: {name}"
  IO.println s!"§1 retract: {checks.length} unit checks passed"
  -- §2
  expectHolds "§2 random functions: parseFunc? (printFunc f) = some f (P2)"
    (∀ (n k₀ : Nat) (bs : List (Nat × Nat × Nat × Nat)), roundTrips printFunc (funcOf n k₀ bs) = true)
  expectHolds "§2 random functions with trivia: N idempotent and trivia quotiented out (P3)"
    (∀ (n k₀ k : Nat) (bs : List (Nat × Nat × Nat × Nat)), idemOn (funcOf n k₀ bs) k = true)
  let fs := (List.range 300).map detFunc
  let withPhi := (fs.filter fun f => f.blocks.any fun b => !b.phis.isEmpty).length
  let withPar := (fs.filter fun f => f.blocks.any fun b =>
    match b.succs with | [x, y] => x == y | _ => false).length
  let trivia := ((List.range 300).filter fun i =>
    withTrivia (mixD i) (printFunc (detFunc i)) != printFunc (detFunc i)).length
  IO.println s!"§2 coverage (300 functions): with a φ {withPhi}; with parallel slots {withPar}; \
    text changed by trivia {trivia}"
  unless withPhi ≥ 100 ∧ withPar ≥ 30 ∧ trivia ≥ 250 do
    throw <| IO.userError "§2 coverage: a region is empty or too small (A2)"
  -- §3
  expectRefuted "§3 canary: a printer dropping outputs round-trips"
    (∀ (n k₀ : Nat) (bs : List (Nat × Nat × Nat × Nat)), roundTrips printNoOuts (funcOf n k₀ bs) = true)
  expectRefuted "§3 canary: a printer with upper-case opcodes round-trips"
    (∀ (n k₀ : Nat) (bs : List (Nat × Nat × Nat × Nat)), roundTrips printUpper (funcOf n k₀ bs) = true)

#eval runAll

end EvmYul.Venom.Category.RetractTests
