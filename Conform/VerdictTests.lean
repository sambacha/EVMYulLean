module

public import Conform.Verdict
public meta import Conform.Verdict
public import EvmYul.Testing.Counted
public meta import EvmYul.Testing.Counted
public import Plausible
public meta import Plausible

@[expose] public meta section

/-!
# Tests for the conformance-run verdict (review O-9)

Run during `lake build Conform`; any failing check fails the build.

1. **Unit tests** on a sample allow-list (never on the production list, whose contents shrink as
   model gaps are closed): `testKey` turns a fixture path and test name into exactly the allow-list
   key; the two defects of the old gate are reproduced (`legacyExitCode`) and fixed (`verdict`);
   exception labels match exactly or within a synonym class (`labelMatches`). The production list
   is checked only for its structure: well-formed distinct keys, each with the unmet requirement.
2. **Property tests** (Plausible, 300 random runs, fixed seed): the exit code is `0` exactly when
   every failure is allow-listed and no allow-listed test passed (mirrors `exitCode_eq_zero_iff`);
   `labelMatches` widens exact matching only inside a synonym class.
3. **Mutation tests**: the gate property must be refuted for the old gate (stale entries ignored)
   and for a gate that ignores the allow-list; the label property for an exact-label oracle and for
   an oracle that accepts any rejection.
-/

namespace EvmYul.Conform.VerdictTests

open Verdict Plausible Plausible.Decorations

/-- A sample allow-list for the gate's unit checks, built with `testKey` from two arbitrary fixture
paths. The gate's rules are stated for every allow-list (`Conform.Verdict`); the checks below use
this sample, not the production list, so that closing a model gap (emptying `knownFailures`) cannot
break a check of the gate itself. -/
def sampleAllowList : List String :=
  [testKey "EthereumTests/BlockchainTests/a/first.json" "first_Cancun",
   testKey "EthereumTests/BlockchainTests/b/second.json" "second_Cancun"]

/-- Named unit checks; each must evaluate to `true`. -/
def unitChecks : List (String × Bool) :=
  [ ("testKey uses the file name (not the directories) and the test name",
      testKey "EthereumTests/BlockchainTests/b/second.json" "second_Cancun"
        == "second.json[second_Cancun]"),
    ("testKey of a path without directories",
      testKey "x.json" "t" == "x.json[t]"),
    ("old gate: an allow-listed failure recorded under its bare name still failed the run",
      legacyExitCode sampleAllowList ["second_Cancun"] == 1),
    ("new gate: the same failure, keyed, passes",
      (verdict sampleAllowList [] [sampleAllowList[1]!]).exitCode == 0),
    ("new gate: all allow-listed failures pass",
      (verdict sampleAllowList ["c.json[x]"] sampleAllowList).exitCode == 0),
    ("new gate: an unexpected failure fails the run",
      (verdict sampleAllowList [] ["c.json[x]"]).exitCode == 1),
    ("new gate: an allow-listed test that now passes is reported as stale",
      (verdict sampleAllowList [sampleAllowList[0]!] []).staleExpected == [sampleAllowList[0]!]),
    ("old gate: the stale entry went unnoticed",
      legacyExitCode sampleAllowList [] == 0),
    ("an allow-listed test that did not run is not stale",
      (verdict sampleAllowList [] []).exitCode == 0),
    -- Exception labels (`labelMatches`).
    ("label: an exact alternative matches",
      labelMatches ["BlockException.A", "BlockException.B"] "BlockException.B"),
    ("label: a different label does not match",
      !labelMatches ["BlockException.A"] "BlockException.B"),
    -- Confirmation of the blob-limit class of `synonymousLabels`: the Cancun fixtures
    -- `invalid_tx_blob_count[too_many_blobs]` and `invalid_block_blob_count[(7,)]` carry
    -- field-for-field identical seven-blob transactions, alone in their blocks, yet expect
    -- `TYPE_3_TX_BLOB_COUNT_EXCEEDED` and `TYPE_3_TX_MAX_BLOB_GAS_ALLOWANCE_EXCEEDED` respectively.
    ("label: the two Cancun blob-limit labels match each other, both ways",
      labelMatches ["TransactionException.TYPE_3_TX_MAX_BLOB_GAS_ALLOWANCE_EXCEEDED"]
          "TransactionException.TYPE_3_TX_BLOB_COUNT_EXCEEDED" &&
        labelMatches ["TransactionException.TYPE_3_TX_BLOB_COUNT_EXCEEDED"]
          "TransactionException.TYPE_3_TX_MAX_BLOB_GAS_ALLOWANCE_EXCEEDED"),
    ("label: a blob-limit label does not match an unrelated expectation",
      !labelMatches ["TransactionException.TYPE_3_TX_ZERO_BLOBS"]
          "TransactionException.TYPE_3_TX_BLOB_COUNT_EXCEEDED"),
    ("label: nothing matches a block expected to be valid",
      !labelMatches [] "TransactionException.TYPE_3_TX_BLOB_COUNT_EXCEEDED") ]

/-- Structural rules for the production allow-list, whatever its contents: every key has the
`<file>.json[<test>]` shape `testKey` produces, keys are distinct, and every entry names the rule
the model does not meet (an entry without a reason is a patched test, not a known gap). -/
def knownFailuresWellFormed : List (String × Bool) :=
  [("every known failure has a testKey-shaped key",
      knownFailures.all fun f => (f.key.splitOn ".json[").length == 2 && f.key.endsWith "]"),
   ("known-failure keys are distinct", expectedToFail.eraseDups.length == expectedToFail.length),
   ("every known failure names the unmet requirement",
      knownFailures.all fun f => !f.unmetRequirement.trimAscii.isEmpty)]

/-- Exception labels from small numbers: the two Cancun blob-limit synonyms and two unrelated
labels, so that random lists hit every case of `labelMatches`. -/
def labels (xs : List Nat) : List String :=
  xs.map fun n => match n % 4 with
    | 0 => "TransactionException.TYPE_3_TX_BLOB_COUNT_EXCEEDED"
    | 1 => "TransactionException.TYPE_3_TX_MAX_BLOB_GAS_ALLOWANCE_EXCEEDED"
    | k => s!"BlockException.L{k}"

/-- `labelMatches` widens an exact match only inside a synonym class
(`labelMatches_iff_of_not_synonym`, executed): it holds iff `actual` is expected, or `actual` and
some expected label share a class. -/
def labelSpec (match? : List String → String → Bool) (e : List Nat) (a : Nat) : Bool :=
  let (e, a) := (labels e, (labels [a]).headD "")
  let cls (l : String) : Option Nat := synonymousLabels.findIdx? (·.contains l)
  match? e a == (e.contains a || (cls a).isSome && e.any (cls · == cls a))

/-- Small random keys, so that allow-list, passed and failed lists overlap often. -/
def keys (xs : List Nat) : List String := xs.map fun n => s!"f.json[t{n % 5}]"

/-- `exitCode_eq_zero_iff`, executed. -/
def verdictSpec (gate : List String → List String → List String → UInt32)
    (e p f : List Nat) : Bool :=
  let (e, p, f) := (keys e, keys p, keys f)
  (gate e p f == 0) == (f.all (· ∈ e) && e.all (· ∉ p))

/-- `expectHolds`/`expectRefuted` with a fixed seed. -/
def cfg : Configuration := { numInst := 300, maxSize := 20, randomSeed := some 20261002,
                             quiet := true }

/-- Fail the build on a counterexample, or when fewer than `minValid` inputs (default: half of the
samples) satisfied the property's guards; print `total/valid/discarded` (`CountedTesting`). -/
def expectHolds (name : String) (p : Prop)
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p']
    (minValid : Nat := CountedTesting.defaultMinValid cfg) : IO Unit :=
  discard <| CountedTesting.holdsCore cfg name p' minValid

/-- Mutation test: fail the build unless a counterexample is found (counts printed). -/
def expectRefuted (name : String) (p : Prop)
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] : IO Unit :=
  discard <| CountedTesting.refutedCore cfg name p'

/-- Run every check; throws on the first failure. -/
def runAll : IO Unit := do
  for (name, ok) in unitChecks ++ knownFailuresWellFormed do
    unless ok do throw <| IO.userError s!"unit check failed: {name}"
  IO.println s!"{unitChecks.length + knownFailuresWellFormed.length} unit checks passed \
    ({knownFailures.length} known failures)"
  expectHolds "exit code 0 iff failures allow-listed and no stale entry"
    (∀ e p f : List Nat, verdictSpec (fun e p f => (verdict e p f).exitCode) e p f = true)
  expectRefuted "mutant: old gate (stale entries ignored)"
    (∀ e p f : List Nat, verdictSpec (fun e _ f => legacyExitCode e f) e p f = true)
  expectRefuted "mutant: allow-list ignored"
    (∀ e p f : List Nat, verdictSpec (fun _ p f => (verdict [] p f).exitCode) e p f = true)
  expectHolds "labelMatches = exact match, widened only within a synonym class"
    (∀ (e : List Nat) (a : Nat), labelSpec labelMatches e a = true)
  expectRefuted "mutant: exact-label oracle (no synonym classes)"
    (∀ (e : List Nat) (a : Nat), labelSpec (fun e a => e.contains a) e a = true)
  expectRefuted "mutant: any rejection accepted, whatever its label"
    (∀ (e : List Nat) (a : Nat), labelSpec (fun e _ => !e.isEmpty) e a = true)

#eval runAll

end EvmYul.Conform.VerdictTests
