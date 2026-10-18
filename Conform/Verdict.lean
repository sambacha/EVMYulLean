module

public section

/-!
# Verdict of a conformance run (review O-9)

`Conform.Main` used to compute its exit code as "failed test names minus `ExpectedToFail`". Two
defects, both found while checking the critique of O-9 against the code:

1. **The allow-list could never match.** Failures were recorded under the bare test name `<test>`,
   but the allow-list entries use the log format `<file>[<test>]`. The two never coincide, so every
   allow-listed failure still failed the run (`legacy_allowList_never_matches`, for every file and
   test name).
2. **Stale entries went unnoticed.** A test that started passing stayed on the allow-list forever.

This module is pure (no `IO`), so its behaviour is proved here and unit/property-tested during the
build (`Conform.VerdictTests`). `Conform.Main` keys every result with `testKey` and exits with
`(verdict expectedToFail passed failed).exitCode`.

The statements about the gate are quantified over every allow-list and every test key; none of them
mentions the current contents of `knownFailures`, which change whenever a model gap is closed.

A third part decides whether a rejected block was rejected **for the expected reason**
(`labelMatches`): the fixture's expected exception label, up to labels that the corpus uses for one
and the same violated rule (`synonymousLabels`).
-/

namespace EvmYul.Conform.Verdict

/-- The key a test result is reported and allow-listed under: `<file name>[<test name>]`, the same
format as the per-test log line written by `Conform.Main.log`. -/
def testKey (file : System.FilePath) (name : String) : String :=
  s!"{file.fileName.getD file.toString}[{name}]"

@[expose] section

/-- A conformance test that is known to fail. An entry is a statement about the **model**, not about
the test: `unmetRequirement` names the rule of the specification that the model does not implement
yet, so that closing the gap (implementing the rule) is what removes the entry. -/
structure KnownFailure where
  /-- The test's key (`testKey`). -/
  key : String
  /-- The specification rule (EIP / Yellow Paper / EELS) the model does not meet. -/
  unmetRequirement : String
  deriving Repr, BEq

end

/-- Tests known to fail. Empty: the last two entries were closed by implementing the rules they
violated, not by matching the tests (`Conform/TestRunner.lean`):

* the header-validity rule `H_g ≤ H_l` (`BlockException.GAS_USED_OVERFLOW`), which a block whose
  header claims more gas than its limit violates before any transaction runs;
* EIP-4844's per-block blob-gas bound, checked per transaction against what the block has left
  (`TYPE_3_TX_MAX_BLOB_GAS_ALLOWANCE_EXCEEDED`), instead of a per-transaction blob count `> 6`,
  which is not a Cancun rule. -/
def knownFailures : List KnownFailure := []

/-- The keys of `knownFailures`: the allow-list the run is compared with. -/
def expectedToFail : List String := knownFailures.map (·.key)

@[expose] section

/-- Outcome of comparing a run with the allow-list. -/
structure Verdict where
  /-- Tests that failed and are not allow-listed. -/
  unexpectedFailures : List String
  /-- Allow-listed tests that ran and **passed**: the allow-list entry is stale. -/
  staleExpected : List String
  deriving Repr, BEq

end

/-- Compare the keys of the passed and failed tests of a run with the allow-list `expected`. -/
def verdict (expected passed failed : List String) : Verdict :=
  { unexpectedFailures := failed.filter (· ∉ expected)
    staleExpected := expected.filter (· ∈ passed) }

/-- Exit code of the run: `0` exactly when nothing failed unexpectedly and no entry is stale. -/
def Verdict.exitCode (v : Verdict) : UInt32 :=
  if v.unexpectedFailures.isEmpty && v.staleExpected.isEmpty then 0 else 1

/-- The **old** exit code, kept as a specification of what was wrong: failures were bare test names,
compared with an allow-list of `<file>[<test>]` keys, and passing tests were ignored. -/
def legacyExitCode (expected failedNames : List String) : UInt32 :=
  if (failedNames.filter (· ∉ expected)).isEmpty then 0 else 1

/-- **Specification of the verdict.** A run succeeds exactly when every failure is allow-listed and
no allow-listed test passed. -/
theorem exitCode_eq_zero_iff (expected passed failed : List String) :
    (verdict expected passed failed).exitCode = 0 ↔
      (∀ k ∈ failed, k ∈ expected) ∧ (∀ k ∈ expected, k ∉ passed) := by
  simp only [Verdict.exitCode, verdict, Bool.and_eq_true, List.isEmpty_iff,
    List.filter_eq_nil_iff, decide_eq_true_eq, Decidable.not_not]
  split <;> rename_i h
  · simp only [true_iff]; exact ⟨h.1, h.2⟩
  · simp only [show (1 : UInt32) ≠ 0 by decide, false_iff]
    exact fun h' => h ⟨h'.1, h'.2⟩

/-- An allow-listed test that passes makes the run fail (stale entries are reported). -/
theorem stale_entry_fails (expected passed failed : List String) (k : String)
    (hk : k ∈ expected) (hp : k ∈ passed) :
    (verdict expected passed failed).exitCode = 1 := by
  have : (verdict expected passed failed).exitCode ≠ 0 := fun h =>
    ((exitCode_eq_zero_iff _ _ _).1 h).2 k hk hp
  simp only [Verdict.exitCode] at this ⊢
  split <;> simp_all

/-- Failures that are all allow-listed, with no stale entry, give exit code `0`. -/
theorem allowListed_failures_pass (expected passed failed : List String)
    (hf : ∀ k ∈ failed, k ∈ expected) (hp : ∀ k ∈ expected, k ∉ passed) :
    (verdict expected passed failed).exitCode = 0 :=
  (exitCode_eq_zero_iff _ _ _).2 ⟨hf, hp⟩

/-- A test's bare name is never its key: the key is strictly longer. -/
theorem name_ne_testKey (file : System.FilePath) (name : String) : name ≠ testKey file name := by
  intro h
  have hlen := congrArg String.length h
  have hl : ("[" : String).length = 1 := rfl
  have hr : ("]" : String).length = 1 := rfl
  have hs : ∀ s : String, toString s = s := fun _ => rfl
  simp only [testKey, String.length_append, hs, hl, hr] at hlen
  omega

/-- **Counterexample to the old gate, for every allow-list entry.** An allow-list keyed by
`testKey` never matched a failure recorded under the test's bare name: the allow-listed test failing
on its own — exactly the situation the entry was written for — made the old run exit with `1`. -/
theorem legacy_allowList_never_matches (file : System.FilePath) (name : String) :
    legacyExitCode [testKey file name] [name] = 1 := by
  simpa [legacyExitCode] using name_ne_testKey file name

/-- With results keyed like the allow-list, the same lone allow-listed failure gives exit code `0`,
for every test. -/
theorem keyed_allowList_matches (file : System.FilePath) (name : String) :
    (verdict [testKey file name] [] [testKey file name]).exitCode = 0 :=
  allowListed_failures_pass _ _ _ (by simp) (by simp)

/-! ## Empty runs (corpus pin follow-up)

`verdict` only looks at the tests that ran. A run in which **nothing** ran — `EthereumTests/`
missing, or a fixture subtree that matched no file — therefore had exit code `0`. `runExitCode` adds
the missing premise: at least one test must have executed. -/

/-- **Counterexample to the old gate:** a run with no tests at all exited with `0`, whatever the
allow-list. -/
theorem empty_run_passed_before (expected : List String) : (verdict expected [] []).exitCode = 0 :=
  allowListed_failures_pass _ _ _ (by simp) (by simp)

/-- Exit code of a whole run of `ran` tests: `1` if no test executed, else the verdict's. -/
def runExitCode (ran : Nat) (v : Verdict) : UInt32 :=
  if ran = 0 then 1 else v.exitCode

/-- **Specification.** A run succeeds exactly when at least one test ran and the verdict is clean. -/
theorem runExitCode_eq_zero_iff (ran : Nat) (v : Verdict) :
    runExitCode ran v = 0 ↔ 0 < ran ∧ v.exitCode = 0 := by
  unfold runExitCode
  split <;> rename_i h
  · simp only [show (1 : UInt32) ≠ 0 by decide, false_iff]; omega
  · simp only [Nat.pos_of_ne_zero h, true_and]

/-- The empty run that used to pass now fails. -/
theorem empty_run_fails (v : Verdict) : runExitCode 0 v = 1 := by simp [runExitCode]

/-! ## Was a block rejected for the expected reason?

A fixture of an invalid block names the exception it expects (`expectException`, possibly several
alternatives separated by `|`). The runner accepts a rejection when the model's exception is one of
them. A single violation can, however, satisfy the description of **more than one label**, and the
specification does not order the checks that would tell them apart. The corpus then uses either
label for the same block. An exact-label oracle would force the model to guess which label a given
fixture chose, that is, to depend on the fixture instead of on the block. Labels are therefore
compared up to the classes below. Each class must be justified by the specification alone; the
fixtures that exhibit a class are recorded in `Conform.VerdictTests`, as confirmation only. -/

/-- Classes of exception labels that name one and the same violated rule. In Cancun, EIP-4844 bounds
blob gas per block (`MAX_BLOB_GAS_PER_BLOCK = 6 · GAS_PER_BLOB`); a transaction whose blob count
exceeds 6 is exactly a transaction whose blob gas exceeds the block allowance of an otherwise empty
block, and the corpus uses both labels for it. -/
def synonymousLabels : List (List String) :=
  [["TransactionException.TYPE_3_TX_BLOB_COUNT_EXCEEDED",
    "TransactionException.TYPE_3_TX_MAX_BLOB_GAS_ALLOWANCE_EXCEEDED"]]

/-- Does the model's exception label `actual` match the fixture's alternatives `expected`, up to
`synonymousLabels`? -/
def labelMatches (expected : List String) (actual : String) : Bool :=
  expected.contains actual ||
    synonymousLabels.any fun c => c.contains actual && expected.any c.contains

/-- An exact match is always accepted. -/
theorem labelMatches_of_mem {expected : List String} {actual : String} (h : actual ∈ expected) :
    labelMatches expected actual = true := by
  simp [labelMatches, h]

/-- A label outside every synonym class matches only exactly: the classes widen nothing else. -/
theorem labelMatches_iff_of_not_synonym {expected : List String} {actual : String}
    (h : ∀ c ∈ synonymousLabels, actual ∉ c) :
    labelMatches expected actual = true ↔ actual ∈ expected := by
  constructor
  · intro hm
    simp only [labelMatches, Bool.or_eq_true, List.contains_iff_mem, List.any_eq_true,
      Bool.and_eq_true] at hm
    rcases hm with hm | ⟨c, hc, ha, -⟩
    · exact hm
    · exact absurd ha (h c hc)
  · exact labelMatches_of_mem

/-- Nothing matches a fixture that expects no exception: a block that should be valid is never
accepted as "rejected for the expected reason". -/
theorem labelMatches_nil (actual : String) : labelMatches [] actual = false := by
  simp [labelMatches]

end EvmYul.Conform.Verdict
