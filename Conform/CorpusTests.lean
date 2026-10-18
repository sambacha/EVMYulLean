module

public import Conform.CorpusTestHarness
public meta import Conform.CorpusTestHarness
@[expose] public meta section

/-!
# Tests for the conformance-corpus pin (`Conform.Corpus`) and the empty-run gate

Run during `lake build Conform`; any failing check fails the build.

1. **The pin itself** (business assertions): the checked-in lock file names `ethereum/tests` tag
   `v14.1` at commit `9201075490807f58811078e9bb5ec895b4ac01a5`; the lakefile's `fetchTests` reads that
   same file; `.gitmodules` no longer declares a second, gitlink-based pin for `EthereumTests`;
   `EthereumTests/` is git-ignored; and README / TESTING / UPGRADE_REVIEW quote the lock's commit, so
   the documentation cannot drift from the pin unnoticed.
2. **Lock parser** unit tests: comments, `=` inside values, and rejection of a missing, duplicate,
   empty, abbreviated or upper-case commit.
3. **`classify`** unit tests and a seeded Plausible property (`classify_ok_iff`, executed), with two
   mutants that must be refuted: accepting an abbreviated hash, and ignoring whether the directory
   exists.
4. **`inspect` against real git repositories** in a temporary directory: missing directory; an empty
   `EthereumTests/` *inside another repository* (regression: `git -C` would report the outer
   repository's `HEAD`, and the test shows that naive probe does exactly that); a checkout at the pin;
   a checkout one commit later.
5. **Empty-run gate**: `runExitCode` fails a run with no test, and keeps every non-empty verdict.
-/

namespace EvmYul.Conform.CorpusTests

open Corpus Verdict Plausible Plausible.Decorations

/-- Pure unit checks; each must be `true`. -/
def unitChecks : List (String × Bool) :=
  [ ("lock: comments, blank lines and '=' inside a value",
      (parseLock s!"# c\n\nurl = https://x/y?a=b\ntag=v1\ncommit={expectedCommit}\n").toOption
        == some { url := "https://x/y?a=b", tag := "v1", commit := expectedCommit }),
    ("lock: missing commit is rejected", rejects "url=u\ntag=t\n"),
    ("lock: duplicate commit is rejected",
      rejects s!"url=u\ntag=t\ncommit={expectedCommit}\ncommit={expectedCommit}"),
    ("lock: empty url is rejected", rejects s!"url=\ntag=t\ncommit={expectedCommit}"),
    ("lock: abbreviated commit is rejected", rejects "url=u\ntag=t\ncommit=9201075"),
    ("lock: upper-case commit is rejected",
      rejects s!"url=u\ntag=t\ncommit={expectedCommit.toUpper}"),
    ("lock: a branch name is not a pin", rejects "url=u\ntag=t\ncommit=develop"),
    ("classify: missing directory", classify pin false none == .missing),
    ("classify: missing directory wins over a stale HEAD reading",
      classify pin false (some expectedCommit) == .missing),
    ("classify: directory without HEAD", classify pin true none == .notACheckout),
    ("classify: pinned commit", classify pin true (some expectedCommit) == .ok),
    ("classify: abbreviated pinned commit is not the pin",
      classify pin true (some abbrev7) == .wrongCommit abbrev7),
    ("exit code: only ok runs", [Status.missing, .notACheckout, .wrongCommit "x"].all
      (·.exitCode == 2) && Status.ok.exitCode == 0),
    ("message names the remedy", ((Status.missing.message pin).splitOn "lake run fetchTests").length
      == 2),
    ("empty run fails even with a clean verdict",
      runExitCode 0 (verdict expectedToFail [] []) == 1),
    ("the same empty run passed the old gate", (verdict expectedToFail [] []).exitCode == 0),
    ("a non-empty clean run passes", runExitCode 1 (verdict [] ["a.json[x]"] []) == 0),
    ("a non-empty failing run fails", runExitCode 5 (verdict [] [] ["a.json[x]"]) == 1) ]

/-- Run every check; throws on the first failure. -/
def runAll : IO Unit := do
  for (name, ok) in unitChecks do
    unless ok do throw <| IO.userError s!"unit check failed: {name}"
  IO.println s!"{unitChecks.length} unit checks passed"
  expectHolds "classify = ok iff the directory exists and HEAD is exactly the pin"
    (∀ (e : Bool) (n : Nat), okSpec classify e n = true)
  expectRefuted "mutant: abbreviated / empty HEAD accepted" (∀ (e : Bool) (n : Nat),
    okSpec mutPrefix e n = true)
  expectRefuted "mutant: directory existence ignored" (∀ (e : Bool) (n : Nat),
    okSpec mutNoDir e n = true)
  gitChecks
  pinChecks

#eval runAll

end EvmYul.Conform.CorpusTests
