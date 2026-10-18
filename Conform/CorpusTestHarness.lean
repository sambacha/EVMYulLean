module

public import Conform.Corpus
public meta import Conform.Corpus
public import Conform.Verdict
public meta import Conform.Verdict
public import EvmYul.Testing.Counted
public meta import EvmYul.Testing.Counted
public import Plausible
public meta import Plausible

@[expose] public meta section

/-!
# Test harness of `CorpusTests`

The definitions that `CorpusTests.lean` runs and that other test files reuse: generators, observers,
runners, mutants and the lemmas about them. They used to live in the test file itself, which made
other test files import a test file as a fixture library; `GUIDELINES.md` Rule 3 keeps shared
fixtures in a harness module instead (layout check L10). Every declaration keeps its name and
namespace.
-/

namespace EvmYul.Conform.CorpusTests

open Corpus Verdict Plausible Plausible.Decorations

/-- The pinned release, as the business requirement states it. -/
def expectedTag : String := "v14.1"

/-- The commit `v14.1` resolves to (`git ls-remote https://github.com/ethereum/tests.git v14.1`). -/
def expectedCommit : String := "9201075490807f58811078e9bb5ec895b4ac01a5"

/-- The 7-digit abbreviation `git log --oneline` shows. -/
def abbrev7 : String := (expectedCommit.take 7).toString

/-- A pin used by the pure tests. -/
def pin : Pin := { url := "u", tag := "t", commit := expectedCommit }

/-- `true` iff `parseLock` rejects `text`. -/
def rejects (text : String) : Bool := (parseLock text).toOption.isNone

/-- Candidate `HEAD` readings: the pin, an abbreviation of it, the empty string, another commit. -/
def headOf (n : Nat) : Option String :=
  match n % 5 with
  | 0 => none
  | 1 => some expectedCommit
  | 2 => some abbrev7
  | 3 => some ""
  | _ => some "0000000000000000000000000000000000000000"

/-- `classify_ok_iff`, executed for a classifier `c`. -/
def okSpec (c : Pin → Bool → Option String → Status) (e : Bool) (n : Nat) : Bool :=
  (c pin e (headOf n) == .ok) == (e && headOf n == some pin.commit)

/-- Mutant: accepts any prefix of the pinned commit (an abbreviated hash, or an empty reading). -/
def mutPrefix (p : Pin) (e : Bool) (h? : Option String) : Status :=
  if !e then .missing else match h? with
    | none => .notACheckout
    | some h => if p.commit.startsWith h then .ok else .wrongCommit h

/-- Mutant: does not look at whether the directory exists. -/
def mutNoDir (p : Pin) (_ : Bool) (h? : Option String) : Status := classify p true h?

/-- Seeded configuration (`TESTING.md` E3). -/
def cfg : Configuration := { numInst := 200, maxSize := 20, randomSeed := some 20261008,
                             quiet := true }

/-- Fail the build on a counterexample or too few valid inputs (`CountedTesting`). -/
def expectHolds (name : String) (p : Prop)
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p']
    (minValid : Nat := CountedTesting.defaultMinValid cfg) : IO Unit :=
  discard <| CountedTesting.holdsCore cfg name p' minValid

/-- Mutation test: fail the build unless a counterexample is found. -/
def expectRefuted (name : String) (p : Prop)
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] : IO Unit :=
  discard <| CountedTesting.refutedCore cfg name p'

/-- Run `git` in `dir`; throw (failing the build) if it fails. -/
def git (dir : System.FilePath) (args : Array String) : IO String := do
  let out ← IO.Process.output
    { cmd := "git", args := #["-C", dir.toString, "-c", "user.name=t", "-c", "user.email=t@t",
                              "-c", "commit.gpgsign=false"] ++ args }
  unless out.exitCode == 0 do
    throw <| IO.userError s!"git {args} in {dir} failed: {out.stderr}"
  return out.stdout.trimAscii.toString

/-- Make a repository in `dir` with one commit; return the commit. -/
def mkRepo (dir : System.FilePath) : IO String := do
  IO.FS.createDirAll dir
  discard <| git dir #["init", "-q"]
  IO.FS.writeFile (dir / "README") "fixture\n"
  discard <| git dir #["add", "README"]
  discard <| git dir #["commit", "-q", "-m", "c1"]
  git dir #["rev-parse", "HEAD"]

/-- `inspect` on real directories and repositories. -/
def gitChecks : IO Unit := IO.FS.withTempDir fun tmp => do
  -- An outer repository, standing for this project's own checkout.
  let outer := tmp / "outer"
  let outerHead ← mkRepo outer
  let corpus := outer / "EthereumTests"
  let st ← inspect pin corpus
  unless st == .missing do throw <| IO.userError s!"missing dir classified as {repr st}"
  -- An empty `EthereumTests/` inside the outer repository (an uninitialised submodule).
  IO.FS.createDirAll corpus
  let naive ← IO.Process.output
    { cmd := "git", args := #["-C", corpus.toString, "rev-parse", "HEAD"] }
  unless naive.exitCode == 0 && naive.stdout.trimAscii.toString == outerHead do
    throw <| IO.userError "regression premise: `git -C` on a nested empty dir no longer reports the \
      outer HEAD; re-examine headCommit?"
  let st ← inspect { pin with commit := outerHead } corpus
  unless st == .notACheckout do
    throw <| IO.userError s!"empty nested dir classified as {repr st} (outer HEAD leaked)"
  -- A real checkout at the pin, then one commit later.
  let inner ← mkRepo corpus
  let pinned : Pin := { pin with commit := inner }
  let st ← inspect pinned corpus
  unless st == .ok do throw <| IO.userError s!"checkout at the pin classified as {repr st}"
  IO.FS.writeFile (corpus / "README") "moved\n"
  discard <| git corpus #["commit", "-q", "-am", "c2"]
  let moved ← git corpus #["rev-parse", "HEAD"]
  let st ← inspect pinned corpus
  unless st == .wrongCommit moved do
    throw <| IO.userError s!"checkout past the pin classified as {repr st}"
  IO.println "inspect on real repositories: missing, nested empty dir (outer HEAD not leaked), \
    pinned checkout, moved checkout all classified correctly"

/-- The repository's own pin and every place that must agree with it. -/
def pinChecks : IO Unit := do
  let p ← loadPin
  unless p.tag == expectedTag && p.commit == expectedCommit &&
      p.url == "https://github.com/ethereum/tests.git" do
    throw <| IO.userError s!"{lockPath} pins {repr p}, expected ethereum/tests {expectedTag} \
      ({expectedCommit})"
  let contains (f : System.FilePath) (needle : String) : IO Bool :=
    return ((← IO.FS.readFile f).splitOn needle).length > 1
  unless ← contains "lakefile.lean" "\"ethereum-tests.lock\"" do
    throw <| IO.userError "lakefile.lean: fetchTests does not read ethereum-tests.lock"
  -- `.gitmodules` may be absent altogether: no submodule pins remain (`solidity` uses a lock too).
  -- (Nested `if`s: in `a && (← b)` the `← b` is run before `a` is looked at.)
  if ← (".gitmodules" : System.FilePath).pathExists then
    if ← contains ".gitmodules" "EthereumTests" then
      throw <| IO.userError ".gitmodules declares EthereumTests: a second pin, separate from the lock"
  unless ← contains ".gitignore" "EthereumTests/" do
    throw <| IO.userError ".gitignore does not ignore the fetched corpus EthereumTests/"
  for doc in ["README.md", "TESTING.md", "docs/toolchain/UPGRADE_REVIEW.md"] do
    unless (← contains doc p.commit) && (← contains doc lockPath.toString) do
      throw <| IO.userError s!"{doc} does not quote the pinned commit {p.commit} and {lockPath}"
  IO.println s!"pin: {lockPath} = ethereum/tests {p.tag} ({p.commit}); lakefile, .gitmodules, \
    .gitignore and 3 docs agree"

end EvmYul.Conform.CorpusTests
