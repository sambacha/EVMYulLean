module

public import Conform.CorpusTestHarness
public meta import Conform.CorpusTestHarness

@[expose] public meta section

/-!
# Tests for the `solidity` corpus pin (`tools/solidity/solidity.lock`)

The Solidity Yul-interpreter harnesses (`vc/test-solidity-yul-interpreter.sh` and, through the
generated modules, the `solidityYulInterpreterTests` executable) read
`solidity/test/libyul/yulInterpreterTests`. That directory used to come from a `solidity` git
submodule whose gitlink had been lost (no mode-`160000` entry in the tree), so there was no commit to
check out and the harness's expected-pass baseline referred to no particular corpus. This is the same
defect `Conform.Corpus` fixed for `EthereumTests/`, and it is fixed the same way: a lock file read by
`lake run fetchSolidity` (the shared `fetchPinned` in the lakefile) and by a guard,
`vc/check-solidity-pin.sh`, which the harness runs before anything else.

Run during `lake build Conform`; any failing check fails the build.

1. **The pin** (business assertions): the lock names `argotorg/solidity` tag `v0.8.35` at commit
   `47b9dedda00ef23974eca07c06c97cc1c80088b4`; the lakefile's `fetchSolidity` reads it; `.gitmodules`
   declares no `solidity` submodule; `solidity/` is git-ignored; the harness runs the guard; and
   `vc/README.md` quotes the lock and its commit.
2. **The guard on real git repositories**, in a temporary repository root: missing `solidity/`; an
   empty `solidity/` *inside another repository* whose `HEAD` is the pinned commit (regression: a
   naive `git -C` probe reports the outer `HEAD`); a checkout at the pin; one commit later; a lock
   with an abbreviated commit. Each exit code must equal the one `Conform.Corpus.classify` assigns to
   the same directory (`Status.exitCode`), observed with `Conform.Corpus.inspect`: two independent
   implementations of one specification (`classify_ok_iff`) must agree.
3. **Planted mutants of the guard**, each of which must fail some scenario: the `.git` check removed,
   the commit comparison removed, and the lock validation removed.
-/

namespace EvmYul.Conform.SolidityPinTests

open Corpus

/-- The lock file, relative to the package root. -/
def solidityLockPath : System.FilePath := "tools" / "solidity" / "solidity.lock"

/-- The guard script, relative to the package root. -/
def guardPath : System.FilePath := "vc" / "check-solidity-pin.sh"

/-- The pinned release, as the business requirement states it. -/
def expectedTag : String := "v0.8.35"

/-- The commit `v0.8.35` resolves to
(`git ls-remote https://github.com/argotorg/solidity.git v0.8.35`). -/
def expectedCommit : String := "47b9dedda00ef23974eca07c06c97cc1c80088b4"

/-- `needle` occurs in `hay`. -/
def containsStr (hay needle : String) : Bool := (hay.splitOn needle).length > 1

/-- `git check-ignore --no-index` on `path`: `some true` ignored, `some false` not, `none` if git
failed (a failure of the oracle is reported, not read as either answer). -/
def gitIgnores (path : String) : IO (Option Bool) := do
  let r ← IO.Process.output { cmd := "git", args := #["check-ignore", "-q", "--no-index", path] }
  return match r.exitCode with
    | 0 => some true
    | 1 => some false
    | _ => none

/-- The repository's own pin and every place that must agree with it. -/
def pinChecks : IO Unit := do
  let p ← match parseLock (← IO.FS.readFile solidityLockPath) with
    | .ok p => pure p
    | .error e => throw <| IO.userError s!"{solidityLockPath}: {e}"
  unless p.tag == expectedTag && p.commit == expectedCommit &&
      p.url == "https://github.com/argotorg/solidity.git" do
    throw <| IO.userError s!"{solidityLockPath} pins {repr p}, expected argotorg/solidity \
      {expectedTag} ({expectedCommit})"
  let lakefile ← IO.FS.readFile "lakefile.lean"
  unless containsStr lakefile "script fetchSolidity" && containsStr lakefile "\"solidity.lock\"" do
    throw <| IO.userError "lakefile.lean: no fetchSolidity script reading solidity.lock"
  if ← (".gitmodules" : System.FilePath).pathExists then
    if containsStr (← IO.FS.readFile ".gitmodules") "solidity" then
      throw <| IO.userError ".gitmodules declares solidity: a second pin, separate from the lock"
  unless (← gitIgnores "solidity/test/libyul/yulInterpreterTests/smoke.yul") == some true do
    throw <| IO.userError ".gitignore does not ignore the fetched corpus solidity/"
  let harness ← IO.FS.readFile ("vc" / "test-solidity-yul-interpreter.sh")
  unless containsStr harness "check-solidity-pin.sh" do
    throw <| IO.userError "vc/test-solidity-yul-interpreter.sh does not run the pin guard"
  let readme ← IO.FS.readFile ("vc" / "README.md")
  unless containsStr readme p.commit && containsStr readme solidityLockPath.toString &&
      containsStr readme "lake run fetchSolidity" do
    throw <| IO.userError s!"vc/README.md does not quote {solidityLockPath}, its commit \
      {p.commit} and `lake run fetchSolidity`"
  IO.println s!"solidity pin: {solidityLockPath} = argotorg/solidity {p.tag} ({p.commit}); \
    lakefile, .gitmodules, .gitignore, harness and vc/README.md agree"

/-- A lock pinning `commit`. -/
def lockText (commit : String) : String :=
  s!"# fixture\nurl=https://example.invalid/solidity.git\ntag=v0\ncommit={commit}\n"

/-- Write `root/tools/solidity/solidity.lock` pinning `commit`. -/
def writeLock (root : System.FilePath) (commit : String) : IO Unit := do
  IO.FS.createDirAll (root / "tools" / "solidity")
  IO.FS.writeFile (root / solidityLockPath) (lockText commit)

/-- Run the guard script at `guard` (absolute) on the repository root `root`; its exit code. -/
def runGuard (guard root : System.FilePath) : IO UInt32 := do
  let out ← IO.Process.output { cmd := "sh", args := #[guard.toString, root.toString] }
  return out.exitCode

/-- The scenarios; returns the failures (empty: the guard under test is correct). In every scenario
with a well-formed lock the guard's exit code must equal `classify`'s, read off the same directory by
`inspect`. -/
def scenarioFailures (guard tmp : System.FilePath) : IO (List String) := do
  let mut fails : List String := []
  let root := tmp / "root"
  let rootHead ← CorpusTests.mkRepo root
  let corpus := root / "solidity"
  -- the oracle: `classify` on what `inspect` observes, for a pin of `commit`
  let oracle (commit : String) : IO UInt32 := do
    return (← inspect { url := "u", tag := "t", commit } corpus).exitCode
  let check (name : String) (commit : String) (expected : UInt32) : IO (List String) := do
    writeLock root commit
    let got ← runGuard guard root
    let want ← oracle commit
    let mut fs := []
    unless want == expected do fs := fs ++ [s!"{name}: oracle premise broken: classify gives {want}"]
    unless got == expected do fs := fs ++ [s!"{name}: guard exit {got}, expected {expected}"]
    return fs
  -- G1 missing directory
  fails := fails ++ (← check "G1 missing solidity/" rootHead 2)
  -- G2 empty `solidity/` inside the outer repository, the lock pinning the *outer* HEAD
  IO.FS.createDirAll corpus
  fails := fails ++ (← check "G2 empty nested solidity/ (outer HEAD must not leak)" rootHead 2)
  -- G3 a checkout at the pin, G4 one commit later
  let inner ← CorpusTests.mkRepo corpus
  fails := fails ++ (← check "G3 checkout at the pin" inner 0)
  IO.FS.writeFile (corpus / "README") "moved\n"
  discard <| CorpusTests.git corpus #["commit", "-q", "-am", "c2"]
  fails := fails ++ (← check "G4 checkout past the pin" inner 2)
  -- G5 a malformed lock (abbreviated commit of the actual HEAD): rejected before probing
  let moved ← CorpusTests.git corpus #["rev-parse", "HEAD"]
  writeLock root (moved.take 7).toString
  let got ← runGuard guard root
  unless got == 1 do fails := fails ++ [s!"G5 abbreviated commit in the lock: guard exit {got}"]
  return fails

/-- Planted mutants of the guard (E1): a name and a text substitution. Each substitution must occur
in the real script, so a mutant cannot silently be the unchanged script. -/
def guardMutants : List (String × String × String) :=
  [("no .git check (outer HEAD leaks)", "[ ! -e \"$dir/.git\" ] || ", ""),
   ("commit not compared", "if [ \"$head\" != \"$commit\" ]; then", "if false; then"),
   ("lock commit not validated", "grep -Eqx '[0-9a-f]{40}'", "true")]

/-- Run the guard scenarios on the real script and on every mutant; throws on the first failure. -/
def guardChecks : IO Unit := IO.FS.withTempDir fun tmp => do
  let cwd ← IO.currentDir
  let real := cwd / guardPath
  let script ← IO.FS.readFile real
  let fs ← scenarioFailures real (tmp / "real")
  unless fs.isEmpty do throw <| IO.userError s!"vc/check-solidity-pin.sh fails: {fs}"
  let mut killed : List String := []
  let mut k := 0
  for (name, a, b) in guardMutants do
    k := k + 1
    unless containsStr script a do
      throw <| IO.userError s!"mutant '{name}': {a} does not occur in {guardPath}"
    let m := tmp / s!"mutant{k}.sh"
    IO.FS.writeFile m (script.replace a b)
    let mfs ← scenarioFailures m (tmp / s!"run{k}")
    match mfs with
    | [] => throw <| IO.userError s!"E1: undetected mutant of the solidity pin guard: {name}"
    | f :: _ => killed := killed ++ [s!"  killed: {name} ({f})"]
  IO.println s!"solidity pin guard: 5 scenarios agree with Corpus.classify on real repositories; \
    mutation adequacy {killed.length}/{guardMutants.length}\n{"\n".intercalate killed}"

/-- Run every check; throws on the first failure. -/
def runAll : IO Unit := do
  pinChecks
  guardChecks

#eval runAll

end EvmYul.Conform.SolidityPinTests
