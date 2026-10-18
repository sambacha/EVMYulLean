module

public section

/-!
# The pinned `ethereum/tests` conformance corpus

`lake exe conform` runs the JSON fixtures under `EthereumTests/`. Two defects made that unsafe:

1. **The pin did not exist.** `.gitmodules` declared an `EthereumTests` submodule and the docs said it
   was pinned to tag `v14.1`, but the repository tree held no gitlink (`git ls-files -s` lists no
   mode-`160000` entry), so `git submodule update --init EthereumTests` had no commit to check out.
   A gitlink is also lost whenever the tree is exported without its submodule metadata, which is how
   it was lost here.
2. **The runner did not check what it ran on.** With `EthereumTests/` missing or empty (an
   uninitialised submodule) it died with an uncaught `no such file or directory`; with the fixture
   directories present but holding no JSON file it ran **zero** tests and exited with `0`
   ("Success rate of: NaN"; `Verdict.empty_run_passed_before`). Both were observed with the
   pre-fix `conform` binary.

The pin now lives in one text file, `tools/ethereum-tests/ethereum-tests.lock`, read both by
`lake run fetchTests` (which fetches exactly that commit and verifies it) and by this module. Before
running anything, `Conform.Main` classifies the checkout (`classify`) and refuses to run unless
`EthereumTests/` is a git checkout whose `HEAD` is the pinned commit; after the run it refuses a run
in which no test executed (`Verdict.runExitCode`).

The decision logic is pure and proved here; `Conform.CorpusTests` tests it, the lock parser and the
`IO` probe (`inspect`) against real temporary git repositories, during `lake build Conform`.
-/

namespace EvmYul.Conform.Corpus

@[expose] section

/-- A pinned corpus: where it comes from, the release tag, and the commit that tag must resolve to. -/
structure Pin where
  /-- Clone URL of `ethereum/tests`. -/
  url : String
  /-- Release tag (informational; `fetchTests` checks that it resolves to `commit`). -/
  tag : String
  /-- Full 40-digit SHA-1 of the pinned commit. This is what the checkout is compared with. -/
  commit : String
  deriving Repr, BEq, DecidableEq

end

/-- The lock file, relative to the package root. -/
def lockPath : System.FilePath := "tools" / "ethereum-tests" / "ethereum-tests.lock"

/-- The checkout directory, relative to the package root (what `Conform.Main` walks). -/
def corpusDir : System.FilePath := "EthereumTests"

/-- `0-9` or `a-f`. -/
def isHexDigitLower (c : Char) : Bool := ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f')

/-- A full, lower-case, 40-digit SHA-1 (an abbreviated hash or a branch name is not a pin). -/
def isCommitHash (s : String) : Bool := s.length == 40 && s.all isHexDigitLower

/-- The `key=value` entries of a lock file; blank lines and `#` comments are ignored. -/
def entries (text : String) : List (String × String) :=
  (text.splitOn "\n").filterMap fun line =>
    let l := line.trimAscii.toString
    if l.isEmpty || l.startsWith "#" then none
    else match l.splitOn "=" with
      | k :: v :: rest =>
        some (k.trimAscii.toString, ("=".intercalate (v :: rest)).trimAscii.toString)
      | _ => none

/-- Parse a lock file. Every key must occur exactly once with a non-empty value, and `commit` must
be a full SHA-1 (`isCommitHash`). -/
def parseLock (text : String) : Except String Pin := do
  let es := entries text
  let get (k : String) : Except String String :=
    match es.filter (·.1 == k) with
    | [(_, v)] => if v.isEmpty then .error s!"lock: `{k}` is empty" else pure v
    | [] => .error s!"lock: missing `{k}`"
    | _ => .error s!"lock: duplicate `{k}`"
  let pin : Pin := { url := ← get "url", tag := ← get "tag", commit := ← get "commit" }
  unless isCommitHash pin.commit do
    throw s!"lock: commit `{pin.commit}` is not a full 40-digit lower-case hex SHA-1"
  return pin

@[expose] section

/-- State of the corpus checkout relative to the pin. -/
inductive Status where
  /-- `EthereumTests/` does not exist (never fetched). -/
  | missing
  /-- `EthereumTests/` exists but is not a git checkout with a readable `HEAD` (e.g. an empty
  directory left by a submodule that was never initialised, or files copied in by hand). -/
  | notACheckout
  /-- A checkout of some other commit. -/
  | wrongCommit (found : String)
  /-- A checkout of exactly the pinned commit. -/
  | ok
  deriving Repr, BEq, DecidableEq

end

/-- Decide the status from the two observations `inspect` makes: does the directory exist, and
what is its own `HEAD` commit, if any. -/
def classify (pin : Pin) (dirExists : Bool) (head? : Option String) : Status :=
  if !dirExists then .missing
  else match head? with
    | none => .notACheckout
    | some h => if h == pin.commit then .ok else .wrongCommit h

/-- Exit code of `conform` for a corpus status: `0` only for `ok`; `2` (distinct from a test
failure's `1`) when the suite was not run at all. -/
def Status.exitCode : Status → UInt32
  | .ok => 0
  | _ => 2

/-- What to tell the user, including the remedy. -/
def Status.message (pin : Pin) : Status → String
  | .ok => s!"conformance corpus: {corpusDir} is {pin.tag} ({pin.commit})"
  | .missing => s!"conformance corpus: {corpusDir}/ does not exist. Run `lake run fetchTests` \
      (pinned to {pin.tag}, {pin.commit}; see {lockPath})."
  | .notACheckout => s!"conformance corpus: {corpusDir}/ is not a git checkout. Remove it and run \
      `lake run fetchTests` (pinned to {pin.tag}, {pin.commit})."
  | .wrongCommit h => s!"conformance corpus: {corpusDir}/ is at {h}, not the pinned {pin.tag} \
      ({pin.commit}). Run `lake run fetchTests`."

/-- **Specification.** The suite runs only on a checkout whose `HEAD` is exactly the pinned commit. -/
theorem classify_ok_iff (pin : Pin) (dirExists : Bool) (head? : Option String) :
    classify pin dirExists head? = .ok ↔ dirExists = true ∧ head? = some pin.commit := by
  unfold classify
  cases dirExists <;> cases head? <;> simp

/-- A checkout of another commit is reported with the commit it is actually at. -/
theorem classify_wrongCommit (pin : Pin) (h : String) (hne : h ≠ pin.commit) :
    classify pin true (some h) = .wrongCommit h := by
  simp [classify, hne]

/-- `conform` exits with `0` before running only when the corpus is the pinned one. -/
theorem Status.exitCode_eq_zero_iff (s : Status) : s.exitCode = 0 ↔ s = .ok := by
  cases s <;> simp [Status.exitCode] <;> decide

/-! ## `IO`: reading the lock and probing the checkout -/

/-- The commit `HEAD` of `dir`'s **own** repository, or `none`.

`dir/.git` must exist: without that check, `git -C dir rev-parse HEAD` walks up to the enclosing
repository and returns *its* `HEAD`, so an empty `EthereumTests/` inside this repository would look
like a checkout (`Conform.CorpusTests` has this case as a regression test). -/
def headCommit? (dir : System.FilePath) : IO (Option String) := do
  unless ← (dir / ".git").pathExists do return none
  let out ← IO.Process.output
    { cmd := "git", args := #["-C", dir.toString, "rev-parse", "--verify", "-q", "HEAD^{commit}"] }
  if out.exitCode != 0 then return none
  return some out.stdout.trimAscii.toString

/-- Observe `dir` and classify it against `pin`. -/
def inspect (pin : Pin) (dir : System.FilePath := corpusDir) : IO Status := do
  return classify pin (← dir.isDir) (← headCommit? dir)

/-- Read and parse the lock file under `root` (the package root by default). -/
def loadPin (root : System.FilePath := ".") : IO Pin := do
  match parseLock (← IO.FS.readFile (root / lockPath)) with
  | .ok pin => return pin
  | .error e => throw <| IO.userError s!"{root / lockPath}: {e}"

end EvmYul.Conform.Corpus
