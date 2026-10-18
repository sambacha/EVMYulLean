module

public import EvmYul.Maps.TrieRootModel
public meta import EvmYul.Maps.TrieRootModel
@[expose] public meta section

/-!
# Tests for the temporary-file handling of `blobComputeTrieRoot`

Run during `lake build EvmYulGasTests`; any failing check fails the build.

`blobComputeTrieRoot` hands its input to `trie_root.py` through a temporary file. It used to delete
that file only after the helper succeeded, so every failed call (Python packages missing, helper
crash, `python3` absent) left one `trieInput_*.txt` behind; one failed conformance run left 876.
These checks run `withTrieInputFile`, the IO action `blobComputeTrieRoot` now uses, in a fresh
temporary directory and require that directory to be empty after every call.

1. **Unit checks**: a succeeding command returns exactly what was written (`cat`); a command that
   exits non-zero (`false`), a command that cannot be spawned, and an input directory that does not
   exist all raise an error and leave no file.
2. **The real helper**: `trie_root.py` itself, run on the empty trie. When its Python packages are
   installed it must return the empty-trie root `56e81f17…b421`; when they are missing (the
   situation that caused the leak) it must raise an error. Either way, no file may remain.
3. **Seeded property test** (200 cases, explicit pure generator): pseudo-random hex key/value
   arrays, each run with a succeeding or failing command; the round trip through the file must be
   exact and the directory must stay empty after every call.
4. **Mutation test**: the old implementation (delete only on success) is run through the same
   property and must be caught leaking.

The same guarantee is *proved*, for every environment behaviour, over a pure file-system model in
`EvmYul.Maps.TrieRootModel` (`withTrieInputFileGen_no_leak`, `withTrieInputFileGen_result`,
`leakyWithTrieInputFileGen_leaks`). These tests check the `IO` side of that model: that the real
operations behave as the model assumes.
-/

namespace EvmYul.TrieRootTests

/-- What `writeTrieInput` must put in the file: key line, then value line, per entry. -/
def expectedSerialization (ws : Array (String × String)) : String :=
  String.join (ws.toList.map fun (k, v) => k ++ "\n" ++ v ++ "\n")

/-- `cat file`: succeeds and echoes the input file. -/
def catCmd (f : System.FilePath) : IO.Process.SpawnArgs := { cmd := "cat", args := #[f.toString] }

/-- `false`: exits with status 1, like a Python helper whose imports fail. -/
def falseCmd (_ : System.FilePath) : IO.Process.SpawnArgs := { cmd := "false" }

/-- A command that does not exist, so spawning it fails. -/
def missingCmd (_ : System.FilePath) : IO.Process.SpawnArgs :=
  { cmd := "evmyul-no-such-command-for-trie-root-tests" }

/-- The pre-fix implementation (delete only on success), in `IO`. -/
def leakyWithTrieInputFile (dir : System.FilePath) (ws : Array (String × String))
    (mkCmd : System.FilePath → IO.Process.SpawnArgs) : IO String :=
  leakyWithTrieInputFileGen dir ws mkCmd

/-- Signature shared by the fixed and the leaky implementation. -/
abbrev Impl :=
  System.FilePath → Array (String × String) → (System.FilePath → IO.Process.SpawnArgs) → IO String

/-- Number of entries in `dir`. -/
def entryCount (dir : System.FilePath) : IO Nat := return (← dir.readDir).size

/-- Run `impl`; return its result (`none` if it raised an error) and the files left in `dir`. -/
def runIn (impl : Impl) (dir : System.FilePath) (ws : Array (String × String))
    (mkCmd : System.FilePath → IO.Process.SpawnArgs) : IO (Option String × Nat) := do
  let r ← (some <$> impl dir ws mkCmd).catchExceptions fun _ => pure none
  return (r, ← entryCount dir)

/-- Sample input: two storage-slot-like entries. -/
def sample : Array (String × String) := #[("00", "2a"), ("0102", "deadbeef")]

/-- Unit checks against the fixed implementation. -/
def unitChecks : IO Unit := IO.FS.withTempDir fun dir => do
  let (r, n) ← runIn withTrieInputFile dir sample catCmd
  unless r == some (expectedSerialization sample) && n == 0 do
    throw <| IO.userError s!"cat: got {r}, {n} files left"
  let (r, n) ← runIn withTrieInputFile dir #[] catCmd
  unless r == some "" && n == 0 do
    throw <| IO.userError s!"cat on empty input: got {r}, {n} files left"
  let (r, n) ← runIn withTrieInputFile dir sample falseCmd
  unless r.isNone && n == 0 do
    throw <| IO.userError s!"failing command: got {r}, {n} files left (temporary file leaked)"
  let (r, n) ← runIn withTrieInputFile dir sample missingCmd
  unless r.isNone && n == 0 do
    throw <| IO.userError s!"unspawnable command: got {r}, {n} files left (temporary file leaked)"
  let r ← (some <$> withTrieInputFile (dir / "does-not-exist") sample catCmd).catchExceptions
    fun _ => pure none
  unless r.isNone && !(← (dir / "does-not-exist").pathExists) do
    throw <| IO.userError "missing input directory: expected an error and nothing created"
  IO.println "trie-root temp file: 5 unit checks passed (success, empty input, non-zero exit, \
    unspawnable command, missing directory)"

/-- Root of the empty Merkle-Patricia trie, `keccak256(rlp(""))`. -/
def emptyTrieRoot : String := "56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421"

/-- The real `trie_root.py`, on the empty trie, in a temporary directory; both outcomes checked. -/
def realHelperCheck : IO Unit := IO.FS.withTempDir fun dir => do
  let (r, n) ← runIn withTrieInputFile dir #[] (trieRootPythonCommand · 0)
  unless n == 0 do
    throw <| IO.userError s!"trie_root.py: {n} files left (temporary file leaked)"
  match r with
  | some out =>
    unless out.trimAscii.toString.endsWith emptyTrieRoot do
      throw <| IO.userError s!"trie_root.py on the empty trie printed {out}"
    IO.println "trie_root.py available: empty-trie root correct, no file left"
  | none =>
    IO.println "trie_root.py failed here (Python packages missing?): error raised, no file left"

/-- One step of a 64-bit linear congruential generator (Knuth's MMIX constants). An explicit,
seeded, pure generator: the cases are the same on every run, and no global RNG is used (`SA7`). -/
def lcgNext (x : Nat) : Nat := (x * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- A value in `[0, bound]` from the generator state, and the next state. -/
def draw (x bound : Nat) : Nat × Nat := let x' := lcgNext x; ((x' >>> 33) % (bound + 1), x')

/-- A pseudo-random lower-case hex string of whole bytes, fewer than `2 * maxBytes + 1` digits. -/
def genHex (x maxBytes : Nat) : String × Nat := Id.run do
  let (len, x) := draw x maxBytes
  let mut x := x
  let mut s := ""
  for _ in [0:2 * len] do
    let (d, x') := draw x 15
    x := x'
    s := s.push (Nat.toDigits 16 d).head!
  return (s, x)

/-- A pseudo-random key/value array of up to 8 entries. -/
def genEntries (x : Nat) : Array (String × String) × Nat := Id.run do
  let (n, x) := draw x 8
  let mut x := x
  let mut ws := #[]
  for _ in [0:n] do
    let (k, x1) := genHex x 32
    let (v, x2) := genHex x1 64
    x := x2
    ws := ws.push (k, v)
  return (ws, x)

/-- Seeded property: on `cases` random inputs, each with a succeeding or failing command, `impl`
returns the exact serialization on success, raises on failure, and leaves no file. Returns the
number of violating cases and how many cases used each command (so the test is not vacuous). -/
def propertyRun (impl : Impl) (cases seed : Nat) : IO (Nat × Nat × Nat) :=
  IO.FS.withTempDir fun dir => do
    let mut g := seed
    let mut bad := 0
    let mut succ := 0
    let mut fail := 0
    for _ in [0:cases] do
      let (ws, g1) := genEntries g
      let (coin, g2) := draw g1 1
      let useFail := coin == 1
      g := g2
      let (r, _) ← runIn impl dir ws (if useFail then falseCmd else catCmd)
      let n ← entryCount dir
      let ok := n == 0 && (if useFail then r.isNone else r == some (expectedSerialization ws))
      if useFail then fail := fail + 1 else succ := succ + 1
      unless ok do bad := bad + 1
      -- Clear the directory so one leak counts once.
      for e in ← dir.readDir do IO.FS.removeFile e.path
    return (bad, succ, fail)

/-- Run every check; throws on the first failure. -/
def runAll : IO Unit := do
  unitChecks
  realHelperCheck
  let (bad, succ, fail) ← propertyRun withTrieInputFile 200 20261008
  unless bad == 0 do
    throw <| IO.userError s!"property: {bad} of 200 cases violated round trip / no-leak"
  unless succ ≥ 50 && fail ≥ 50 do
    throw <| IO.userError
      s!"property: too few cases of one kind ({succ} succeeding, {fail} failing)"
  IO.println s!"property: 200 seeded cases ({succ} succeeding, {fail} failing commands), exact \
    round trip and no file left in every case"
  let (badOld, _, failOld) ← propertyRun leakyWithTrieInputFile 200 20261008
  unless badOld == failOld && badOld > 0 do
    throw <| IO.userError s!"mutant (delete only on success) not caught: {badOld} violations, \
      expected {failOld}"
  IO.println s!"mutant (delete only on success) caught: leaked on all {badOld} failing cases"

#eval runAll

end EvmYul.TrieRootTests
