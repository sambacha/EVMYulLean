module

public import EvmYul.PerformIO
public import EvmYul.Wheels

/-!
# Trie roots through the Python helper

Computes a Merkle-Patricia trie root by writing the entries to a temporary file and running
`trie_root.py`. The file handling is written over an abstract `TrieInputOps` so that
`TrieRootModel` can prove that the temporary file is always removed.
-/

public section

/-- Write the trie input `ws` (one key line, then one value line, per entry) to `inputFile`. -/
def writeTrieInput (inputFile : System.FilePath) (ws : Array (String × String)) : IO Unit :=
  IO.FS.withFile inputFile .write λ h ↦
    forM ws.toList λ s ↦ do
      h.putStrLn s.1
      h.putStrLn s.2

/-- Fresh name for the temporary input file of one trie-root computation, inside `dir`. -/
def freshTrieInputPath (dir : System.FilePath) : IO System.FilePath := do
  let entropy ← IO.getRandomBytes 3
  let entropy' ← IO.monoNanosNow
  pure <| dir / s!"trieInput_{entropy}{entropy'}.txt"

/--
The file and process operations the trie-root helper call needs. `withTrieInputFileGen` is written
against this interface only, so the code that runs in `IO` (instance below) is literally the code
whose cleanup guarantee is proved over a pure file-system model in `EvmYul.Maps.TrieRootModel`.
-/
class TrieInputOps (m : Type → Type) where
  /-- A fresh temporary path inside a directory. -/
  freshPath : System.FilePath → m System.FilePath
  /-- Write the key/value input to a file (may create the file and then fail). -/
  writeInput : System.FilePath → Array (String × String) → m Unit
  /-- Run the helper and return its standard output (throws on failure). -/
  runCmd : IO.Process.SpawnArgs → m String
  /-- Does the path exist? -/
  pathExists : System.FilePath → m Bool
  /-- Delete a file (throws if it does not exist). -/
  removeFile : System.FilePath → m Unit

/-- The real operations. -/
@[expose] instance : TrieInputOps IO where
  freshPath := freshTrieInputPath
  writeInput := writeTrieInput
  runCmd := IO.Process.run
  pathExists p := p.pathExists
  removeFile := IO.FS.removeFile

/--
Run `mkCmd inputFile` after writing `ws` to a fresh temporary `inputFile` inside `dir`, in any monad
providing the operations.

The temporary file is removed on **every** exit path: when the command succeeds, when it exits
non-zero or cannot be spawned (the run throws), and when writing the input itself fails.
Previously the file was removed only after a successful run, so each failed call (e.g. with the
Python packages missing) leaked one `trieInput_*.txt` file. See `TrieRootModel` for the proofs.
-/
@[expose] def withTrieInputFileGen {m : Type → Type} [Monad m] [MonadFinally m] [TrieInputOps m]
    (dir : System.FilePath) (ws : Array (String × String))
    (mkCmd : System.FilePath → IO.Process.SpawnArgs) : m String := do
  let inputFile ← TrieInputOps.freshPath dir
  try
    TrieInputOps.writeInput inputFile ws
    TrieInputOps.runCmd (mkCmd inputFile)
  finally
    if ← TrieInputOps.pathExists inputFile then
      TrieInputOps.removeFile inputFile

/-- The pre-fix implementation, kept (and proved to leak in `TrieRootModel`) as a reference:
the file is removed only when the command succeeds. Not used by the interpreter. -/
@[expose] def leakyWithTrieInputFileGen {m : Type → Type} [Monad m] [TrieInputOps m]
    (dir : System.FilePath) (ws : Array (String × String))
    (mkCmd : System.FilePath → IO.Process.SpawnArgs) : m String := do
  let inputFile ← TrieInputOps.freshPath dir
  TrieInputOps.writeInput inputFile ws
  let result ← TrieInputOps.runCmd (mkCmd inputFile)
  TrieInputOps.removeFile inputFile
  pure result

/-- `withTrieInputFileGen` in `IO`: what `blobComputeTrieRoot` runs. -/
def withTrieInputFile (dir : System.FilePath) (ws : Array (String × String))
    (mkCmd : System.FilePath → IO.Process.SpawnArgs) : IO String :=
  withTrieInputFileGen dir ws mkCmd

/-- The `trie_root.py` invocation for an input file holding `n` entries. -/
def trieRootPythonCommand (inputFile : System.FilePath) (n : Nat) : IO.Process.SpawnArgs := {
  cmd := "python3",
  args := #["python/EllipticCurvesPy/trie_root.py", inputFile.toString, n.repr]
}

/-- Directory in which the temporary trie input files are created. -/
def trieInputDir : System.FilePath := "python/EllipticCurvesPy"

/-- The trie root of `ws`, computed by the Python helper, as an IO action. -/
def computeTrieRootIO (ws : Array (String × String)) : IO String :=
  /-
    Yes, this makes testing in parallel technically nondeterministic, but it is also the
    fastest to implement.

    This 'using a file trick' to get around big command line arguments should probably go
    at some point.
  -/
  withTrieInputFile trieInputDir ws (trieRootPythonCommand · ws.size)

def blobComputeTrieRoot (ws : Array (String × String)) : String :=
  totallySafePerformIO (computeTrieRootIO ws)
