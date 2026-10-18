module

public import Conform.TestRunner
public import Conform.Verdict
public import Conform.Corpus
public import EvmYul.FFI.Primitives

/-!
# Entry point of the conformance runner

`lake exe conform`: finds the `BlockchainTests` JSON files, runs them through `Conform.TestRunner`,
and writes the per-phase results to `tests_N.txt`. It only parses arguments and calls the runner
(`GUIDELINES.md` Rule 7).
-/
@[expose] public section

def TestsSubdir : System.FilePath := "BlockchainTests"
def isTestFile (file : System.FilePath) : Bool := file.extension.option false (· == "json")

private def basicSuccess (name : System.FilePath)
                         (result : Std.TreeMap String EvmYul.Conform.TestResult compare) : IO Bool := do
  if result.all (λ _ v ↦ v.isNone)
  then IO.println s!"SUCCESS! - {name}"; pure true
  else pure false

private def success (result : Std.TreeMap String EvmYul.Conform.TestResult compare) : Array String × Array String :=
  let (succeeded, failed) := result.partition (λ _ v ↦ v.isNone)
  (succeeded.keysArray, failed.keysArray)

def logFile (phase : ℕ) : System.FilePath := s!"tests_{phase}.txt"

open EvmYul.Conform in
instance : ToString TestResult where
  toString tr := tr.elim "Success." id

open EvmYul.Conform in
def log (testFile : System.FilePath) (testName : String) (result : TestResult) (phase : ℕ := 0) : IO Unit :=
  IO.FS.withFile (logFile phase) .append λ h ↦ h.putStrLn s!"{testFile.fileName.get!}[{testName}] - {result}\n"

def directoryBlacklist : List System.FilePath := []

def fileBlacklist : List System.FilePath := []

def testFiles (root               : System.FilePath)
              (directoryBlacklist : Array System.FilePath := #[])
              (fileBlacklist      : Array System.FilePath := #[])
              (testBlacklist      : Array String := #[])
              (testWhitelist      : Array String := #[])
              (phase              : ℕ)
              (threads            : ℕ := 1)
              (timed              : Bool := false) : IO (Array String × Array String) := do
  let isToBeTested (testname : String) : Bool :=
    let whitelist := testWhitelist
    let blacklist := testBlacklist ++ EvmYul.Conform.GlobalBlacklist
    testname ∉ blacklist ∧ (whitelist.isEmpty ∨ testname ∈ whitelist)

  -- A phase whose root is absent (e.g. a sparse checkout without `vmPerformance/`) contributes no
  -- test instead of aborting the run; `Verdict.runExitCode` fails a run in which nothing ran.
  let testFiles ←
    if ← root.isDir then
      Array.filter isTestFile <$>
        System.FilePath.walkDir root (pure <| · ∉ directoryBlacklist)
    else
      IO.println s!"{root} does not exist; no tests in this phase."
      pure #[]

  let testFiles := testFiles.filter (· ∉ fileBlacklist)

  let mut discardedFiles : Array EvmYul.Conform.TestId := #[]
  -- Results are keyed `<file>[<test>]` (`Verdict.testKey`), the format of the log lines and of the
  -- allow-list `Verdict.expectedToFail` (review O-9: bare test names never matched it).
  let mut passedTests : Array String := .empty

  if ←System.FilePath.pathExists (logFile phase) then IO.FS.removeFile (logFile phase)

  let testJsons ← testFiles.mapM Lean.Json.fromFile
  let testNames : Array (System.FilePath × Array String) :=
    testJsons.zip testFiles |>.map
      λ (json, filepath) ↦
        match json.getObj? with
        | .error _ => panic! "Malformed test json."
        | .ok x => (filepath, x.keysArray.filter isToBeTested)  

  let mut tasks : Array (Task _) := .empty
  let mut thread := 0
  let mut tests : Array (Array (System.FilePath × String)) := .replicate threads #[]

  IO.println s!"Scheduling tests for parallel execution..."
  for (path, names) in testNames do
    for name in names do
      tests := tests.set! thread (tests[thread]! |>.push (path, name))
      thread := thread + 1; thread := thread % threads
  for i in [0:threads] do
    tasks := tasks.push (←IO.asTask <| EvmYul.Conform.processTests tests[i]! (if timed then .some i else .none))

  let mut failedTests : Array String := .empty

  IO.println s!"Scheduled {tests.foldl (· + ·.size) 0} tests on {threads} thread{if threads == 1 then "" else "s"}."
  IO.println s!"Running..."
  let testResults ← tasks.mapM (IO.wait · >>= IO.ofExcept)
  for (discarded, batch) in testResults do
    discardedFiles := discardedFiles.append discarded
    for ((file, test), res) in batch do
      log file test res phase
      let key := EvmYul.Conform.Verdict.testKey file test
      if res.isNone
      then passedTests := passedTests.push key
      else failedTests := failedTests.push key
  return (passedTests, failedTests)

def nproc : IO Nat := do
  let out ← IO.Process.output {cmd := "nproc", stdin := .null}
  return out.stdout.trimAscii.toString.toNat? |>.getD 1

def main (args : List String) : IO UInt32 := do
  -- Refuse to run against anything but the pinned corpus (`Conform.Corpus`).
  let pin ← EvmYul.Conform.Corpus.loadPin
  let status ← EvmYul.Conform.Corpus.inspect pin
  if status != .ok || args.head? == some "--check-corpus" then
    (if status == .ok then IO.println else IO.eprintln) (status.message pin)
    return status.exitCode
  IO.println (status.message pin)
  let NumThreads : ℕ := args.head? <&> String.toNat! |>.getD (←nproc)

  let DelayFiles : Array String :=
    #["static_Call50000bytesContract50_2_d1g0v0_Cancun",
      "static_Call50000bytesContract50_2_d0g0v0_Cancun",
      "static_Call50000bytesContract50_3_d1g0v0_Cancun",
      "static_Call50000_sha256_d0g0v0_Cancun",
      "static_Call50000_sha256_d1g0v0_Cancun",
      "CALLBlake2f_MaxRounds_d0g0v0_Cancun",
      "SuicideIssue_Cancun"]

  let printResults (result : Array String × Array String) : IO (Array String × Array String) := do
    let (passed, failure) := result
    let success := passed.size
    IO.println s!"Total tests: {success + failure.size}"
    IO.println s!"The post was NOT equal to the resulting state: {failure.size}"
    IO.println s!"Succeeded: {success}"
    IO.println s!"Success rate of: {(success.toFloat / (failure.size + success).toFloat) * 100.0}"
    IO.println s!"Failed tests:\n{failure}"
    return result

  IO.println s!"Phase 1/3 - No performance tests."
  let res₁ ← testFiles (root := "EthereumTests/BlockchainTests/")
                          (directoryBlacklist := #["EthereumTests/BlockchainTests//GeneralStateTests/VMTests/vmPerformance"])
                          (testBlacklist := DelayFiles)
                          (phase := 1)
                          (threads := NumThreads) >>= printResults
  
  IO.println s!"Phase 2/3 - Performance tests only."
  let res₂ ← testFiles (root := "EthereumTests/BlockchainTests/GeneralStateTests/VMTests/vmPerformance/")
                          (phase := 2)
                          (threads := NumThreads) >>= printResults


  IO.println s!"Phase 3/3 - Individually scheduled tests."
  let res₃ ← testFiles (root := "EthereumTests/BlockchainTests/")
                          (testWhitelist := DelayFiles)
                          (phase := 3)
                          (threads := NumThreads) >>= printResults

  let (passed₁, failed₁) := res₁
  let (passed₂, failed₂) := res₂
  let (passed₃, failed₃) := res₃
  let v := EvmYul.Conform.Verdict.verdict EvmYul.Conform.Verdict.expectedToFail
    (passed₁ ++ passed₂ ++ passed₃).toList (failed₁ ++ failed₂ ++ failed₃).toList
  unless v.unexpectedFailures.isEmpty do
    IO.println s!"Unexpected failures:\n{v.unexpectedFailures}"
  unless v.staleExpected.isEmpty do
    IO.println s!"Expected to fail but PASSED (remove from `Verdict.expectedToFail`):\n{v.staleExpected}"
  let ran := passed₁.size + passed₂.size + passed₃.size + failed₁.size + failed₂.size + failed₃.size
  if ran == 0 then
    IO.eprintln s!"No test ran: {EvmYul.Conform.Corpus.corpusDir}/BlockchainTests holds no fixture."
  return EvmYul.Conform.Verdict.runExitCode ran v
