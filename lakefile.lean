import Lake
open Lake DSL System

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"v4.28.0"

/-- Clean 4.28 break: every warning (deprecations, `sorry`, linters) is a build error, and no file may
bind variables implicitly. `Audits.Upgrade` checks that these flags stay in place. The one
exception is the optional, machine-written `GeneratedEvmYul` library (`generatedLeanOptions`). -/
package «evmyul» {
  moreLeanArgs := #["-DautoImplicit=false", "-DwarningAsError=true"]
  moreServerOptions := #[⟨`autoImplicit, false⟩, ⟨`warningAsError, true⟩]
}

def cloneWithCache (pkg : NPackage __name__) (dirname url : String) : FetchM (Job GitRepo) := do
  let repoDir : GitRepo := ⟨pkg.dir / dirname⟩
  if !(← repoDir.dir.pathExists) then dbg_trace s!"Cloning: {url}"; GitRepo.clone url repoDir
  return pure repoDir

target cloneSha2 pkg : GitRepo := cloneWithCache pkg "sha2" "https://github.com/amosnier/sha-2.git"

target cloneKeccak256 pkg : GitRepo := cloneWithCache pkg "keccak256" "https://github.com/brainhub/SHA3IUF.git"

def hash256CDir (hash256repo : GitRepo) : FilePath :=
  hash256repo.dir

abbrev compiler := "cc"

target ffi.o pkg : FilePath := do
  let sha2 ← (←cloneSha2.fetch).await
  let keccak256 ← (←cloneKeccak256.fetch).await
  let oFile := pkg.buildDir / "ffi.o"
  let srcJob ← inputTextFile <| pkg.dir / "EvmYul" / "FFI" / "ffi.c"
  let weakArgs := #[
    "-I", (← getLeanIncludeDir).toString,
    "-I", sha2.dir.toString,
    "-I", keccak256.dir.toString
  ]
  buildO oFile srcJob weakArgs #["-fPIC"] compiler getLeanTrace

def buildFFILib (pkg : Package) (repo : GitRepo) (fileName : String) : FetchM (Job FilePath) := do
  let srcJob ← inputTextFile $ repo.dir / fileName |>.addExtension "c"
  let oFile := pkg.buildDir / fileName |>.addExtension "o"
  let includeArgs := #["-I", repo.dir.toString]
  let weakArgs := includeArgs
  buildO oFile srcJob weakArgs #["-fPIC"] compiler getLeanTrace

def buildSha256Obj (pkg : Package) (fileName : String) := do
  buildFFILib pkg (← (←cloneSha2.fetch).await).1 fileName

def buildKeccak256Obj (pkg : Package) (fileName : String) := do
  buildFFILib pkg (← (←cloneKeccak256.fetch).await).1 fileName

extern_lib libleanffi pkg := do
  -- In the static lib we include:
  -- the `sha-256` library itself
  let sha256O ← buildSha256Obj pkg "sha-256"
  let keccak256 ← buildKeccak256Obj pkg "sha3"
  -- our own `ffi.c`
  let ffiO ← ffi.o.fetch

  -- NB: this target used to run `git submodule update --init` (all submodules, gigabytes of test
  -- data) whenever `EthereumTests` was missing, as a side effect of building *any* executable.
  -- Fetching test data is now an explicit, opt-in step: `lake run fetchTests` (pinned in
  -- `tools/ethereum-tests/ethereum-tests.lock`).
  let name := nameToStaticLib "leanffi"
  buildStaticLib (pkg.staticLibDir / name) #[sha256O, keccak256, ffiO]

/--
The FFI primitives as a shared library that `lean` can load while elaborating (`--load-dynlib`):
the C sources (`ffi.c`, SHA-256, Keccak-256) plus the compiled Lean wrapper module
`EvmYul.FFI.Primitives`, whose exported symbols (e.g. `lp_evmyul_ffi_keccak256___boxed`) are what the
interpreter looks up when it meets an `@[extern]` declaration. Loading it lets `#eval` run the
interpreter end to end, so the FFI-bound gas tests run inside `lake build EvmYulGasTests`.
-/
target evmFFIDynlib pkg : Dynlib := do
  let some mod ← findModule? `EvmYul.FFI.Primitives
    | error "module `EvmYul.FFI.Primitives` not found"
  let wrapperO ← mod.oExport.fetch
  let sha256O ← buildSha256Obj pkg "sha-256"
  let keccak256O ← buildKeccak256Obj pkg "sha3"
  let ffiO ← ffi.o.fetch
  buildLeanSharedLib "evmffi" (pkg.sharedLibDir / nameToSharedLib "evmffi")
    #[wrapperO, sha256O, keccak256O, ffiO] #[]

/-- Conformance-test runner (`ethereum/tests` JSON fixtures); its parent file `Conform.lean` imports
every runner module (`GUIDELINES.md` §3). -/
lean_lib «Conform»

@[default_target]
lean_lib «EvmYul»

/-- The pure Lean Keccak-256 specification (`EvmYul.SpongeHash.Sponge`) as its own target
(`lake build SpongeHash`); its root is the node's parent file `EvmYul/SpongeHash.lean`. Its tests
against the C implementation run in `EvmYulGasTests` (`EvmYul.SpongeHash.SpongeTests`). -/
lean_lib «SpongeHash» where
  roots := #[`EvmYul.SpongeHash]

/--
Test modules that *execute* FFI primitives (`@[extern]` C functions) while they are elaborated.

Lake loads a library's `dynlibs` only for the modules that belong to that library, and a module
belongs to the last-declared library whose roots cover it. A test module reached only through the
test indexes is therefore compiled as part of `EvmYul`, without the FFI library, and its `#eval`
aborts ("could not find native implementation of external declaration"). These modules are named
here so they are compiled as roots of `EvmYulGasTests`. Forgetting one is not silent: the build
fails with that abort. `Audits.Layout` (L8) checks that this list holds only test modules that the
indexes reach, so it cannot become a second, hand-kept test list.
-/
def ffiTestRoots : Array Lean.Name :=
  #[`EvmYul.EVM.Gas.FFIBuildTests, `EvmYul.SpongeHash.SpongeTests, `EvmYul.Vyper.FixtureTests,
    `EvmYul.Solc.MatrixTests, `EvmYul.Venom.ThetaTests, `EvmYul.Venom.EvmMachineTests,
    `EvmYul.Venom.BlockLoweringTests, `EvmYul.Venom.TextTests,
    `EvmYul.Venom.StackLoweringTests]

/-- Gas regression suite (unit, Plausible property and mutation tests); run with
`lake build EvmYulGasTests`. Any failing check fails the build. -/
lean_lib «EvmYulGasTests» where
  -- The roots are the top-level test indexes. Each folder keeps its own index (`FTests.lean` next
  -- to `F.lean`), so adding a test edits only the index of its own folder, never this file
  -- (`GUIDELINES.md` §3; completeness is checked by `Audits.Layout`).
  roots := #[`EvmYulTests, `ConformTests, `Audits] ++ ffiTestRoots
  -- The FFI primitives are loaded into the elaborator, so the modules in `ffiTestRoots` can `#eval`
  -- the interpreter and the C hash functions during the build.
  dynlibs := #[evmFFIDynlib]

@[test_driver]
lean_exe «conform» where
  root := `Conform.Main

/-- Executable gas checks that run the interpreter (its memory and hash primitives are FFI calls,
which cannot run while the elaborator builds): `lake exe gasStepFrameTests`. -/
lean_exe «gasStepFrameTests» where
  root := `EvmYul.EVM.Gas.StepFrameTestsMain

lean_exe «yulSemanticsTests» where
  root := `EvmYul.Yul.YulSemanticsTests.Main

/-- Options for the VC generator's output (`GeneratedEvmYul`), which is machine-written and not
held to the hand-written code's lint policy:

* The generator emits one uniform proof script per statement shape (the same `simp` set and the
  same `(fuel, codeOverride)` VC signature everywhere), so in any one file some `simp` arguments and
  VC parameters go unused by design; those two linters are off.
* The `_user` files are skeletons whose `sorry`s are the proof obligations the user is meant to fill
  in, so `sorry` is reported as a warning here, not an error. Whether a correctness theorem is really
  proved is checked semantically instead, by the axiom audit `vc/PeanoAudit.lean` (run by
  `vc/test.sh`): it fails if a completed theorem depends on `sorryAx`.

Every elaboration *error* still fails the build. -/
def generatedLeanOptions : Array LeanOption :=
  #[⟨`linter.unusedSimpArgs, false⟩, ⟨`linter.unusedVariables, false⟩, ⟨`warningAsError, false⟩]

/-
The Solidity Yul-interpreter tests import modules under `GeneratedEvmYul/`, which are produced from
the `solidity` submodule's test corpus and are **not** checked in. Both targets are therefore only
declared when explicitly requested with `lake -Kgenerated=on …`; otherwise `lake build` cannot
select a target whose sources do not exist.
-/
meta if get_config? generated |>.isSome then do
  lean_lib «GeneratedEvmYul» where
    leanOptions := generatedLeanOptions
  lean_exe «solidityYulInterpreterTests» where
    root := `EvmYul.Yul.SolidityYulInterpreterTests.Main

/-- Python packages required by the precompile helpers in `python/EllipticCurvesPy`. -/
def pythonRequirements : Array String :=
  #["Crypto", "coincurve", "py_ecc", "eth_typing", "typing_extensions"]

/-- Run `git` with `args`; return its trimmed stdout, or `none` (after printing stderr) on failure. -/
def runGit (args : Array String) : IO (Option String) := do
  let out ← IO.Process.output {cmd := "git", args}
  if out.exitCode != 0 then
    IO.eprint out.stderr
    return none
  return some out.stdout.trimAscii.toString

/-- The `key=value` entries of a pin lock file (`#` comments ignored); the same format as
`Conform.Corpus.parseLock`, which the tests use to read the locks independently of this script. -/
def lockEntries (text : String) : List (String × String) :=
  (text.splitOn "\n").filterMap fun line =>
    match (line.trimAscii.toString.splitOn "=") with
    | k :: v :: rest =>
      if k.startsWith "#" then none
      else some (k.trimAscii.toString, ("=".intercalate (v :: rest)).trimAscii.toString)
    | _ => none

/--
Check out the repository pinned by `lock` (`url=`, `tag=`, `commit=`) into `dir` at **exactly** the
pinned commit.

* It fetches the lock's `tag` (shallow) and fails, leaving the checkout untouched, unless the tag
  resolves to the lock's `commit`; so a moved tag is detected rather than followed.
* With `paths` it makes a sparse, blob-filtered checkout of just those subtrees; without paths it
  checks out everything.
* Afterwards it verifies `HEAD` of `dir` itself equals the pinned commit.

Pins are deliberately not submodule gitlinks: a gitlink is lost when the tree is exported without
git metadata, which is how both the `EthereumTests` (`v14.1`) and the `solidity` pins disappeared.
-/
def fetchPinned (lock : System.FilePath) (dir : String) (paths : List String) : IO UInt32 := do
  let kv := lockEntries (← IO.FS.readFile lock)
  let (some url, some tag, some commit) := (kv.lookup "url", kv.lookup "tag", kv.lookup "commit")
    | IO.eprintln s!"{lock}: needs url=, tag= and commit=" ; return 1
  let git (xs : Array String) := runGit (#["-C", dir] ++ xs)
  unless ← (System.FilePath.mk dir / ".git").pathExists do
    IO.FS.createDirAll dir
    let some _ ← git #["init", "-q"] | return 1
    let some _ ← git #["remote", "add", "origin", url] | return 1
  let some _ ← git #["remote", "set-url", "origin", url] | return 1
  let sparse := !paths.isEmpty
  let some _ ← (if sparse then git (#["sparse-checkout", "set", "--"] ++ paths.toArray)
                else git #["sparse-checkout", "disable"]) | return 1
  let filter := if sparse then #["--filter=blob:none"] else #[]
  IO.println s!"fetching {url} tag {tag}{if sparse then s!" (sparse: {paths})" else ""} …"
  let some _ ← git (#["fetch", "-q", "--depth", "1", "--no-tags"] ++ filter ++
      #["origin", s!"+refs/tags/{tag}:refs/tags/{tag}"]) | return 1
  let some resolved ← git #["rev-parse", "--verify", s!"refs/tags/{tag}^\{commit}"] | return 1
  if resolved != commit then
    IO.eprintln s!"tag {tag} resolves to {resolved}, but {lock} pins {commit}; not checking out"
    return 1
  let some _ ← git #["-c", "advice.detachedHead=false", "checkout", "-q", "--detach", commit]
    | return 1
  let some head ← git #["rev-parse", "HEAD"] | return 1
  if head != commit then
    IO.eprintln s!"{dir} HEAD is {head} after checkout, expected {commit}"
    return 1
  IO.println s!"{dir} is at {tag} ({commit})"
  return 0

/--
`lake run fetchTests [<path> …]`: check out the `ethereum/tests` conformance corpus into
`EthereumTests/` at the commit pinned in `tools/ethereum-tests/ethereum-tests.lock` (`fetchPinned`).
With paths (e.g. `BlockchainTests/GeneralStateTests/VMTests`) the checkout is sparse (a few MB
instead of the full multi-GB corpus). `lake exe conform` refuses to run on any other state
(`Conform.Corpus`). Never run by `lake build` (TESTING.md 0.2).
-/
script fetchTests (args) do
  fetchPinned ("tools" / "ethereum-tests" / "ethereum-tests.lock") "EthereumTests" args

/-- The `solidity` subtree the VC-generator harnesses read (`vc/test-solidity-yul-interpreter.sh`). -/
def solidityCorpusPath : String := "test/libyul/yulInterpreterTests"

/--
`lake run fetchSolidity [<path> …]`: check out the Solidity repository into `solidity/` at the
commit pinned in `tools/solidity/solidity.lock` (`fetchPinned`). By default the checkout is sparse
and holds only `test/libyul/yulInterpreterTests`, the corpus of
`vc/test-solidity-yul-interpreter.sh`; that harness refuses any other checkout
(`vc/check-solidity-pin.sh`). Never run by `lake build`.
-/
script fetchSolidity (args) do
  fetchPinned ("tools" / "solidity" / "solidity.lock") "solidity"
    (if args.isEmpty then [solidityCorpusPath] else args)

/--
`lake run checkVyperFixtures [--no-latest]`: regenerate the Vyper bytecode fixtures
(`EvmYul/Vyper/Fixtures.lean`) from the compilers pinned in `tools/vyper/vyper-matrix.lock` and
fail (exit 1) if they differ from the checked-in file, if a pinned wheel's sha256 does not match, or
(unless `--no-latest`) if PyPI has a newer stable Vyper than the pinned latest. Needs network access
on first use; never run by `lake build` (TESTING.md 0.2).
-/
script checkVyperFixtures (args) do
  let gen := "tools/vyper/gen_vyper_fixtures.py"
  for step in [#[gen, "--self-test"], #[gen, "--check"] ++ args.toArray] do
    let out ← IO.Process.output {cmd := "python3", args := step}
    IO.print out.stdout
    IO.eprint out.stderr
    if out.exitCode != 0 then return out.exitCode
  return 0

/--
`lake run checkSolcFixtures [--no-latest]`: regenerate the solc Yul-lowering fixtures
(`EvmYul/Solc/Fixtures.lean`, `EvmYul/Solc/Corpus.lean`) from the compilers pinned in
`tools/solc/solc-matrix.lock` and fail (exit 1) if they differ from the checked-in files, if a pinned
binary's sha256 does not match, or (unless `--no-latest`) if binaries.soliditylang.org lists a newer
release than the pinned latest. Needs network access on first use; never run by `lake build`.
-/
script checkSolcFixtures (args) do
  let gen := "tools/solc/gen_solc_fixtures.py"
  for step in [#[gen, "--self-test"], #[gen, "--check"] ++ args.toArray] do
    let out ← IO.Process.output {cmd := "python3", args := step}
    IO.print out.stdout
    IO.eprint out.stderr
    if out.exitCode != 0 then return out.exitCode
  return 0

/--
`lake run checkPythonDeps`: fail (exit 1) unless every Python package needed by the precompile
helpers can be imported. Install them with `pip install -r requirements.txt`.
-/
script checkPythonDeps do
  let mut missing : Array String := #[]
  for m in pythonRequirements do
    let out ← IO.Process.output {cmd := "python3", args := #["-c", s!"import {m}"]}
    if out.exitCode != 0 then missing := missing.push m
  if missing.isEmpty then
    IO.println s!"all {pythonRequirements.size} Python modules importable"
    return 0
  else
    IO.eprintln s!"missing Python modules: {missing}; run `pip install -r requirements.txt`"
    return 1
