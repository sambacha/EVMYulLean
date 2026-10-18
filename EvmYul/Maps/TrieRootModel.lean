module

public import EvmYul.Maps.TrieRoot
public section

/-!
# The trie-root temporary file is always cleaned up (formal proof over a file-system model)

`blobComputeTrieRoot` runs `withTrieInputFileGen` in `IO`. Here the *same* definition is run in a
pure model monad, and its cleanup behaviour is proved for **every** environment behaviour.

## The model

* The file system is the set of existing paths, `FS := System.FilePath → Bool`.
* The monad is `ExceptT String (StateM FS)`: an operation may throw, and the file system **keeps**
  the changes made before the throw (as the real world does in `IO`; note that
  `StateT FS (Except String)` would instead roll the state back on an exception and could not
  express a leak at all).
* An environment `Env` fixes, arbitrarily, how each operation behaves:
  - `fresh`: the path the fresh-name generator returns;
  - `writeCreates` / `writeFails`: whether writing the input creates the file, and whether it then
    throws (all four combinations are allowed: success; creating the file then failing, e.g. a full
    disk; failing before creating it, e.g. a missing directory; and the degenerate fourth case);
  - `run`: the outcome of running the helper, any `Except String String`, depending on the
    command (success with any output, or failure with any message: non-zero exit, unspawnable
    command, missing Python packages, …).
* `pathExists` reads the file system, and `removeFile` deletes the file or throws if it is absent,
  as `IO.FS.removeFile` does.

## Results

* `withTrieInputFileGen_fs`: after the call, the file system is the initial one with `env.fresh`
  removed — in every environment. Hence `withTrieInputFileGen_no_leak`: if the fresh path did not
  exist before, the file system is exactly as before.
* `withTrieInputFileGen_result`: the call returns the helper's outcome, unless writing the input
  failed, in which case it returns that error.
* `leakyWithTrieInputFileGen_leaks`: the pre-fix code leaves `env.fresh` behind whenever the input
  is written and the helper fails; `leaky_counterexample` is a concrete instance.

The trusted step is the correspondence between the model operations and the `IO` instance of
`TrieInputOps`; the control flow (`try … finally`, the existence check, the order of operations) is
the verified definition itself.
-/

namespace EvmYul.TrieRootModel

/-- The file system: which paths exist. -/
abbrev FS := System.FilePath → Bool

/-- The model monad: exceptions that keep the file-system changes made before them. -/
abbrev M := ExceptT String (StateM FS)

/-- How the environment behaves (arbitrary). -/
structure Env where
  /-- Path returned by the fresh-name generator. -/
  fresh : System.FilePath
  /-- Writing the input creates the file. -/
  writeCreates : Bool
  /-- Writing the input throws (after creating the file, if `writeCreates`). -/
  writeFails : Bool
  /-- Error message of a failed write. -/
  writeErr : String
  /-- Outcome of running the helper command. -/
  run : IO.Process.SpawnArgs → Except String String

/-- `fs` with `p` added. -/
def addPath (fs : FS) (p : System.FilePath) : FS := fun q => fs q || q == p

/-- `fs` with `p` removed. -/
def erasePath (fs : FS) (p : System.FilePath) : FS := fun q => fs q && q != p

/-- The model operations of environment `env`. -/
def modelOps (env : Env) : TrieInputOps M where
  freshPath _ := pure env.fresh
  writeInput p _ := do
    if env.writeCreates then modify (addPath · p)
    if env.writeFails then throw env.writeErr
  runCmd args := ExceptT.mk (pure (env.run args))
  pathExists p := do return (← get) p
  removeFile p := do
    if (← get) p then modify (erasePath · p) else throw s!"no such file: {p}"

/-- Run the fixed code in the model from file system `fs`. -/
def runFixed (env : Env) (fs : FS) (dir : System.FilePath) (ws : Array (String × String))
    (mkCmd : System.FilePath → IO.Process.SpawnArgs) : Except String String × FS :=
  (@withTrieInputFileGen M _ _ (modelOps env) dir ws mkCmd).run fs

/-- Run the pre-fix code in the model from file system `fs`. -/
def runLeaky (env : Env) (fs : FS) (dir : System.FilePath) (ws : Array (String × String))
    (mkCmd : System.FilePath → IO.Process.SpawnArgs) : Except String String × FS :=
  (@leakyWithTrieInputFileGen M _ (modelOps env) dir ws mkCmd).run fs

/-- Adding then removing a path leaves exactly the removal. -/
theorem erasePath_addPath (fs : FS) (p : System.FilePath) :
    erasePath (addPath fs p) p = erasePath fs p := by
  funext q
  simp only [erasePath, addPath, bne]
  cases q == p <;> simp

/-- Removing an absent path changes nothing. -/
theorem erasePath_of_not_mem (fs : FS) (p : System.FilePath) (h : fs p = false) :
    erasePath fs p = fs := by
  funext q
  simp only [erasePath, bne]
  cases hq : q == p
  · simp
  · rw [eq_of_beq hq, h]; rfl

/-- **Cleanup, in every environment**: after the fixed code runs, the file system is the initial
one with the temporary path removed — whether the write fails (before or after creating the file),
the helper fails, or everything succeeds. -/
theorem withTrieInputFileGen_fs (env : Env) (fs : FS) (dir : System.FilePath)
    (ws : Array (String × String)) (mkCmd : System.FilePath → IO.Process.SpawnArgs) :
    (runFixed env fs dir ws mkCmd).2 = erasePath fs env.fresh := by
  obtain ⟨fresh, wc, wf, we, run⟩ := env
  cases wc <;> cases wf <;> cases hr : run (mkCmd fresh) <;> cases hfs : fs fresh <;>
    simp [runFixed, withTrieInputFileGen, modelOps, tryFinally, MonadFinally.tryFinally',
    ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift,
    ExceptT.map, StateT.bind, StateT.get, StateT.pure, StateT.modifyGet, StateT.map, Functor.map,
    bind, pure, get, getThe, MonadStateOf.get, modify, modifyGet, MonadStateOf.modifyGet, throw,
    throwThe, MonadExceptOf.throw, liftM, monadLift, MonadLift.monadLift, hr, hfs, addPath,
    erasePath_addPath, erasePath_of_not_mem]

/-- **No leak**: if the temporary path did not exist before the call, the file system after the
call is exactly the one before it, in every environment. -/
theorem withTrieInputFileGen_no_leak (env : Env) (fs : FS) (dir : System.FilePath)
    (ws : Array (String × String)) (mkCmd : System.FilePath → IO.Process.SpawnArgs)
    (hfresh : fs env.fresh = false) :
    (runFixed env fs dir ws mkCmd).2 = fs := by
  rw [withTrieInputFileGen_fs, erasePath_of_not_mem _ _ hfresh]

/-- **Result**: the call returns the helper's outcome (success with its output, or its error),
unless writing the input failed, in which case it returns the write error. The cleanup never
masks the outcome. -/
theorem withTrieInputFileGen_result (env : Env) (fs : FS) (dir : System.FilePath)
    (ws : Array (String × String)) (mkCmd : System.FilePath → IO.Process.SpawnArgs) :
    (runFixed env fs dir ws mkCmd).1 =
      if env.writeFails then .error env.writeErr else env.run (mkCmd env.fresh) := by
  obtain ⟨fresh, wc, wf, we, run⟩ := env
  cases wc <;> cases wf <;> cases hr : run (mkCmd fresh) <;> cases hfs : fs fresh <;>
    simp [runFixed, withTrieInputFileGen, modelOps, tryFinally, MonadFinally.tryFinally',
    ExceptT.run, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.pure, ExceptT.lift,
    ExceptT.map, StateT.bind, StateT.get, StateT.pure, StateT.modifyGet, StateT.map, Functor.map,
    bind, pure, get, getThe, MonadStateOf.get, modify, modifyGet, MonadStateOf.modifyGet, throw,
    throwThe, MonadExceptOf.throw, liftM, monadLift, MonadLift.monadLift, hr, hfs, addPath,
    erasePath_addPath, erasePath_of_not_mem]

/-- **The pre-fix code leaks**: whenever the input file is written and the helper then fails
(e.g. missing Python packages), the temporary file is still there afterwards, and the call
reports the helper's error. -/
theorem leakyWithTrieInputFileGen_leaks (env : Env) (fs : FS) (dir : System.FilePath)
    (ws : Array (String × String)) (mkCmd : System.FilePath → IO.Process.SpawnArgs) (e : String)
    (hcreate : env.writeCreates = true) (hwrite : env.writeFails = false)
    (hrun : env.run (mkCmd env.fresh) = .error e) :
    (runLeaky env fs dir ws mkCmd).2 env.fresh = true ∧
      (runLeaky env fs dir ws mkCmd).1 = .error e := by
  obtain ⟨fresh, wc, wf, we, run⟩ := env
  simp only at hcreate hwrite hrun
  subst hcreate hwrite
  cases hfs : fs fresh <;>
    simp [runLeaky, leakyWithTrieInputFileGen, modelOps, ExceptT.run, ExceptT.mk, ExceptT.bind,
    ExceptT.bindCont, ExceptT.pure, ExceptT.lift, StateT.bind, StateT.pure, StateT.modifyGet,
    StateT.map, Functor.map, bind, pure, get, getThe, MonadStateOf.get, modify, modifyGet,
    MonadStateOf.modifyGet, throw, throwThe, MonadExceptOf.throw, liftM, monadLift,
    MonadLift.monadLift, hrun, hfs, addPath]

/-- The environment of the 876-file incident: the write succeeds, `python3` exits non-zero. -/
def pythonMissingEnv : Env :=
  { fresh := "python/EllipticCurvesPy/trieInput_0.txt", writeCreates := true, writeFails := false,
    writeErr := "", run := fun _ => .error "ModuleNotFoundError: No module named 'Crypto'" }

/-- **Concrete counterexample to the old code**: starting from an empty file system, the pre-fix
code leaves `trieInput_0.txt` behind, while the fixed code leaves the file system empty. -/
theorem leaky_counterexample :
    (runLeaky pythonMissingEnv (fun _ => false) trieInputDir #[] (trieRootPythonCommand · 0)).2
        "python/EllipticCurvesPy/trieInput_0.txt" = true ∧
      (runFixed pythonMissingEnv (fun _ => false) trieInputDir #[]
        (trieRootPythonCommand · 0)).2 = fun _ => false := by
  refine ⟨(leakyWithTrieInputFileGen_leaks _ _ _ _ _ _ rfl rfl rfl).1, ?_⟩
  exact withTrieInputFileGen_no_leak _ _ _ _ _ rfl

end EvmYul.TrieRootModel
