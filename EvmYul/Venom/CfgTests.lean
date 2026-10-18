module

public import EvmYul.Venom.Cfg
public meta import EvmYul.Venom.Cfg
public import EvmYul.Testing.Counted
public meta import EvmYul.Testing.Counted
public import Plausible
public meta import Plausible

@[expose] public meta section

/-!
# Tests of the Venom control-flow graph module: falsified design claims, φ, and the fixes

Each section names the `TESTING.md` rule it applies.

1. **§1 Regression (the sketch's own test).** φ is a parallel copy: the swap loop stores
   `1, 2, 1`. A sequential copy would store `1, 2, 2`, and the test checks that it does
   (`seqSwapTrace`), so the regression test can fail.
   **§1b** checks the branch direction of `jnz` against real Vyper 0.4.3 output, and checks that
   the real entry block's `djmp` dispatch faults.
2. **§2 Falsification of `Refines` (E1, proved counterexamples).**
   * `refines_rejects_constant_folding`: `%x = add 1, 2` → `%x = assign 3` is not a `Refines`
     step, because some machine interface does not interpret `add` as addition. Hence
     `no_validator_accepts_constant_folding`: no sound `Validator` accepts it.
   * `refines_admits_loop_to_stop`: a loop that never ends "refines" to `stop`.
   * `check_accepts_faulting_djmp` and `faulting_source_refined_by_anything`: `Func.check` accepts a
     `djmp` block that `run` cannot execute, and such a source is refined by every target.
3. **§3 The corrections (proved).** Under one machine interface where `add` is addition,
   constant folding is a `RefinesIn` step (`refinesIn_constant_folding`). `RefinesTotal`
   rejects loop-to-stop (`refinesTotal_rejects_loop_to_stop`). `Func.wf` rejects every
   counterexample `Func.check` accepted, and still accepts the swap loop.
4. **§4 φ order independence (A2, counted Plausible), with its canary (E1).** For φs with distinct
   outputs, the parallel copy gives the same environment in any order. The same law for a
   sequential copy is refuted.
5. **§5 `djmp` with label addresses (§7 of `Cfg.lean`).** Unit checks: the real dispatch shape
   (`entryDispatch`, which faults in `run`) now reaches each bucket through its address, also when
   the address is computed from a label operand (`add @selector_bucket_1, 0`); a value that is no
   bucket's address faults; `Func.wfD` accepts it, `Func.wf` still rejects it. Counted properties
   (A2, D1): on random target lists and random address maps, a `djmp` dispatch ends as an oracle
   computed by index search says (the first listed label with that address, else a fault); with
   pairwise different addresses every target is reached through its own address (the iff of
   `execTermL_djmp_iff`, counted on its antecedent). Canaries (E1): the same reachability law
   without distinct addresses, and the old semantics `run` in place of `runL`, must be refuted.
-/

namespace EvmYul.Venom.CfgTests

open EvmYul.Venom.Cfg Plausible Plausible.Decorations

/-! ## Machines -/

/-- A store-log machine: `sstore v` appends `v`, `sub` and `add` are arithmetic, `assign` copies. -/
def logMachine : EvmInterface (List Word) where
  exec
    | .sstore, [v], s => some ([], s ++ [v])
    | .sub, [a, b], s => some ([a - b], s)
    | .add, [a, b], s => some ([a + b], s)
    | .assign, [v], s => some ([v], s)
    | _, _, _ => none

/-- The same machine with an `add` that is not addition: `Refines` must hold for it too. -/
def oddMachine : EvmInterface (List Word) where
  exec
    | .sstore, [v], s => some ([], s ++ [v])
    | .assign, [v], s => some ([v], s)
    | .add, _, s => some ([0], s)
    | _, _, _ => none

/-! ## §1 The swap loop (the sketch's regression test) -/

/-- The sketch's swap loop: `x, y` swap through φs on every iteration, three iterations. -/
def swapLoop : Func := { name := "swap", entry := "entry", blocks := [
  { label := "entry", insts := [ { op := .jmp, args := [.lbl "loop"], outs := [] } ] },
  { label := "loop", insts := [
      { op := .phi, args := [.lbl "entry", .lit 1, .lbl "loop", .var "y"], outs := ["x"] },
      { op := .phi, args := [.lbl "entry", .lit 2, .lbl "loop", .var "x"], outs := ["y"] },
      { op := .phi, args := [.lbl "entry", .lit 3, .lbl "loop", .var "m"], outs := ["n"] },
      { op := .sstore, args := [.var "x"], outs := [] },
      { op := .sub, args := [.var "n", .lit 1], outs := ["m"] },
      { op := .jnz, args := [.var "m", .lbl "loop", .lbl "done"], outs := [] } ] },
  { label := "done", insts := [ { op := .stop, args := [], outs := [] } ] } ] }

/-- The stores of a run, as naturals (`none` if it does not halt). -/
def trace (f : Func) (fuel : Nat) : Option (List Nat) :=
  match @run (List Word) logMachine f fuel "" f.entry Env.empty [] with
  | .halted s => some (s.map BitVec.toNat)
  | _ => none

/-- A **sequential** φ copy (each source read from the copies already made): the mutant. -/
def applyPhisSeq (prev : Label) (old : Env) (phis : List Inst) : Option Env :=
  phis.foldlM (init := old) fun acc i => do
    let src ← phiPick prev i.args
    let w ← evalOp acc src
    match i.outs with
    | [x] => pure (acc.set x w)
    | _ => none

/-- The swap loop's stores under the sequential mutant, computed by hand from `applyPhisSeq`:
iteration by iteration, the env after the φs. -/
def seqSwapTrace : List Nat :=
  let step (e : Env) : Option Env := applyPhisSeq "loop" e
    [ { op := .phi, args := [.lbl "entry", .lit 1, .lbl "loop", .var "y"], outs := ["x"] },
      { op := .phi, args := [.lbl "entry", .lit 2, .lbl "loop", .var "x"], outs := ["y"] } ]
  let e₀ := (Env.empty.set "x" 1).set "y" 2
  let e₁ := (step e₀).getD Env.empty
  let e₂ := (step e₁).getD Env.empty
  [e₀ "x", e₁ "x", e₂ "x"].map fun o => (o.map BitVec.toNat).getD 0

#guard swapLoop.check
#guard swapLoop.wf
#guard trace swapLoop 50 == some [1, 2, 1]
-- the mutant gives a different trace, so the regression test above can fail
#guard seqSwapTrace == [1, 2, 2]
-- fuel: three iterations need 5 blocks; with 4 the run is cut short, with 5 it finishes
#guard trace swapLoop 4 == none
#guard trace swapLoop 5 == some [1, 2, 1]

/-! ## §1b Branch direction and dispatch, against real Vyper output

`docs/research/venom/store_bb_runtime_0.4.3.txt` (real `vyper 0.4.3 -f bb_runtime
--experimental-codegen` output) has, in block `selector_bucket_0`:

```
%43 = xor %59, %58            ; selector XOR 0xb20eb4c4: zero iff the selector matches
jnz %43, @9_if_exit, @6_then  ; 6_then is the matched function's body
```

So a **zero** condition goes to the **second** label, as `execTerm` has it. The entry block of the
same function ends in `djmp %7, @selector_bucket_0, @selector_bucket_1`, which `run` cannot execute.
-/

/-- `selector_bucket_0` with the `xor` result given as the literal `x`: `6_then` stores 6,
`9_if_exit` stores 9. -/
def bucket0 (x : Nat) : Func := { name := "bucket0", entry := "selector_bucket_0", blocks := [
  { label := "selector_bucket_0", insts := [
      { op := .assign, args := [.lit (BitVec.ofNat 256 x)], outs := ["43"] },
      { op := .jnz, args := [.var "43", .lbl "9_if_exit", .lbl "6_then"], outs := [] } ] },
  { label := "6_then", insts := [ { op := .sstore, args := [.lit 6], outs := [] },
                                  { op := .stop, args := [], outs := [] } ] },
  { label := "9_if_exit", insts := [ { op := .sstore, args := [.lit 9], outs := [] },
                                     { op := .stop, args := [], outs := [] } ] } ] }

/-- The entry block's dispatch, `djmp %7, @selector_bucket_0, @selector_bucket_1`. -/
def entryDispatch : Func := { name := "__main_entry", entry := "__main_entry", blocks := [
  { label := "__main_entry", insts := [
      { op := .assign, args := [.lit 0], outs := ["7"] },
      { op := .djmp, args := [.var "7", .lbl "selector_bucket_0", .lbl "selector_bucket_1"],
        outs := [] } ] },
  { label := "selector_bucket_0", insts := [ { op := .stop, args := [], outs := [] } ] },
  { label := "selector_bucket_1", insts := [ { op := .stop, args := [], outs := [] } ] } ] }

-- selector matches (xor = 0): the function body; any other selector: the next check
#guard trace (bucket0 0) 10 == some [6]
#guard [1, 0xb20eb4c4, 2 ^ 256 - 1].all fun x => trace (bucket0 x) 10 == some [9]
-- the real dispatch is accepted by `Func.check` but faults in `run`, for every fuel tried
#guard entryDispatch.check && !entryDispatch.wf
#guard (List.range 6).all fun n =>
  match @run (List Word) logMachine entryDispatch n "" "__main_entry" Env.empty [] with
  | .fault | .fuelOut => true
  | _ => false

/-! ## §2 Falsification of the sketch's `Refines` and `Func.check` -/

/-- A one-block function: `first`, then `sstore %x`, then `stop`. -/
def oneBlock (first : Inst) : Func := { name := "f", entry := "entry", blocks := [
  { label := "entry", insts := [ first,
      { op := .sstore, args := [.var "x"], outs := [] },
      { op := .stop, args := [], outs := [] } ] } ] }

/-- Before constant folding: `%x = add 1, 2`. -/
def foldSrc : Func := oneBlock { op := .add, args := [.lit 1, .lit 2], outs := ["x"] }

/-- After constant folding: `%x = assign 3`. -/
def foldTgt : Func := oneBlock { op := .assign, args := [.lit 3], outs := ["x"] }

/-- **Falsified: "`Refines` is the correctness notion for passes."** Constant folding
`%x = add 1, 2` → `%x = assign 3` is not a `Refines` step: under `oddMachine` the source stores `0`
and the target stores `3` whatever the fuel. -/
theorem refines_rejects_constant_folding : ¬ Refines foldSrc foldTgt := by
  intro h
  obtain ⟨fuel', hf⟩ := @h (List Word) oddMachine 1 [] (Result.halted [0]) rfl trivial
  cases fuel' with
  | zero =>
    have h0 : @run (List Word) oddMachine foldTgt 0 "" foldTgt.entry Env.empty [] =
        Result.fuelOut := rfl
    rw [h0] at hf
    cases hf
  | succ n =>
    have h3 : @run (List Word) oddMachine foldTgt (n + 1) "" foldTgt.entry Env.empty [] =
        Result.halted [3] := rfl
    rw [h3] at hf
    injection hf with hf
    revert hf; decide

/-- Hence no sound `Validator` can accept constant folding. -/
theorem no_validator_accepts_constant_folding (v : Validator) : v.check foldSrc foldTgt = false :=
  Bool.eq_false_iff.2 fun h => refines_rejects_constant_folding (v.sound _ _ h)

/-- A loop that never ends: `entry: jmp @entry`. -/
def spin : Func := { name := "spin", entry := "entry", blocks := [
  { label := "entry", insts := [ { op := .jmp, args := [.lbl "entry"], outs := [] } ] } ] }

/-- `stop`. -/
def stopF : Func := { name := "stop", entry := "entry", blocks := [
  { label := "entry", insts := [ { op := .stop, args := [], outs := [] } ] } ] }

/-- `spin` runs out of every fuel, for every machine (induction on the fuel). -/
theorem spin_fuelOut {σ : Type} [EvmInterface σ] :
    ∀ (n : Nat) (prev : Label) (env : Env) (s : σ), run spin n prev "entry" env s = .fuelOut
  | 0, _, _, _ => rfl
  | n + 1, _, env, s => spin_fuelOut n "entry" env s

/-- **Falsified: "`Refines` is a full correctness notion."** It says nothing about runs that never
finish: the endless loop "refines" to `stop`. -/
theorem refines_admits_loop_to_stop : Refines spin stopF := by
  intro σ _ fuel s r hr ht
  rw [show spin.entry = "entry" from rfl, spin_fuelOut] at hr
  subst hr
  exact absurd ht id

/-- `entry: djmp %x, @a, @b` with blocks `a`, `b` that stop. -/
def djmpF : Func := { name := "dj", entry := "entry", blocks := [
  { label := "entry", insts := [ { op := .djmp, args := [.var "x", .lbl "a", .lbl "b"], outs := [] } ] },
  { label := "a", insts := [ { op := .stop, args := [], outs := [] } ] },
  { label := "b", insts := [ { op := .stop, args := [], outs := [] } ] } ] }

/-- **Falsified: "`Func.check` guards `run`."** It accepts `djmpF`, and `run` faults on it for
every machine and fuel. -/
theorem check_accepts_faulting_djmp :
    djmpF.check = true ∧ ∀ {σ : Type} [EvmInterface σ] (n : Nat) (s : σ),
      run djmpF n "" "entry" Env.empty s = .fuelOut ∨ run djmpF n "" "entry" Env.empty s = .fault :=
  ⟨by decide, fun n s => match n with | 0 => .inl rfl | _ + 1 => .inr rfl⟩

/-- A faulting source is refined by **every** target: a validator that only asks for `Func.check`
accepts any pass output for `djmpF`. -/
theorem faulting_source_refined_by_anything (g : Func) : Refines djmpF g := by
  intro σ _ fuel s r hr ht
  rcases check_accepts_faulting_djmp.2 fuel s with h | h <;>
    (rw [show djmpF.entry = "entry" from rfl, h] at hr; subst hr; exact absurd ht id)

/-- A terminator in the middle of a block: `jmp @a; jmp @b`. -/
def midTerm : Func := { name := "mid", entry := "entry", blocks := [
  { label := "entry", insts := [ { op := .jmp, args := [.lbl "entry"], outs := [] },
                                 { op := .stop, args := [], outs := [] } ] } ] }

/-- A φ after an ordinary instruction (sent to the machine interface as an ordinary op). -/
def latePhi : Func := { name := "late", entry := "entry", blocks := [
  { label := "entry", insts := [ { op := .assign, args := [.lit 1], outs := ["a"] },
                                 { op := .phi, args := [.lbl "", .var "a"], outs := ["b"] },
                                 { op := .stop, args := [], outs := [] } ] } ] }

/-- Two φs defining the same variable (the later silently wins). -/
def dupPhi : Func := { name := "dup", entry := "entry", blocks := [
  { label := "entry", insts := [ { op := .phi, args := [.lbl "", .lit 1], outs := ["a"] },
                                 { op := .phi, args := [.lbl "", .lit 2], outs := ["a"] },
                                 { op := .stop, args := [], outs := [] } ] } ] }

/-- `jnz` without a condition. -/
def badJnz : Func := { name := "jnz", entry := "entry", blocks := [
  { label := "entry", insts := [ { op := .jnz, args := [.lbl "entry", .lbl "entry"], outs := [] } ] } ] }

-- `Func.check` accepts all four malformed functions …
#guard midTerm.check && latePhi.check && dupPhi.check && badJnz.check && djmpF.check

/-! ## §3 The corrections -/

/-- With the interface fixed to `logMachine` (`add` is addition), constant folding is correct. -/
theorem refinesIn_constant_folding :
    @RefinesIn (List Word) logMachine foldSrc foldTgt := by
  intro fuel s r hr ht
  cases fuel with
  | zero => subst hr; exact absurd ht id
  | succ n => exact ⟨n + 1, hr ▸ rfl⟩

/-- A machine with no operations. -/
def unitMachine : EvmInterface Unit := ⟨fun _ _ _ => none⟩

/-- `RefinesTotal` rejects turning the endless loop into `stop` (any machine; here `Unit`). -/
theorem refinesTotal_rejects_loop_to_stop :
    ¬ @RefinesTotal Unit unitMachine spin stopF := by
  intro h
  have hd := h.2 () (fun n => @spin_fuelOut Unit unitMachine n "" Env.empty ())
  have h1 : @runEntry Unit unitMachine stopF 1 () = .halted () := rfl
  cases h1 ▸ hd 1

-- … and `Func.wf` rejects all five, while still accepting the swap loop (§1)
#guard !midTerm.wf && !latePhi.wf && !dupPhi.wf && !badJnz.wf && !djmpF.wf
#guard spin.wf && stopF.wf && foldSrc.wf && foldTgt.wf

/-! ## §3b `assert` and the EVM `return` -/

/-- `assert a`, then `sstore 9`, then `return`. -/
def assertF (a : Operand) : Func := { name := "a", entry := "entry", blocks := [
  { label := "entry", insts := [ { op := .assert, args := [a], outs := [] },
                                 { op := .sstore, args := [.lit 9], outs := [] },
                                 { op := .evmReturn, args := [.lit 0, .lit 0], outs := [] } ] } ] }

/-- The result of a run under `logMachine` as a tag and the stores (`none` for fault/fuel). -/
def outcome (f : Func) : Option (String × List Nat) :=
  match @run (List Word) logMachine f 10 "" f.entry Env.empty [] with
  | .halted s => some ("halted", s.map BitVec.toNat)
  | .reverted s => some ("reverted", s.map BitVec.toNat)
  | _ => none

-- a zero condition reverts before the store; a non-zero one runs on to `return` (a halt)
#guard outcome (assertF (.lit 0)) == some ("reverted", [])
#guard [1, 2, 2 ^ 256 - 1].all fun n => outcome (assertF (.lit (BitVec.ofNat 256 n))) == some ("halted", [9])
-- an undefined condition faults (the assert does not silently pass)
#guard outcome (assertF (.var "undefined")) == none
-- `Func.wf` accepts the well-formed assert and rejects one with two operands
#guard (assertF (.lit 1)).wf
#guard !({ name := "a2", entry := "entry", blocks := [
  { label := "entry", insts := [ { op := .assert, args := [.lit 1, .lit 2], outs := [] },
                                 { op := .stop, args := [], outs := [] } ] } ] } : Func).wf

/-! ## §4 φ order independence (A2, counted) and its canary (E1) -/

/-- φ number `i` defines `o{i}`; its source from predecessor `p` is `o{a mod n}` (kind even) or the
literal `b` (kind odd). From predecessor `q` the source is `0`. -/
def mkPhis (xs : List (Nat × Nat × Nat)) : List Inst :=
  let n := max xs.length 1
  xs.zipIdx.map fun ((kind, a, b), i) =>
    { op := .phi, outs := [s!"o{i}"],
      args := [.lbl "q", .lit 0, .lbl "p",
        if kind % 2 = 0 then .var s!"o{a % n}" else .lit (BitVec.ofNat 256 b)] }

/-- The environment at block entry: `o{j} = 100 + j`. -/
def oldEnv (n : Nat) : Env :=
  (List.range n).foldl (fun e j => e.set s!"o{j}" (BitVec.ofNat 256 (100 + j))) Env.empty

/-- The values of `o0 … o{n-1}` after a φ application (`none` if it failed). -/
def observe (n : Nat) (r : Option Env) : Option (List (Option Nat)) :=
  r.map fun e => (List.range n).map fun j => (e s!"o{j}").map BitVec.toNat

/-- The law, for a φ copy `apply`: reversing and rotating the φs changes nothing. -/
def orderLaw (apply : Label → Env → List Inst → Option Env) (xs : List (Nat × Nat × Nat))
    (t : Nat) : Bool :=
  let ps := mkPhis xs
  let n := ps.length
  let r := observe n (apply "p" (oldEnv n) ps)
  r.isSome && r == observe n (apply "p" (oldEnv n) ps.reverse) &&
    r == observe n (apply "p" (oldEnv n) (ps.drop (t % max n 1) ++ ps.take (t % max n 1)))

/-- A φ list in which some φ reads another φ's output: the inputs where order could matter. -/
def readsAnother (xs : List (Nat × Nat × Nat)) : Bool :=
  let n := max xs.length 1
  xs.zipIdx.any fun ((kind, a, _), i) => kind % 2 = 0 && a % n ≠ i

/-- Seeded configuration (`TESTING.md` E3). -/
def cfg : Configuration := { numInst := 300, maxSize := 30, randomSeed := some 20261012,
                             quiet := true }

/-- Fail the build on a counterexample or on too few valid inputs (counts printed). -/
def expectHolds (name : String) (p : Prop)
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] : IO Unit :=
  discard <| EvmYul.CountedTesting.holdsCore cfg name p' (EvmYul.CountedTesting.defaultMinValid cfg)

/-- Mutation test: fail the build unless a counterexample is found (counts printed). -/
def expectRefuted (name : String) (p : Prop)
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] : IO Unit :=
  discard <| EvmYul.CountedTesting.refutedCore cfg name p'

/-- Run the §4 properties; throws on the first failure. -/
def runAll : IO Unit := do
  -- A2: the law is tested only where order could matter (some φ reads another φ's output)
  expectHolds "§4 parallel φ copy: order of the φs does not matter"
    (∀ (xs : List (Nat × Nat × Nat)) (t : Nat), readsAnother xs = true →
      orderLaw applyPhis xs t = true)
  expectRefuted "§4 canary: sequential φ copy is order independent"
    (∀ (xs : List (Nat × Nat × Nat)) (t : Nat), readsAnother xs = true →
      orderLaw applyPhisSeq xs t = true)

#eval runAll

/-! ## §5 `djmp` with label addresses -/

/-- Addresses for the real dispatch: `selector_bucket_0 ↦ 0x10`, `selector_bucket_1 ↦ 0x20`. -/
def bucketAddr : LabelAddr := fun l =>
  if l = "selector_bucket_0" then some 0x10 else if l = "selector_bucket_1" then some 0x20 else none

/-- `entryDispatch` with storing buckets: `%7 = first`; `djmp %7, @selector_bucket_0,
@selector_bucket_1`; bucket `k` stores `100 + k`. -/
def dispatchWith (first : Inst) : Func := { name := "__main_entry", entry := "__main_entry", blocks := [
  { label := "__main_entry", insts := [ first,
      { op := .djmp, args := [.var "7", .lbl "selector_bucket_0", .lbl "selector_bucket_1"],
        outs := [] } ] },
  { label := "selector_bucket_0", insts := [ { op := .sstore, args := [.lit 100], outs := [] },
                                             { op := .stop, args := [], outs := [] } ] },
  { label := "selector_bucket_1", insts := [ { op := .sstore, args := [.lit 101], outs := [] },
                                             { op := .stop, args := [], outs := [] } ] } ] }

/-- The stores of a `runL` run under `logMachine` (`none` unless it halts). -/
def traceL (addr : LabelAddr) (f : Func) (fuel : Nat) : Option (List Nat) :=
  match @runL (List Word) logMachine addr f fuel "" f.entry Env.empty [] with
  | .halted s => some (s.map BitVec.toNat)
  | _ => none

/-- `%7 = assign w`. -/
def assignW (w : Nat) : Inst := { op := .assign, args := [.lit (BitVec.ofNat 256 w)], outs := ["7"] }

-- each bucket through its own address; another value faults (no silent fall-through)
#guard traceL bucketAddr (dispatchWith (assignW 0x10)) 10 == some [100]
#guard traceL bucketAddr (dispatchWith (assignW 0x20)) 10 == some [101]
#guard [0, 0x11, 0x30, 2 ^ 256 - 1].all fun w =>
  match @runL (List Word) logMachine bucketAddr (dispatchWith (assignW w)) 10 "" "__main_entry"
      Env.empty [] with
  | .fault => true
  | _ => false
-- the address computed from a label operand, as in `%6 = add @selector_buckets, %5`
#guard traceL bucketAddr (dispatchWith
  { op := .add, args := [.lbl "selector_bucket_1", .lit 0], outs := ["7"] }) 10 == some [101]
-- without addresses the new semantics is the old one: the dispatch faults (`runL_noAddr`)
#guard (List.range 6).all fun n =>
  match @runL (List Word) logMachine noAddr entryDispatch n "" "__main_entry" Env.empty [] with
  | .fault | .fuelOut => true
  | _ => false
-- `Func.wfD` accepts the real dispatch shape, `Func.wf` still rejects it; `addrOk` checks addresses
#guard entryDispatch.wfD && !entryDispatch.wf && (dispatchWith (assignW 0)).wfD
#guard entryDispatch.addrOk bucketAddr && !entryDispatch.addrOk noAddr
#guard !entryDispatch.addrOk (fun _ => some 7)
-- `wfD` rejects a `djmp` with a label condition, no targets, a non-label or a repeated target
#guard [[.lbl "a", .lbl "a"], [.var "x"], [.var "x", .var "y"], [.var "x", .lbl "a", .lbl "a"]].all
  fun (args : List Operand) => !({ name := "d", entry := "a", blocks := [
    { label := "a", insts := [ { op := .djmp, args := args, outs := [] } ] } ] } : Func).wfD

/-- Targets `t0 … t{n-1}` (`n ≥ 1`), target `j` stores `j`; the dispatch value is `w`. -/
def dispatchN (n w : Nat) : Func :=
  let entry : Block := { label := "e", insts := [ assignW w,
      { op := .djmp, args := .var "7" :: (List.range n).map (fun j => .lbl s!"t{j}"), outs := [] } ] }
  let target (j : Nat) : Block := { label := s!"t{j}", insts := [
      { op := .sstore, args := [.lit (BitVec.ofNat 256 j)], outs := [] },
      { op := .stop, args := [], outs := [] } ] }
  { name := "dn", entry := "e", blocks := entry :: (List.range n).map target }

/-- Address map from a list: `t{j} ↦ as[j]`. -/
def addrOfList (as : List Nat) : LabelAddr := fun l =>
  ((List.range as.length).find? (fun j => s!"t{j}" = l)).map fun j => BitVec.ofNat 256 (as.getD j 0)

/-- The oracle, by index search: the first `j < n` with `as[j] = w` (as words). -/
def oracle (n : Nat) (as : List Nat) (w : Nat) : Option (List Nat) :=
  ((List.range (min n as.length)).find? fun j => as.getD j 0 % 2 ^ 256 = w % 2 ^ 256).map ([·])

/-- The dispatch value: one of the addresses (even `pick`) or an arbitrary word (odd `pick`). -/
def pickW (as : List Nat) (pick : Nat) : Nat :=
  if pick % 2 = 0 ∧ as ≠ [] then as.getD (pick / 2 % as.length) 0 else pick * 7919

/-- Addresses from a small range, so that some collide. -/
def smallAddrs (as : List Nat) : List Nat := as.map (· % 6)

/-- Run the §4 and §5 properties; throws on the first failure. -/
def runAll5 : IO Unit := do
  expectHolds "§5 djmp dispatch = index-search oracle (first listed label with that address, else fault)"
    (∀ (n : Nat) (as : List Nat) (pick : Nat),
      let n := n % 5 + 1
      traceL (addrOfList (smallAddrs as)) (dispatchN n (pickW (smallAddrs as) pick)) 10 ==
        oracle n (smallAddrs as) (pickW (smallAddrs as) pick))
  expectHolds "§5 distinct addresses: every target is reached through its own address"
    (∀ (as : List Nat) (k : Nat), as ≠ [] → (smallAddrs as).Nodup →
      traceL (addrOfList (smallAddrs as)) (dispatchN as.length ((smallAddrs as).getD (k % as.length) 0)) 10 ==
        some [k % as.length])
  -- A2: the two regions of the first law (a target reached / a fault), counted on the same inputs
  let samples := (List.range 300).map fun i =>
    let as := (List.range (i % 5 + 1)).map fun j => (i * 31 + j * 17) % 6
    let w := pickW as i
    traceL (addrOfList as) (dispatchN (i % 5 + 1) w) 10
  let reached := (samples.filter Option.isSome).length
  IO.println s!"§5 coverage (300 dispatches): reached a target {reached}, faulted {300 - reached}"
  unless reached ≥ 50 ∧ 300 - reached ≥ 50 do
    throw <| IO.userError "§5 coverage: a region is empty or too small (A2)"
  expectRefuted "§5 canary: every target is reached through its own address (addresses may collide)"
    (∀ (as : List Nat) (k : Nat), as ≠ [] →
      traceL (addrOfList (smallAddrs as)) (dispatchN as.length ((smallAddrs as).getD (k % as.length) 0)) 10 ==
        some [k % as.length])
  expectRefuted "§5 canary: the semantics without label addresses (run) dispatches"
    (∀ (n : Nat) (as : List Nat) (pick : Nat),
      let n := n % 5 + 1
      (match @run (List Word) logMachine (dispatchN n (pickW (smallAddrs as) pick)) 10 "" "e"
          Env.empty [] with
       | .halted s => some (s.map BitVec.toNat)
       | _ => none) == oracle n (smallAddrs as) (pickW (smallAddrs as) pick))

#eval runAll5

end EvmYul.Venom.CfgTests
