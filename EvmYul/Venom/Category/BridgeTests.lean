module

public import EvmYul.Venom.Category.BridgeTestHarness
public meta import EvmYul.Venom.Category.BridgeTestHarness

@[expose] public meta section

/-!
# Tests of the path-category semantics and its bridge to the fuel interpreter

`Bridge.lean` proves that the functor `Paths.lift` builds from the decoration of a Venom function
agrees with the compiled interpreter `run` (`run_succ_iff_outcomeWithin`: `run f (n + 1) = ⟦f⟧ₙ`)
and that all outcomes agree (`funcDecor_deterministic`). These tests run the categorical
definitions themselves. Each section names the `TESTING.md` rule it applies.

1. **§1 Unit checks (the compiled sketch's regression, through the categories).** The swap loop of
   the root-level `Venom.lean` (`x, y := y, x` as φs on the back edge): the composite of the arrow
   morphisms along `entry → loop → loop → loop → done`, computed by `Decor.semPath` (that is,
   `Paths.lift`), followed by the exit of `done`, halts with the trace `[1, 2, 1]` (P3.1: φs are a
   parallel copy); the compiled `run` gives the same; a path whose guard is not selected (leaving
   the loop on the first iteration) is undefined (⊥, not a fault).
2. **§2 Random functions (counted, A2, D1).** On random functions with loops, φs (some with no
   source for the incoming edge), parallel slots `jnz c, @a, @a`, missing labels, `stop` and
   `revert`: the outcomes of all slot paths of length `≤ n` (enumerated here from the arrow and exit
   morphisms, independently of `run`) are exactly the result of `run f (n + 1)` (at most one
   outcome, and none iff `fuelOut`). The coverage of every result kind is printed and checked.
3. **§3 Canaries (E1).** A guard on the jump *label* instead of the slot gives two defined paths on
   parallel slots (determinism refuted); comparing `run f n` instead of `run f (n + 1)` with paths
   of length `≤ n` (the off-by-one of D3.7) is refuted.
-/

namespace EvmYul.Venom.Category.BridgeTests

open EvmYul.Venom.Cfg EvmYul.Venom.Category CategoryTheory Plausible Plausible.Decorations

/-- The swap loop of `Venom.lean`. -/
def swapLoop : Func := { name := "swap", entry := "entry", blocks := [
  ⟨"entry", [I .jmp [.lbl "loop"]]⟩,
  ⟨"loop", [I .phi [.lbl "entry", .lit 1, .lbl "loop", .var "y"] ["x"],
            I .phi [.lbl "entry", .lit 2, .lbl "loop", .var "x"] ["y"],
            I .phi [.lbl "entry", .lit 3, .lbl "loop", .var "m"] ["n"],
            I .sstore [.var "x"],
            I .sub [.var "n", .lit 1] ["m"],
            I .jnz [.var "m", .lbl "loop", .lbl "done"]]⟩,
  ⟨"done", [I .stop []]⟩] }

/-- An arrow of the swap loop's flow quiver, from its slot. -/
def arr (u v : Label) (k : Nat) (h : ∃ b, swapLoop.find? u = some b ∧ k < b.succs.length)
    (ht : slotTarget swapLoop ⟨(u, k), h⟩ = v) : @Quiver.Hom (flowOf swapLoop).B _ u v :=
  ⟨⟨(u, k), h⟩, rfl, ht⟩

/-- `entry → loop`. -/
def eL : @Quiver.Hom (flowOf swapLoop).B _ "entry" "loop" :=
  arr "entry" "loop" 0 ⟨_, rfl, by decide⟩ (by decide)
/-- `loop → loop` (slot 0 of `jnz`). -/
def lL : @Quiver.Hom (flowOf swapLoop).B _ "loop" "loop" :=
  arr "loop" "loop" 0 ⟨_, rfl, by decide⟩ (by decide)
/-- `loop → done` (slot 1 of `jnz`). -/
def lD : @Quiver.Hom (flowOf swapLoop).B _ "loop" "done" :=
  arr "loop" "done" 1 ⟨_, rfl, by decide⟩ (by decide)

/-- The path the swap loop takes. -/
def swapPath : @Quiver.Path (flowOf swapLoop).B _ "entry" "done" :=
  (((Quiver.Path.nil.cons eL).cons lL).cons lL).cons lD

/-- A path that leaves the loop on its first iteration (its guard is not selected). -/
def shortPath : @Quiver.Path (flowOf swapLoop).B _ "entry" "done" :=
  (Quiver.Path.nil.cons eL).cons lD

/-- The semantics of a path of the swap loop followed by the exit of `done`, from the empty
environment and the empty trace. -/
def runPath (p : @Quiver.Path (flowOf swapLoop).B _ "entry" "done") :
    Option (Except (Exit (List Word)) (Empty × List Word)) :=
  (((funcDecor (σ := List Word) swapLoop).semPath p ≫ (funcDecor swapLoop).exit "done")
    EvmYul.Venom.Cfg.Env.empty).run []

/-- Does the result halt with the trace `ws`? -/
def haltsWith (o : Option (Except (Exit (List Word)) (Empty × List Word))) (ws : List Nat) : Bool :=
  match o with
  | some (.error (.halt s)) => s.map BitVec.toNat == ws
  | _ => false

/-- §1 unit checks; each must be `true`. -/
def unitChecks : List (String × Bool) :=
  [("swap loop through Paths.lift: entry → loop → loop → loop → done halts with [1, 2, 1]",
      haltsWith (runPath swapPath) [1, 2, 1]),
   ("swap loop with the compiled run (the sketch's #guard): halts with [1, 2, 1]",
      match run (σ := List Word) swapLoop 50 "" "entry" EvmYul.Venom.Cfg.Env.empty [] with
      | .halted s => s.map BitVec.toNat == [1, 2, 1]
      | _ => false),
   ("a path whose guard is not selected (leaving the loop at once) is undefined, not a fault",
      (runPath shortPath).isNone),
   ("swapPath has length 4: run with fuel 4 + 1 halts, with fuel 4 runs out (run (n+1) = ⟦f⟧ₙ)",
      swapPath.length == 4 &&
      (match run (σ := List Word) swapLoop 5 "" "entry" EvmYul.Venom.Cfg.Env.empty [] with
       | .halted _ => true | _ => false) &&
      (match run (σ := List Word) swapLoop 4 "" "entry" EvmYul.Venom.Cfg.Env.empty [] with
       | .fuelOut => true | _ => false))]

/-! ## The path enumeration (independent of `run`) -/

/-- The outcomes of all slot paths of length `≤ n` from `cur`, each followed by the exit at its
end, computed from the arrow morphisms `stepFn` (slot `k` to the `k`-th successor) and the exit
morphisms `exitFn` of the decoration. `guard` chooses the arrow function (the real one, or a
canary). -/
def pathOutcomes (stepF : Func → Label → Label → Nat → EvmYul.Venom.Cfg.Env → List Word →
    Option (Except (Exit (List Word)) (EvmYul.Venom.Cfg.Env × List Word)))
    (f : Func) : Nat → Label → EvmYul.Venom.Cfg.Env → List Word → List (Exit (List Word))
  | n, cur, env, s =>
    let here := match exitFn (σ := List Word) f cur env s with
      | some (.error x) => [x]
      | _ => []
    match n with
    | 0 => here
    | m + 1 =>
      let succs := ((f.find? cur).map Block.succs).getD []
      here ++ (succs.zipIdx.flatMap fun (v, k) =>
        match stepF f cur v k env s with
        | some (.error x) => [x]
        | some (.ok (env', s')) => pathOutcomes stepF f m v env' s'
        | none => [])

/-- The decoration's own arrow function. -/
def realStep (f : Func) (u v : Label) (k : Nat) (env : EvmYul.Venom.Cfg.Env) (s : List Word) :
    Option (Except (Exit (List Word)) (EvmYul.Venom.Cfg.Env × List Word)) :=
  stepFn f u v k env s

/-- **Canary**: guard on the jump label instead of the slot index. -/
def labelGuardStep (f : Func) (u v : Label) (_k : Nat) (env : EvmYul.Venom.Cfg.Env)
    (s : List Word) : Option (Except (Exit (List Word)) (EvmYul.Venom.Cfg.Env × List Word)) :=
  match f.find? u with
  | none => none
  | some b =>
    match blockRest b env s with
    | some (.goto l, env', s') =>
      if l = v then
        match f.find? v with
        | none => some (.error .fault)
        | some bv =>
          match applyPhis u env' bv.phis with
          | none => some (.error .fault)
          | some env'' => some (.ok (env'', s'))
      else none
    | _ => none

/-- The outcomes of a whole run with fuel `n + 1`: the entry block's φs, then the paths. -/
def wholeOutcomes (stepF : Func → Label → Label → Nat → EvmYul.Venom.Cfg.Env → List Word →
    Option (Except (Exit (List Word)) (EvmYul.Venom.Cfg.Env × List Word))) (f : Func) (n : Nat) :
    List (Exit (List Word)) :=
  match f.find? f.entry with
  | none => [.fault]
  | some b =>
    match applyPhis "" EvmYul.Venom.Cfg.Env.empty b.phis with
    | none => [.fault]
    | some env => pathOutcomes stepF f n f.entry env []

/-- Does a result of `run` equal an exit? -/
def sameResult (r : Result (List Word)) (x : Exit (List Word)) : Bool :=
  match r, x with
  | .halted s, .halt s' => s == s'
  | .reverted s, .revert s' => s == s'
  | .fault, .fault => true
  | _, _ => false

/-- The bridge, checked on one function and fuel: no outcome iff `fuelOut`, otherwise exactly one,
equal to the result of `run`. -/
def agrees (r : Result (List Word)) (outs : List (Exit (List Word))) : Bool :=
  match r, outs with
  | .fuelOut, [] => true
  | r, [x] => sameResult r x
  | _, _ => false

/-! ## Random functions -/

/-- Run everything; throws on the first failure. -/
def runAll : IO Unit := do
  -- §1
  for (name, ok) in unitChecks do
    unless ok do throw <| IO.userError s!"§1 unit check failed: {name}"
  IO.println s!"§1 bridge: {unitChecks.length} unit checks passed"
  -- §2
  expectHolds "§2 random functions: the outcomes of all paths of length ≤ n are run f (n + 1)"
    (∀ (n k₀ : Nat) (bs : List (Nat × Nat × Nat × Nat)) (fuel : Nat),
      agrees (run (funcOf n k₀ bs) (fuel % 12 + 1) "" (funcOf n k₀ bs).entry
        EvmYul.Venom.Cfg.Env.empty []) (wholeOutcomes realStep (funcOf n k₀ bs) (fuel % 12)) = true)
  let samples := (List.range 300).map fun i => (detFunc i, mixD (i + 3) % 12)
  let results := samples.map fun (f, n) => run (σ := List Word) f (n + 1) "" f.entry
    EvmYul.Venom.Cfg.Env.empty []
  let count (p : Result (List Word) → Bool) := (results.filter p).length
  let halted := count fun | .halted _ => true | _ => false
  let reverted := count fun | .reverted _ => true | _ => false
  let faults := count fun | .fault => true | _ => false
  let fuelOuts := count fun | .fuelOut => true | _ => false
  let parallel := (samples.filter fun (f, _) => f.blocks.any fun b =>
    match b.succs with | [x, y] => x == y | _ => false).length
  let disagree := (samples.filter fun (f, n) =>
    !agrees (run f (n + 1) "" f.entry EvmYul.Venom.Cfg.Env.empty [])
      (wholeOutcomes realStep f n)).length
  IO.println s!"§2 coverage (300 functions): halted {halted}, reverted {reverted}, fault \
    {faults}, fuelOut {fuelOuts}; with parallel slots {parallel}; disagreements {disagree}"
  unless halted ≥ 20 ∧ reverted ≥ 20 ∧ faults ≥ 20 ∧ fuelOuts ≥ 10 ∧ parallel ≥ 30 ∧
      disagree = 0 do
    throw <| IO.userError "§2 coverage: a result kind is too rare, or a disagreement (A2)"
  -- §3
  expectRefuted "§3 canary: a guard on the jump label gives two defined paths on parallel slots"
    (∀ (n k₀ : Nat) (bs : List (Nat × Nat × Nat × Nat)) (fuel : Nat),
      decide ((wholeOutcomes labelGuardStep (funcOf n k₀ bs) (fuel % 12)).length ≤ 1) = true)
  expectRefuted "§3 canary: run f n (no + 1) equals the paths of length ≤ n"
    (∀ (n k₀ : Nat) (bs : List (Nat × Nat × Nat × Nat)) (fuel : Nat),
      agrees (run (funcOf n k₀ bs) (fuel % 12) "" (funcOf n k₀ bs).entry
        EvmYul.Venom.Cfg.Env.empty []) (wholeOutcomes realStep (funcOf n k₀ bs) (fuel % 12)) = true)
  IO.println "bridge: standing caveat (D1): the enumeration uses the decoration's own arrow and \
    exit morphisms; that they compose to run is the theorem run_succ_iff_outcomeWithin"

#eval runAll

end EvmYul.Venom.Category.BridgeTests
