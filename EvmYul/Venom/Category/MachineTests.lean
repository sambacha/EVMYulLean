module

public import EvmYul.Venom.Category.BridgeTestHarness
public meta import EvmYul.Venom.Category.BridgeTestHarness

@[expose] public meta section

/-!
# Tests of the parallel φ-copy (P3.1) and of the Kleisli composition of the machine monad

`Machine.lean` defines the φ-copy of an edge as one precomposition (`phiCopy`), proves that it
swaps (`phiCopy_swap`) and that the sequential reading loses a value (`seqCopy_swap_loses`). These
tests characterise exactly when the two readings agree. Each section names the `TESTING.md` rule it
applies.

1. **§1 Unit checks.** The swap through `phiCopy`, the sequential swap losing `x`, and the Kleisli
   composite of a φ-copy with a halting morphism run through `Mach.run` (state threaded, the
   halting exit propagated, `𝟙` neutral).
2. **§2 Random copy lists (counted, A2).** Over a four-variable context: the φ-copy agrees with
   the sequential copy whenever no copy reads a variable an earlier copy wrote, and the φ-copy of
   any list equals the copy that reads every source from the *old* environment. The number of
   lists with a read-after-write conflict, and of those where the two readings really differ, is
   printed and thresholded.
3. **§3 Canary (E1).** The claim that the sequential reading always agrees with the φ-copy must be
   refuted.
-/

namespace EvmYul.Venom.Category.MachineTests

open CategoryTheory EvmYul.Venom.Cfg EvmYul.Venom.Category EvmYul.Venom.Category.BridgeTests
  Plausible Plausible.Decorations

/-- Copies `xᵢ := srcᵢ` over variables `0‥3`, with distinct targets (the first copy of a target
wins). -/
def copiesOf (raw : List (Nat × Nat)) : List (Nat × Nat) :=
  raw.foldl (fun acc (x, s) => if acc.any (·.1 == x % 4) then acc else acc ++ [(x % 4, s % 4)]) []

/-- An environment over `ℕ` from a list of values. -/
def envOf (vals : List Nat) : Env Nat := fun i => BitVec.ofNat 256 (vals.getD i 0)

/-- The φ-copy of the list, via `phiCopy`: targets read `.inr`, the rest pass through `.inl`. -/
def parCopy (l : List (Nat × Nat)) (e : Env Nat) : Env Nat := fun x =>
  let c := phiCopy (Γdom := Nat) (Phi := Nat) id (fun y => (l.lookup y).getD y) e
  if l.any (·.1 == x) then c (.inr x) else c (.inl x)

/-- Compare two environments on `0‥3`. -/
def agree (e e' : Env Nat) : Bool := (List.range 4).all fun i => e i == e' i

/-- No copy reads a variable written by an earlier copy. -/
def conflictFree (l : List (Nat × Nat)) : Bool :=
  (List.range l.length).all fun j => (l.take j).all fun (x, _) => (l.getD j (0, 0)).2 != x

/-- Old-environment reading, written directly. -/
def oldRead (l : List (Nat × Nat)) (e : Env Nat) : Env Nat := fun x =>
  match l.lookup x with
  | some s => e s
  | none => e x

/-- A halting morphism: halt with the current state. -/
def haltHom {X Y : Type} : MachCat.of (List Word) X ⟶ MachCat.of (List Word) Y :=
  fun _ => Mach.mk fun s => some (.error (.halt (s ++ [7])))

/-- Classify a run. -/
def describe {X : Type} : Option (Except (Exit (List Word)) (X × List Word)) → String
  | none => "⊥"
  | some (.ok (_, s)) => s!"ok {s.map BitVec.toNat}"
  | some (.error (.halt s)) => s!"halt {s.map BitVec.toNat}"
  | some (.error (.revert s)) => s!"revert {s.map BitVec.toNat}"
  | some (.error .fault) => "fault"

/-- §1 unit checks. -/
def unitChecks : List (String × Bool) :=
  let e : Env Bool := fun b => if b then 1 else 2
  let ρ := phiCopyHom (List Word) (Γdom := Empty) Empty.elim (fun b : Bool => !b)
  [("phiCopy swaps x, y := y, x",
      phiCopy (Γdom := Empty) Empty.elim (fun b : Bool => !b) e (.inr true) == 2 &&
      phiCopy (Γdom := Empty) Empty.elim (fun b : Bool => !b) e (.inr false) == 1),
   ("the sequential swap gives both variables y's old value",
      seqCopy [(true, false), (false, true)] e true == 2 &&
      seqCopy [(true, false), (false, true)] e false == 2),
   ("ρ ≫ halt halts with the threaded state",
      describe (Mach.run ((ρ ≫ haltHom (Y := Unit)) e) [5]) == "halt [5, 7]"),
   ("𝟙 ≫ ρ runs as ρ and keeps the state",
      describe (Mach.run ((𝟙 _ ≫ ρ) e) [5]) == "ok [5]" &&
      describe (Mach.run (ρ e) [5]) == "ok [5]")]

/-- Run everything; throws on the first failure. -/
def runAll : IO Unit := do
  -- §1
  for (name, ok) in unitChecks do
    unless ok do throw <| IO.userError s!"§1 unit check failed: {name}"
  IO.println s!"§1 machine: {unitChecks.length} unit checks passed"
  -- §2
  expectHolds "§2 copy lists: conflict-free ⇒ sequential copy = φ-copy"
    (∀ (raw : List (Nat × Nat)) (vals : List Nat),
      (!conflictFree (copiesOf raw) ||
        agree (seqCopy (copiesOf raw) (envOf vals)) (parCopy (copiesOf raw) (envOf vals))) = true)
  expectHolds "§2 copy lists: the φ-copy reads every source from the old environment"
    (∀ (raw : List (Nat × Nat)) (vals : List Nat),
      agree (parCopy (copiesOf raw) (envOf vals)) (oldRead (copiesOf raw) (envOf vals)) = true)
  let samples := (List.range 300).map fun i =>
    (copiesOf ((List.range (mixD i % 5 + 1)).map fun j => (mixD (i + j), mixD (i * 7 + j))),
     (List.range 4).map fun j => 100 * j + mixD (i * 4 + j) % 100)
  let conflicts := (samples.filter fun (l, _) => !conflictFree l).length
  let differ := (samples.filter fun (l, v) =>
    !agree (seqCopy l (envOf v)) (parCopy l (envOf v))).length
  IO.println s!"§2 coverage (300 copy lists): with a read-after-write {conflicts}; where the \
    readings differ {differ}"
  unless conflicts ≥ 50 ∧ differ ≥ 20 do
    throw <| IO.userError "§2 coverage: a region is empty or too small (A2)"
  -- §3
  expectRefuted "§3 canary: the sequential copy always equals the φ-copy"
    (∀ (raw : List (Nat × Nat)) (vals : List Nat),
      agree (seqCopy (copiesOf raw) (envOf vals)) (parCopy (copiesOf raw) (envOf vals)) = true)

#eval runAll

end EvmYul.Venom.Category.MachineTests
