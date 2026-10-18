module

public import EvmYul.Venom.Category.Bridge
public meta import EvmYul.Venom.Category.Bridge
public import EvmYul.Testing.Counted
public meta import EvmYul.Testing.Counted
public import Plausible
public meta import Plausible

@[expose] public meta section

/-!
# Test support for the path-category semantics: a trace machine and random functions

Shared by `BridgeTests.lean` and `CfgNormalizationTests.lean`: the machine of the compiled
sketch's regression (`sstore` appends to a trace, `sub` subtracts), a generator of random Venom
functions with loops, φs, parallel slots, missing labels, `stop` and `revert` (`funcOf`), its
deterministic counterpart for coverage counts (`detFunc`), and the seeded counted runners
(`TESTING.md` A2, E3).
-/

namespace EvmYul.Venom.Category.BridgeTests

open EvmYul.Venom.Cfg EvmYul.Venom.Category Plausible Plausible.Decorations

/-- The machine of the compiled sketch's regression: `sstore` appends to a trace, `sub`
subtracts. -/
instance traceMachine : EvmInterface (List Word) where
  exec
    | .sstore, [v], s => some ([], s ++ [v])
    | .sub, [a, b], s => some ([a - b], s)
    | _, _, _ => none

/-- `%x = op args`. -/
def I (op : Op) (args : List Operand) (outs : List Var := []) : Inst := ⟨op, args, outs⟩

/-- Label of block `j`. -/
def lab (j : Nat) : Label := "b" ++ toString j

/-- A random function of `m = n % 5 + 1` blocks. The entry sets the counter `%c := k₀ - 0`; every
block stores `%c`, decrements it, and ends in `jmp`, `jnz %c` (sometimes with both slots naming
the same block: parallel arrows), `stop` or `revert`; targets may be a missing label `b_m`. Blocks
after the entry may open with a φ `%d = phi @b_q, %c`, whose source is missing for the other
predecessors (a fault). -/
def funcOf (n k₀ : Nat) (bs : List (Nat × Nat × Nat × Nat)) : Func :=
  let m := n % 5 + 1
  let blk (j : Nat) : Block :=
    let (kind, t₁, t₂, q) := bs.getD j (j, j + 1, j, 0)
    let tgt₁ := lab ((j + 1 + t₁ % 2) % (m + 1))
    let tgt₂ := if t₂ % 3 = 0 then tgt₁ else lab (t₂ % (m + 1))
    let term := match kind % 5 with
      | 0 => I .jmp [.lbl tgt₁]
      | 1 | 2 => I .jnz [.var "c", .lbl tgt₁, .lbl tgt₂]
      | 3 => I .stop []
      | _ => I .revert []
    let phis := if j > 0 ∧ q % 3 = 0 then [I .phi [.lbl (lab (q / 3 % m)), .var "c"] ["d"]]
      else []
    let init := if j = 0 then [I .sub [.lit (BitVec.ofNat 256 (k₀ % 4)), .lit 0] ["c"]] else []
    ⟨lab j, phis ++ init ++ [I .sstore [.var "c"], I .sub [.var "c", .lit 1] ["c"], term]⟩
  ⟨"g", lab 0, (List.range m).map blk⟩

/-- Seeded configuration (`TESTING.md` E3). -/
def cfg : Configuration := { numInst := 300, maxSize := 30, randomSeed := some 20261013,
                             quiet := true }

/-- Fail the build on a counterexample or on too few valid inputs (counts printed). -/
def expectHolds (name : String) (p : Prop)
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] : IO Unit :=
  discard <| EvmYul.CountedTesting.holdsCore cfg name p' (EvmYul.CountedTesting.defaultMinValid cfg)

/-- Mutation test: fail the build unless a counterexample is found (counts printed). -/
def expectRefuted (name : String) (p : Prop)
    (p' : Decorations.DecorationsOf p := by mk_decorations) [Testable p'] : IO Unit :=
  discard <| EvmYul.CountedTesting.refutedCore cfg name p'

/-- A deterministic pseudo-random number. -/
def mixD (x : Nat) : Nat := (x + 1) * 0x9E3779B97F4A7C15 % 2 ^ 61

/-- Deterministic functions for the coverage lines. -/
def detFunc (i : Nat) : Func :=
  funcOf (mixD i % 5) (mixD (i + 7)) ((List.range 5).map fun j =>
    (mixD (i * 5 + j) % 5, mixD (i + j * 3) % 9, mixD (i * j + 1) % 9, mixD (i + 5 * j) % 9))

end EvmYul.Venom.Category.BridgeTests
