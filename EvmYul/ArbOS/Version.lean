import Mathlib.Data.Nat.Basic

/-!
# ArbOS protocol versions

Robinhood Chain runs Arbitrum Nitro; the L2 protocol behaviour it exposes is selected by
an *ArbOS version* rather than by a boolean `isArbitrum` switch.  Modelling the version
explicitly is what makes historical replay meaningful: applying ArbOS 61 rules to a block
produced under an earlier version would silently invalidate a replay claim.
-/

namespace EvmYul

namespace ArbOS

/-- An ArbOS protocol version.  Only the major number is externally observable. -/
structure Version where
  major : Nat
  deriving DecidableEq, Repr, BEq, Ord, Inhabited

instance : LE Version := ⟨fun v w => v.major ≤ w.major⟩
instance : LT Version := ⟨fun v w => v.major < w.major⟩
instance (v w : Version) : Decidable (v ≤ w) := inferInstanceAs (Decidable (v.major ≤ w.major))
instance (v w : Version) : Decidable (v < w) := inferInstanceAs (Decidable (v.major < w.major))

instance : ToString Version := ⟨fun v => s!"ArbOS {v.major}"⟩

/-- The ArbOS version currently run by Robinhood Chain nodes. -/
def v61 : Version := ⟨61⟩

/--
A scheduled protocol upgrade: from L2 block `activation` onwards, `version` is in force.
-/
structure ProtocolUpgrade where
  activation : Nat
  version    : Version
  deriving DecidableEq, Repr, BEq, Inhabited

/--
The ArbOS version in force at `blockNumber`, given a genesis version and a schedule.

The result is the version of the activated upgrade with the largest activation height, or
`base` when no upgrade has activated yet.  It is *never* a version that does not occur in
the schedule (see `activeArbOS_mem`), so a replay cannot silently be attributed to a
protocol version that the chain never ran.
-/
def activeArbOS (base : Version) (schedule : List ProtocolUpgrade) (blockNumber : Nat) :
    Version :=
  go blockNumber base 0 schedule
where
  go (n : Nat) (best : Version) (bestAt : Nat) : List ProtocolUpgrade → Version
    | [] => best
    | u :: us =>
      if u.activation ≤ n ∧ bestAt ≤ u.activation
      then go n u.version u.activation us
      else go n best bestAt us

@[simp]
theorem activeArbOS_nil (base : Version) (n : Nat) : activeArbOS base [] n = base := rfl

/-- Auxiliary form of `activeArbOS_mem`, generalised over the accumulator. -/
private theorem activeArbOS_go_mem (n : Nat) :
    ∀ (schedule : List ProtocolUpgrade) (best : Version) (bestAt : Nat),
      activeArbOS.go n best bestAt schedule = best ∨
        ∃ u ∈ schedule, u.activation ≤ n ∧ activeArbOS.go n best bestAt schedule = u.version
  | [], _, _ => Or.inl rfl
  | u :: us, best, bestAt => by
    by_cases h : u.activation ≤ n ∧ bestAt ≤ u.activation
    · have ih := activeArbOS_go_mem n us u.version u.activation
      simp only [activeArbOS.go, if_pos h]
      rcases ih with ih | ⟨w, hw, hwn, hweq⟩
      · exact Or.inr ⟨u, List.mem_cons_self, h.1, ih⟩
      · exact Or.inr ⟨w, List.mem_cons_of_mem _ hw, hwn, hweq⟩
    · have ih := activeArbOS_go_mem n us best bestAt
      simp only [activeArbOS.go, if_neg h]
      rcases ih with ih | ⟨w, hw, hwn, hweq⟩
      · exact Or.inl ih
      · exact Or.inr ⟨w, List.mem_cons_of_mem _ hw, hwn, hweq⟩

/--
The active version is either the genesis version or the version of an upgrade that has
actually activated at `blockNumber`.
-/
theorem activeArbOS_mem (base : Version) (schedule : List ProtocolUpgrade) (n : Nat) :
    activeArbOS base schedule n = base ∨
      ∃ u ∈ schedule, u.activation ≤ n ∧ activeArbOS base schedule n = u.version :=
  activeArbOS_go_mem n schedule base 0

/-- Before any upgrade activates, the genesis version is in force. -/
theorem activeArbOS_of_not_activated
    (base : Version) (schedule : List ProtocolUpgrade) (n : Nat)
    (h : ∀ u ∈ schedule, n < u.activation) :
    activeArbOS base schedule n = base := by
  rcases activeArbOS_mem base schedule n with hb | ⟨u, hu, hun, _⟩
  · exact hb
  · exact absurd hun (Nat.not_le.mpr (h u hu))

end ArbOS

end EvmYul
