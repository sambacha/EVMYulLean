import EvmYul.Wheels

/-!
# Arbitrum L1 → L2 address aliasing

When a message originates from an L1 *contract*, Nitro presents the sender on L2 under an
aliased address

```text
f(A) = (A + 0x1111000000000000000000000000000000001111) mod 2^160
```

so that an L2 contract cannot be impersonated by an L1 contract sitting at the same
address.  Because `AccountAddress` is `Fin 2^160`, the reduction modulo `2^160` is exactly
the `Fin` group operation and no bespoke modular arithmetic is needed.

Getting this wrong invalidates every access-control argument about an L1-originated call
(RFC §32.1), so the round trip is proved rather than tested.
-/

namespace EvmYul

namespace ArbOS

/-- The Arbitrum alias offset, `0x1111000000000000000000000000000000001111`. -/
def addressAliasOffset : AccountAddress := 0x1111000000000000000000000000000000001111

/-- Alias an L1 contract address for presentation as an L2 sender. -/
def applyAddressAlias (a : AccountAddress) : AccountAddress := a + addressAliasOffset

/-- Recover the L1 contract address from an aliased L2 sender. -/
def undoAddressAlias (a : AccountAddress) : AccountAddress := a - addressAliasOffset

@[simp]
theorem undoAddressAlias_applyAddressAlias (a : AccountAddress) :
    undoAddressAlias (applyAddressAlias a) = a := by
  simp [undoAddressAlias, applyAddressAlias]

@[simp]
theorem applyAddressAlias_undoAddressAlias (a : AccountAddress) :
    applyAddressAlias (undoAddressAlias a) = a := by
  simp [undoAddressAlias, applyAddressAlias]

theorem applyAddressAlias_injective :
    Function.Injective applyAddressAlias := by
  intro a b h
  have := congrArg undoAddressAlias h
  simpa using this

theorem undoAddressAlias_injective :
    Function.Injective undoAddressAlias := by
  intro a b h
  have := congrArg applyAddressAlias h
  simpa using this

theorem applyAddressAlias_surjective :
    Function.Surjective applyAddressAlias :=
  fun a => ⟨undoAddressAlias a, applyAddressAlias_undoAddressAlias a⟩

theorem applyAddressAlias_bijective :
    Function.Bijective applyAddressAlias :=
  ⟨applyAddressAlias_injective, applyAddressAlias_surjective⟩

/--
Aliasing stays inside the 160-bit address domain.  This is immediate for `Fin`, and is
recorded explicitly because RFC §10.3 requires it.
-/
theorem applyAddressAlias_lt_size (a : AccountAddress) :
    (applyAddressAlias a).val < AccountAddress.size :=
  (applyAddressAlias a).isLt

theorem undoAddressAlias_lt_size (a : AccountAddress) :
    (undoAddressAlias a).val < AccountAddress.size :=
  (undoAddressAlias a).isLt

/-- Aliasing is a fixed shift: it never maps two distinct L1 addresses together. -/
theorem applyAddressAlias_ne (a b : AccountAddress) (h : a ≠ b) :
    applyAddressAlias a ≠ applyAddressAlias b :=
  fun heq => h (applyAddressAlias_injective heq)

/--
The alias offset is odd, hence nonzero: no address is its own alias.
-/
theorem applyAddressAlias_ne_self (a : AccountAddress) : applyAddressAlias a ≠ a := by
  intro h
  have h' : a + addressAliasOffset = a + 0 := by simpa [applyAddressAlias] using h
  have : addressAliasOffset = (0 : AccountAddress) := add_left_cancel h'
  exact absurd (congrArg Fin.val this) (by decide)

end ArbOS

end EvmYul
