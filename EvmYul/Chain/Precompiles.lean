import Batteries.Data.RBMap

import EvmYul.ArbOS.Precompiles
import EvmYul.State.Account

/-!
# Chain-aware precompile registry

The generic model recognises precompiles through the global set `π = {1,…,10}`
(`EvmYul/State/Account.lean`).  That is an Ethereum fact, not a universal one: an Arbitrum
chain additionally routes calls to the ArbOS system contracts.

This module replaces the global notion with a registry keyed by address (RFC §18) and
composes profiles instead of copying them:

```text
robinhoodPrecompiles = ethereumPrecompiles.extend arbOS61SystemContracts
```

Lookup is a persistent map rather than a list scan, as required by RFC §31.2.
-/

namespace EvmYul

open Batteries (RBMap)

/-- What kind of code sits behind a precompile address. -/
inductive PrecompileKind where
  /-- One of the Ethereum precompiles, executed by `EvmYul.EVM.Ξ_precompile`. -/
  | ethereumBuiltin
  /-- An ArbOS system contract, executed by the ArbOS layer. -/
  | arbOSSystem (contract : ArbOS.SystemContract)

/-- A registry entry. -/
structure Precompile where
  address : AccountAddress
  name    : String
  kind    : PrecompileKind

/-- A chain's precompile surface. -/
structure PrecompileRegistry where
  entries : RBMap AccountAddress Precompile compare

namespace PrecompileRegistry

def empty : PrecompileRegistry := ⟨RBMap.empty⟩

instance : Inhabited PrecompileRegistry := ⟨empty⟩

def ofList (ps : List Precompile) : PrecompileRegistry :=
  ⟨ps.foldl (fun acc p => acc.insert p.address p) RBMap.empty⟩

def lookup (r : PrecompileRegistry) (a : AccountAddress) : Option Precompile :=
  r.entries.find? a

def isPrecompile (r : PrecompileRegistry) (a : AccountAddress) : Bool :=
  (r.lookup a).isSome

/-- Add (or override) entries.  Used to layer ArbOS on top of Ethereum. -/
def extend (r : PrecompileRegistry) (ps : List Precompile) : PrecompileRegistry :=
  ⟨ps.foldl (fun acc p => acc.insert p.address p) r.entries⟩

/-- Add every system contract of an ArbOS registry. -/
def extendWithSystemContracts
    (r : PrecompileRegistry) (reg : ArbOS.Registry) : PrecompileRegistry :=
  r.extend (reg.toList.map fun (a, c) =>
    { address := a, name := c.name, kind := .arbOSSystem c })

/-- The ArbOS system contract at `a`, if the registry routes `a` to one. -/
def systemContract? (r : PrecompileRegistry) (a : AccountAddress) :
    Option ArbOS.SystemContract :=
  match r.lookup a with
    | some ⟨_, _, .arbOSSystem c⟩ => some c
    | _ => none

end PrecompileRegistry

/-- The Ethereum precompiles, `π = {1,…,10}` (Yellow Paper (142)). -/
def ethereumPrecompiles : PrecompileRegistry :=
  PrecompileRegistry.ofList
    [ { address := 1,  name := "ECREC",       kind := .ethereumBuiltin }
    , { address := 2,  name := "SHA256",      kind := .ethereumBuiltin }
    , { address := 3,  name := "RIP160",      kind := .ethereumBuiltin }
    , { address := 4,  name := "ID",          kind := .ethereumBuiltin }
    , { address := 5,  name := "EXPMOD",      kind := .ethereumBuiltin }
    , { address := 6,  name := "BN_ADD",      kind := .ethereumBuiltin }
    , { address := 7,  name := "BN_MUL",      kind := .ethereumBuiltin }
    , { address := 8,  name := "SNARKV",      kind := .ethereumBuiltin }
    , { address := 9,  name := "BLAKE2_F",    kind := .ethereumBuiltin }
    , { address := 10, name := "POINT_EVAL",  kind := .ethereumBuiltin } ]

/-- The Robinhood/Arbitrum surface: Ethereum precompiles plus ArbOS 61 system contracts. -/
def arbitrumPrecompiles : PrecompileRegistry :=
  ethereumPrecompiles.extendWithSystemContracts ArbOS.arbOS61SystemContracts

/-! ### Agreement with the Ethereum precompile set -/

/-- Every member of `π` is in the Ethereum registry. -/
theorem ethereumPrecompiles_contains_π :
    ∀ a ∈ (List.range 11).tail, ethereumPrecompiles.isPrecompile (AccountAddress.ofNat a) := by
  decide

/-- `0` and `11` are not Ethereum precompiles, matching `π`. -/
theorem ethereumPrecompiles_not_contains :
    ethereumPrecompiles.isPrecompile 0 = false ∧
    ethereumPrecompiles.isPrecompile 11 = false := by
  constructor <;> rfl

/-- Layering ArbOS on top does not remove any Ethereum precompile. -/
theorem arbitrumPrecompiles_contains_ethereum :
    ∀ a ∈ (List.range 11).tail, arbitrumPrecompiles.isPrecompile (AccountAddress.ofNat a) := by
  decide

/-- ArbSys is reachable on an Arbitrum profile and is not an Ethereum builtin. -/
theorem arbitrumPrecompiles_arbSys :
    (arbitrumPrecompiles.systemContract? ArbOS.ArbSysAddress).isSome = true ∧
    ethereumPrecompiles.isPrecompile ArbOS.ArbSysAddress = false := by
  constructor <;> rfl

end EvmYul
