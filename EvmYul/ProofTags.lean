module

public meta import Lean.Elab.Attributes
public meta import Lean.Compiler.InitAttr

/-!
# Review tags for the proof-term audits

The project-wide proof-term audits (`Audits/TestSuite.lean` SA2, `Audits/GasLint.lean` A5) reject a
theorem whose proof term is literally `rfl`, and a theorem whose statement mentions no definition of
the project, unless the theorem has been reviewed. The review used to be three central lists in the
audit files, so every new `rfl` lemma anywhere meant editing a file shared by the whole project
(`GUIDELINES.md` Rule 10). The review is now an attribute on the theorem itself, next to its proof:

* `@[reviewed_rfl "reason"]` — the theorem is proved by `rfl` and restates a definition (rewriting
  API: an equation form, a projection, a fork table entry).
* `@[reviewed_pin Partner.name]` — the theorem is proved by `rfl` and pins a value (a golden pin);
  `Partner.name` is a theorem about the same behaviour that is **not** proved by `rfl`, so the pinned
  value is backed by reasoning. The partner may be declared later or in another module, so it is
  written fully qualified and resolved by the audit, which fails if it does not exist.
* `@[reviewed_generic "reason"]` — the theorem legitimately mentions no definition of the project
  (an `Except` plumbing lemma, a tree map fact, an arithmetic helper).

Each attribute accepts theorems only, and the reason must not be empty. The audits collect the tags
from the environment (`taggedEntries`) and fail on a stale tag, so the tags stay exact.
-/

public meta section

namespace EvmYul.ProofTags

open Lean

/-- `@[reviewed_rfl "reason"]`: a theorem proved by `rfl` that restates a definition. -/
syntax (name := reviewed_rfl) "reviewed_rfl " str : attr

/-- `@[reviewed_pin Partner.name]`: a theorem proved by `rfl` that pins a value; `Partner.name` (fully
qualified) is a theorem about the same behaviour that is not proved by `rfl`. -/
syntax (name := reviewed_pin) "reviewed_pin " ident : attr

/-- `@[reviewed_generic "reason"]`: a theorem that legitimately mentions no project definition. -/
syntax (name := reviewed_generic) "reviewed_generic " str : attr

/-- Fail unless `decl` is a theorem (the tags review proof terms, so they make no sense elsewhere). -/
def requireTheorem (attr : String) (decl : Name) : AttrM Unit := do
  -- the private view of the environment: in a module, a public theorem is exported as an axiom;
  -- `findAsync?` because its proof may still be elaborating (its kind is known immediately)
  let isThm := (((← getEnv).setExporting false).findAsync? decl).any (·.kind == .thm)
  unless isThm do throwError "@[{attr}] applies to theorems only, and `{decl}` is not a theorem"

/-- The non-empty reason string of a `reviewed_rfl` / `reviewed_generic` attribute. -/
def reasonOf (attr : String) (decl : Name) (stx : Syntax) : AttrM String := do
  requireTheorem attr decl
  let some r := stx[1].isStrLit? | throwError "@[{attr}] expects a reason string"
  if r.trimAscii.isEmpty then throwError "@[{attr}] on `{decl}`: the reason must not be empty"
  return r

/-- The attribute `reviewed_rfl`; its parameter is the reason. -/
initialize reviewedRflAttr : ParametricAttribute String ←
  registerParametricAttribute {
    name := `reviewed_rfl
    descr := "reviewed theorem proved by `rfl` that restates a definition (rewriting API)"
    getParam := reasonOf "reviewed_rfl" }

/-- The attribute `reviewed_pin`; its parameter is the partner theorem (fully qualified). -/
initialize reviewedPinAttr : ParametricAttribute Name ←
  registerParametricAttribute {
    name := `reviewed_pin
    descr := "reviewed golden pin proved by `rfl`, backed by a partner theorem that is not"
    getParam := fun decl stx => do
      requireTheorem "reviewed_pin" decl
      let partner := stx[1].getId.eraseMacroScopes
      if partner.isAnonymous then throwError "@[reviewed_pin] expects the partner theorem's name"
      if partner == decl then throwError "@[reviewed_pin] on `{decl}`: a pin cannot be its own partner"
      return partner }

/-- The attribute `reviewed_generic`; its parameter is the reason. -/
initialize reviewedGenericAttr : ParametricAttribute String ←
  registerParametricAttribute {
    name := `reviewed_generic
    descr := "reviewed theorem that legitimately mentions no definition of the project"
    getParam := reasonOf "reviewed_generic" }

/-- Every declaration tagged with `attr` in the environment (imported modules and the current one),
with its parameter. -/
def taggedEntries {α : Type} [Inhabited α] (attr : ParametricAttribute α) (env : Environment) :
    Array (Name × α) := Id.run do
  let mut out := #[]
  for i in [0:env.header.moduleNames.size] do
    out := out ++ attr.ext.getModuleEntries env i
  for (n, a) in (attr.ext.getState env).2 do
    out := out.push (n, a)
  return out

end EvmYul.ProofTags
