import EvmYul
import Conform
import Conform.Main
import EvmYulTests
import ConformTests
import Audits

/-!
# Declaration inventory (refactoring guard)

`lake env lean tools/repo/DeclInventory.lean > after.txt` prints one line per declaration of the
project (`EvmYul.*`, `Conform.*`, the test indexes and the audits): its name, its kind and a hash of
its type. A pure move of files (the layout refactors of `GUIDELINES.md` §3) must leave this list
unchanged — diff the output taken before and after the move. Module names are deliberately *not*
printed, because a move changes them by design; the declaration names and their statements are the
public API that must not change.

Compiler-generated auxiliary declarations are skipped (their names depend on elaboration order).
Names of `private` declarations embed the name of the module that declares them
(`_private.<Module>.0.<name>`), so a move changes them, and with them the hash of every statement
that mentions one; the hash is therefore taken after replacing each private name by its user-facing
name. `Conform.Main` is the one executable root imported (the others also define `main`).
-/

open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  let mut rows : Array String := #[]
  for (n, ci) in env.constants.map₁.toList do
    let some i := env.getModuleIdxFor? n | continue
    let root := env.header.moduleNames[i.toNat]!.getRoot
    unless root == `EvmYul || root == `Conform || root == `EvmYulTests || root == `ConformTests ||
        root == `Audits do continue
    if n.isInternal then continue
    let kind := match ci with
      | .thmInfo _ => "theorem" | .defnInfo _ => "def" | .axiomInfo _ => "axiom"
      | .opaqueInfo _ => "opaque" | .inductInfo _ => "inductive" | .ctorInfo _ => "ctor"
      | .recInfo _ => "rec" | .quotInfo _ => "quot"
    let ty := ci.type.replace fun
      | .const c ls => some (.const (privateToUserName c) ls)
      | _ => none
    rows := rows.push s!"{privateToUserName n} {kind} {ty.hash}"
  for r in rows.qsort (· < ·) do IO.println r
