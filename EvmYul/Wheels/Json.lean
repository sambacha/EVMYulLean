module

public import Lean.Data.Json
public import Std.Data.TreeMap
public import EvmYul.Wheels.Blob

public section

/-!
# JSON helpers

Reading typed fields with defaults out of `Lean.Json` objects, as the `FromJson` instances of the
model's types (transactions, withdrawals, block headers) and the conformance runner do. Moved from
`Conform/Wheels.lean`: the model must not depend on the test runner (`GUIDELINES.md` Rule 6).
-/

namespace Lean.Json

def getObjValAs!
  (self : Json) (α : Type) (key : String) [Inhabited α] [FromJson α] : α :=
  match self.getObjValAs? α key with
          | .error _ => panic! s!"Expected the key {key} in the map."
          | .ok pre  => pre

/--
Turn non-existance of the key into default initialisation.

This silences ONLY the `property not found:` error.
If the parsing of an existing value fails, we propagate the error.
-/
def getObjValAsD (j : Json) (α : Type) [FromJson α] (k : String) (D : α) : Except String α :=
  match j.getObjVal? k with
    | .error _   => pure D
    | .ok    val => fromJson? val

/--
`getObjValAsD! = getObjValAsD default` for inhabited types.
-/
def getObjValAsD! (j : Json) (α : Type) [FromJson α] [Inhabited α] (k : String) : Except String α :=
  getObjValAsD j α k default

def getObjVals?
  (self : Json) (α β : Type) [Ord α] [FromJson α] [FromJson β] : Except String (Std.TreeMap α β compare) := do
  let keys ← (·.keysArray) <$> self.getObj?
  let mut result : Std.TreeMap α β compare := ∅
  for k in keys do
    if let .ok key := FromJson.fromJson? k then
    result := result.insert key (← self.getObjValAs? β k)
  pure result

def fromFile (path : System.FilePath) : IO Json := do
  let .ok json ← Json.parse <$> IO.FS.readFile path | panic! s!"Failed to parse Json at: {path}"
  pure json

end Lean.Json
