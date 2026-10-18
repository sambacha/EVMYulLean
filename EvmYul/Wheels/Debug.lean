module

public import EvmYul.Wheels.Json

public section

/-!
# Debugging and profiling helpers

Timing a pure function (`report`) and trying a JSON parser on a string (`testJsonParser`).
-/

namespace EvmYul

namespace DebuggingAndProfiling

section

unsafe def report.{u} {β : Type} {α : Sort u} [Inhabited β] (s : String) (f : α → β) (a : α) : β :=
  dbg_trace s!"BEGIN: {s}"
  let res := timeit s!"The function '{s}' took:" <| pure (f a)
  dbg_trace s!"END: {s}"
  unsafeIO res |>.toOption.get!

def testJsonParser (α : Type) [Repr α] [Lean.FromJson α] (s : String) : String :=
  match Lean.FromJson.fromJson? (α := α) <| (Lean.Json.parse s).toOption.getD Lean.Json.null with
    | .error e  => s!"err: {e}"
    | .ok    ok => s!"ok: {repr ok}"

end

end DebuggingAndProfiling

end EvmYul
