module

/-!
# Running `IO` inside pure code

`totallySafePerformIO`, the bridge the precompile and trie helpers use to call external programs
from pure definitions. Its logical value is `default`; the compiled code runs the `IO` action
(`TCB.md`).
-/

public section

unsafe def unsafePerformIO {τ} [Inhabited τ] (io : IO τ) : τ :=
  match unsafeIO io with
    | Except.ok    a => a
    | Except.error e => panic! s!"unsafePerformIO was a not great idea after all: {e}"

@[expose, implemented_by unsafePerformIO]
def totallySafePerformIO {τ} [Inhabited τ] (io : IO τ) : τ := Inhabited.default
