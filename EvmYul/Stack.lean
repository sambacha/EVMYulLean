module

public import EvmYul.ProofTags

/-!
# The machine stack

`Stack α` as a list with `push`, `pop`, the multi-element `pop2` … `pop7`, and its rewriting
lemmas.
-/

public section

namespace EvmYul

@[expose] abbrev Stack (α : Type) := List α

namespace Stack

variable {α : Type}

@[expose] def new : Stack α := []

@[expose] def isEmpty (s : Stack α) := List.isEmpty s

@[expose] def size (s : Stack α) : Nat := List.length s
@[expose] def push (s : Stack α) (v : α) : Stack α := v :: s

@[expose] def pop : Stack α → Option (Stack α × α)
  | hd :: tl => .some (tl, hd)
  | []       => .none

@[expose] def pop2 : Stack α → Option (Stack α × α × α)
  | hd :: hd₁ :: tl => .some (tl, hd, hd₁)
  | _               => .none

@[expose] def pop3 : Stack α → Option (Stack α × α × α × α)
  | hd :: hd₁ :: hd₂ :: tl => .some (tl, hd, hd₁, hd₂)
  | _                      => .none

@[expose] def pop4 : Stack α → Option (Stack α × α × α × α × α)
  | hd :: hd₁ :: hd₂ :: hd₃ :: tl => .some (tl, hd, hd₁, hd₂, hd₃)
  | _                             => .none

@[expose] def pop5 : Stack α → Option (Stack α × α × α × α × α × α)
  | hd :: hd₁ :: hd₂ :: hd₃ :: hd₄ :: tl => .some (tl, hd, hd₁, hd₂, hd₃, hd₄)
  | _                             => .none

@[expose] def pop6 : Stack α → Option (Stack α × α × α × α × α × α × α)
  | hd :: hd₁ :: hd₂ :: hd₃ :: hd₄ :: hd₅ :: tl => .some (tl, hd, hd₁, hd₂, hd₃, hd₄, hd₅)
  | _                             => .none

@[expose] def pop7 : Stack α → Option (Stack α × α × α × α × α × α × α × α)
  | hd :: hd₁ :: hd₂ :: hd₃ :: hd₄ :: hd₅ :: hd₆ :: tl =>
    .some (tl, hd, hd₁, hd₂, hd₃, hd₄, hd₅, hd₆)
  | _                             => .none

section StackLemmas

variable {x : α} {s : Stack α}

@[simp, reviewed_rfl "stack API, by definition"]
theorem isEmpty_push_false : (s.push x).isEmpty = false := rfl

@[simp, reviewed_rfl "stack API, by definition"]
theorem isEmpty_nil : Stack.isEmpty (α := α) [] := rfl

@[simp, reviewed_rfl "stack API, by definition"]
theorem isEmpty_cons_false : Stack.isEmpty (α := α) (x :: s) = false := rfl

@[simp, reviewed_rfl "stack API, by definition"]
theorem size_nil : Stack.size (α := α) [] = 0 := rfl

@[simp, reviewed_rfl "stack API, by definition"]
theorem size_new : Stack.new.size (α := α) = 0 := rfl

@[simp, reviewed_rfl "stack API, by definition"]
theorem size_cons : Stack.size (α := α) (x :: s) = Stack.size s + 1 := rfl

theorem size_zero_iff_isEmpty_eq_true : s.size = 0 ↔ s.isEmpty = true := by
  cases s <;> simp

@[simp, reviewed_rfl "stack API, by definition"]
theorem size_push : (s.push x).size = s.size + 1 := rfl

@[simp, reviewed_rfl "stack API, by definition"]
theorem pop_push : (s.push x).pop = some (s, x) := rfl

end StackLemmas

@[expose] instance {α} : Inhabited (Stack α) := ⟨Stack.new⟩
@[expose] instance {α} [DecidableEq α] : DecidableEq (Stack α) := inferInstanceAs (DecidableEq (List α))
@[expose] instance {α} : EmptyCollection (Stack α) := ⟨Stack.new⟩

end Stack

@[expose] instance {α : Type} [ToString α] : ToString (Stack α) := inferInstanceAs (ToString (List α))

end EvmYul
