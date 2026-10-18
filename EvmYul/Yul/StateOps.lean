module

public import EvmYul.Yul.State

/-!
# Operations on the Yul state

Variable insertion and lookup, multi-assignment, and the setters for the shared, machine and world
state.
-/

public section

namespace EvmYul

namespace Yul

namespace State

-- | Insert an (identifier, literal) pair into the varstore.
@[expose] def insert (var : Identifier) (val : Literal) : Yul.State → Yul.State
  | (Ok sharedState store) => Ok sharedState (store.insert var val)
  | s => s

-- | Zip a list of variables with a list of literals and insert right-to-left.
@[expose] def multifill (vars : List Identifier) (vals : List Literal) : Yul.State → Yul.State
  | s@(Ok _ _) => (List.zip vars vals).foldr (λ (var, val) s ↦ s.insert var val) s
  | s => s

-- | Overwrite the EvmYul.Yul.State state of some state.
@[expose] def setSharedState (sharedState : EvmYul.SharedState .Yul) : Yul.State → Yul.State
  | Ok _ store => Ok sharedState store
  | s => s

@[expose] def setMachineState (mstate : EvmYul.MachineState) : Yul.State → Yul.State
  | Ok sstate store => Ok {sstate with toMachineState := mstate} store
  | s => s

@[expose] def setState (state : EvmYul.State .Yul) : Yul.State → Yul.State
  | Ok sstate store => Ok {sstate with toState := state} store
  | s => s

-- | Overwrite the varstore of some state.
@[expose] def setStore (s s' : Yul.State) : Yul.State :=
  match s, s' with
    | (Ok sharedState _), (Ok _ store) => Ok sharedState store
    | s, _ => s

@[expose] def setContinue : Yul.State → Yul.State
  | Ok sharedState store => Checkpoint (.Continue sharedState store)
  | s => s

@[expose] def setBreak : Yul.State → Yul.State
  | Ok sharedState store => Checkpoint (.Break sharedState store)
  | s => s

@[simp]
theorem insert_setBreak (s : Yul.State) (var : Identifier) (val : Literal) :
    (State.setBreak s).insert var val = State.setBreak s := by
  cases s <;> simp [State.setBreak, State.insert]

@[expose] def setLeave : Yul.State → Yul.State
  | Ok sharedState store => Checkpoint (.Leave sharedState store)
  | s => s

-- | Indicate that we've hit an infinite loop/ran out of fuel.
@[expose] def diverge : Yul.State → Yul.State
  | Ok _ _ => .OutOfFuel
  | s => s

-- | Initialize function parameters and return values in varstore.
@[expose] def initcall (params : List Identifier) (args : List Literal) : Yul.State → Yul.State
  | s@(Ok _ _) =>
    let s₁ := s.setStore default
    s₁.multifill params args
  | s => s

-- | Since it literally does not matter what happens if the state is non-Ok, we just use the default.
@[expose] def mkOk : Yul.State → Yul.State
  | Checkpoint _ => default
  | s => s

-- | Helper function for `reviveJump`.
@[expose] def revive : Jump → Yul.State
  | .Continue sharedState store => Ok sharedState store
  | .Break sharedState store => Ok sharedState store
  | .Leave sharedState store => Ok sharedState store

-- | Revive a saved state (sharedState, varstore), discarding top-level (sharedState, varstore).
--
-- Called after we've finished executing:
--    * A loop
--    * A function call
--
-- The compiler disallows top-level `Continue`s or `Break`s in function bodies,
-- thus it is safe to assume the state we're reviving is a checkpoint from the
-- expected flavor of `Jump`.
@[expose] def reviveJump : Yul.State → Yul.State
  | Checkpoint c => revive c
  | s => s

-- | If s' is non-Ok, overwrite s with s'.
@[expose] def overwrite? (s s' : Yul.State) : Yul.State :=
  match s' with
    | Ok _ _ => s
    | _ => s'

-- ============================================================================
--  STATE QUERIES
-- ============================================================================

-- | Lookup the literal associated with an variable in the varstore, returning 0 if not found.
@[expose] def lookup! (var : Identifier) : Yul.State → Literal
  | Ok _ store => (store.lookup var).get!
  | Checkpoint (.Continue _ store) => (store.lookup var).get!
  | Checkpoint (.Break _ store) => (store.lookup var).get!
  | Checkpoint (.Leave _ store) => (store.lookup var).get!
  | _ => ⟨0⟩

@[simp]
theorem lookup_insert_same_ok
    (sharedState : EvmYul.SharedState .Yul) (store : VarStore)
    (var : Identifier) (val : Literal) :
    State.lookup! var ((State.Ok sharedState store).insert var val) = val := by
  simp [State.insert, State.lookup!, Finmap.lookup_insert]

@[simp]
theorem lookup_insert_ne_ok
    (sharedState : EvmYul.SharedState .Yul) (store : VarStore)
    {var var' : Identifier} (val : Literal) (h : var' ≠ var) :
    State.lookup! var' ((State.Ok sharedState store).insert var val) =
      State.lookup! var' (State.Ok sharedState store) := by
  simp [State.insert, State.lookup!, Finmap.lookup_insert_of_ne store h]

-- ============================================================================
--  STATE NOTATION
-- ============================================================================

@[expose] def toSharedState : State → EvmYul.SharedState .Yul
  | Ok s _ => s
  | _ => default

@[expose] def executionEnv : State → EvmYul.ExecutionEnv .Yul
  | Ok s _ => s.executionEnv
  | _ => default

@[expose] def toMachineState : State → EvmYul.MachineState
  | Ok s _ => s.toMachineState
  | _ => default

@[expose] def toState : State → EvmYul.State .Yul
  | Ok s _ => s.toState
  | _ => default

@[expose] def store : State → VarStore
  | Ok _ store => store
  | _ => default

-- | All state-related functions should be prefix operators so they can be read right-to-left.

-- Yul.State queries
-- notation:65 s:64"[" var "]!" => Yul.State.lookup! var s

/--
TODO - The notation is a bit of a remnant from EvmYul and it is unnecessarily overzaelous.
This should have been an instance of GetElem in the first place.

N.B. We also ignore the validity condition altogether for the time being.
-/
@[expose] instance : GetElem Yul.State Identifier Literal (λ s idx ↦ idx ∈ s.store) where
  getElem s ident _ := s.lookup! ident

notation "❓" => Yul.State.isOutOfFuel

-- Yul.State transformers
notation:65 s:64 "⟦" var "↦" lit "⟧" => Yul.State.insert var lit s
notation:65 "🔁" s:64 => Yul.State.setContinue s
notation:65 "💔" s:64 => Yul.State.setBreak s
notation:65 "🚪" s:64 => Yul.State.setLeave s
notation:65 s:64 "🏪⟦" s' "⟧" => Yul.State.setStore s s'
notation:65 s:64 "🇪⟦" sharedState "⟧" => Yul.State.setSharedState sharedState s
notation:65 "🪫" s:64 => Yul.State.diverge s
notation:65 "👌" s:64 => Yul.State.mkOk s
notation:65 s:64 "☎️⟦" params "," args "⟧" => Yul.State.initcall params args s
notation:65 s:64 "✏️⟦" s' "⟧?"  => Yul.State.overwrite? s s'
notation:64 (priority := high) "🧟" s:max => Yul.State.reviveJump s

end State

end Yul

end EvmYul
