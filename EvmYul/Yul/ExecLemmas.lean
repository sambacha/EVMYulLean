module

public import EvmYul.Yul.Interpreter
public import EvmYul.ProofTags

/-!
# Lemmas about the Yul interpreter

Equations for variable lookup and for `exec` / `eval` on literals, variables, `let`, blocks and
primitive calls at small fuel, used by the reasoning principles and the relational proofs.
-/

public section

namespace EvmYul
namespace Yul

open Ast

@[simp]
theorem ok_match_ok_else_self (s : State) :
    (match s with
     | .Ok _ _ => Except.ok s
     | _ => Except.ok s) = (Except.ok s : Except Exception State) := by
  cases s <;> rfl

@[simp, reviewed_rfl "the Yul step of a primitive, by definition"]
theorem step_yul_add (s : State) (a b : UInt256) :
    step (Operation.ADD : Operation .Yul) none s [a, b] =
      .ok (s, some (UInt256.add a b)) := by
  rfl

@[simp, reviewed_rfl "the Yul step of a primitive, by definition"]
theorem step_yul_sub (s : State) (a b : UInt256) :
    step (Operation.SUB : Operation .Yul) none s [a, b] =
      .ok (s, some (UInt256.sub a b)) := by
  rfl

@[simp, reviewed_rfl "the Yul step of a primitive, by definition"]
theorem step_yul_eq (s : State) (a b : UInt256) :
    step (Operation.EQ : Operation .Yul) none s [a, b] =
      .ok (s, some (UInt256.eq a b)) := by
  rfl

@[simp, reviewed_rfl "Yul variable store API, by definition"]
theorem getElem_eq_lookup (s : State) (id : Identifier) (h : id ∈ s.store) :
    s[id] = State.lookup! id s := by
  rfl

@[expose] def lookupVar (s : State) (id : Identifier) : Literal :=
  s[id]!

theorem lookupVar_ok_eq_lookup!
    (sharedState : EvmYul.SharedState .Yul) (store : VarStore) (id : Identifier) :
    lookupVar (State.Ok sharedState store) id =
      State.lookup! id (State.Ok sharedState store) := by
  by_cases hmem : id ∈ store
  · simp [lookupVar, GetElem?.getElem!, decidableGetElem?, State.store,
      State.instGetElemIdentifierLiteralMemVarStoreStore, State.lookup!, hmem]
  · simp [lookupVar, GetElem?.getElem!, decidableGetElem?, State.store,
      State.lookup!, hmem,
      Finmap.lookup_eq_none.mpr hmem, outOfBounds_eq_default]

@[simp]
theorem lookupVar_ok_sharedState_irrelevant
    (sharedState sharedState2 : EvmYul.SharedState .Yul) (store : VarStore)
    (id : Identifier) :
    lookupVar (State.Ok sharedState store) id =
      lookupVar (State.Ok sharedState2 store) id := by
  rw [lookupVar_ok_eq_lookup!, lookupVar_ok_eq_lookup!]
  rfl

@[simp, reviewed_rfl "variable lookup reads only the variable store, by definition"]
theorem lookup!_ok_sharedState_irrelevant
    (sharedState sharedState2 : EvmYul.SharedState .Yul) (store : VarStore)
    (id : Identifier) :
    State.lookup! id (State.Ok sharedState store) =
      State.lookup! id (State.Ok sharedState2 store) := by
  rfl

@[simp]
theorem getElem!_ok_sharedState_irrelevant
    (sharedState sharedState2 : EvmYul.SharedState .Yul) (store : VarStore)
    (id : Identifier) :
    (State.Ok sharedState store)[id]! =
      (State.Ok sharedState2 store)[id]! := by
  exact lookupVar_ok_sharedState_irrelevant sharedState sharedState2 store id


@[simp]
theorem getElem!_finmap_insert_same_ok
    (sharedState : EvmYul.SharedState .Yul) (store : VarStore)
    (var : Identifier) (val : Literal) :
    (State.Ok sharedState (Finmap.insert var val store))[var]! = val := by
  have hmem : var ∈ Finmap.insert var val store := by
    simp [Finmap.mem_insert]
  simp [GetElem?.getElem!, decidableGetElem?, State.store,
    State.instGetElemIdentifierLiteralMemVarStoreStore, hmem, State.lookup!, Finmap.lookup_insert]

@[simp]
theorem getElem!_finmap_insert_ne_ok
    (sharedState : EvmYul.SharedState .Yul) (store : VarStore)
    {var other : Identifier} (val : Literal) (h : other ≠ var) :
    (State.Ok sharedState (Finmap.insert var val store))[other]! =
      (State.Ok sharedState store)[other]! := by
  by_cases hmem : other ∈ store
  · have hmem_insert : other ∈ Finmap.insert var val store := by
      simp [Finmap.mem_insert, h, hmem]
    simp [GetElem?.getElem!, decidableGetElem?, State.store,
      State.instGetElemIdentifierLiteralMemVarStoreStore, hmem, hmem_insert,
      State.lookup!, Finmap.lookup_insert_of_ne store h]
  · have hmem_insert : other ∉ Finmap.insert var val store := by
      simp [Finmap.mem_insert, h, hmem]
    simp [GetElem?.getElem!, decidableGetElem?, State.store, hmem, hmem_insert]

@[simp]
theorem lookupVar_insert_same_ok
    (sharedState : EvmYul.SharedState .Yul) (store : VarStore)
    (var : Identifier) (val : Literal) :
    lookupVar ((State.Ok sharedState store).insert var val) var = val := by
  simp [State.insert, lookupVar]

@[simp]
theorem lookupVar_finmap_insert_same_ok
    (sharedState : EvmYul.SharedState .Yul) (store : VarStore)
    (var : Identifier) (val : Literal) :
    lookupVar (State.Ok sharedState (Finmap.insert var val store)) var = val := by
  simp [lookupVar]

@[simp]
theorem lookupVar_insert_ne_ok
    (sharedState : EvmYul.SharedState .Yul) (store : VarStore)
    {var other : Identifier} (val : Literal) (h : other ≠ var) :
    lookupVar ((State.Ok sharedState store).insert var val) other =
      lookupVar (State.Ok sharedState store) other := by
  simp [State.insert, lookupVar, h]

@[simp]
theorem lookupVar_finmap_insert_ne_ok
    (sharedState : EvmYul.SharedState .Yul) (store : VarStore)
    {var other : Identifier} (val : Literal) (h : other ≠ var) :
    lookupVar (State.Ok sharedState (Finmap.insert var val store)) other =
      lookupVar (State.Ok sharedState store) other := by
  simp [lookupVar, h]

@[simp]
theorem eval_var_succ
    (fuel : Nat) (id : Identifier) (codeOverride : Option YulContract) (s : State) :
    eval fuel.succ (.Var id) codeOverride s = .ok (s, s[id]!) := by
  simp [eval]

@[simp]
theorem eval_lit_succ
    (fuel : Nat) (lit : Literal) (codeOverride : Option YulContract) (s : State) :
    eval fuel.succ (.Lit lit) codeOverride s = .ok (s, lit) := by
  simp [eval]

@[simp]
theorem evalArgs_nil_succ
    (fuel : Nat) (codeOverride : Option YulContract) (s : State) :
    evalArgs fuel.succ [] codeOverride s = .ok (s, []) := by
  simp [evalArgs]

@[simp]
theorem exec_block_nil_succ
    (fuel : Nat) (codeOverride : Option YulContract) (s : State) :
    exec fuel.succ (.Block []) codeOverride s = .ok s := by
  simp [exec]

@[simp]
theorem exec_block_cons_succ
    (fuel : Nat) (stmt : Stmt) (stmts : List Stmt) (codeOverride : Option YulContract)
    (s : State) :
    exec fuel.succ (.Block (stmt :: stmts)) codeOverride s =
      match exec fuel stmt codeOverride s with
      | .error e => .error e
      | .ok s₁ =>
          match s₁ with
          | .Ok _ _ => exec fuel (.Block stmts) codeOverride s₁
          | _ => .ok s₁ := by
  simp [exec]
  rfl

@[simp]
theorem exec_let_none_succ
    (fuel : Nat) (vars : List Identifier) (codeOverride : Option YulContract) (s : State) :
    exec fuel.succ (.Let vars none) codeOverride s =
      .ok (List.foldr (fun var s => s.insert var ⟨0⟩) s vars) := by
  simp [exec]

@[simp]
theorem exec_let_lit_succ
    (fuel : Nat) (vars : List Identifier) (lit : Literal) (codeOverride : Option YulContract)
    (s : State) :
    exec fuel.succ (.Let vars (some (.Lit lit))) codeOverride s =
      .ok (s.insert vars.head! lit) := by
  simp [exec]

@[simp]
theorem exec_let_var_succ
    (fuel : Nat) (vars : List Identifier) (id : Identifier) (codeOverride : Option YulContract)
    (s : State) :
    exec fuel.succ (.Let vars (some (.Var id))) codeOverride s =
      .ok (s.insert vars.head! s[id]!) := by
  simp [exec]

@[simp]
theorem execPrimCall_add_fuel5
    (fuel : Nat) (var : Identifier) (s : State) (a b : Literal) :
    execPrimCall (fuel + 5) Operation.ADD [var] (.ok (s, [a, b])) =
      .ok (s.insert var (UInt256.add a b)) := by
  cases fuel <;> cases s <;> simp [execPrimCall, primCall, multifill', State.multifill,
    State.insert]

@[simp]
theorem execPrimCall_sub_fuel5
    (fuel : Nat) (var : Identifier) (s : State) (a b : Literal) :
    execPrimCall (fuel + 5) Operation.SUB [var] (.ok (s, [a, b])) =
      .ok (s.insert var (UInt256.sub a b)) := by
  cases fuel <;> cases s <;> simp [execPrimCall, primCall, multifill', State.multifill,
    State.insert]

@[simp]
theorem execPrimCall_eq_fuel5
    (fuel : Nat) (var : Identifier) (s : State) (a b : Literal) :
    execPrimCall (fuel + 5) Operation.EQ [var] (.ok (s, [a, b])) =
      .ok (s.insert var (UInt256.eq a b)) := by
  cases fuel <;> cases s <;> simp [execPrimCall, primCall, multifill', State.multifill,
    State.insert]

@[simp]
theorem evalPrimCall_eq_fuel5
    (fuel : Nat) (s : State) (a b : Literal) :
    evalPrimCall (fuel + 5) Operation.EQ (.ok (s, [a, b])) =
      .ok (s, UInt256.eq a b) := by
  cases fuel <;> simp [evalPrimCall, head', primCall]

@[simp]
theorem exec_let_add_var_lit_succ6
    (fuel : Nat) (var x : Identifier) (n : Literal)
    (codeOverride : Option YulContract) (s : State) :
    exec fuel.succ.succ.succ.succ.succ.succ
      (.Let [var] (some (.Call (Sum.inl Operation.ADD) [.Var x, .Lit n])))
      codeOverride s =
      .ok (s.insert var (UInt256.add (lookupVar s x) n)) := by
  simp [exec, evalArgs, evalTail, reverse', cons', lookupVar]

@[simp]
theorem exec_let_sub_var_lit_succ6
    (fuel : Nat) (var x : Identifier) (n : Literal)
    (codeOverride : Option YulContract) (s : State) :
    exec fuel.succ.succ.succ.succ.succ.succ
      (.Let [var] (some (.Call (Sum.inl Operation.SUB) [.Var x, .Lit n])))
      codeOverride s =
      .ok (s.insert var (UInt256.sub (lookupVar s x) n)) := by
  simp [exec, evalArgs, evalTail, reverse', cons', lookupVar]

@[simp]
theorem exec_let_eq_var_lit_succ6
    (fuel : Nat) (var x : Identifier) (n : Literal)
    (codeOverride : Option YulContract) (s : State) :
    exec fuel.succ.succ.succ.succ.succ.succ
      (.Let [var] (some (.Call (Sum.inl Operation.EQ) [.Var x, .Lit n])))
      codeOverride s =
      .ok (s.insert var (UInt256.eq (lookupVar s x) n)) := by
  simp [exec, evalArgs, evalTail, reverse', cons', lookupVar]

@[simp]
theorem eval_eq_var_lit_succ7
    (fuel : Nat) (x : Identifier) (n : Literal)
    (codeOverride : Option YulContract) (s : State) :
    eval fuel.succ.succ.succ.succ.succ.succ.succ
      (.Call (Sum.inl Operation.EQ) [.Var x, .Lit n])
      codeOverride s =
      .ok (s, UInt256.eq (lookupVar s x) n) := by
  simp [eval, evalArgs, evalTail, reverse', cons', lookupVar]

@[simp]
theorem exec_block_single_let_add_var_lit_succ7
    (fuel : Nat) (var x : Identifier) (n : Literal)
    (codeOverride : Option YulContract) (s : State) :
    exec fuel.succ.succ.succ.succ.succ.succ.succ
      (.Block [.Let [var] (some (.Call (Sum.inl Operation.ADD) [.Var x, .Lit n]))])
      codeOverride s =
      .ok (s.insert var (UInt256.add (lookupVar s x) n)) := by
  simp [lookupVar]

@[simp]
theorem exec_block_single_let_sub_var_lit_succ7
    (fuel : Nat) (var x : Identifier) (n : Literal)
    (codeOverride : Option YulContract) (s : State) :
    exec fuel.succ.succ.succ.succ.succ.succ.succ
      (.Block [.Let [var] (some (.Call (Sum.inl Operation.SUB) [.Var x, .Lit n]))])
      codeOverride s =
      .ok (s.insert var (UInt256.sub (lookupVar s x) n)) := by
  simp [lookupVar]

@[simp]
theorem exec_block_single_let_eq_var_lit_succ7
    (fuel : Nat) (var x : Identifier) (n : Literal)
    (codeOverride : Option YulContract) (s : State) :
    exec fuel.succ.succ.succ.succ.succ.succ.succ
      (.Block [.Let [var] (some (.Call (Sum.inl Operation.EQ) [.Var x, .Lit n]))])
      codeOverride s =
      .ok (s.insert var (UInt256.eq (lookupVar s x) n)) := by
  simp [lookupVar]

@[simp]
theorem exec_if_eq_var_lit_break_succ7
    (fuel : Nat) (x : Identifier) (n : Literal)
    (codeOverride : Option YulContract) (s : State) :
    exec fuel.succ.succ.succ.succ.succ.succ.succ
      (.If (.Call (Sum.inl Operation.EQ) [.Var x, .Lit n]) [.Break])
      codeOverride s =
      .ok (if UInt256.eq (lookupVar s x) n ≠ ⟨0⟩ then 💔 s else s) := by
  simp [exec, eval, evalArgs, evalTail, reverse', cons', lookupVar]
  split <;> rfl

@[simp]
theorem exec_block_single_let_none_succ_succ
    (fuel : Nat) (vars : List Identifier) (codeOverride : Option YulContract) (s : State) :
    exec fuel.succ.succ (.Block [.Let vars none]) codeOverride s =
      .ok (List.foldr (fun var s => s.insert var ⟨0⟩) s vars) := by
  simp

@[simp]
theorem exec_block_single_let_lit_succ_succ
    (fuel : Nat) (vars : List Identifier) (lit : Literal) (codeOverride : Option YulContract)
    (s : State) :
    exec fuel.succ.succ (.Block [.Let vars (some (.Lit lit))]) codeOverride s =
      .ok (s.insert vars.head! lit) := by
  simp

@[simp]
theorem exec_block_single_let_var_succ_succ
    (fuel : Nat) (vars : List Identifier) (id : Identifier) (codeOverride : Option YulContract)
    (s : State) :
    exec fuel.succ.succ (.Block [.Let vars (some (.Var id))]) codeOverride s =
      .ok (s.insert vars.head! s[id]!) := by
  simp

@[simp]
theorem exec_block_single_let_none_one
    (vars : List Identifier) (codeOverride : Option YulContract) (s : State) :
    exec 1 (.Block [.Let vars none]) codeOverride s = .error .OutOfFuel := by
  simp [exec]

@[simp]
theorem exec_block_single_let_lit_one
    (vars : List Identifier) (lit : Literal) (codeOverride : Option YulContract) (s : State) :
    exec 1 (.Block [.Let vars (some (.Lit lit))]) codeOverride s = .error .OutOfFuel := by
  simp [exec]

@[simp]
theorem exec_block_single_let_var_one
    (vars : List Identifier) (id : Identifier) (codeOverride : Option YulContract) (s : State) :
    exec 1 (.Block [.Let vars (some (.Var id))]) codeOverride s = .error .OutOfFuel := by
  simp [exec]

@[simp]
theorem exec_continue_succ
    (fuel : Nat) (codeOverride : Option YulContract) (s : State) :
    exec fuel.succ .Continue codeOverride s = .ok (🔁 s) := by
  simp [exec]

@[simp]
theorem exec_break_succ
    (fuel : Nat) (codeOverride : Option YulContract) (s : State) :
    exec fuel.succ .Break codeOverride s = .ok (💔 s) := by
  simp [exec]

@[simp]
theorem exec_leave_succ
    (fuel : Nat) (codeOverride : Option YulContract) (s : State) :
    exec fuel.succ .Leave codeOverride s = .ok (🚪 s) := by
  simp [exec]

end Yul
end EvmYul
