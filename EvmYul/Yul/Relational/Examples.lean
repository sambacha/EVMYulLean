module

public import EvmYul.Yul.Relational.WP
public import EvmYul.Yul.ExecLemmas
public import EvmYul.Yul.WellScoped
public import EvmYul.ProofTags

public section

/-!
# Worked examples for the Yul WP calculus

1. **A loop, proved for every input and every fuel.** `doubling n` is

   ```yul
   { let i := 0  let x := 0  for {} lt(i, n) { i := add(i, 1) } { x := add(x, 2) } }
   ```

   `doubling_wp` proves, with the invariant rule `wp_for` and invariant `x = 2i ∧ i ≤ n`, that every
   result the relational semantics allows is a successful state with `i = n` and `x = 2n`.
   `doubling_exec` and `doubling_exec_error` transfer this to the interpreter `exec` through
   `wp_exec`: whatever the fuel, `exec` either runs out of fuel or returns exactly that state. No
   fuel reasoning appears in the proof.
2. **A counterexample.** `switch_default_error_aborts`: the interpreter runs the `default` block of
   a `switch` even when a case matches, and an error there (here `stop()`) aborts the statement.
   The Yul specification would execute the matching (empty) case and continue.
-/

namespace EvmYul
namespace Yul
namespace Relational

open Ast

/-! ## Builtin facts used by the example -/

theorem primResult_add (s : State) (a b : Literal) :
    primResult s .ADD [a, b] = .ok (s, [UInt256.add a b]) := by
  simp [primResult, primCallK]

theorem primResult_lt (s : State) (a b : Literal) :
    primResult s .LT [a, b] = .ok (s, [UInt256.lt a b]) := by
  simp [primResult, primCallK]
  rfl

theorem add_not_callFamily : (Operation.ADD : PrimOp) ∉ callFamily := by decide
theorem lt_not_callFamily : (Operation.LT : PrimOp) ∉ callFamily := by decide

theorem UInt256.toNat_inj {a b : Literal} (h : a.toNat = b.toNat) : a = b := by
  cases a; cases b; simp only [UInt256.toNat] at h; congr; exact Fin.ext h

@[reviewed_rfl "value of a word constant, by definition"]
theorem UInt256.toNat_one : UInt256.toNat ⟨1⟩ = 1 := rfl
@[reviewed_rfl "value of a word constant, by definition"]
theorem UInt256.toNat_two : UInt256.toNat ⟨2⟩ = 2 := rfl

theorem UInt256.lt_eq_zero_iff (a b : Literal) :
    UInt256.lt a b = ⟨0⟩ ↔ b.toNat ≤ a.toNat := by
  have hlt : a < b ↔ a.toNat < b.toNat := Iff.rfl
  unfold UInt256.lt
  by_cases h : a < b
  · have h' := hlt.1 h
    simp only [h, decide_true, Bool.toUInt256, if_true]
    constructor
    · intro he; exact absurd (congrArg UInt256.toNat he) (by decide)
    · intro hle; omega
  · have h' : b.toNat ≤ a.toNat := by rw [hlt] at h; omega
    simp only [h, decide_false, Bool.toUInt256, h', iff_true]
    rfl

theorem UInt256.toNat_add_of_lt (a b : Literal) (h : a.toNat + b.toNat < UInt256.size) :
    (UInt256.add a b).toNat = a.toNat + b.toNat := by
  simp only [UInt256.add, UInt256.toNat, Fin.val_add] at h ⊢
  exact Nat.mod_eq_of_lt h

/-! ## Worked example: a doubling loop -/

/-- `x := add(x, 2)` (Yul's assignment is the interpreter's `Let` on an existing variable). -/
def dblBody : Stmt := .Let ["x"] (some (.Call (.inl .ADD) [.Var "x", .Lit ⟨2⟩]))
/-- `i := add(i, 1)` -/
def dblPost : Stmt := .Let ["i"] (some (.Call (.inl .ADD) [.Var "i", .Lit ⟨1⟩]))
/-- `lt(i, n)` -/
def dblCond (n : Literal) : Expr := .Call (.inl .LT) [.Var "i", .Lit n]
/-- `for {} lt(i, n) { i := add(i, 1) } { x := add(x, 2) }` -/
def dblLoop (n : Literal) : Stmt := .For (dblCond n) [dblPost] [dblBody]
/-- `{ let i := 0  let x := 0  for {} lt(i, n) { i := add(i, 1) } { x := add(x, 2) } }` -/
def doubling (n : Literal) : Stmt :=
  .Block [.Let ["i"] (some (.Lit ⟨0⟩)), .Let ["x"] (some (.Lit ⟨0⟩)), dblLoop n]

/-- The loop invariant: `x = 2 * i` and `i ≤ n` (as natural numbers). -/
@[expose] def dblInv (n : Literal) (s : State) : Prop :=
  IsOk s ∧ (lookupVar s "x").toNat = 2 * (lookupVar s "i").toNat ∧
    (lookupVar s "i").toNat ≤ n.toNat

/-- The postcondition: the run succeeds with `i = n` and `x = 2 * n`. -/
def dblPostcond (n : Literal) : Res → Prop
  | .ok s => IsOk s ∧ lookupVar s "i" = n ∧ (lookupVar s "x").toNat = 2 * n.toNat
  | .error _ => False

theorem dblLoop_wp (co : Option YulContract) (n : Literal) (hn : 2 * n.toNat < UInt256.size)
    {s : State} (hs : dblInv n s) : wp co (dblLoop n) (dblPostcond n) s := by
  unfold dblLoop
  refine wp_for (Q := dblPostcond n) (dblInv n) (fun s h => h.1) ?_ hs
  rintro s ⟨hok, hx, hi⟩
  cases s with
  | Ok ss st =>
    unfold dblCond
    refine wpE_prim lt_not_callFamily ?_
    refine wpA_cons (wpE_lit (wpA_cons (wpE_var (wpA_nil ?_))))
    simp only [cons', List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      primResult_lt, head', List.head!]
    change (UInt256.lt (lookupVar _ "i") n = _ → _) ∧ (UInt256.lt (lookupVar _ "i") n ≠ _ → _)
    refine ⟨fun h0 => ?_, fun h1 => ?_⟩
    · rw [UInt256.lt_eq_zero_iff] at h0
      have hin : lookupVar (State.Ok ss st) "i" = n := UInt256.toNat_inj (by omega)
      exact ⟨trivial, hin, by rw [hx, hin]⟩
    · rw [Ne, UInt256.lt_eq_zero_iff, not_le] at h1
      unfold dblBody
      refine wp_blockCons (wp_letPrim add_not_callFamily ?_)
      refine wpA_cons (wpE_lit (wpA_cons (wpE_var (wpA_nil ?_))))
      simp only [cons', List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
        primResult_add, multifill', State.multifill, List.zip_cons_cons, List.zip_nil_left,
        List.foldr_cons, List.foldr_nil, State.insert, blockK]
      refine wp_blockNil ⟨trivial, ?_⟩
      unfold dblPost
      refine wp_blockCons (wp_letPrim add_not_callFamily ?_)
      refine wpA_cons (wpE_lit (wpA_cons (wpE_var (wpA_nil ?_))))
      simp only [cons', List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
        primResult_add, multifill', State.multifill, List.zip_cons_cons, List.zip_nil_left,
        List.foldr_cons, List.foldr_nil, State.insert, blockK]
      refine wp_blockNil ⟨trivial, ?_, ?_⟩
      all_goals
        simp only [lookupVar] at hx hi h1 ⊢
        simp only [getElem!_finmap_insert_same_ok,
          getElem!_finmap_insert_ne_ok _ _ _ (show ("x" : Identifier) ≠ "i" by decide),
          getElem!_finmap_insert_ne_ok _ _ _ (show ("i" : Identifier) ≠ "x" by decide)]
      · rw [UInt256.toNat_add_of_lt, UInt256.toNat_add_of_lt] <;>
          simp only [UInt256.toNat_two, UInt256.toNat_one] <;> omega
      · rw [UInt256.toNat_add_of_lt] <;> simp only [UInt256.toNat_one] <;> omega
  | _ => exact hok.elim

/-- **The worked example, at the level of the calculus.** From any ordinary state, every result of
`doubling n` is a successful state with `i = n` and `x = 2n` (when `2n` does not overflow). -/
theorem doubling_wp (co : Option YulContract) (n : Literal) (hn : 2 * n.toNat < UInt256.size)
    (ss : EvmYul.SharedState .Yul) (st : VarStore) :
    wp co (doubling n) (dblPostcond n) (.Ok ss st) := by
  unfold doubling
  refine wp_blockCons (wp_letLit ?_)
  simp only [State.insert, blockK]
  refine wp_blockCons (wp_letLit ?_)
  simp only [State.insert, blockK]
  refine wp_blockCons (wp_mono ?_ (dblLoop_wp co n hn ⟨trivial, ?_, ?_⟩))
  · rintro (e | s) hr
    · exact hr.elim
    · cases s with
      | Ok ss' st' => exact wp_blockNil hr
      | _ => exact hr.1.elim
  all_goals
    simp only [lookupVar, getElem!_finmap_insert_same_ok,
      getElem!_finmap_insert_ne_ok _ _ _ (show ("i" : Identifier) ≠ "x" by decide)]
  · rfl
  · exact Nat.zero_le _

/-- **The worked example, for the interpreter.** Every terminating run of `exec` on `doubling n`,
at any fuel, ends with `i = n` and `x = 2n`. -/
theorem doubling_exec {co : Option YulContract} {n : Literal} (hn : 2 * n.toNat < UInt256.size)
    {ss : EvmYul.SharedState .Yul} {st : VarStore} {fuel : ℕ} {s' : State}
    (h : exec fuel (doubling n) co (.Ok ss st) = .ok s') :
    lookupVar s' "i" = n ∧ (lookupVar s' "x").toNat = 2 * n.toNat :=
  (wp_exec_ok (doubling_wp co n hn ss st) h).2

/-- The only way `exec` can fail on `doubling n` is by running out of fuel. -/
theorem doubling_exec_error {co : Option YulContract} {n : Literal}
    (hn : 2 * n.toNat < UInt256.size) {ss : EvmYul.SharedState .Yul} {st : VarStore} {fuel : ℕ}
    {e : Yul.Exception} (h : exec fuel (doubling n) co (.Ok ss st) = .error e) :
    e = .OutOfFuel := by
  by_contra hne
  exact wp_exec (doubling_wp co n hn ss st) h (by simpa using hne)

/-! ## Counterexample: the `switch` default-block quirk

The Yul specification runs the default block of a `switch` only when no case matches. The
interpreter evaluates the default block *eagerly* (to compute the fallback state) and propagates
its error even when a case matched. Below, case `1` matches and has an empty body, so by the
specification the statement does nothing; the interpreter instead halts with `stop()`'s
`YulHalt`. The relational semantics reproduces this (rule `switchDefaultErr`), so `exec_sound` is
a statement about the interpreter as written, quirk included. -/

/-- `switch 1 case 1 { } default { stop() }` -/
def switchQuirk : Stmt :=
  .Switch (.Lit ⟨1⟩) [(⟨1⟩, [])] [.ExprStmtCall (.Call (.inl .STOP) [])]

theorem switch_default_error_aborts (ss : EvmYul.SharedState .Yul) (st : VarStore) :
    exec 10 switchQuirk none (.Ok ss st) = .error (.YulHalt (.Ok ss st) ⟨0⟩) := by
  have hstop : primCall 7 (State.Ok ss st) Operation.STOP [] =
      .error (.YulHalt (.Ok ss st) ⟨0⟩) := by
    rw [primCall_succ_eq_primCallK]
    simp [primCallK]
    rfl
  simp only [switchQuirk, exec, eval, evalArgs, execSwitchCases, execPrimCall, reverse',
    List.reverse_nil, hstop, multifill']

/-- The relational semantics derives the same aborting result (so the quirk is part of `ExecR`). -/
theorem switchQuirk_execR (ss : EvmYul.SharedState .Yul) (st : VarStore) :
    ExecR none switchQuirk (.Ok ss st) (.error (.YulHalt (.Ok ss st) ⟨0⟩)) :=
  exec_sound (switch_default_error_aborts ss st) (by simp)

/-! ## What the well-scopedness check excludes

Two programs the interpreter runs without complaint but the Yul specification rejects, and which
`WellScoped` rejects. -/

/-- `{ let y := x }` with `x` never declared. -/
def illScopedRead : Stmt := .Block [.Let ["y"] (some (.Var "x"))]

/-- The interpreter silently reads an undeclared variable as `0`. -/
theorem ill_scoped_read_defaults_to_zero (ss : EvmYul.SharedState .Yul) :
    exec 2 illScopedRead none (.Ok ss ∅) = .ok (.Ok ss (Finmap.insert "y" ⟨0⟩ ∅)) := by
  have h0 : lookupVar (State.Ok ss ∅) "x" = ⟨0⟩ := by
    rw [lookupVar_ok_eq_lookup!]
    simp [State.lookup!]
    rfl
  simp only [illScopedRead, exec_block_cons_succ, exec_let_var_succ, List.head!_cons,
    State.insert, exec_block_nil_succ]
  exact congrArg (fun v => Except.ok (State.Ok ss (Finmap.insert "y" v ∅))) h0

theorem illScopedRead_not_wellScoped : ¬ WellScoped illScopedRead := by decide

/-- A top-level `break` escapes as a checkpoint state instead of being rejected. -/
theorem stray_break_escapes (ss : EvmYul.SharedState .Yul) (st : VarStore) :
    exec 1 .Break none (.Ok ss st) = .ok (.Checkpoint (.Break ss st)) := by
  simp [State.setBreak]

/-- The worked example is well scoped, for every bound `n`. -/
theorem doubling_wellScoped (n : Literal) : WellScoped (doubling n) := by
  simp [WellScoped, doubling, dblLoop, dblCond, dblPost, dblBody, checkStmt, checkBlock,
    exprScoped, argsScoped]

end Relational
end Yul
end EvmYul
