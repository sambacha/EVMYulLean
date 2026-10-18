module

public import EvmYul.Yul.Gas.MeteredSound

public section

/-!
# Yul gas, part 4: fuel adequacy of the interpreter on the fragment (conjecture K10)

`exec_eq_execG` (`MeteredSound.lean`) says that every run of the interpreter `exec` that does
**not** run out of fuel returns the metered result `(execG c st s).1`. This file supplies the other
half: a static amount of fuel that is always enough.

* `fuelS st`: a syntactic fuel measure. It grows with the **length** of blocks and argument lists
  and with the **nesting depth** of the program, not with its total size: a block costs one unit
  per statement plus the largest need of a single statement.
* `exec_eq_execG_of_fuel`: on the loop-free, call-free fragment, `exec fuel st co s` with
  `fuelS st ≤ fuel` **equals** `(execG c st s).1`, for every start state and every code override.
* `execG_ne_OOF`: on the fragment the metered evaluator never reports running out of fuel, because
  no builtin outside the contract-call family can (`primResult_ne_OOF`).
* `exec_ne_OOF_of_fuel`: hence the interpreter with `fuelS st` fuel never runs out of fuel on a
  fragment program.

The executable mirror of K10 and its concrete bound `4·|ns| + 50` are in
`EvmYul/Yul/Gas/MeteredTests.lean` (`genProg_fuel_adequate`).
-/

namespace EvmYul
namespace Yul
namespace Gas

open Ast Relational

/-! ## The fuel measure -/

mutual

/-- Fuel that is enough to evaluate an expression. -/
@[expose] def fuelE : Expr → ℕ
  | .Lit _ => 1
  | .Var _ => 1
  | .Call _ args => maxFuelE args + 2 * args.length + 3

/-- The largest `fuelE` of a list of expressions (`0` for the empty list). -/
@[expose] def maxFuelE : List Expr → ℕ
  | [] => 0
  | a :: as => max (fuelE a) (maxFuelE as)

end

mutual

/-- Fuel that is enough to execute a statement of the fragment. -/
@[expose] def fuelS : Stmt → ℕ
  | .Block sts => fuelB sts
  | .Let _ none => 1
  | .Let _ (some e) => fuelE e
  | .ExprStmtCall e => fuelE e
  | .If cond body => max (fuelE cond) (fuelB body) + 1
  | .Switch cond cases dflt => max (fuelE cond) (max (fuelCases cases) (fuelB dflt)) + 1
  | .For _ _ _ => 0
  | .Continue => 1
  | .Break => 1
  | .Leave => 1

/-- Fuel that is enough to execute a block: one unit per statement plus the largest need. -/
@[expose] def fuelB : List Stmt → ℕ
  | [] => 1
  | st :: sts => max (fuelS st) (fuelB sts) + 1

/-- Fuel that is enough to run every case body of a `switch` (`execSwitchCases`). -/
@[expose] def fuelCases : List (Literal × List Stmt) → ℕ
  | [] => 0
  | (_, body) :: rest => max (fuelB body) (fuelCases rest) + 1

end

theorem fuelE_le_maxFuelE : ∀ {as : List Expr} {a : Expr}, a ∈ as → fuelE a ≤ maxFuelE as
  | [], _, h => by simp at h
  | b :: as, a, h => by
    simp only [maxFuelE]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (fuelE_le_maxFuelE h) (le_max_right _ _)

theorem fragArgs_mem : ∀ {as : List Expr} {a : Expr}, fragArgs as = true → a ∈ as → fragE a = true
  | [], _, _, h => by simp at h
  | b :: as, a, hf, h => by
    simp only [fragArgs, Bool.and_eq_true] at hf
    rcases List.mem_cons.mp h with rfl | h
    · exact hf.1
    · exact fragArgs_mem hf.2 h

variable (c : CostModel)

/-! ## Arguments, left to right -/

/-- Evaluate a list of expressions **left to right** with the metered evaluator's results (no
fuel). The interpreter's `evalArgs` computes this; `argsG` is it on the reversed list. -/
def argsL : List Expr → State → ResL
  | [], s => .ok (s, [])
  | a :: as, s =>
    match (evalG c a s).1 with
    | .error e => .error e
    | .ok (s₁, v) => cons' v (argsL as s₁)

theorem argsL_snoc : ∀ (l : List Expr) (a : Expr) (s : State),
    argsL c (l ++ [a]) s =
      match argsL c l s with
      | .error e => .error e
      | .ok (s₁, vs) =>
        match (evalG c a s₁).1 with
        | .error e => .error e
        | .ok (s₂, v) => .ok (s₂, vs ++ [v]) := by
  intro l a s
  induction l generalizing s with
  | nil =>
    simp only [List.nil_append, argsL]
    rcases (evalG c a s).1 with e | ⟨s₂, v⟩ <;> rfl
  | cons b l ih =>
    simp only [List.cons_append, argsL]
    rcases (evalG c b s).1 with e | ⟨s₁, v⟩
    · rfl
    · simp only [ih]
      rcases argsL c l s₁ with e | ⟨s₂, vs⟩
      · rfl
      · simp only [cons']
        rcases (evalG c a s₂).1 with e | ⟨s₃, w⟩ <;> rfl

theorem argsG_eq_argsL : ∀ (l : List Expr) (s : State), (argsG c l s).1 = argsL c l.reverse s := by
  intro l s
  induction l generalizing s with
  | nil => rfl
  | cons a as ih =>
    rw [List.reverse_cons, argsL_snoc, ← ih]
    simp only [argsG]
    rcases argsG c as s with ⟨e | ⟨s₁, vs⟩, g⟩
    · rfl
    · dsimp only
      rcases evalG c a s₁ with ⟨e | ⟨s₂, v⟩, g'⟩ <;> rfl

/-- The interpreter's `evalArgs` computes `argsL`, given enough fuel for every argument. -/
theorem evalArgs_eq_argsL {co : Option YulContract} {M : ℕ} :
    ∀ (l : List Expr) (f : ℕ) (s : State),
    (∀ a ∈ l, ∀ (f : ℕ) (s : State), fuelE a ≤ f → eval f a co s = (evalG c a s).1) →
    (∀ a ∈ l, fuelE a ≤ M) → M + 2 * l.length + 1 ≤ f →
    evalArgs f l co s = argsL c l s := by
  intro l
  induction l with
  | nil =>
    intro f s _ _ hf
    obtain ⟨f, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    simp [argsL, evalArgs]
  | cons a as ih =>
    intro f s H hM hf
    simp only [List.length_cons] at hf
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 2 := ⟨f - 2, by omega⟩
    have ha : eval (g + 1) a co s = (evalG c a s).1 :=
      H a List.mem_cons_self _ _ (le_trans (hM a List.mem_cons_self) (by omega))
    simp only [evalArgs, ha, argsL]
    rcases (evalG c a s).1 with e | ⟨s₁, v⟩
    · simp [evalTail]
    · simp only [evalTail]
      rw [ih g s₁ (fun b hb => H b (List.mem_cons_of_mem _ hb))
        (fun b hb => hM b (List.mem_cons_of_mem _ hb)) (by omega)]

/-! ## Builtins -/

/-- With fuel, the interpreter's `primCall` of a builtin outside the contract-call family is
`primResult`. -/
theorem primCall_eq_primResult {prim : PrimOp} (hp : prim ∉ callFamily) {f : ℕ} (hf : 1 ≤ f)
    (s : State) (args : List Literal) : primCall f s prim args = primResult s prim args := by
  obtain ⟨n, rfl⟩ : ∃ n, f = n + 1 := ⟨f - 1, by omega⟩
  rw [primCall_succ_eq_primCallK, primResult]
  exact primCallK_indep hp _ _ s args

/-! ## Builtins that never report running out of fuel -/

theorem execBinOp_ne_OOF (f : Primop.Binary) (s : State) (args : List Literal) :
    Yul.execBinOp f s args ≠ .error .OutOfFuel := by
  unfold Yul.execBinOp; split <;> simp [throw, throwThe, MonadExceptOf.throw]

theorem execUnOp_ne_OOF (f : Primop.Unary) (s : State) (args : List Literal) :
    Yul.execUnOp f s args ≠ .error .OutOfFuel := by
  unfold Yul.execUnOp; split <;> simp [throw, throwThe, MonadExceptOf.throw]

theorem lift_ne_OOF {r : Except Yul.Exception (State × Option Literal)}
    (h : r ≠ .error .OutOfFuel) :
    ¬ (match r with
      | .ok (s, lit) => .ok (s, lit.toList)
      | .error e => .error e : ResL) = OOF := by
  rcases r with e | ⟨s, l⟩
  · intro h'; cases h'; exact h rfl
  · simp [OOF]

/-- Builtins proved never to report running out of fuel (`primResult_ne_OOF`): the arithmetic,
comparison and memory builtins used by the test generator. -/
@[expose] def oofFreePrims : List PrimOp :=
  [.ADD, .MUL, .SUB, .MOD, .EXP, .LT, .AND, .ISZERO, .NOT, .POP, .MLOAD, .MSTORE]

theorem primResult_ne_OOF {prim : PrimOp} (hp : prim ∈ oofFreePrims) (s : State)
    (args : List Literal) : primResult s prim args ≠ OOF := by
  simp only [oofFreePrims, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [primResult, primCallK]
  · have h : step (.ADD : Operation .Yul) none s args ≠ .error .OutOfFuel := execBinOp_ne_OOF UInt256.add s args
    split <;> simp_all [OOF]
  · have h : step (.MUL : Operation .Yul) none s args ≠ .error .OutOfFuel := execBinOp_ne_OOF UInt256.mul s args
    split <;> simp_all [OOF]
  · have h : step (.SUB : Operation .Yul) none s args ≠ .error .OutOfFuel := execBinOp_ne_OOF UInt256.sub s args
    split <;> simp_all [OOF]
  · have h : step (.MOD : Operation .Yul) none s args ≠ .error .OutOfFuel := execBinOp_ne_OOF UInt256.mod s args
    split <;> simp_all [OOF]
  · have h : step (.EXP : Operation .Yul) none s args ≠ .error .OutOfFuel := execBinOp_ne_OOF UInt256.exp s args
    split <;> simp_all [OOF]
  · have h : step (.LT : Operation .Yul) none s args ≠ .error .OutOfFuel := execBinOp_ne_OOF UInt256.lt s args
    split <;> simp_all [OOF]
  · have h : step (.AND : Operation .Yul) none s args ≠ .error .OutOfFuel := execBinOp_ne_OOF UInt256.land s args
    split <;> simp_all [OOF]
  · have h : step (.ISZERO : Operation .Yul) none s args ≠ .error .OutOfFuel := execUnOp_ne_OOF UInt256.isZero s args
    split <;> simp_all [OOF]
  · have h : step (.NOT : Operation .Yul) none s args ≠ .error .OutOfFuel := execUnOp_ne_OOF UInt256.lnot s args
    split <;> simp_all [OOF]
  · have h : step (.POP : Operation .Yul) none s args ≠ .error .OutOfFuel := by
      change Except.ok (s, none) ≠ _; simp
    split <;> simp_all [OOF]
  · have h : step (.MLOAD : Operation .Yul) none s args ≠ .error .OutOfFuel := by
      rcases args with _ | ⟨a, _ | ⟨b, rest⟩⟩ <;> (intro hc; cases hc)
    split <;> simp_all [OOF]
  · have h : step (.MSTORE : Operation .Yul) none s args ≠ .error .OutOfFuel := by
      change Yul.binaryMachineStateOp MachineState.mstore s args ≠ _
      unfold Yul.binaryMachineStateOp; split <;> simp
    split <;> simp_all [OOF]
/-! ## Expressions -/

mutual

theorem eval_eq_evalG {co : Option YulContract} : (e : Expr) → fragE e = true →
    (f : ℕ) → (s : State) → fuelE e ≤ f → eval f e co s = (evalG c e s).1
  | .Lit _, _, f, _, h => by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp only [fuelE] at h; omega⟩
    simp [eval, evalG]
  | .Var _, _, f, _, h => by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp only [fuelE] at h; omega⟩
    simp [eval, evalG]
  | .Call (.inl prim) args, hf, f, s, h => by
    simp only [fragE, Bool.and_eq_true, decide_eq_true_eq] at hf
    simp only [fuelE] at h
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    have hargs : evalArgs g args.reverse co s = (argsG c args s).1 := by
      rw [argsG_eq_argsL]
      refine evalArgs_eq_argsL c (M := maxFuelE args) args.reverse g s ?_ ?_ ?_
      · intro a ha
        exact eval_eq_evalG_mem args hf.2 a (List.mem_reverse.mp ha)
      · intro a ha
        exact fuelE_le_maxFuelE (List.mem_reverse.mp ha)
      · rw [List.length_reverse]; omega
    rw [eval]
    simp only [hargs, evalG]
    rcases argsG c args s with ⟨e | ⟨s₁, vs⟩, gas⟩
    · simp [reverse', evalPrimCall]
    · simp only [reverse', evalPrimCall]
      rw [primCall_eq_primResult hf.1 (by omega)]
  | .Call (.inr _) _, hf, _, _, _ => by simp [fragE] at hf

theorem eval_eq_evalG_mem {co : Option YulContract} : (as : List Expr) → fragArgs as = true →
    ∀ a ∈ as, ∀ (f : ℕ) (s : State), fuelE a ≤ f → eval f a co s = (evalG c a s).1
  | [], _, _, ha => by simp at ha
  | b :: bs, hf, a, ha => by
    simp only [fragArgs, Bool.and_eq_true] at hf
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact eval_eq_evalG a hf.1
    · exact eval_eq_evalG_mem bs hf.2 a ha'

end

/-- Evaluating the (reversed) arguments of a fragment call with enough fuel gives `argsG`. -/
theorem evalArgs_reverse_eq_argsG {co : Option YulContract} {args : List Expr}
    (hf : fragArgs args = true) {f : ℕ} (hfuel : maxFuelE args + 2 * args.length + 1 ≤ f)
    (s : State) : evalArgs f args.reverse co s = (argsG c args s).1 := by
  rw [argsG_eq_argsL]
  refine evalArgs_eq_argsL c (M := maxFuelE args) args.reverse f s ?_ ?_ ?_
  · intro a ha
    exact eval_eq_evalG_mem c args hf a (List.mem_reverse.mp ha)
  · intro a ha
    exact fuelE_le_maxFuelE (List.mem_reverse.mp ha)
  · rw [List.length_reverse]; omega

/-! ## Statements -/

/-- `execSwitchCases` with enough fuel evaluates every case body. -/
theorem execSwitchCases_eq {co : Option YulContract} (cases : List (Literal × List Stmt))
    (hcases : ∀ p ∈ cases, ∀ (f : ℕ) (s : State), fuelB p.2 ≤ f →
      exec f (.Block p.2) co s = (blockG c p.2 s).1)
    {f : ℕ} (hf : fuelCases cases ≤ f) (s : State) :
    execSwitchCases f co s cases = .ok (cases.map fun p => (p.1, (blockG c p.2 s).1)) := by
  induction cases generalizing f with
  | nil => simp [execSwitchCases]
  | cons p rest ih =>
    obtain ⟨v, b⟩ := p
    simp only [fuelCases] at hf
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    have hb := hcases (v, b) List.mem_cons_self g s (by dsimp only; omega)
    have hr := ih (fun p hp => hcases p (List.mem_cons_of_mem _ hp)) (f := g) (by omega)
    simp only [execSwitchCases, hb, hr, List.map_cons]
    rcases (blockG c b s).1 with e | s₂
    · cases e <;> rfl
    · rfl

/-- Selecting a branch from the evaluated cases (the interpreter's fold) is `casesG`. -/
theorem foldr_branches_eq (cases : List (Literal × List Stmt)) (v : Literal) (s s₂ : State) :
    List.foldr (fun (valᵢ, sᵢ) r => if valᵢ = v then sᵢ else r) (Except.ok s₂ : Res)
        (cases.map fun p => (p.1, (blockG c p.2 s).1)) =
      match casesG c cases v s with
      | some (r, _) => r
      | none => .ok s₂ := by
  induction cases with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨l, b⟩ := p
    simp only [List.map_cons, List.foldr_cons, casesG]
    by_cases hl : l = v
    · simp [hl]
    · simp only [hl, if_false]
      exact ih

mutual

theorem exec_eq_execG_aux {co : Option YulContract} : (st : Stmt) → fragS st = true →
    (f : ℕ) → (s : State) → fuelS st ≤ f → exec f st co s = (execG c st s).1
  | .Block sts, hf, f, s, h => by
    simp only [fragS] at hf
    simp only [fuelS] at h
    simp only [execG]
    exact block_eq_blockG_aux sts hf f s h
  | .Let _ none, _, f, _, h => by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp only [fuelS] at h; omega⟩
    simp [exec, execG]
  | .Let _ (some (.Var _)), _, f, _, h => by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp only [fuelS, fuelE] at h; omega⟩
    simp [exec, execG]
  | .Let _ (some (.Lit _)), _, f, _, h => by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp only [fuelS, fuelE] at h; omega⟩
    simp [exec, execG]
  | .Let vars (some (.Call (.inl prim) args)), hf, f, s, h => by
    simp only [fragS, fragE, Bool.and_eq_true, decide_eq_true_eq] at hf
    simp only [fuelS, fuelE] at h
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [exec]
    simp only [evalArgs_reverse_eq_argsG c hf.2 (f := g) (by omega), execG]
    rcases argsG c args s with ⟨e | ⟨s₁, vs⟩, gas⟩
    · simp [reverse', execPrimCall]
    · simp only [reverse', execPrimCall]
      rw [primCall_eq_primResult hf.1 (by omega)]
  | .Let _ (some (.Call (.inr _) _)), hf, _, _, _ => by simp [fragS, fragE] at hf
  | .ExprStmtCall (.Call (.inl prim) args), hf, f, s, h => by
    simp only [fragS, fragE, Bool.and_eq_true, decide_eq_true_eq] at hf
    simp only [fuelS, fuelE] at h
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [exec]
    simp only [evalArgs_reverse_eq_argsG c hf.2 (f := g) (by omega), execG]
    rcases argsG c args s with ⟨e | ⟨s₁, vs⟩, gas⟩
    · simp [reverse', execPrimCall]
    · simp only [reverse', execPrimCall]
      rw [primCall_eq_primResult hf.1 (by omega)]
  | .ExprStmtCall (.Call (.inr _) _), hf, _, _, _ => by simp [fragS, fragE] at hf
  | .ExprStmtCall (.Var _), _, f, _, h => by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp only [fuelS, fuelE] at h; omega⟩
    simp [exec, execG]
  | .ExprStmtCall (.Lit _), _, f, _, h => by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp only [fuelS, fuelE] at h; omega⟩
    simp [exec, execG]
  | .If cond body, hf, f, s, h => by
    simp only [fragS, Bool.and_eq_true] at hf
    simp only [fuelS] at h
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [exec]
    simp only [eval_eq_evalG c cond hf.1 g s (by omega), execG]
    rcases evalG c cond s with ⟨e | ⟨s₁, v⟩, gas⟩
    · rfl
    · by_cases hv : v = ⟨0⟩
      · simp [hv]
      · simp only [ne_eq, hv, not_false_eq_true, if_true]
        rw [block_eq_blockG_aux body hf.2 g s₁ (by omega)]
  | .Switch cond cases dflt, hf, f, s, h => by
    simp only [fragS, Bool.and_eq_true] at hf
    obtain ⟨⟨hfc, hfcs⟩, hfd⟩ := hf
    simp only [fuelS] at h
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [exec]
    simp only [eval_eq_evalG c cond hfc g s (by omega), execG]
    rcases evalG c cond s with ⟨e | ⟨s₁, v⟩, gas⟩
    · rfl
    · simp only [execSwitchCases_eq c cases (cases_eq_aux cases hfcs) (f := g) (by omega) s₁,
        block_eq_blockG_aux dflt hfd g s₁ (by omega)]
      rcases blockG c dflt s₁ with ⟨e | s₂, gd⟩
      · rfl
      · simp only [foldr_branches_eq]
        rcases casesG c cases v s₁ with _ | ⟨r, gb⟩ <;> rfl
  | .For _ _ _, hf, _, _, _ => by simp [fragS] at hf
  | .Continue, _, f, _, h => by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp only [fuelS] at h; omega⟩
    simp [exec, execG]
  | .Break, _, f, _, h => by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp only [fuelS] at h; omega⟩
    simp [exec, execG]
  | .Leave, _, f, _, h => by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp only [fuelS] at h; omega⟩
    simp [exec, execG]

theorem block_eq_blockG_aux {co : Option YulContract} : (sts : List Stmt) → fragB sts = true →
    (f : ℕ) → (s : State) → fuelB sts ≤ f → exec f (.Block sts) co s = (blockG c sts s).1
  | [], _, f, _, h => by
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by simp only [fuelB] at h; omega⟩
    simp [exec, blockG]
  | st :: sts, hf, f, s, h => by
    simp only [fragB, Bool.and_eq_true] at hf
    simp only [fuelB] at h
    obtain ⟨g, rfl⟩ : ∃ g, f = g + 1 := ⟨f - 1, by omega⟩
    rw [exec]
    simp only [exec_eq_execG_aux st hf.1 g s (by omega), blockG]
    rcases execG c st s with ⟨e | (⟨ss, vs⟩ | _ | j), gas⟩
    · rfl
    · simp only [block_eq_blockG_aux sts hf.2 g _ (by omega)]
    · rfl
    · rfl

theorem cases_eq_aux {co : Option YulContract} : (cases : List (Literal × List Stmt)) →
    fragCases cases = true → ∀ p ∈ cases, ∀ (f : ℕ) (s : State), fuelB p.2 ≤ f →
      exec f (.Block p.2) co s = (blockG c p.2 s).1
  | [], _, _, hp => by simp at hp
  | (l, b) :: rest, hf, p, hp => by
    simp only [fragCases, Bool.and_eq_true] at hf
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact block_eq_blockG_aux b hf.1
    · exact cases_eq_aux rest hf.2 p hp'

end

/-- **Fuel adequacy (K10).** On the loop-free, call-free fragment, the interpreter with at least
`fuelS st` fuel computes exactly the metered result, from every start state and for every code
override. -/
theorem exec_eq_execG_of_fuel {fuel : ℕ} {st : Stmt} {co : Option YulContract} {s : State}
    (hf : InFragment st) (hfuel : fuelS st ≤ fuel) : exec fuel st co s = (execG c st s).1 :=
  exec_eq_execG_aux c st hf fuel s hfuel

/-! ## The metered evaluator never runs out of fuel on safe programs -/

mutual

/-- Expressions whose builtins are all in `oofFreePrims`. -/
@[expose] def safeE : Expr → Bool
  | .Lit _ => true
  | .Var _ => true
  | .Call (.inl prim) args => decide (prim ∈ oofFreePrims) && safeArgs args
  | .Call (.inr _) _ => false

/-- Argument lists of `safeE` expressions. -/
@[expose] def safeArgs : List Expr → Bool
  | [] => true
  | a :: as => safeE a && safeArgs as

end

mutual

/-- Fragment statements whose builtins are all in `oofFreePrims`. -/
@[expose] def safeS : Stmt → Bool
  | .Block sts => safeB sts
  | .Let _ none => true
  | .Let _ (some e) => safeE e
  | .ExprStmtCall e => safeE e
  | .If cond body => safeE cond && safeB body
  | .Switch cond cases dflt => safeE cond && safeCases cases && safeB dflt
  | .For _ _ _ => false
  | .Continue => true
  | .Break => true
  | .Leave => true

/-- Blocks of `safeS` statements. -/
@[expose] def safeB : List Stmt → Bool
  | [] => true
  | st :: sts => safeS st && safeB sts

/-- `switch` cases with `safeB` bodies. -/
@[expose] def safeCases : List (Literal × List Stmt) → Bool
  | [] => true
  | (_, body) :: rest => safeB body && safeCases rest

end

theorem not_mem_callFamily {prim : PrimOp} (h : prim ∈ oofFreePrims) : prim ∉ callFamily := by
  simp only [oofFreePrims, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [callFamily]

mutual

theorem fragE_of_safeE : (e : Expr) → safeE e = true → fragE e = true
  | .Lit _, _ => rfl
  | .Var _, _ => rfl
  | .Call (.inl _) args, h => by
    simp only [safeE, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [fragE, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨not_mem_callFamily h.1, fragArgs_of_safeArgs args h.2⟩
  | .Call (.inr _) _, h => by simp [safeE] at h

theorem fragArgs_of_safeArgs : (as : List Expr) → safeArgs as = true → fragArgs as = true
  | [], _ => rfl
  | a :: as, h => by
    simp only [safeArgs, Bool.and_eq_true] at h
    simp only [fragArgs, Bool.and_eq_true]
    exact ⟨fragE_of_safeE a h.1, fragArgs_of_safeArgs as h.2⟩

end

mutual

theorem fragS_of_safeS : (st : Stmt) → safeS st = true → fragS st = true
  | .Block sts, h => by
    simp only [safeS] at h; simp only [fragS]; exact fragB_of_safeB sts h
  | .Let _ none, _ => rfl
  | .Let _ (some e), h => by
    simp only [safeS] at h; simp only [fragS]; exact fragE_of_safeE e h
  | .ExprStmtCall e, h => by
    simp only [safeS] at h; simp only [fragS]; exact fragE_of_safeE e h
  | .If cond body, h => by
    simp only [safeS, Bool.and_eq_true] at h
    simp only [fragS, Bool.and_eq_true]
    exact ⟨fragE_of_safeE cond h.1, fragB_of_safeB body h.2⟩
  | .Switch cond cases dflt, h => by
    simp only [safeS, Bool.and_eq_true] at h
    simp only [fragS, Bool.and_eq_true]
    exact ⟨⟨fragE_of_safeE cond h.1.1, fragCases_of_safeCases cases h.1.2⟩,
      fragB_of_safeB dflt h.2⟩
  | .For _ _ _, h => by simp [safeS] at h
  | .Continue, _ => rfl
  | .Break, _ => rfl
  | .Leave, _ => rfl

theorem fragB_of_safeB : (sts : List Stmt) → safeB sts = true → fragB sts = true
  | [], _ => rfl
  | st :: sts, h => by
    simp only [safeB, Bool.and_eq_true] at h
    simp only [fragB, Bool.and_eq_true]
    exact ⟨fragS_of_safeS st h.1, fragB_of_safeB sts h.2⟩

theorem fragCases_of_safeCases : (cases : List (Literal × List Stmt)) → safeCases cases = true →
    fragCases cases = true
  | [], _ => rfl
  | (_, b) :: rest, h => by
    simp only [safeCases, Bool.and_eq_true] at h
    simp only [fragCases, Bool.and_eq_true]
    exact ⟨fragB_of_safeB b h.1, fragCases_of_safeCases rest h.2⟩

end

theorem head'_ne_OOF {r : ResL} (h : r ≠ OOF) : head' r ≠ OOF := by
  rcases r with e | ⟨s, vs⟩
  · intro h'; cases h'; exact h rfl
  · simp [head', OOF]

theorem multifill'_ne_OOF {vars : List Identifier} {r : ResL} (h : r ≠ OOF) :
    multifill' vars r ≠ OOF := by
  rcases r with e | ⟨s, vs⟩
  · intro h'; cases h'; exact h rfl
  · simp [multifill', OOF]

mutual

theorem evalG_ne_OOF : (e : Expr) → safeE e = true → (s : State) → (evalG c e s).1 ≠ OOF
  | .Lit _, _, _ => by simp [evalG, OOF]
  | .Var _, _, _ => by simp [evalG, OOF]
  | .Call (.inl prim) args, h, s => by
    simp only [safeE, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := argsG_ne_OOF args h.2 s
    simp only [evalG]
    rcases hA : argsG c args s with ⟨e | ⟨s₁, vs⟩, g⟩
    · rw [hA] at ih; dsimp only at ih ⊢; exact err_ne_oof ih
    · exact head'_ne_OOF (primResult_ne_OOF h.1 s₁ _)
  | .Call (.inr _) _, h, _ => by simp [safeE] at h

theorem argsG_ne_OOF : (as : List Expr) → safeArgs as = true → (s : State) →
    (argsG c as s).1 ≠ OOF
  | [], _, _ => by simp [argsG, OOF]
  | a :: as, h, s => by
    simp only [safeArgs, Bool.and_eq_true] at h
    have ih := argsG_ne_OOF as h.2 s
    simp only [argsG]
    rcases hA : argsG c as s with ⟨e | ⟨s₁, vs⟩, g⟩
    · rw [hA] at ih; dsimp only at ih ⊢; exact err_ne_oof ih
    · have iha := evalG_ne_OOF a h.1 s₁
      rcases hE : evalG c a s₁ with ⟨e' | ⟨s₂, v⟩, g'⟩
      · rw [hE] at iha; dsimp only at iha ⊢; rw [hE]; exact err_ne_oof iha
      · dsimp only; rw [hE]; simp [OOF]

end

mutual

theorem execG_ne_OOF : (st : Stmt) → safeS st = true → (s : State) → (execG c st s).1 ≠ OOF
  | .Block sts, h, s => by
    simp only [safeS] at h; simp only [execG]; exact blockG_ne_OOF sts h s
  | .Let _ none, _, _ => by simp [execG, OOF]
  | .Let _ (some (.Var _)), _, _ => by simp [execG, OOF]
  | .Let _ (some (.Lit _)), _, _ => by simp [execG, OOF]
  | .Let vars (some (.Call (.inl prim) args)), h, s => by
    simp only [safeS, safeE, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := argsG_ne_OOF c args h.2 s
    simp only [execG]
    rcases hA : argsG c args s with ⟨e | ⟨s₁, vs⟩, g⟩
    · rw [hA] at ih; dsimp only at ih ⊢; exact err_ne_oof ih
    · exact multifill'_ne_OOF (primResult_ne_OOF h.1 s₁ _)
  | .Let _ (some (.Call (.inr _) _)), h, _ => by simp [safeS, safeE] at h
  | .ExprStmtCall (.Call (.inl prim) args), h, s => by
    simp only [safeS, safeE, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := argsG_ne_OOF c args h.2 s
    simp only [execG]
    rcases hA : argsG c args s with ⟨e | ⟨s₁, vs⟩, g⟩
    · rw [hA] at ih; dsimp only at ih ⊢; exact err_ne_oof ih
    · exact multifill'_ne_OOF (primResult_ne_OOF h.1 s₁ _)
  | .ExprStmtCall (.Call (.inr _) _), h, _ => by simp [safeS, safeE] at h
  | .ExprStmtCall (.Var _), _, _ => by simp [execG, OOF]
  | .ExprStmtCall (.Lit _), _, _ => by simp [execG, OOF]
  | .If cond body, h, s => by
    simp only [safeS, Bool.and_eq_true] at h
    have ih := evalG_ne_OOF c cond h.1 s
    simp only [execG]
    rcases hC : evalG c cond s with ⟨e | ⟨s₁, v⟩, g⟩
    · rw [hC] at ih; dsimp only at ih ⊢; exact err_ne_oof ih
    · dsimp only
      split
      · exact blockG_ne_OOF body h.2 s₁
      · simp [OOF]
  | .Switch cond cases dflt, h, s => by
    simp only [safeS, Bool.and_eq_true] at h
    have ih := evalG_ne_OOF c cond h.1.1 s
    simp only [execG]
    rcases hC : evalG c cond s with ⟨e | ⟨s₁, v⟩, g⟩
    · rw [hC] at ih; dsimp only at ih ⊢; exact err_ne_oof ih
    · dsimp only
      have ihd := blockG_ne_OOF dflt h.2 s₁
      rcases hD : blockG c dflt s₁ with ⟨e | s₂, gd⟩
      · rw [hD] at ihd; try rw [hD]
        dsimp only at ihd ⊢; exact err_ne_oof ihd
      · try rw [hD]
        dsimp only
        rcases hS : casesG c cases v s₁ with _ | ⟨r, gb⟩
        · try rw [hS]
          simp [OOF]
        · try rw [hS]
          exact casesG_ne_OOF cases h.1.2 v s₁ hS
  | .For _ _ _, h, _ => by simp [safeS] at h
  | .Continue, _, _ => by simp [execG, OOF]
  | .Break, _, _ => by simp [execG, OOF]
  | .Leave, _, _ => by simp [execG, OOF]

theorem blockG_ne_OOF : (sts : List Stmt) → safeB sts = true → (s : State) →
    (blockG c sts s).1 ≠ OOF
  | [], _, _ => by simp [blockG, OOF]
  | st :: sts, h, s => by
    simp only [safeB, Bool.and_eq_true] at h
    have ih := execG_ne_OOF st h.1 s
    simp only [blockG]
    rcases hE : execG c st s with ⟨e | (⟨ss, vs⟩ | _ | j), g⟩
    · rw [hE] at ih; dsimp only at ih ⊢; exact err_ne_oof ih
    · exact blockG_ne_OOF sts h.2 _
    · simp [OOF]
    · simp [OOF]

theorem casesG_ne_OOF : (cases : List (Literal × List Stmt)) → safeCases cases = true →
    (v : Literal) → (s : State) → {r : Res} → {g : ℕ} → casesG c cases v s = some (r, g) →
    r ≠ OOF
  | [], _, _, _, _, _, h => by simp [casesG] at h
  | (l, b) :: rest, hs, v, s, r, g, h => by
    simp only [safeCases, Bool.and_eq_true] at hs
    simp only [casesG] at h
    split at h
    · simp only [Option.some.injEq] at h
      have := blockG_ne_OOF b hs.1 s
      rw [h] at this
      exact this
    · exact casesG_ne_OOF rest hs.2 v s h

end

/-- **The interpreter does not run out of fuel (K10).** For a fragment program whose builtins are
all in `oofFreePrims`, the interpreter with at least `fuelS st` fuel never returns `OutOfFuel`,
from any start state and for any code override. -/
theorem exec_ne_OOF_of_fuel {fuel : ℕ} {st : Stmt} {co : Option YulContract} {s : State}
    (hs : safeS st = true) (hfuel : fuelS st ≤ fuel) : exec fuel st co s ≠ OOF := by
  rw [exec_eq_execG_of_fuel (c := ⟨fun _ => 0, 0⟩) (fragS_of_safeS st hs) hfuel]
  exact execG_ne_OOF _ st hs s


/-- A block of statements that each need at most `K` fuel needs at most `K + length + 1`. -/
theorem fuelB_le_of_forall (K : ℕ) : ∀ (l : List Stmt), (∀ st ∈ l, fuelS st ≤ K) →
    fuelB l ≤ K + l.length + 1
  | [], _ => by simp [fuelB]
  | st :: sts, h => by
    have ih := fuelB_le_of_forall K sts (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have hst := h st List.mem_cons_self
    simp only [fuelB, List.length_cons]
    omega

theorem safeB_of_forall : ∀ (l : List Stmt), (∀ st ∈ l, safeS st = true) → safeB l = true
  | [], _ => rfl
  | st :: sts, h => by
    simp only [safeB, Bool.and_eq_true]
    exact ⟨h st List.mem_cons_self, safeB_of_forall sts (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩

end Gas
end Yul
end EvmYul
