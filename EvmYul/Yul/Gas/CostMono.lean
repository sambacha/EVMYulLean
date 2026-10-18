module

public import EvmYul.Yul.Gas.Functions.Basic
public section

/-!
# Yul gas is monotone in the cost model; the call-price hypothesis cannot be dropped

`docs/SOLC_VYPER_PLAN.md`, Step 4, asks for two Lean results about how the Yul model's gas relates
to the gas of compiled code.

* **Preservation (`runF_costMono`).** Describe a lowering by the price it pays for each construct:
  a cost model `c'` whose builtin, branch and call prices are what the compiled code spends on
  them. If every price of `c'` is at least the model's (`c ≤ c'`, `FnCostModel.Le`), then on every
  program, every state and every pair of budgets the metered semantics `runF` gives **the same
  result** under both models, and the model's gas is **at most** the lowering's. So the Yul model
  is a floor on compiled gas exactly when it underprices every construct that survives
  compilation. The theorem is generic: it says nothing about solc, only about cost models.
* **The hypothesis on calls is needed (`inlining_breaks_floor`).** An inlining lowering removes
  the call and return jumps, so its call price is `0`. With every other price unchanged, the
  model's gas is strictly *above* the lowering's on a concrete program with one call. So the
  unrestricted K13(b) ("the model is a floor on compiled control flow") is refuted in Lean, not
  only by measurement (`docs/SOLC_VYPER_PLAN.md` R3). The executable side, on real solc output, is
  `EvmYul/Solc/MatrixTests.lean`.

Also proved: the result never depends on the cost model (`runF_result_indep`).
-/

namespace EvmYul
namespace Yul
namespace Gas

open Ast Relational EVM

/-- `c ≤ c'` pointwise: every builtin, the branch and the call cost at least as much in `c'`. -/
structure FnCostModel.Le (c c' : FnCostModel) : Prop where
  /-- Builtins. -/
  prim : ∀ op, c.prim op ≤ c'.prim op
  /-- Conditional branch. -/
  branch : c.branch ≤ c'.branch
  /-- User-function call. -/
  call : c.call ≤ c'.call

theorem FnCostModel.Le.refl (c : FnCostModel) : c.Le c := ⟨fun _ => le_rfl, le_rfl, le_rfl⟩

theorem FnCostModel.Le.trans {c₁ c₂ c₃ : FnCostModel} (h₁ : c₁.Le c₂) (h₂ : c₂.Le c₃) :
    c₁.Le c₃ :=
  ⟨fun op => (h₁.prim op).trans (h₂.prim op), h₁.branch.trans h₂.branch, h₁.call.trans h₂.call⟩

/-- Two metered outcomes agree on the result, and the first charges at most the second (both may
also give up, together). -/
def GLe {α : Type} : Option (α × ℕ) → Option (α × ℕ) → Prop
  | none, none => True
  | some (r, g), some (r', g') => r = r' ∧ g ≤ g'
  | _, _ => False

theorem GLe.cases {α : Type} {x y : Option (α × ℕ)} (h : GLe x y) :
    (x = none ∧ y = none) ∨ ∃ r g g', x = some (r, g) ∧ y = some (r, g') ∧ g ≤ g' := by
  rcases x with _ | ⟨r, g⟩ <;> rcases y with _ | ⟨r', g'⟩ <;> simp_all [GLe]

theorem GLe.of_some {α : Type} {r : α} {g g' : ℕ} (h : g ≤ g') : GLe (some (r, g)) (some (r, g')) :=
  ⟨rfl, h⟩

theorem GLe.none {α : Type} : GLe (none : Option (α × ℕ)) none := trivial

theorem GLe.refl {α : Type} (x : Option (α × ℕ)) : GLe x x := by
  rcases x with _ | ⟨r, g⟩ <;> simp [GLe]

/-- Two runners agree on results, the first charging at most the second. -/
@[expose] def RunnerGLe (rc rc' : Runner) : Prop := ∀ args f s, GLe (rc args f s) (rc' args f s)

section
variable {c c' : FnCostModel}

mutual

theorem evalF_costMono (hc : c.Le c') {rc rc' : Runner} (hrc : RunnerGLe rc rc') :
    (e : Expr) → (s : State) → GLe (evalF c rc e s) (evalF c' rc' e s)
  | .Lit _, _ => by simp [evalF, GLe]
  | .Var _, _ => by simp [evalF, GLe]
  | .Call (.inl prim) args, s => by
    have hp := hc.prim prim
    obtain ⟨ha, ha'⟩ | ⟨r, g, g', ha, ha', hg⟩ := (argsF_costMono hc hrc args s).cases
    · simp [evalF, ha, ha', GLe]
    · rcases r with e | ⟨s₁, vs⟩ <;> simp only [evalF, ha, ha', GLe, true_and] <;> omega
  | .Call (.inr f) args, s => by
    have hcl := hc.call
    rcases hb : evalObjectDataBuiltin? f args s with _ | r₀
    · obtain ⟨ha, ha'⟩ | ⟨r, g, g', ha, ha', hg⟩ := (argsF_costMono hc hrc args s).cases
      · simp [evalF, hb, ha, ha', GLe]
      · rcases r with e | ⟨s₁, vs⟩
        · simp only [evalF, hb, ha, ha', GLe, true_and]; omega
        · obtain ⟨hr, hr'⟩ | ⟨r₁, g₁, g₁', hr, hr', hg₁⟩ := (hrc vs.reverse f s₁).cases
          · simp [evalF, hb, ha, ha', hr, hr', GLe]
          · simp only [evalF, hb, ha, ha', hr, hr', GLe, true_and]; omega
    · simp [evalF, hb, GLe]

theorem argsF_costMono (hc : c.Le c') {rc rc' : Runner} (hrc : RunnerGLe rc rc') :
    (as : List Expr) → (s : State) → GLe (argsF c rc as s) (argsF c' rc' as s)
  | [], _ => by simp [argsF, GLe]
  | a :: as, s => by
    obtain ⟨ha, ha'⟩ | ⟨r, g, g', ha, ha', hg⟩ := (argsF_costMono hc hrc as s).cases
    · simp [argsF, ha, ha', GLe]
    · rcases r with e | ⟨s₁, vs⟩
      · simp only [argsF, ha, ha', GLe, true_and]; omega
      · obtain ⟨he, he'⟩ | ⟨r₁, g₁, g₁', he, he', hg₁⟩ := (evalF_costMono hc hrc a s₁).cases
        · simp [argsF, ha, ha', he, he', GLe]
        · rcases r₁ with e | ⟨s₂, v⟩ <;> simp only [argsF, ha, ha', he, he', GLe, true_and] <;>
            omega

end

theorem addGas_costMono {a a' : ℕ} {x y : Option (Res × ℕ)} (ha : a ≤ a') (h : GLe x y) :
    GLe (addGas a x) (addGas a' y) := by
  obtain ⟨hx, hy⟩ | ⟨r, g, g', hx, hy, hg⟩ := h.cases
  · simp [addGas, hx, hy, GLe]
  · simp only [addGas, hx, hy, GLe, true_and]; omega

/-- The tail of a loop iteration (post block, then the rest of the loop), for related runners. -/
theorem loopTail_costMono {rp rp' : State → Option (Res × ℕ)}
    {loop loop' : State → Option (Res × ℕ)} (hp : ∀ s, GLe (rp s) (rp' s))
    (hl : ∀ s, GLe (loop s) (loop' s)) (s st : State) {A A' : ℕ} (hA : A ≤ A') :
    GLe (match rp st with
          | none => none
          | some (.error e, gp) => some (.error e, A + gp)
          | some (.ok s₃, gp) =>
            match loop (s₃.overwrite? s) with
            | none => none
            | some (r, g') => some (r.map (·.overwrite? s), A + gp + g'))
        (match rp' st with
          | none => none
          | some (.error e, gp) => some (.error e, A' + gp)
          | some (.ok s₃, gp) =>
            match loop' (s₃.overwrite? s) with
            | none => none
            | some (r, g') => some (r.map (·.overwrite? s), A' + gp + g')) := by
  obtain ⟨p1, p2⟩ | ⟨rp₀, gp, gp', p1, p2, hgp⟩ := (hp st).cases
  · simp [p1, p2, GLe]
  · rcases rp₀ with e | s₃
    · simp only [p1, p2, GLe, true_and]; omega
    · simp only [p1, p2]
      obtain ⟨l1, l2⟩ | ⟨rl, gl, gl', l1, l2, hgl⟩ := (hl (s₃.overwrite? s)).cases
      · simp [l1, l2, GLe]
      · simp only [l1, l2, GLe, true_and]; omega

/-- The loop driver, for runners related by `GLe`. -/
theorem loopF_costMono (hc : c.Le c') {rcd rcd' : State → Option (ResV × ℕ)} {rb rp rb' rp' : State → Option (Res × ℕ)}
    (hcd : ∀ s, GLe (rcd s) (rcd' s)) (hb : ∀ s, GLe (rb s) (rb' s))
    (hp : ∀ s, GLe (rp s) (rp' s)) :
    ∀ k s, GLe (loopF c rcd rb rp k s) (loopF c' rcd' rb' rp' k s) := by
  have hbr := hc.branch
  intro k
  induction k with
  | zero =>
    intro s
    unfold loopF
    obtain ⟨h1, h2⟩ | ⟨r, g, g', h1, h2, hg⟩ := (hcd (State.mkOk s)).cases
    · simp [h1, h2, GLe]
    · rcases r with e | ⟨s₁, x⟩
      · simp only [h1, h2, GLe, true_and]; omega
      · simp only [h1, h2]
        split
        · simp only [GLe, true_and]; omega
        · simp [GLe]
  | succ k ih =>
    intro s
    unfold loopF
    obtain ⟨h1, h2⟩ | ⟨r, g, g', h1, h2, hg⟩ := (hcd (State.mkOk s)).cases
    · simp [h1, h2, GLe]
    · rcases r with e | ⟨s₁, x⟩
      · simp only [h1, h2, GLe, true_and]; omega
      · simp only [h1, h2]
        split
        · simp only [GLe, true_and]; omega
        · obtain ⟨b1, b2⟩ | ⟨rb₀, gb, gb', b1, b2, hgb⟩ := (hb s₁).cases
          · simp [b1, b2, GLe]
          · rcases rb₀ with e | (⟨ss, vs⟩ | _ | ((⟨ss, vs⟩ | ⟨ss, vs⟩ | ⟨ss, vs⟩)))
            all_goals first
              | (simp only [b1, b2, GLe, true_and]; omega)
              | (simp only [b1, b2]
                 exact loopTail_costMono hp (ih ·) s _ (by omega))

theorem stmtPrimF_costMono (hc : c.Le c') {rc rc' : Runner} (hrc : RunnerGLe rc rc') (vars : List Identifier)
    (prim : PrimOp) (args : List Expr) (s : State) :
    GLe (stmtPrimF c rc vars prim args s) (stmtPrimF c' rc' vars prim args s) := by
  have hp := hc.prim prim
  obtain ⟨ha, ha'⟩ | ⟨r, g, g', ha, ha', hg⟩ := (argsF_costMono hc hrc args s).cases
  · simp [stmtPrimF, ha, ha', GLe]
  · rcases r with e | ⟨s₁, vs⟩ <;> simp only [stmtPrimF, ha, ha', GLe, true_and] <;> omega

theorem stmtCallF_costMono (hc : c.Le c') {rc rc' : Runner} (hrc : RunnerGLe rc rc') (vars : List Identifier)
    (f : YulFunctionName) (args : List Expr) (s : State) :
    GLe (stmtCallF c rc vars f args s) (stmtCallF c' rc' vars f args s) := by
  have hcl := hc.call
  obtain ⟨ha, ha'⟩ | ⟨r, g, g', ha, ha', hg⟩ := (argsF_costMono hc hrc args s).cases
  · simp [stmtCallF, ha, ha', GLe]
  · rcases r with e | ⟨s₁, vs⟩
    · simp only [stmtCallF, ha, ha', GLe, true_and]; omega
    · rcases hb : execObjectDataBuiltin? f vars (.ok (s₁, vs.reverse)) with _ | r₀
      · obtain ⟨hr, hr'⟩ | ⟨r₁, g₁, g₁', hr, hr', hg₁⟩ := (hrc vs.reverse f s₁).cases
        · simp [stmtCallF, ha, ha', hb, hr, hr', GLe]
        · simp only [stmtCallF, ha, ha', hb, hr, hr', GLe, true_and]; omega
      · simp only [stmtCallF, ha, ha', hb, GLe, true_and]; omega

/-- `GLe` for the selected `switch` case (an extra `Option` layer for "no case matched"). -/
def GLeCase : Option (Option (Res × ℕ)) → Option (Option (Res × ℕ)) → Prop
  | none, none => True
  | some none, some none => True
  | some (some (r, g)), some (some (r', g')) => r = r' ∧ g ≤ g'
  | _, _ => False

mutual

theorem execF_costMono (hc : c.Le c') {rc rc' : Runner} (hrc : RunnerGLe rc rc') (n : ℕ) :
    (st : Stmt) → (s : State) → GLe (execF c rc n st s) (execF c' rc' n st s)
  | .Block sts, s => by simpa only [execF] using blockF_costMono hc hrc n sts s
  | .Let _ none, _ => by simp [execF, GLe]
  | .Let _ (some (.Var _)), _ => by simp [execF, GLe]
  | .Let _ (some (.Lit _)), _ => by simp [execF, GLe]
  | .Let vars (some (.Call (.inl prim) args)), s => by
    simpa only [execF] using stmtPrimF_costMono hc hrc vars prim args s
  | .Let vars (some (.Call (.inr f) args)), s => by
    simpa only [execF] using stmtCallF_costMono hc hrc vars f args s
  | .ExprStmtCall (.Call (.inl prim) args), s => by
    simpa only [execF] using stmtPrimF_costMono hc hrc [] prim args s
  | .ExprStmtCall (.Call (.inr f) args), s => by
    simpa only [execF] using stmtCallF_costMono hc hrc [] f args s
  | .ExprStmtCall (.Var _), _ => by simp [execF, GLe]
  | .ExprStmtCall (.Lit _), _ => by simp [execF, GLe]
  | .If cond body, s => by
    have hbr := hc.branch
    obtain ⟨h1, h2⟩ | ⟨r, g, g', h1, h2, hg⟩ := (evalF_costMono hc hrc cond s).cases
    · simp [execF, h1, h2, GLe]
    · rcases r with e | ⟨s₁, v⟩
      · simp only [execF, h1, h2, GLe, true_and]; omega
      · by_cases hv : v = ⟨0⟩
        · simp only [execF, h1, h2, hv, ne_eq, not_true_eq_false, if_false, GLe, true_and]; omega
        · simp only [execF, h1, h2, hv, ne_eq, not_false_eq_true, if_true]
          exact addGas_costMono (by omega) (blockF_costMono hc hrc n body s₁)
  | .Switch cond cases dflt, s => by
    have hbr := hc.branch
    obtain ⟨h1, h2⟩ | ⟨r, g, g', h1, h2, hg⟩ := (evalF_costMono hc hrc cond s).cases
    · simp [execF, h1, h2, GLe]
    · rcases r with e | ⟨s₁, v⟩
      · simp only [execF, h1, h2, GLe, true_and]; omega
      · obtain ⟨d1, d2⟩ | ⟨rd, gd, gd', d1, d2, hgd⟩ := (blockF_costMono hc hrc n dflt s₁).cases
        · simp [execF, h1, h2, d1, d2, GLe]
        · rcases rd with e | s₂
          · simp only [execF, h1, h2, d1, d2, GLe, true_and]; omega
          · have hcs := casesF_costMono hc hrc n cases v s₁
            rcases hx : casesF c rc n cases v s₁ with _ | _ | ⟨r₁, g₁⟩ <;>
              rcases hy : casesF c' rc' n cases v s₁ with _ | _ | ⟨r₁', g₁'⟩ <;>
              simp only [hx, hy, GLeCase] at hcs
            · simp [execF, h1, h2, d1, d2, hx, hy, GLe]
            · simp only [execF, h1, h2, d1, d2, hx, hy, GLe, true_and]; omega
            · obtain ⟨rfl, hg₁⟩ := hcs
              simp only [execF, h1, h2, d1, d2, hx, hy, GLe, true_and]; omega
  | .For cond post body, s => by
    simp only [execF]
    exact loopF_costMono hc (fun s => evalF_costMono hc hrc cond s)
      (fun s => blockF_costMono hc hrc n body s) (fun s => blockF_costMono hc hrc n post s) n s
  | .Continue, _ => by simp [execF, GLe]
  | .Break, _ => by simp [execF, GLe]
  | .Leave, _ => by simp [execF, GLe]

theorem blockF_costMono (hc : c.Le c') {rc rc' : Runner} (hrc : RunnerGLe rc rc') (n : ℕ) :
    (sts : List Stmt) → (s : State) → GLe (blockF c rc n sts s) (blockF c' rc' n sts s)
  | [], _ => by simp [blockF, GLe]
  | st :: sts, s => by
    obtain ⟨h1, h2⟩ | ⟨r, g, g', h1, h2, hg⟩ := (execF_costMono hc hrc n st s).cases
    · simp [blockF, h1, h2, GLe]
    · rcases r with e | (⟨ss, vs⟩ | _ | j)
      · simp only [blockF, h1, h2, GLe, true_and]; omega
      · simp only [blockF, h1, h2]
        exact addGas_costMono hg (blockF_costMono hc hrc n sts _)
      · simp only [blockF, h1, h2, GLe, true_and]; omega
      · simp only [blockF, h1, h2, GLe, true_and]; omega

theorem casesF_costMono (hc : c.Le c') {rc rc' : Runner} (hrc : RunnerGLe rc rc') (n : ℕ) :
    (cases : List (Literal × List Stmt)) → (v : Literal) → (s : State) →
      GLeCase (casesF c rc n cases v s) (casesF c' rc' n cases v s)
  | [], _, _ => by simp [casesF, GLeCase]
  | (l, body) :: rest, v, s => by
    by_cases hl : l = v
    · simp only [casesF, hl, if_true]
      obtain ⟨h1, h2⟩ | ⟨r, g, g', h1, h2, hg⟩ := (blockF_costMono hc hrc n body s).cases
      · simp [h1, h2, GLeCase]
      · simp only [h1, h2, Option.map_some, GLeCase, true_and]; exact hg
    · simp only [casesF, hl, if_false]
      exact casesF_costMono hc hrc n rest v s

end

/-- The call runners at every depth budget are related by `GLe`. -/
theorem callF_costMono (hc : c.Le c') (co : Option YulContract) (n : ℕ) :
    ∀ d, RunnerGLe (callF c co n d) (callF c' co n d) := by
  intro d
  induction d with
  | zero => intro args f s; simp [callF, GLe]
  | succ d ih =>
    intro args f s
    simp only [callF]
    rcases hl : lookupFunction (some f) co s with e | fd
    · simp [GLe]
    · obtain ⟨h1, h2⟩ | ⟨r, g, g', h1, h2, hg⟩ :=
        (blockF_costMono hc ih n fd.body (State.mkOk (s.initcall fd.params args))).cases
      · simp [h1, h2, GLe]
      · simp only [h1, h2, GLe, true_and]; exact hg

/-- **Preservation.** If every price of `c'` is at least the corresponding price of `c`, then on
every program, state and budgets the metered semantics gives the same result under both models
(or gives up under both), and the gas under `c` is at most the gas under `c'`. -/
theorem runF_costMono (hc : c.Le c') (co : Option YulContract) (n d : ℕ) (st : Stmt) (s : State) :
    GLe (runF c co n d st s) (runF c' co n d st s) :=
  execF_costMono hc (callF_costMono hc co n d) n st s

/-- The same, in the shape of the `runF ≤ gasF` theorems: a successful run under `c` has a
successful run under `c'` with the same result and at least as much gas. -/
theorem runF_le_of_costLe (hc : c.Le c') {co : Option YulContract} {n d : ℕ} {st : Stmt} {s : State} {r : Res}
    {g : ℕ} (h : runF c co n d st s = some (r, g)) :
    ∃ g', runF c' co n d st s = some (r, g') ∧ g ≤ g' := by
  have hm := runF_costMono hc co n d st s
  rw [h] at hm
  rcases hy : runF c' co n d st s with _ | ⟨r', g'⟩ <;> simp only [hy, GLe] at hm
  exact ⟨g', by rw [hm.1], hm.2⟩

end

/-- **The result never depends on the cost model**: two cost models give the same result (or both
give up); only the gas differs. -/
theorem runF_result_indep (c c' : FnCostModel) (co : Option YulContract) (n d : ℕ) (st : Stmt)
    (s : State) : (runF c co n d st s).map Prod.fst = (runF c' co n d st s).map Prod.fst := by
  -- Both are related to the model that charges nothing.
  let z : FnCostModel := { prim := fun _ => 0, branch := 0, call := 0 }
  have hz : ∀ c : FnCostModel, z.Le c := fun c => ⟨fun _ => Nat.zero_le _, Nat.zero_le _,
    Nat.zero_le _⟩
  have h1 := runF_costMono (hz c) co n d st s
  have h2 := runF_costMono (hz c') co n d st s
  rcases hx : runF z co n d st s with _ | ⟨r, g⟩ <;>
    rcases hy : runF c co n d st s with _ | ⟨r₁, g₁⟩ <;>
    rcases hw : runF c' co n d st s with _ | ⟨r₂, g₂⟩ <;>
    simp_all [GLe]

/-! ## The call-price hypothesis cannot be dropped (inlining) -/

/-- An inlining lowering: every price as in `c`, but a call costs nothing (no call or return
jump survives). -/
@[expose] def inlined (c : FnCostModel) : FnCostModel := { c with call := 0 }

/-- `inc(x) -> r { r := add(x, 1) }`. -/
def incDef : FunctionDefinition :=
  .Def ["x"] ["r"] [.Let ["r"] (some (.Call (.inl .ADD) [.Var "x", .Lit (UInt256.ofNat 1)]))]

/-- A contract with the single function `inc`. -/
def incContract : YulContract :=
  ⟨.Block [], List.toFinmap ([⟨"inc", incDef⟩] : List (Σ _ : YulFunctionName, FunctionDefinition))⟩

/-- `let y := inc(0)`. -/
def callInc : Stmt := .Let ["y"] (some (.Call (.inr "inc") [.Lit (UInt256.ofNat 0)]))

/-- A start state whose code owner has an account (the interpreter looks it up on every call). -/
def incState : State :=
  .Ok { (default : SharedState .Yul) with
        accountMap := Std.TreeMap.insert ∅ (default : AccountAddress) default } ∅

/-- On `let y := inc(0)` the Cancun model charges `ADD` and the 21-gas call, 24 gas; the inlined
lowering charges only `ADD`, 3 gas. -/
theorem callInc_gas :
    (runF cancunFn (some incContract) 0 1 callInc incState).map Prod.snd = some 24 ∧
    (runF (inlined cancunFn) (some incContract) 0 1 callInc incState).map Prod.snd = some 3 := by
  constructor <;> rfl

/-- **Inlining breaks the floor.** There is a cost model `c'` (the Cancun model with calls
inlined) that agrees with `cancunFn` on every builtin and on branches, and a program on which the
Cancun model charges strictly *more* than `c'`. So in `runF_costMono` the hypothesis
`c.call ≤ c'.call` cannot be dropped, and the unrestricted claim "the Yul model is a floor on
compiled gas" is false for any compiler that inlines. -/
theorem inlining_breaks_floor :
    (∀ op, cancunFn.prim op = (inlined cancunFn).prim op) ∧
    cancunFn.branch = (inlined cancunFn).branch ∧
    ∃ (co : Option YulContract) (st : Stmt) (s : State) (r : Res) (g g' : ℕ),
      runF cancunFn co 0 1 st s = some (r, g) ∧
      runF (inlined cancunFn) co 0 1 st s = some (r, g') ∧ g' < g := by
  refine ⟨fun _ => rfl, rfl, ?_⟩
  obtain ⟨h1, h2⟩ := callInc_gas
  rcases hx : runF cancunFn (some incContract) 0 1 callInc incState with _ | ⟨r, g⟩
  · simp [hx] at h1
  rcases hy : runF (inlined cancunFn) (some incContract) 0 1 callInc incState with _ | ⟨r', g'⟩
  · simp [hy] at h2
  have hr := runF_result_indep cancunFn (inlined cancunFn) (some incContract) 0 1 callInc incState
  simp only [hx, hy, Option.map_some, Option.some.injEq] at hr h1 h2
  subst hr
  exact ⟨_, _, _, r, g, g', hx, hy, by omega⟩

end Gas
end Yul
end EvmYul
