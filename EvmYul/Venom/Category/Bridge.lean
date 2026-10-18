module

public import EvmYul.Venom.Category.FuncFlow
public import EvmYul.Venom.Category.PathSemantics

public section

/-!
# The bridge: the path-category semantics of a Venom function is its fuel interpreter (T5b)

`funcDecor f` decorates the flow quiver of a function `f` (`FuncFlow.lean`) in the machine's
Kleisli category, as D3.4 prescribes:

* the object at every block is the environment *after* its φs (`Cfg.Env`);
* the arrow of slot `k` from `u` to `v` runs `u`'s body and terminator (`blockRest`), is defined
  only if the terminator selects slot `k` (the guard: the jump target's first index in `u`'s
  successor list is `k`, so of two parallel slots `jnz c, @a, @a` exactly one is taken), then
  copies `v`'s φs from `u` (`applyPhis`, a parallel copy); a missing `v` or a φ with no source for
  `u` is a fault;
* the exit of a block runs its body and terminator and throws `halt`/`revert`, or `fault` for a
  block that is missing or cannot run; it is undefined when the block jumps.

**Bridge theorem (`runPost_iff_outcomeWithin`, proved by induction on the fuel).** For every fuel
`n`, the outcomes of the free functor over paths of length `≤ n` are exactly the results of the
compiled interpreter: `runPost f n cur env s = r` iff `r` is an outcome within `n`. On whole runs
(`run_succ_iff_outcomeWithin`): `run f (n + 1)` equals the union over paths of length `≤ n`, after
the entry block's own φs. This settles the off-by-one of D3.7: **`run f (n + 1) = ⟦f⟧ₙ`**, and
`run f 0` is always `fuelOut` (the empty filtration stage). A run that ends in `fuelOut` is one with
no outcome within `n` (`run_succ_fuelOut_iff`).

**P3.2 (`funcDecor_deterministic`).** All outcomes of a function from one input agree, so the
union of D3.6 is a join; this is derived from the bridge and the fuel stability of `run`
(`run_stable`).
-/

namespace EvmYul.Venom.Category

open CategoryTheory EvmYul.Venom.Cfg

/-- The exits as results of the interpreter. -/
@[expose] def Exit.toResult {σ : Type} : Exit σ → Result σ
  | .halt s => .halted s
  | .revert s => .reverted s
  | .fault => .fault

theorem Exit.toResult_injective {σ : Type} : Function.Injective (Exit.toResult (σ := σ)) :=
  fun a b h => by cases a <;> cases b <;> simp_all [Exit.toResult]

theorem Exit.toResult_ne_fuelOut {σ : Type} (r : Exit σ) : r.toResult ≠ .fuelOut := by
  cases r <;> simp [Exit.toResult]

/-- Every result of `run` other than `fuelOut` is an exit. -/
theorem result_cases {σ : Type} : (r : Result σ) → r = .fuelOut ∨ ∃ x : Exit σ, r = x.toResult
  | .halted s => .inr ⟨.halt s, rfl⟩
  | .reverted s => .inr ⟨.revert s, rfl⟩
  | .fault => .inr ⟨.fault, rfl⟩
  | .fuelOut => .inl rfl

section
variable {σ : Type} [EvmInterface σ]

/-- A block after its φs: the body, then the terminator. -/
@[expose] def blockRest (b : Block) (env : Cfg.Env) (s : σ) : Option (Next × Cfg.Env × σ) := do
  let term ← b.term?
  match ← runPlain env s b.body with
  | .abort s' => pure (.revert, env, s')
  | .cont env s =>
    let n ← execTerm env term
    pure (n, env, s)

/-- `runBlock` is the φs followed by `blockRest`. -/
@[reviewed_rfl "API: unfolds the do-block of runBlock into its φ part and the rest"]
theorem runBlock_eq_bind (b : Block) (prev : Label) (env : Cfg.Env) (s : σ) :
    runBlock b prev env s = (applyPhis prev env b.phis).bind fun env' => blockRest b env' s := rfl

/-- A jump of `blockRest` names one of the block's successors. -/
theorem blockRest_goto_mem {b : Block} {env env' : Cfg.Env} {s s' : σ} {l : Label}
    (h : blockRest b env s = some (.goto l, env', s')) : l ∈ b.succs := by
  simp only [blockRest, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨t, ht, r, _, hr⟩ := h
  cases r <;> simp [Option.bind_eq_some_iff] at hr
  simpa [Block.succs, ht] using execTerm_goto_mem hr.1

/-- The arrow of slot `k` from `u` to `v`, as a plain function. -/
@[expose] def stepFn (f : Func) (u v : Label) (k : Nat) (env : Cfg.Env) (s : σ) :
    Option (Except (Exit σ) (Cfg.Env × σ)) :=
  match f.find? u with
  | none => none
  | some b =>
    match blockRest b env s with
    | some (.goto l, env', s') =>
      if b.succs.idxOf l = k then
        match f.find? v with
        | none => some (.error .fault)
        | some bv =>
          match applyPhis u env' bv.phis with
          | none => some (.error .fault)
          | some env'' => some (.ok (env'', s'))
      else none
    | _ => none

/-- The exit of block `c`, as a plain function. -/
@[expose] def exitFn (f : Func) (c : Label) (env : Cfg.Env) (s : σ) :
    Option (Except (Exit σ) (Empty × σ)) :=
  match f.find? c with
  | none => some (.error .fault)
  | some b =>
    match blockRest b env s with
    | none => some (.error .fault)
    | some (.halt, _, s') => some (.error (.halt s'))
    | some (.revert, _, s') => some (.error (.revert s'))
    | some (.goto _, _, _) => none

/-- **The decoration of a Venom function (D3.4).** -/
@[expose] def funcDecor (f : Func) : Decor (flowOf f).B σ where
  obj _ := Cfg.Env
  step {u v} e := fun env => Mach.mk (stepFn f u v e.1.1.2 env)
  exit c := fun env => Mach.mk (exitFn f c env)

/-- A run that starts after the φs of block `cur`: the block itself costs no fuel, then `run`
continues with fuel `n`. -/
@[expose] def runPost (f : Func) (n : Nat) (cur : Label) (env : Cfg.Env) (s : σ) : Result σ :=
  match f.find? cur with
  | none => .fault
  | some b =>
    match blockRest b env s with
    | none => .fault
    | some (.goto l, env', s') => run f n cur l env' s'
    | some (.halt, _, s') => .halted s'
    | some (.revert, _, s') => .reverted s'

/-- `run` with one more unit of fuel: the φs of `cur`, then `runPost`. -/
theorem run_succ (f : Func) (n : Nat) (prev cur : Label) (env : Cfg.Env) (s : σ) :
    run f (n + 1) prev cur env s =
      match f.find? cur with
      | none => .fault
      | some b =>
        match applyPhis prev env b.phis with
        | none => .fault
        | some env' => runPost f n cur env' s := by
  simp only [run, runBlock_eq_bind, runPost]
  rcases f.find? cur with _ | b <;> simp only
  rcases applyPhis prev env b.phis with _ | env' <;> simp only [Option.bind_none, Option.bind_some]
  rcases blockRest b env' s with _ | ⟨_ | _ | _, _, _⟩ <;> rfl

/-- The arrow of slot `k` from `u` to `v`, evaluated. -/
theorem step_run (f : Func) {u v : Label} (e : @Quiver.Hom (flowOf f).B _ u v) (env : Cfg.Env)
    (s : σ) : (((funcDecor f).step e) env).run s = stepFn f u v e.1.1.2 env s :=
  Mach.run_mk _ s

/-- The exit of block `c`, evaluated. -/
theorem exit_run (f : Func) (c : Label) (env : Cfg.Env) (s : σ) :
    (((funcDecor f).exit c) env).run s = exitFn f c env s :=
  Mach.run_mk _ s

/-- How block `cur` ends when it does not jump: `none` iff it jumps. -/
@[expose] def immediate (f : Func) (cur : Label) (env : Cfg.Env) (s : σ) : Option (Exit σ) :=
  match f.find? cur with
  | none => some .fault
  | some b =>
    match blockRest b env s with
    | none => some .fault
    | some (.halt, _, s') => some (.halt s')
    | some (.revert, _, s') => some (.revert s')
    | some (.goto _, _, _) => none

theorem exitFn_eq_immediate (f : Func) (cur : Label) (env : Cfg.Env) (s : σ) :
    exitFn f cur env s = (immediate f cur env s).map .error := by
  unfold exitFn immediate
  rcases f.find? cur with _ | b; · rfl
  simp only; rcases blockRest b env s with _ | ⟨_ | _ | _, _, _⟩ <;> rfl

theorem runPost_of_immediate {f : Func} {n : Nat} {cur : Label} {env : Cfg.Env} {s : σ}
    {x : Exit σ} (h : immediate f cur env s = some x) : runPost f n cur env s = x.toResult := by
  unfold immediate at h; unfold runPost
  split at h <;> [skip; split at h] <;> cases h <;> simp [*, Exit.toResult]

/-- A block that jumps continues with `run` and the same fuel. -/
theorem runPost_of_goto {f : Func} {n : Nat} {cur l : Label} {b : Block} {env env' : Cfg.Env}
    {s s' : σ} (hb : f.find? cur = some b) (hr : blockRest b env s = some (.goto l, env', s')) :
    runPost f n cur env s = run f n cur l env' s' := by
  simp [runPost, hb, hr]

theorem stepFn_of_immediate {f : Func} {u v : Label} {k : Nat} {env : Cfg.Env} {s : σ}
    {x : Exit σ} (h : immediate f u env s = some x) : stepFn f u v k env s = none := by
  unfold immediate at h; unfold stepFn
  split at h <;> [skip; split at h] <;> cases h <;> simp [*]

theorem goto_of_immediate {f : Func} {cur : Label} {env : Cfg.Env} {s : σ}
    (h : immediate f cur env s = none) :
    ∃ b l env' s', f.find? cur = some b ∧ blockRest b env s = some (.goto l, env', s') := by
  unfold immediate at h
  split at h <;> [cases h; split at h] <;> first | exact ⟨_, _, _, _, ‹_›, ‹_›⟩ | cases h

/-- A path with at least one arrow starts with an arrow. -/
@[reviewed_generic "a fact about Mathlib quiver paths, used by the fuel bridge"]
theorem path_front {V : Type} [Quiver V] {a : V} :
    ∀ {b c : V} (p : Quiver.Path a b) (e : b ⟶ c),
      ∃ (d : V) (e₀ : a ⟶ d) (q : Quiver.Path d c), p.cons e = e₀.toPath.comp q ∧
        q.length = p.length
  | _, _, .nil, e => ⟨_, e, .nil, rfl, rfl⟩
  | _, _, .cons p e', e =>
    let ⟨d, e₀, q, h, hl⟩ := path_front p e'
    ⟨d, e₀, q.cons e, by rw [h, Quiver.Path.comp_cons], by simp [hl]⟩

/-- The slot of a successor `l` of the block labelled `u`. -/
@[expose] def succSlot (f : Func) {u : Label} {b : Block} (hb : f.find? u = some b) {l : Label}
    (hl : l ∈ b.succs) : Slot f :=
  ⟨(u, b.succs.idxOf l), b, hb, List.idxOf_lt_length_iff.2 hl⟩

theorem slotTarget_succSlot (f : Func) {u : Label} {b : Block} (hb : f.find? u = some b)
    {l : Label} (hl : l ∈ b.succs) : slotTarget f (succSlot f hb hl) = l := by
  simp [slotTarget, succSlot, hb, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (List.idxOf_lt_length_iff.2 hl), List.getElem_idxOf]

/-- The arrow from `u` to a successor `l` of its block. -/
@[expose] def slotArrow (f : Func) {u : Label} {b : Block} (hb : f.find? u = some b) {l : Label}
    (hl : l ∈ b.succs) : @Quiver.Hom (flowOf f).B _ u l :=
  ⟨succSlot f hb hl, rfl, slotTarget_succSlot f hb hl⟩

/-- The arrow of a successor, evaluated. -/
theorem step_run_slot (f : Func) {u : Label} {b : Block} (hb : f.find? u = some b) {l : Label}
    (hl : l ∈ b.succs) (env : Cfg.Env) (s : σ) :
    (((funcDecor f).step (slotArrow f hb hl)) env).run s = stepFn f u l (b.succs.idxOf l) env s :=
  Mach.run_mk _ s

/-- The arrow of a slot names the label at its index. -/
theorem arrow_target (f : Func) {u v : Label} (e : @Quiver.Hom (flowOf f).B _ u v) :
    ∃ b, f.find? u = some b ∧ e.1.1.2 < b.succs.length ∧ b.succs[e.1.1.2]? = some v := by
  obtain ⟨⟨⟨u', k⟩, b, hb, hk⟩, rfl, rfl⟩ := e
  exact ⟨b, hb, hk, by simp [flowOf, slotTarget, hb, hk]⟩

/-- After a jump of `u` to `l`, the selected arrow either faults (missing `l`, a φ with no source
for `u`) or continues after `l`'s φs; `run f (n + 1) u l` gives the same. -/
theorem stepFn_goto {f : Func} {u l : Label} {b : Block} {env env' : Cfg.Env} {s s' : σ}
    (hb : f.find? u = some b) (hr : blockRest b env s = some (.goto l, env', s')) :
    stepFn f u l (b.succs.idxOf l) env s =
      match f.find? l with
      | none => some (.error .fault)
      | some bl =>
        match applyPhis u env' bl.phis with
        | none => some (.error .fault)
        | some env'' => some (.ok (env'', s')) := by
  simp only [stepFn, hb, hr, if_pos]

/-- An arrow whose slot is not the one selected is undefined. -/
theorem stepFn_unselected {f : Func} {u v l : Label} {b : Block} {env env' : Cfg.Env} {s s' : σ}
    {k : Nat} (hb : f.find? u = some b) (hr : blockRest b env s = some (.goto l, env', s'))
    (hk : b.succs.idxOf l ≠ k) : stepFn f u v k env s = none := by
  simp [stepFn, hb, hr, hk]

/-- A block that does not jump has exactly its immediate exit as outcome, for every fuel. -/
theorem outcomeWithin_immediate {f : Func} {n : Nat} {cur : Label} {env : Cfg.Env} {s : σ}
    {x : Exit σ} (h : immediate f cur env s = some x) (r : Exit σ) :
    (funcDecor f).OutcomeWithin n cur env s r ↔ r = x := by
  constructor
  · rintro ⟨c, _ | ⟨p, e⟩, -, he⟩
    · rw [Decor.semPath_nil, Category.id_comp, exit_run, exitFn_eq_immediate, h] at he
      exact (Except.error.inj (Option.some.inj he)).symm
    · obtain ⟨d, e₀, q, hpq, -⟩ := path_front p e
      simp [hpq, Decor.semPath_comp, Decor.semPath_toPath, MachCat.comp_run, step_run,
        stepFn_of_immediate h] at he
  · rintro rfl
    refine ⟨cur, .nil, Nat.zero_le _, ?_⟩
    rw [Decor.semPath_nil, Category.id_comp, exit_run, exitFn_eq_immediate, h]; rfl

/-- A block that jumps to `l` has no outcome without fuel. -/
theorem outcomeWithin_zero_goto {f : Func} {cur : Label} {env : Cfg.Env} {s : σ}
    (h : immediate f cur env s = none) (r : Exit σ) :
    ¬ (funcDecor f).OutcomeWithin 0 cur env s r := by
  rintro ⟨c, _ | ⟨p, e⟩, hp, he⟩
  · rw [Decor.semPath_nil, Category.id_comp, exit_run, exitFn_eq_immediate, h] at he; cases he
  · simp at hp

/-- A block that jumps to `l`: its outcomes within `m + 1` are the faults of the selected arrow and
the outcomes within `m` after `l`'s φs. -/
theorem outcomeWithin_succ_goto {f : Func} {m : Nat} {cur l : Label} {b : Block}
    {env env' : Cfg.Env} {s s' : σ} (hb : f.find? cur = some b)
    (hr : blockRest b env s = some (.goto l, env', s')) (r : Exit σ) :
    (funcDecor f).OutcomeWithin (m + 1) cur env s r ↔
      match f.find? l with
      | none => r = .fault
      | some bl =>
        match applyPhis cur env' bl.phis with
        | none => r = .fault
        | some env'' => (funcDecor f).OutcomeWithin m l env'' s' r := by
  have himm : immediate f cur env s = none := by simp [immediate, hb, hr]
  have hl := blockRest_goto_mem hr
  have hs := stepFn_goto hb hr
  constructor
  · rintro ⟨c, _ | ⟨p, e⟩, hp, he⟩
    · rw [Decor.semPath_nil, Category.id_comp, exit_run, exitFn_eq_immediate, himm] at he
      cases he
    obtain ⟨d, e₀, q, hpq, hlen⟩ := path_front p e
    rw [hpq, Decor.semPath_comp, Decor.semPath_toPath, Category.assoc, MachCat.comp_run,
      step_run] at he
    obtain ⟨b₀, hb₀, -, hkv⟩ := arrow_target f e₀
    obtain rfl : b = b₀ := Option.some.inj (hb.symm.trans hb₀)
    by_cases hsel : b.succs.idxOf l = e₀.1.1.2
    · obtain rfl : l = d := by
        rwa [← hsel, List.getElem?_eq_getElem (List.idxOf_lt_length_iff.2 hl), List.getElem_idxOf,
          Option.some_inj] at hkv
      rw [← hsel, hs] at he
      rcases hfl : f.find? l with _ | bl <;> simp only [hfl] at he ⊢
      · simpa [eq_comm] using he
      rcases hph : applyPhis cur env' bl.phis with _ | env'' <;> simp only [hph] at he ⊢
      · simpa [eq_comm] using he
      exact ⟨c, q, by simp at hp; omega, he⟩
    · simp [stepFn_unselected hb hr hsel] at he
  · intro h
    rcases hfl : f.find? l with _ | bl <;> simp only [hfl] at h hs
    · subst h
      exact ⟨l, (slotArrow f hb hl).toPath, by simp,
        by rw [Decor.semPath_toPath, MachCat.comp_run, step_run_slot, hs]⟩
    rcases hph : applyPhis cur env' bl.phis with _ | env'' <;> simp only [hph] at h hs
    · subst h
      exact ⟨l, (slotArrow f hb hl).toPath, by simp,
        by rw [Decor.semPath_toPath, MachCat.comp_run, step_run_slot, hs]⟩
    obtain ⟨c, q, hq, hqe⟩ := h
    refine ⟨c, (slotArrow f hb hl).toPath.comp q, by simp; omega, ?_⟩
    rwa [Decor.semPath_comp, Decor.semPath_toPath, Category.assoc, MachCat.comp_run,
      step_run_slot, hs]

/-- **The bridge theorem.** The outcomes over paths of length `≤ n` are exactly the results of
`runPost f n`. -/
theorem runPost_iff_outcomeWithin (f : Func) :
    ∀ (n : Nat) (cur : Label) (env : Cfg.Env) (s : σ) (r : Exit σ),
      runPost f n cur env s = r.toResult ↔ (funcDecor f).OutcomeWithin n cur env s r := by
  intro n
  induction n <;> intro cur env s r <;> rcases hi : immediate f cur env s with _ | x <;>
    try (rw [runPost_of_immediate hi, outcomeWithin_immediate hi]
         exact Exit.toResult_injective.eq_iff.trans eq_comm)
  all_goals obtain ⟨b, l, env', s', hb, hr⟩ := goto_of_immediate hi
  · rw [runPost_of_goto hb hr]
    exact iff_of_false (fun h => Exit.toResult_ne_fuelOut r h.symm) (outcomeWithin_zero_goto hi r)
  · rename_i ih
    rw [runPost_of_goto hb hr, run_succ, outcomeWithin_succ_goto hb hr]
    rcases f.find? l with _ | bl <;> simp only
    · cases r <;> simp [Exit.toResult]
    rcases applyPhis cur env' bl.phis with _ | env'' <;> simp only
    · cases r <;> simp [Exit.toResult]
    · exact ih l env'' s' r

/-- **Whole runs: `run f (n + 1) = ⟦f⟧ₙ`.** After the φs of the starting block, the results of
`run` with fuel `n + 1` are the outcomes over paths of length `≤ n`. -/
theorem run_succ_iff_outcomeWithin (f : Func) (n : Nat) (prev cur : Label) (env : Cfg.Env)
    (s : σ) (r : Exit σ) :
    run f (n + 1) prev cur env s = r.toResult ↔
      match f.find? cur with
      | none => r = .fault
      | some b =>
        match applyPhis prev env b.phis with
        | none => r = .fault
        | some env' => (funcDecor f).OutcomeWithin n cur env' s r := by
  rw [run_succ]
  rcases f.find? cur with _ | b
  · cases r <;> simp [Exit.toResult]
  · simp only
    rcases applyPhis prev env b.phis with _ | env'
    · cases r <;> simp [Exit.toResult]
    · exact runPost_iff_outcomeWithin f n cur env' s r

/-- `fuelOut` after the starting block's φs is exactly "no outcome within `n`". -/
theorem runPost_fuelOut_iff (f : Func) (n : Nat) (cur : Label) (env : Cfg.Env) (s : σ) :
    runPost f n cur env s = .fuelOut ↔ ∀ r, ¬ (funcDecor f).OutcomeWithin n cur env s r := by
  refine ⟨fun h r ho => Exit.toResult_ne_fuelOut r
    (h ▸ (runPost_iff_outcomeWithin f n cur env s r).2 ho).symm, fun h => ?_⟩
  rcases result_cases (runPost f n cur env s) with h' | ⟨x, hx⟩
  exacts [h', absurd ((runPost_iff_outcomeWithin f n cur env s x).1 hx) (h x)]

/-- Fuel stability of `runPost` (from `run_stable`). -/
theorem runPost_stable (f : Func) (n k : Nat) (cur : Label) (env : Cfg.Env) (s : σ)
    (h : runPost f n cur env s ≠ .fuelOut) : runPost f (n + k) cur env s = runPost f n cur env s := by
  rcases hi : immediate f cur env s with _ | x
  · obtain ⟨b, l, env', s', hb, hr⟩ := goto_of_immediate hi
    simp only [runPost_of_goto hb hr] at h ⊢
    exact run_stable f n k _ _ env' s' h
  · simp only [runPost_of_immediate hi]

/-- **P3.2 for Venom functions.** All outcomes from one input agree. -/
theorem funcDecor_deterministic (f : Func) : (funcDecor (σ := σ) f).Deterministic := by
  intro a x s r r' h h'
  obtain ⟨n, hn⟩ := ((funcDecor f).outcome_iff_exists_within a x s r).1 h
  obtain ⟨m, hm⟩ := ((funcDecor f).outcome_iff_exists_within a x s r').1 h'
  have e₁ := (runPost_iff_outcomeWithin f n a x s r).2 hn
  have e₂ := (runPost_iff_outcomeWithin f m a x s r').2 hm
  have s₁ := runPost_stable f n m a x s (by rw [e₁]; exact Exit.toResult_ne_fuelOut r)
  have s₂ := runPost_stable f m n a x s (by rw [e₂]; exact Exit.toResult_ne_fuelOut r')
  apply Exit.toResult_injective
  rw [← e₁, ← e₂, ← s₁, ← s₂, Nat.add_comm]

end

end EvmYul.Venom.Category
