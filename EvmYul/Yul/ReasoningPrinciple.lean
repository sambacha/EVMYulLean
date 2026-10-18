module

public import EvmYul.Yul.Interpreter
public import EvmYul.ProofTags

/-!
# Reasoning principles for Yul

Specifications `Spec` / `FuelSpec` of Yul executions and the rules to prove them compositionally:
sequencing, conditionals, loops and purity.
-/

public section

namespace EvmYul
namespace Yul
namespace ReasoningPrinciple

open Ast

@[expose] def Spec (R : State → State → Prop) (s₀ s₉ : State) : Prop :=
  R s₀ s₉

@[expose] def FuelSpec (R : Nat → State → State → Prop) (fuel : Nat) (s₀ s₉ : State) : Prop :=
  R fuel s₀ s₉

theorem spec_eq {P P' : State → State → Prop} {s₀ s₉ : State} :
    (P s₀ s₉ → P' s₀ s₉) → Spec P s₀ s₉ → Spec P' s₀ s₉ := by
  intro h hspec
  exact h hspec

@[expose] def State.isOk : State → Prop
  | .Ok _ _ => True
  | _ => False

def State.isBreak : State → Prop
  | .Checkpoint (.Break _ _) => True
  | _ => False

def State.isContinue : State → Prop
  | .Checkpoint (.Continue _ _) => True
  | _ => False

def State.isLeave : State → Prop
  | .Checkpoint (.Leave _ _) => True
  | _ => False

def State.isCheckpoint : State → Prop
  | .Checkpoint _ => True
  | _ => False

def State.isOutOfFuel : State → Prop
  | .OutOfFuel => True
  | _ => False

@[expose] def isPure (s₀ s₁ : State) : Prop :=
  s₀.sharedState = s₁.sharedState

@[simp]
theorem State.isOk_ok (sharedState : EvmYul.SharedState .Yul) (store : VarStore) :
    State.isOk (.Ok sharedState store) := by
  trivial

@[simp]
theorem State.not_isOk_outOfFuel : ¬ State.isOk .OutOfFuel := by
  intro h
  cases h

@[simp]
theorem State.not_isOk_checkpoint (jump : Jump) : ¬ State.isOk (.Checkpoint jump) := by
  intro h
  cases h

@[simp]
theorem State.isOutOfFuel_outOfFuel : State.isOutOfFuel .OutOfFuel := by
  trivial

@[simp]
theorem State.not_isOutOfFuel_ok (sharedState : EvmYul.SharedState .Yul) (store : VarStore) :
    ¬ State.isOutOfFuel (.Ok sharedState store) := by
  intro h
  cases h

@[simp]
theorem State.not_isOutOfFuel_checkpoint (jump : Jump) :
    ¬ State.isOutOfFuel (.Checkpoint jump) := by
  intro h
  cases h

@[simp]
theorem State.isBreak_break (sharedState : EvmYul.SharedState .Yul) (store : VarStore) :
    State.isBreak (.Checkpoint (.Break sharedState store)) := by
  trivial

@[simp]
theorem State.isContinue_continue (sharedState : EvmYul.SharedState .Yul) (store : VarStore) :
    State.isContinue (.Checkpoint (.Continue sharedState store)) := by
  trivial

@[simp]
theorem State.isLeave_leave (sharedState : EvmYul.SharedState .Yul) (store : VarStore) :
    State.isLeave (.Checkpoint (.Leave sharedState store)) := by
  trivial

@[simp, reviewed_rfl "reflexivity of the Yul purity relation (`isPure s s` is `sharedState` equality)"]
theorem isPure_rfl (s : State) : isPure s s := by
  rfl

theorem isPure_trans {s₀ s₁ s₂ : State} :
    isPure s₀ s₁ → isPure s₁ s₂ → isPure s₀ s₂ := by
  intro h₀ h₁
  exact h₀.trans h₁

@[simp]
theorem isPure_insert (s : State) (var : Identifier) (val : Ast.Literal) :
    isPure s (s.insert var val) := by
  cases s <;> simp [isPure, State.insert, State.sharedState]

@[expose] def LoopExact
    (cond : Expr) (post body : List Stmt) (codeOverride : Option YulContract)
    (fuel : Nat) (s₀ s₉ : State) : Prop :=
  exec fuel (.For cond post body) codeOverride s₀ = .ok s₉

@[expose] def FunctionBodyExact
    (f : FunctionDefinition) (codeOverride : Option YulContract)
    (fuel : Nat) (s₀ s₉ : State) : Prop :=
  exec fuel (.Block f.body) codeOverride s₀ = .ok s₉

@[expose] def FunctionCallSummary
    (AFunc : Nat → State → State → Prop) (f : FunctionDefinition)
    (args : List Ast.Literal) (vars : List Identifier) (s₀ s₉ : State) : Prop :=
  ∃ bodyFuel sBody,
    AFunc bodyFuel (👌 s₀.initcall f.params args) sBody ∧
    s₉ = (sBody.reviveJump.overwrite? s₀ |>.setStore s₀).multifill vars (List.map sBody.lookup! f.rets)

@[expose] def ResolvedFunctionInCode
    (code : YulContract) (name : YulFunctionName) (f : FunctionDefinition) : Prop :=
  code.functions.lookup name = some f

@[expose] def OrdinaryFunctionName (name : YulFunctionName) : Prop :=
  name ≠ "datacopy" ∧ name ≠ "dataoffset" ∧ name ≠ "datasize"

@[expose] def ResolvedFunction
    (codeOverride : Option YulContract) (s : State)
    (name : YulFunctionName) (f : FunctionDefinition) : Prop :=
  OrdinaryFunctionName name ∧
    match codeOverride with
    | some code => ResolvedFunctionInCode code name f
    | none =>
        ∃ account,
          s.sharedState.accountMap.get? s.executionEnv.codeOwner = some account ∧
          ResolvedFunctionInCode account.code name f

theorem execObjectDataBuiltin?_none_of_ordinary
    {name : YulFunctionName} {vars : List Identifier} {args : List Ast.Literal} {s : State}
    (hordinary : OrdinaryFunctionName name) :
    execObjectDataBuiltin? name vars (.ok (s, args)) = none := by
  rcases hordinary with ⟨hdatacopy, _, _⟩
  cases name; simp [execObjectDataBuiltin?] at hdatacopy ⊢
  split <;> simp_all

@[expose] def PureFunctionCallVC
    (AFunc : Nat → State → State → Prop) (f : FunctionDefinition)
    (args : List Ast.Literal) (vars : List Identifier) (s₀ s₉ : State) : Prop :=
  FunctionCallSummary AFunc f args vars s₀ s₉

@[expose] def LoopConcrete
    (ABody APost : State → State → Prop) (ACond : State → Ast.Literal)
    (fuel : Nat) (s₀ s₉ : State) : Prop :=
  match fuel with
  | 0 => False
  | 1 => False
  | 2 => False
  | fuel' + 3 =>
      if ACond (👌 s₀) = ⟨0⟩ then
        s₉ = (👌 s₀).overwrite? s₀
      else
        ∃ s₂,
          Spec ABody (👌 s₀) s₂ ∧
            match s₂ with
            | .OutOfFuel => s₉ = s₂.overwrite? s₀
            | .Checkpoint (.Break _ _) => s₉ = s₂.reviveJump.overwrite? s₀
            | .Checkpoint (.Leave _ _) => s₉ = s₂.overwrite? s₀
            | .Checkpoint (.Continue _ _) | .Ok _ _ =>
                ∃ s₃ s₅,
                  Spec APost (🧟 s₂) s₃ ∧
                  Spec (LoopConcrete ABody APost ACond fuel') (s₃.overwrite? s₀) s₅ ∧
                  s₉ = s₅.overwrite? s₀

theorem loopConcrete_implies_spec
    (ACond : State → Ast.Literal)
    (APost ABody AFor : State → State → Prop)
    {fuel : Nat} {s₀ s₉ : State}
    (AZero :
      ∀ {s₀ s₉ : State},
        ACond (👌 s₀) = ⟨0⟩ →
        s₉ = (👌 s₀).overwrite? s₀ →
        AFor s₀ s₉)
    (AOutOfFuel :
      ∀ {s₀ : State},
        ACond (👌 s₀) ≠ ⟨0⟩ →
        ABody (👌 s₀) .OutOfFuel →
        AFor s₀ (State.OutOfFuel.overwrite? s₀))
    (ABreak :
      ∀ {s₀ : State} {sharedState : EvmYul.SharedState .Yul} {store : VarStore},
        ACond (👌 s₀) ≠ ⟨0⟩ →
        ABody (👌 s₀) (.Checkpoint (.Break sharedState store)) →
        AFor s₀ ((State.Checkpoint (.Break sharedState store)).reviveJump.overwrite? s₀))
    (ALeave :
      ∀ {s₀ : State} {sharedState : EvmYul.SharedState .Yul} {store : VarStore},
        ACond (👌 s₀) ≠ ⟨0⟩ →
        ABody (👌 s₀) (.Checkpoint (.Leave sharedState store)) →
        AFor s₀ ((State.Checkpoint (.Leave sharedState store)).overwrite? s₀))
    (AStepContinue :
      ∀ {s₀ s₃ s₅ : State} {sharedState : EvmYul.SharedState .Yul} {store : VarStore},
        ACond (👌 s₀) ≠ ⟨0⟩ →
        ABody (👌 s₀) (.Checkpoint (.Continue sharedState store)) →
        APost (🧟 (.Checkpoint (.Continue sharedState store))) s₃ →
        AFor (s₃.overwrite? s₀) s₅ →
        AFor s₀ (s₅.overwrite? s₀))
    (AStepOk :
      ∀ {s₀ s₃ s₅ : State} {sharedState : EvmYul.SharedState .Yul} {store : VarStore},
        ACond (👌 s₀) ≠ ⟨0⟩ →
        ABody (👌 s₀) (.Ok sharedState store) →
        APost (🧟 (.Ok sharedState store)) s₃ →
        AFor (s₃.overwrite? s₀) s₅ →
        AFor s₀ (s₅.overwrite? s₀)) :
    Spec (LoopConcrete ABody APost ACond fuel) s₀ s₉ →
      Spec AFor s₀ s₉ := by
  unfold Spec
  induction fuel using Nat.strong_induction_on generalizing s₀ s₉ with
  | h fuel ih =>
      intro hconcrete
      cases fuel with
      | zero =>
          simp [LoopConcrete] at hconcrete
      | succ fuel₁ =>
          cases fuel₁ with
          | zero =>
              simp [LoopConcrete] at hconcrete
          | succ fuel₂ =>
              cases fuel₂ with
              | zero =>
                  simp [LoopConcrete] at hconcrete
              | succ fuel' =>
                  simp [LoopConcrete] at hconcrete
                  by_cases hzero : ACond (👌 s₀) = ⟨0⟩
                  · simp [hzero] at hconcrete
                    exact AZero hzero hconcrete
                  · simp [hzero] at hconcrete
                    rcases hconcrete with ⟨s₂, hbody, htail⟩
                    cases s₂ with
                    | OutOfFuel =>
                        rw [htail]
                        exact AOutOfFuel hzero hbody
                    | Checkpoint jump =>
                        cases jump with
                        | Break sharedState store =>
                            rw [htail]
                            exact ABreak hzero hbody
                        | Leave sharedState store =>
                            rw [htail]
                            exact ALeave hzero hbody
                        | Continue sharedState store =>
                            rcases htail with ⟨s₃, hpost, s₅, hrec, hs₉⟩
                            subst s₉
                            have hfor : AFor (s₃.overwrite? s₀) s₅ :=
                              ih fuel' (Nat.lt_add_of_pos_right (by decide : 0 < 3)) hrec
                            exact AStepContinue hzero hbody hpost hfor
                    | Ok sharedState store =>
                        rcases htail with ⟨s₃, hpost, s₅, hrec, hs₉⟩
                        subst s₉
                        have hfor : AFor (s₃.overwrite? s₀) s₅ :=
                          ih fuel' (Nat.lt_add_of_pos_right (by decide : 0 < 3)) hrec
                        exact AStepOk hzero hbody hpost hfor

theorem loop_exec_implies_concrete
    (cond : Expr) (post body : List Stmt) (codeOverride : Option YulContract)
    (ACond : State → Ast.Literal) (APost ABody : State → State → Prop)
    {fuel : Nat} {s₀ s₉ : State}
    (hcond :
      ∀ {fuel : Nat} {s₀ s₁ : State} {condLit : Ast.Literal},
        eval fuel cond codeOverride s₀ = .ok (s₁, condLit) →
          s₁ = s₀ ∧ condLit = ACond s₀)
    (hpost :
      ∀ {fuel : Nat} {s₀ s₉ : State},
        exec fuel (.Block post) codeOverride s₀ = .ok s₉ → Spec APost s₀ s₉)
    (hbody :
      ∀ {fuel : Nat} {s₀ s₉ : State},
        exec fuel (.Block body) codeOverride s₀ = .ok s₉ → Spec ABody s₀ s₉) :
    exec fuel (.For cond post body) codeOverride s₀ = .ok s₉ →
      Spec (LoopConcrete ABody APost ACond fuel) s₀ s₉ := by
  unfold Spec
  induction fuel using Nat.strong_induction_on generalizing s₀ s₉ with
  | h fuel ih =>
      intro hcode
      cases fuel with
      | zero =>
          simp [exec] at hcode
      | succ loopFuel =>
          cases loopFuel with
          | zero =>
              simp [exec, loop] at hcode
          | succ loopFuel =>
              cases loopFuel with
              | zero =>
                  simp [exec, loop] at hcode
              | succ fuel' =>
                  simp [exec, loop] at hcode
                  generalize hcondExec :
                      eval fuel' cond codeOverride (👌 s₀) = condResult at hcode
                  cases condResult with
                  | error e =>
                      simp at hcode
                  | ok condResult =>
                      cases condResult with
                      | mk s₁ condLit =>
                          rcases hcond hcondExec with ⟨hs₁, hcondLit⟩
                          subst s₁
                          subst condLit
                          simp [LoopConcrete]
                          by_cases hzero : ACond (👌 s₀) = ⟨0⟩
                          · simp [hzero] at hcode ⊢
                            exact hcode.symm
                          · simp [hzero] at hcode ⊢
                            generalize hbodyExec :
                                exec fuel' (.Block body) codeOverride (👌 s₀) = bodyResult at hcode
                            cases bodyResult with
                            | error e =>
                                simp at hcode
                            | ok s₂ =>
                                have hbodySpec : Spec ABody (👌 s₀) s₂ := hbody hbodyExec
                                refine ⟨s₂, hbodySpec, ?_⟩
                                cases s₂ with
                                | OutOfFuel =>
                                    simp at hcode ⊢
                                    exact hcode.symm
                                | Checkpoint jump =>
                                    cases jump with
                                    | Break sharedState store =>
                                        simp at hcode ⊢
                                        exact hcode.symm
                                    | Leave sharedState store =>
                                        simp at hcode ⊢
                                        exact hcode.symm
                                    | Continue sharedState store =>
                                        simp at hcode
                                        generalize hpostExec :
                                            exec fuel' (.Block post) codeOverride
                                              (🧟 (State.Checkpoint (.Continue sharedState store))) =
                                              postResult at hcode
                                        cases postResult with
                                        | error e =>
                                            simp at hcode
                                        | ok s₃ =>
                                            simp at hcode
                                            have hpostSpec :
                                                Spec APost
                                                  (🧟 (State.Checkpoint (.Continue sharedState store))) s₃ :=
                                              hpost hpostExec
                                            generalize hrecExec :
                                                exec fuel' (.For cond post body) codeOverride
                                                  (s₃.overwrite? s₀) = recResult at hcode
                                            cases recResult with
                                            | error e =>
                                                simp at hcode
                                            | ok s₅ =>
                                                have hrec :
                                                    Spec (LoopConcrete ABody APost ACond fuel')
                                                      (s₃.overwrite? s₀) s₅ :=
                                                  ih fuel' (Nat.lt_add_of_pos_right (by decide : 0 < 3))
                                                    hrecExec
                                                simp at hcode
                                                exact ⟨s₃, hpostSpec, s₅, hrec, hcode.symm⟩
                                | Ok sharedState store =>
                                    simp at hcode
                                    generalize hpostExec :
                                        exec fuel' (.Block post) codeOverride
                                          (🧟 (State.Ok sharedState store)) = postResult at hcode
                                    cases postResult with
                                    | error e =>
                                        simp at hcode
                                    | ok s₃ =>
                                        simp at hcode
                                        have hpostSpec :
                                            Spec APost (🧟 (State.Ok sharedState store)) s₃ :=
                                          hpost hpostExec
                                        generalize hrecExec :
                                            exec fuel' (.For cond post body) codeOverride
                                              (s₃.overwrite? s₀) = recResult at hcode
                                        cases recResult with
                                        | error e =>
                                            simp at hcode
                                        | ok s₅ =>
                                            have hrec :
                                                Spec (LoopConcrete ABody APost ACond fuel')
                                                  (s₃.overwrite? s₀) s₅ :=
                                              ih fuel' (Nat.lt_add_of_pos_right (by decide : 0 < 3))
                                                hrecExec
                                            simp at hcode
                                            exact ⟨s₃, hpostSpec, s₅, hrec, hcode.symm⟩

theorem loop_exec_implies_spec
    (cond : Expr) (post body : List Stmt) (codeOverride : Option YulContract)
    (ACond : State → Ast.Literal) (APost ABody AFor : State → State → Prop)
    {fuel : Nat} {s₀ s₉ : State}
    (hcond :
      ∀ {fuel : Nat} {s₀ s₁ : State} {condLit : Ast.Literal},
        eval fuel cond codeOverride s₀ = .ok (s₁, condLit) →
          s₁ = s₀ ∧ condLit = ACond s₀)
    (hpost :
      ∀ {fuel : Nat} {s₀ s₉ : State},
        exec fuel (.Block post) codeOverride s₀ = .ok s₉ → Spec APost s₀ s₉)
    (hbody :
      ∀ {fuel : Nat} {s₀ s₉ : State},
        exec fuel (.Block body) codeOverride s₀ = .ok s₉ → Spec ABody s₀ s₉)
    (AZero :
      ∀ {s₀ s₉ : State},
        ACond (👌 s₀) = ⟨0⟩ →
        s₉ = (👌 s₀).overwrite? s₀ →
        AFor s₀ s₉)
    (AOutOfFuel :
      ∀ {s₀ : State},
        ACond (👌 s₀) ≠ ⟨0⟩ →
        ABody (👌 s₀) .OutOfFuel →
        AFor s₀ (State.OutOfFuel.overwrite? s₀))
    (ABreak :
      ∀ {s₀ : State} {sharedState : EvmYul.SharedState .Yul} {store : VarStore},
        ACond (👌 s₀) ≠ ⟨0⟩ →
        ABody (👌 s₀) (.Checkpoint (.Break sharedState store)) →
        AFor s₀ ((State.Checkpoint (.Break sharedState store)).reviveJump.overwrite? s₀))
    (ALeave :
      ∀ {s₀ : State} {sharedState : EvmYul.SharedState .Yul} {store : VarStore},
        ACond (👌 s₀) ≠ ⟨0⟩ →
        ABody (👌 s₀) (.Checkpoint (.Leave sharedState store)) →
        AFor s₀ ((State.Checkpoint (.Leave sharedState store)).overwrite? s₀))
    (AStepContinue :
      ∀ {s₀ s₃ s₅ : State} {sharedState : EvmYul.SharedState .Yul} {store : VarStore},
        ACond (👌 s₀) ≠ ⟨0⟩ →
        ABody (👌 s₀) (.Checkpoint (.Continue sharedState store)) →
        APost (🧟 (.Checkpoint (.Continue sharedState store))) s₃ →
        AFor (s₃.overwrite? s₀) s₅ →
        AFor s₀ (s₅.overwrite? s₀))
    (AStepOk :
      ∀ {s₀ s₃ s₅ : State} {sharedState : EvmYul.SharedState .Yul} {store : VarStore},
        ACond (👌 s₀) ≠ ⟨0⟩ →
        ABody (👌 s₀) (.Ok sharedState store) →
        APost (🧟 (.Ok sharedState store)) s₃ →
        AFor (s₃.overwrite? s₀) s₅ →
        AFor s₀ (s₅.overwrite? s₀)) :
    exec fuel (.For cond post body) codeOverride s₀ = .ok s₉ →
      Spec AFor s₀ s₉ := by
  intro hcode
  exact loopConcrete_implies_spec ACond APost ABody AFor
    AZero AOutOfFuel ABreak ALeave AStepContinue AStepOk
    (loop_exec_implies_concrete cond post body codeOverride ACond APost ABody
      hcond hpost hbody hcode)

theorem pureFunctionCallVC_intro
    {AFunc : Nat → State → State → Prop} {f : FunctionDefinition}
    {args : List Ast.Literal} {vars : List Identifier}
    {bodyFuel : Nat} {s₀ sBody s₉ : State} :
    AFunc bodyFuel (👌 s₀.initcall f.params args) sBody →
    s₉ = (sBody.reviveJump.overwrite? s₀ |>.setStore s₀).multifill vars (List.map sBody.lookup! f.rets) →
    PureFunctionCallVC AFunc f args vars s₀ s₉ := by
  intro hFunc hRet
  exact ⟨bodyFuel, sBody, hFunc, hRet⟩

theorem functionCallSummary_of_call
    {AFunc : Nat → State → State → Prop} {f : FunctionDefinition}
    {name : YulFunctionName} {args rets : List Ast.Literal} {vars : List Identifier}
    {fuel : Nat} {codeOverride : Option YulContract} {s₀ sCall : State}
    (hresolve : ResolvedFunction codeOverride s₀ name f)
    (habs :
      ∀ {bodyFuel : Nat} {sBody : State},
        FunctionBodyExact f codeOverride bodyFuel (👌 s₀.initcall f.params args) sBody →
          AFunc bodyFuel (👌 s₀.initcall f.params args) sBody) :
    call fuel args (some name) codeOverride s₀ = .ok (sCall, rets) →
    FunctionCallSummary AFunc f args vars s₀ (sCall.multifill vars rets) := by
  intro hcall
  cases fuel with
  | zero =>
      simp [call] at hcall
  | succ bodyFuel =>
      simp [call, ResolvedFunction, ResolvedFunctionInCode] at hcall hresolve
      rcases hresolve with ⟨hordinary, hresolve⟩
      split at hcall
      · contradiction
      next account haccount =>
        cases codeOverride with
        | none =>
            rcases hresolve with ⟨account', haccount', hlookup⟩
            rw [haccount] at haccount'
            cases haccount'
            simp [hlookup] at hcall
            split at hcall
            · contradiction
            next sBody hbody =>
              cases hcall
              exact ⟨bodyFuel, sBody, habs hbody, rfl⟩
        | some code =>
            simp [hresolve] at hcall
            split at hcall
            · contradiction
            next sBody hbody =>
              cases hcall
              exact ⟨bodyFuel, sBody, habs hbody, rfl⟩

theorem functionCallSummary_of_execCall_ok
    {AFunc : Nat → State → State → Prop} {f : FunctionDefinition}
    {name : YulFunctionName} {args : List Ast.Literal} {vars : List Identifier}
    {fuel : Nat} {codeOverride : Option YulContract} {s₀ s₉ : State}
    (hresolve : ResolvedFunction codeOverride s₀ name f)
    (habs :
      ∀ {bodyFuel : Nat} {sBody : State},
        FunctionBodyExact f codeOverride bodyFuel (👌 s₀.initcall f.params args) sBody →
          AFunc bodyFuel (👌 s₀.initcall f.params args) sBody) :
    execCall fuel name vars codeOverride (.ok (s₀, args)) = .ok s₉ →
    FunctionCallSummary AFunc f args vars s₀ s₉ := by
  intro hexec
  have hobject :
      execObjectDataBuiltin? name vars (.ok (s₀, args)) = none :=
    execObjectDataBuiltin?_none_of_ordinary hresolve.1
  cases fuel with
  | zero =>
      simp [execCall] at hexec
  | succ callFuel =>
      simp [execCall, multifill'] at hexec
      generalize hcall : call callFuel args (some name) codeOverride s₀ = callResult at hexec
      cases callResult with
      | error e =>
          simp at hexec
      | ok result =>
          cases result with
          | mk sCall rets =>
              simp at hexec
              cases hexec
              exact functionCallSummary_of_call hresolve habs hcall

theorem functionCallSummary_of_exec_let_call
    {AFunc : Nat → State → State → Prop} {f : FunctionDefinition}
    {name : YulFunctionName} {argExprs : List Expr} {args : List Ast.Literal}
    {vars : List Identifier} {fuel : Nat} {codeOverride : Option YulContract}
    {s₀ sCall s₉ : State}
    (hresolve : ResolvedFunction codeOverride sCall name f)
    (habs :
      ∀ {bodyFuel : Nat} {sBody : State},
        FunctionBodyExact f codeOverride bodyFuel (👌 sCall.initcall f.params args) sBody →
          AFunc bodyFuel (👌 sCall.initcall f.params args) sBody)
    (heval : reverse' (evalArgs fuel argExprs.reverse codeOverride s₀) = .ok (sCall, args)) :
    exec (.succ fuel) (.Let vars (some (.Call (Sum.inr name) argExprs))) codeOverride s₀ = .ok s₉ →
    FunctionCallSummary AFunc f args vars sCall s₉ := by
  intro hexec
  have hobject :
      execObjectDataBuiltin? name vars (.ok (sCall, args)) = none :=
    execObjectDataBuiltin?_none_of_ordinary hresolve.1
  simp [exec, heval] at hexec
  rw [hobject] at hexec
  exact functionCallSummary_of_execCall_ok hresolve habs hexec

theorem functionCallSummary_of_exec_block_prefix_let_call
    {AFunc : Nat → State → State → Prop} {f : FunctionDefinition}
    {name : YulFunctionName} {pref : Stmt} {argExprs : List Expr}
    {args : List Ast.Literal} {vars : List Identifier}
    {argFuel : Nat} {codeOverride : Option YulContract} {s₀ sPrefix sCall s₉ : State}
    (hprefix : exec (.succ (.succ argFuel)) pref codeOverride s₀ = .ok sPrefix)
    (hprefixOk : State.isOk sPrefix)
    (hresolve : ResolvedFunction codeOverride sCall name f)
    (habs :
      ∀ {bodyFuel : Nat} {sBody : State},
        FunctionBodyExact f codeOverride bodyFuel (👌 sCall.initcall f.params args) sBody →
          AFunc bodyFuel (👌 sCall.initcall f.params args) sBody)
    (heval : reverse' (evalArgs argFuel argExprs.reverse codeOverride sPrefix) = .ok (sCall, args)) :
    exec (.succ (.succ (.succ argFuel))) (.Block [pref, .Let vars (some (.Call (Sum.inr name) argExprs))]) codeOverride s₀ = .ok s₉ →
    FunctionCallSummary AFunc f args vars sCall s₉ := by
  intro hexec
  cases sPrefix with
  | Ok sharedState store =>
      simp [exec, hprefix, heval] at hexec
      have hobject :
          execObjectDataBuiltin? name vars (.ok (sCall, args)) = none :=
        execObjectDataBuiltin?_none_of_ordinary hresolve.1
      rw [hobject] at hexec
      generalize hcall : execCall argFuel name vars codeOverride (.ok (sCall, args)) = result at hexec
      cases result with
      | error e =>
          simp at hexec
      | ok sResult =>
          cases sResult <;> simp at hexec <;> cases hexec <;>
            exact functionCallSummary_of_execCall_ok hresolve habs hcall
  | OutOfFuel =>
      cases hprefixOk
  | Checkpoint jump =>
      cases hprefixOk

theorem function_exec_implies_bodyExact
    {f : FunctionDefinition} {codeOverride : Option YulContract}
    {fuel : Nat} {s₀ s₉ : State} :
    exec fuel (.Block f.body) codeOverride s₀ = .ok s₉ →
    FunctionBodyExact f codeOverride fuel s₀ s₉ := by
  intro h
  exact h

theorem functionBodyExact_implies_fuelSpec
    {f : FunctionDefinition} {codeOverride : Option YulContract}
    {fuel : Nat} {s₀ s₉ : State} {AFunc : Nat → State → State → Prop}
    (habs :
      ∀ {fuel : Nat} {s₀ s₉ : State},
        FunctionBodyExact f codeOverride fuel s₀ s₉ → AFunc fuel s₀ s₉) :
    FunctionBodyExact f codeOverride fuel s₀ s₉ →
    FuelSpec AFunc fuel s₀ s₉ := by
  intro h
  exact habs h

theorem function_exec_implies_fuelSpec
    {f : FunctionDefinition} {codeOverride : Option YulContract}
    {fuel : Nat} {s₀ s₉ : State} {AFunc : Nat → State → State → Prop}
    (habs :
      ∀ {fuel : Nat} {s₀ s₉ : State},
        FunctionBodyExact f codeOverride fuel s₀ s₉ → AFunc fuel s₀ s₉) :
    exec fuel (.Block f.body) codeOverride s₀ = .ok s₉ →
    FuelSpec AFunc fuel s₀ s₉ := by
  intro h
  exact functionBodyExact_implies_fuelSpec habs (function_exec_implies_bodyExact h)

theorem for_exec_implies_loopExact
    {cond : Expr} {post body : List Stmt} {codeOverride : Option YulContract}
    {fuel : Nat} {s₀ s₉ : State} :
    exec fuel (.For cond post body) codeOverride s₀ = .ok s₉ →
    LoopExact cond post body codeOverride fuel s₀ s₉ := by
  intro h
  exact h

theorem loopExact_implies_spec
    {cond : Expr} {post body : List Stmt} {codeOverride : Option YulContract}
    {fuel : Nat} {s₀ s₉ : State} {AFor : State → State → Prop}
    (habs :
      ∀ {fuel : Nat} {s₀ s₉ : State},
        LoopExact cond post body codeOverride fuel s₀ s₉ → AFor s₀ s₉) :
    LoopExact cond post body codeOverride fuel s₀ s₉ →
    Spec AFor s₀ s₉ := by
  intro h
  exact habs h

theorem for_exec_implies_spec
    {cond : Expr} {post body : List Stmt} {codeOverride : Option YulContract}
    {fuel : Nat} {s₀ s₉ : State} {AFor : State → State → Prop}
    (habs :
      ∀ {fuel : Nat} {s₀ s₉ : State},
        LoopExact cond post body codeOverride fuel s₀ s₉ → AFor s₀ s₉) :
    exec fuel (.For cond post body) codeOverride s₀ = .ok s₉ →
    Spec AFor s₀ s₉ := by
  intro h
  exact loopExact_implies_spec habs (for_exec_implies_loopExact h)

theorem loopExact_implies_fuelSpec
    {cond : Expr} {post body : List Stmt} {codeOverride : Option YulContract}
    {fuel : Nat} {s₀ s₉ : State} {AFor : Nat → State → State → Prop}
    (habs :
      ∀ {fuel : Nat} {s₀ s₉ : State},
        LoopExact cond post body codeOverride fuel s₀ s₉ → AFor fuel s₀ s₉) :
    LoopExact cond post body codeOverride fuel s₀ s₉ →
    FuelSpec AFor fuel s₀ s₉ := by
  intro h
  exact habs h

theorem for_exec_implies_fuelSpec
    {cond : Expr} {post body : List Stmt} {codeOverride : Option YulContract}
    {fuel : Nat} {s₀ s₉ : State} {AFor : Nat → State → State → Prop}
    (habs :
      ∀ {fuel : Nat} {s₀ s₉ : State},
        LoopExact cond post body codeOverride fuel s₀ s₉ → AFor fuel s₀ s₉) :
    exec fuel (.For cond post body) codeOverride s₀ = .ok s₉ →
    FuelSpec AFor fuel s₀ s₉ := by
  intro h
  exact loopExact_implies_fuelSpec habs (for_exec_implies_loopExact h)

end ReasoningPrinciple
end Yul
end EvmYul
