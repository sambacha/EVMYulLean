module

public import EvmYul.UInt256
public import EvmYul.Operations
public import EvmYul.Wheels

/-!
# Yul abstract syntax

Identifiers, literals, expressions, statements, function definitions and contracts of Yul
(https://docs.soliditylang.org/en/v0.8.9/yul.html).
-/

public section

namespace EvmYul

namespace Yul

namespace Ast

open EvmYul UInt256

abbrev Literal := UInt256
-- def Identifier := String

@[expose] instance : ToString Identifier := inferInstanceAs (ToString String)

@[expose] instance : Inhabited Identifier := ⟨""⟩
@[expose] instance : DecidableEq Identifier := String.decEq

abbrev PrimOp := Operation .Yul

def stringOfPrimOp : PrimOp → String := toString ∘ repr

@[expose] instance : ToString PrimOp := ⟨stringOfPrimOp⟩

-- https://docs.soliditylang.org/en/latest/yul.html#informal-description-of-yul

abbrev YulFunctionName := String

@[expose] section

mutual
  inductive FunctionDefinition where
    | Def : List Identifier → List Identifier → List Stmt → FunctionDefinition
  deriving BEq, Inhabited

  inductive Expr where
    | Call : (PrimOp ⊕ YulFunctionName) → List Expr → Expr
    | Var : Identifier → Expr
    | Lit : Literal → Expr

  -- | The loop constructor 'Stmt.For' has no initialiser because of
  -- https://docs.soliditylang.org/en/latest/internals/optimizer.html#forloopinitrewriter
  inductive Stmt where
    | Block : List Stmt → Stmt
    | Let : List Identifier → Option Expr → Stmt
    | ExprStmtCall : Expr → Stmt
    | Switch : Expr → List (Literal × List Stmt) → List Stmt → Stmt
    | For : Expr → List Stmt → List Stmt → Stmt
    | If : Expr → List Stmt → Stmt
    | Continue : Stmt
    | Break : Stmt
    | Leave : Stmt
    deriving BEq, Inhabited, Repr
end

end

@[expose] section

structure YulContract where
  dispatcher : Yul.Ast.Stmt
  functions : Finmap (fun (_ : YulFunctionName) ↦ Yul.Ast.FunctionDefinition)
  deriving Inhabited

end

@[expose] instance : Repr YulContract where
  reprPrec _ _ := "YulContract" -- TODO: implement an actual `reprPrec` for YulContract

@[expose] instance : BEq YulContract where
  beq a b := 
    a.dispatcher == b.dispatcher
    && (a.functions.keys == b.functions.keys &&
        a.functions.all (λ k _ => a.functions.lookup k == b.functions.lookup k))

abbrev contractCode (τ : OperationType) :=
  match τ with
    | OperationType.EVM => ByteArray
    | OperationType.Yul => YulContract

@[expose] instance {τ} : BEq (contractCode τ) where
  beq a b := match τ with
              | .EVM => a == b
              | .Yul => a == b

@[expose] instance {τ} : Inhabited (contractCode τ) where
  default := match τ with
                | .EVM => default
                | .Yul => default
              
@[expose] instance {τ} : Repr (contractCode τ) where
  reprPrec a _ := match τ with
                     | .EVM => reprPrec a 0
                     | .Yul => reprPrec a 0


namespace FunctionDefinition

@[expose] def params : FunctionDefinition → List Identifier
  | Def params _ _ => params

@[expose] def rets : FunctionDefinition → List Identifier
  | Def _ rets _ => rets

@[expose] def body : FunctionDefinition → List Stmt
  | Def _ _ body => body

end FunctionDefinition

end Ast

end Yul

end EvmYul
