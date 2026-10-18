module

public import EvmYul.UInt256
public import Mathlib.Data.String.Defs

public section

/-!
# Primitive-operation signatures

Identifiers and the `n`-ary word-function types `Primop.Nullary` … `Primop.Quaternary` (with the
`!nary[T ^ n]` notation that builds them).
-/

namespace EvmYul

@[expose] def Identifier := String
@[expose] instance : ToString Identifier := inferInstanceAs (ToString String)
@[expose] instance : Inhabited Identifier := inferInstanceAs (Inhabited String)
@[expose] instance : DecidableEq Identifier := inferInstanceAs (DecidableEq String)
@[expose] instance : Repr Identifier := inferInstanceAs (Repr String)

namespace NaryNotation

scoped syntax "!nary[" ident "^" num "]" : term

open Lean in
scoped macro_rules
  | `(!nary[ $idn:ident ^ $nat:num ]) =>
    let rec go (n : ℕ) : MacroM Term :=
      match n with
        | 0     => `($idn)
        | n + 1 => do `($idn → $(←go n))
    go nat.getNat

end NaryNotation

namespace Primop

section

open NaryNotation

@[expose] def Nullary    := !nary[UInt256 ^ 0]
@[expose] def Unary      := !nary[UInt256 ^ 1]
@[expose] def Binary     := !nary[UInt256 ^ 2]
@[expose] def Ternary    := !nary[UInt256 ^ 3]
@[expose] def Quaternary := !nary[UInt256 ^ 4]

end

end Primop

end EvmYul
