module

public import EvmYul.FFI.Primitives
public import Std.Data.TreeMap

public import EvmYul.Wheels

public import EvmYul.Maps.StorageMap

public import EvmYul.State.Account
public import EvmYul.State.AccountOps

/-!
# Account maps

`AddrMap α` (and hence `AccountMap`, the world state σ) is a `Std.TreeMap` ordered by `compare`.

`Std.TreeMap` is maintained in Lean core and is what Batteries recommends instead of
`Batteries.RBMap`. Its lemma library (`Std.TreeMap.getElem?_insert`, `Std.TreeMap.contains_erase`,
...) only assumes a lawful comparator (`Std.TransOrd`, `Std.LawfulEqOrd`); those instances for
`UInt256` and `AccountAddress` are proved next to the types. Iteration (`foldl`, `toList`,
`toArray`) visits keys in increasing order, exactly as the former `Batteries.RBMap` did, so the trie
roots computed from these maps do not change. See `EvmYul.Maps.TreeMapTests`.
-/

public section

namespace EvmYul

section RemoveLater

abbrev AddrMap (α : Type) [Inhabited α] := Std.TreeMap AccountAddress α compare
abbrev AccountMap (τ : OperationType) := AddrMap (Account τ)
abbrev PersistentAccountMap (τ : OperationType) := AddrMap (PersistentAccountState τ)
def AccountMap.toPersistentAccountMap (τ : OperationType) (a : AccountMap τ) : PersistentAccountMap τ :=
  a.map (λ _ acc ↦ acc.toPersistentAccountState)

@[expose] def AccountMap.increaseBalance (τ : OperationType) (σ : AccountMap τ) (addr : AccountAddress) (amount : UInt256)
  : AccountMap τ
:=
  match σ.get? addr with
    | none => σ.insert addr {(default : Account τ) with balance := amount}
    | some acc => σ.insert addr {acc with balance := acc.balance + amount}

/--
  Returns `none` in the case of an overflow below zero.
-/
@[expose] def AccountMap.decreaseBalance (τ : OperationType) (σ : AccountMap τ) (addr : AccountAddress) (amount : UInt256)
  : Option (AccountMap τ)
:=
  match σ.get? addr with
    | none => .none
    | some acc =>
      if acc.balance < amount then .none else .some (σ.insert addr {acc with balance := acc.balance - amount})

/--
  Returns `none` in the case of an overflow below zero.
-/
@[expose] def AccountMap.transferBalance (τ : OperationType) (σ : AccountMap τ) (from_addr to_addr : AccountAddress) (amount : UInt256)
  : Option (AccountMap τ)
:=
  match (σ.decreaseBalance τ from_addr amount) with
    | .none => .none
    | .some σ' => σ'.increaseBalance τ to_addr amount

@[expose] def toExecute (τ : OperationType) (σ : AccountMap τ) (t : AccountAddress) : ToExecute τ :=
  if /- t is a precompiled account -/ t ∈ π then
    ToExecute.Precompiled t
  else Id.run do
    match τ with
      | .EVM =>
        -- We use the code directly without an indirection a'la `codeMap[t]`.
        let .some tDirect := σ.get? t | ToExecute.Code default
        ToExecute.Code tDirect.code
      | .Yul =>
        let .some tDirect := σ.get? t | ToExecute.Code default
        ToExecute.Code tDirect.code

@[expose] def L_S (σ : PersistentAccountMap .EVM) : Array (ByteArray × ByteArray) :=
  σ.foldl
    (λ arr (addr : AccountAddress) acc ↦
      arr.push (p addr acc)
    )
    .empty
 where
  p (addr : AccountAddress) (acc : PersistentAccountState .EVM) : ByteArray × ByteArray :=
    (ffi.KEC addr.toByteArray, rlp acc)
  rlp (acc : PersistentAccountState .EVM) :=
    Option.get! <|
      RLP <|
        .𝕃
          [ .𝔹 (BE acc.nonce.toNat)
          , .𝔹 (BE acc.balance.toNat)
          , .𝔹 <| (computeTrieRoot acc.storage).getD .empty
          , .𝔹 acc.codeHash.toByteArray
          ]

@[expose] def stateTrieRoot (σ : PersistentAccountMap .EVM) : Option ByteArray :=
  let a := Array.map toBlobPair (L_S σ)
  (ByteArray.ofBlob (blobComputeTrieRoot a)).toOption
 where
  toBlobPair entry : String × String :=
    let b₁ := EvmYul.toHex entry.1
    let b₂ := EvmYul.toHex entry.2
    (b₁, b₂)

end RemoveLater

end EvmYul
