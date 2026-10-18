module

public import EvmYul.Wheels.Hex

public section

/-!
# Recursive-length prefix (RLP)

The RLP tree `𝕋`, its encoding (`RLP`, Yellow Paper Appendix B) and the decoder.
-/

@[expose] section

inductive 𝕋 where
  | 𝔹 : ByteArray → 𝕋
  | 𝕃 : (List 𝕋) → 𝕋
  deriving Repr, BEq

end


def lengthRLP (rlp : ByteArray) : Option ℕ :=
  let len := rlp.size
  if len = 0 then
    none
  else
    let rlp₀ := rlp.get! 0
    if rlp₀ ≤ 0x7f then
      some 1
    else
      let strLen := rlp₀.toNat - 0x80
      if rlp₀ ≤ 0xb7 ∧ len > strLen then
        some (1 + strLen)
      else
        let lenOfStrLen := rlp₀.toNat - 0xb7
        if rlp₀ ≤ 0xbf ∧ len > lenOfStrLen + strLen then
          let strLen :=
            EvmYul.fromByteArrayBigEndian
              (rlp.readWithoutPadding 1 lenOfStrLen)
          some (1 + lenOfStrLen + strLen)
        else
          let listLen := rlp₀.toNat - 0xc0
          if rlp₀ ≤ 0xf7 ∧ len > listLen then do
            some (1 + listLen)
          else
            let lenOfListLen := rlp₀.toNat - 0xf7
            let listLen :=
              EvmYul.fromByteArrayBigEndian
                (rlp.readWithoutPadding 1 lenOfListLen)
            if len > lenOfListLen + listLen then do
              some (1 + lenOfListLen + listLen)
            else
              none

partial def separateListRLP (rlp : ByteArray) : Option (List ByteArray) := do
  if rlp.isEmpty then pure []
  else
    let headLen ← lengthRLP rlp
    let head := rlp.readWithoutPadding 0 headLen
    let tail ← separateListRLP (rlp.readWithoutPadding headLen rlp.size)
    pure <| head :: tail

def oneStepRLP (rlp : ByteArray) : Option (Sum ByteArray (List ByteArray)) :=
  let len := rlp.size
  if len = 0 then
    none
  else
    let rlp₀ := rlp.get! 0
    if rlp₀ ≤ 0x7f then
      let data := .inl ⟨#[rlp₀]⟩
      some data
    else
      let strLen := rlp₀.toNat - 0x80
      if rlp₀ ≤ 0xb7 ∧ len > strLen then
        let data := .inl (rlp.readWithoutPadding 1 strLen)
        some data
      else
        let lenOfStrLen := rlp₀.toNat - 0xb7
        if rlp₀ ≤ 0xbf ∧ len > lenOfStrLen + strLen then
          let strLen :=
            EvmYul.fromByteArrayBigEndian
              (rlp.readWithoutPadding 1 lenOfStrLen)
          let data := .inl (rlp.readWithoutPadding (1 + lenOfStrLen) strLen)
          some data
        else
          let listLen := rlp₀.toNat - 0xc0
          if rlp₀ ≤ 0xf7 ∧ len > listLen then do
            let list ← separateListRLP (rlp.readWithoutPadding 1 listLen)
            some <| .inr list
          else
            let lenOfListLen := rlp₀.toNat - 0xf7
            let listLen :=
              EvmYul.fromByteArrayBigEndian
                (rlp.readWithoutPadding 1 lenOfListLen)
            if len > lenOfListLen + listLen then do
              let list ← separateListRLP (rlp.readWithoutPadding (1 + lenOfListLen) listLen)
              some <| .inr list
            else
              none

partial def deserializeRLP (rlp : ByteArray) : Option 𝕋 := do
  match ← oneStepRLP rlp with
    | .inl byteArray =>
      some (.𝔹 byteArray)
    | .inr list =>
      let l ← list.mapM deserializeRLP
      some (.𝕃 l)

def R_b (x : ByteArray) : Option ByteArray :=
  if x.size = 1 ∧ x.get! 0 < 128 then some x
  else
    if x.size < 56 then some <| [⟨128 + x.size⟩].toByteArray ++ x
    else
      if x.size < 2^64 then
        let be := BE x.size
        some <| [⟨183 + be.size⟩].toByteArray ++ be ++ x
      else none

mutual

@[expose] def s (l : List 𝕋) : Option ByteArray :=
  match l with
    | [] => some .empty
    | t :: ts =>
      match RLP t, s ts with
        | none     , _         => none
        | _        , none      => none
        | some rlpₗ, some rlpᵣ => rlpₗ ++ rlpᵣ

def R_l (l : List 𝕋) : Option ByteArray :=
  match s l with
    | none => none
    | some s_x =>
      if s_x.size < 56 then
        some <| [⟨192 + s_x.size⟩].toByteArray ++ s_x
      else
        if s_x.size < 2^64 then
          let be := BE s_x.size
          some <| [⟨247 + be.size⟩].toByteArray ++ be ++ s_x
        else none

def RLP (t : 𝕋) : Option ByteArray :=
  match t with
    | .𝔹 ba => R_b ba
    | .𝕃 l => R_l l

end
