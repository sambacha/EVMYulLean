module

public import EvmYul.Venom.BlockLowering
public import EvmYul.Vyper.Harness

public section

/-!
# Assembling compiled Venom code, a byte-level reference model, and the run on `Θ`

* `assemble` encodes `Asm` code as EVM bytecode (Cancun opcodes) and appends the shared revert block
  `JUMPDEST; PUSH0; PUSH0; REVERT` that every `assert` jumps to. Every instruction has a fixed size,
  so the block's offset is known before encoding (`asmSize`).
* `assembleS` does the same for stack code with `SWAP` and `POP` (`LoweringCheck.lean`); on code
  without them it emits exactly the bytes of `assemble` (`assembleS_embed`).
* `assembleCfg` lays out a whole stack function (`BlockLowering.lean`): every block starts with
  a `JUMPDEST` at the offset `blockOffsets` gives it (`encodeBlock_length`), jumps are
  `PUSH2 l; JUMP`, a `jumpi` is `PUSH2 t; JUMPI; PUSH2 e; JUMP`.
* `Ref` / `refPrims` is a reference model of the primitive effects, written from the Yellow Paper:
  byte-addressed memory with the quadratic expansion cost, zero-padded big-endian `CALLDATALOAD`,
  a storage map with the Cancun storage gas: the EIP-2929 warm/cold slot set (`G_coldsload` on the
  first access of a slot, `G_warmaccess` after) and the EIP-2200 `SSTORE` cost from the original,
  current and new value (`G_sset`, `G_sreset`, `G_warmaccess`). It is written from the EIP texts,
  not through the interpreter's `Csstore`, so the tests are a second route (D1). Refunds are not
  modelled: they are applied at the end of the transaction, outside the message call `Θ` whose gas
  the tests compare.
* `onTheta` runs assembled code on the project's EVM `Θ` (through `EvmYul.Vyper.execute`).

Nothing here is proved about `Θ`: the claim "the bytecode does on `Θ` what `runAsm` says" is
checked by the build-time differential tests of `ThetaTests.lean`, and the gap is stated in
`docs/VENOM_PLAN.md`.
-/

namespace EvmYul.Venom

open GasConstants

/-! ## Bytecode -/

/-- The 32 big-endian bytes of a word. -/
def bytes32 (n : UInt256) : List UInt8 := Vyper.word n.toNat

/-- Opcode byte of a pure operation. -/
def PureOp.opcode : PureOp → UInt8
  | .add => 0x01 | .mul => 0x02 | .sub => 0x03 | .div => 0x04 | .mod => 0x06
  | .lt => 0x10 | .gt => 0x11 | .eq => 0x14 | .iszero => 0x15
  | .and => 0x16 | .or => 0x17 | .xor => 0x18 | .shl => 0x1b | .shr => 0x1c

/-- Opcode byte of an effect. -/
def Eff.opcode : Eff → UInt8
  | .callvalue => 0x34 | .calldataload => 0x35 | .calldatasize => 0x36
  | .mload => 0x51 | .mstore => 0x52 | .sload => 0x54 | .sstore => 0x55

/-- Opcode byte of a terminator. -/
def Halt.opcode : Halt → UInt8
  | .stop => 0x00 | .ret => 0xf3 | .revert => 0xfd

/-- Encoded size of one instruction. -/
def asmSize : Asm → ℕ
  | .push _ => 33
  | .assertJ => 5
  | _ => 1

/-- Encode one instruction; `r` is the offset of the revert block. -/
def encode (r : ℕ) : Asm → List UInt8
  | .push n => 0x7f :: bytes32 n
  | .dup k => [UInt8.ofNat (0x80 + k - 1)]
  | .op o => [o.opcode]
  | .eff e => [e.opcode]
  | .assertJ => [0x15, 0x61, UInt8.ofNat (r / 256), UInt8.ofNat (r % 256), 0x57]
  | .halt h => [h.opcode]

theorem encode_length (r : ℕ) (a : Asm) : (encode r a).length = asmSize a := by
  cases a <;> simp [encode, asmSize, bytes32, Vyper.word_length]

/-- The shared revert block: `JUMPDEST; PUSH0; PUSH0; REVERT`. -/
def revertBlock : List UInt8 := [0x5b, 0x5f, 0x5f, 0xfd]

/-- Bytecode of compiled code: the code, then the revert block at offset `Σ asmSize`. -/
def assemble (c : List Asm) : ByteArray :=
  let r := (c.map asmSize).sum
  ⟨(c.flatMap (encode r) ++ revertBlock).toArray⟩

/-- The revert block starts exactly where the code ends, so every `assert` jumps onto its
`JUMPDEST`. -/
theorem assemble_revert_offset (c : List Asm) :
    (c.flatMap (encode (c.map asmSize).sum)).length = (c.map asmSize).sum := by
  simp [List.length_flatMap, encode_length]

/-! ## Bytecode of stack code with `SWAP` and `POP` -/

/-- Encoded size of one stack-code instruction. -/
def asmSizeS : SAsm → ℕ
  | .push _ => 33
  | .assertJ => 5
  | _ => 1

/-- Encode one stack-code instruction; `r` is the offset of the revert block. `SWAPk` is
`0x8f + k` (`SWAP1 = 0x90`) and `POP` is `0x50` (Yellow Paper, Appendix H). -/
def encodeS (r : ℕ) : SAsm → List UInt8
  | .push n => 0x7f :: bytes32 n
  | .dup k => [UInt8.ofNat (0x80 + k - 1)]
  | .swap k => [UInt8.ofNat (0x8f + k)]
  | .pop => [0x50]
  | .op o => [o.opcode]
  | .eff e => [e.opcode]
  | .assertJ => [0x15, 0x61, UInt8.ofNat (r / 256), UInt8.ofNat (r % 256), 0x57]
  | .halt h => [h.opcode]

theorem encodeS_length (r : ℕ) (a : SAsm) : (encodeS r a).length = asmSizeS a := by
  cases a <;> simp [encodeS, asmSizeS, bytes32, Vyper.word_length]

/-- Bytecode of stack code: the code, then the revert block at offset `Σ asmSizeS`. -/
def assembleS (c : List SAsm) : ByteArray :=
  let r := (c.map asmSizeS).sum
  ⟨(c.flatMap (encodeS r) ++ revertBlock).toArray⟩

/-- The revert block of `assembleS` starts exactly where the code ends. -/
theorem assembleS_revert_offset (c : List SAsm) :
    (c.flatMap (encodeS (c.map asmSizeS).sum)).length = (c.map asmSizeS).sum := by
  simp [List.length_flatMap, encodeS_length]

theorem asmSizeS_toSAsm (a : Asm) : asmSizeS a.toSAsm = asmSize a := by
  cases a <;> rfl

theorem encodeS_toSAsm (r : ℕ) (a : Asm) : encodeS r a.toSAsm = encode r a := by
  cases a <;> rfl

/-- **The new assembler extends the old one byte for byte**: on code without `SWAP`/`POP` it emits
exactly the bytes of `assemble`, so every `Θ` test of `assemble` is also a test of `assembleS`. -/
theorem assembleS_embed (c : List Asm) : assembleS (c.map Asm.toSAsm) = assemble c := by
  have hs : ((c.map Asm.toSAsm).map asmSizeS).sum = (c.map asmSize).sum := by
    simp [List.map_map, Function.comp_def, asmSizeS_toSAsm]
  simp only [assembleS, assemble, hs, List.flatMap_map, encodeS_toSAsm]

/-! ## Bytecode of whole stack functions -/

/-- Encoded size of a stack-code terminator: `PUSH2 l; JUMP` (4), `PUSH2 t; JUMPI; PUSH2 e; JUMP`
(8), `STOP` (1). -/
def stermSize : STerm → ℕ
  | .jump _ => 4
  | .jumpi _ _ => 8
  | .halts => 1

/-- Encoded size of a block: its `JUMPDEST`, its code and its terminator. -/
def sblockSize (b : SBlock) : ℕ := 1 + (b.code.map asmSizeS).sum + stermSize b.term

/-- The offset of every block when the blocks are laid out in order from offset `o`. -/
def blockOffsets : ℕ → List SBlock → List (ℕ × ℕ)
  | _, [] => []
  | o, b :: bs => (b.label, o) :: blockOffsets (o + sblockSize b) bs

/-- `PUSH2 n`. -/
def push2 (n : ℕ) : List UInt8 := [0x61, UInt8.ofNat (n / 256), UInt8.ofNat (n % 256)]

/-- Encode a terminator with the block offsets `offs` (`none` for an unknown label). -/
def encodeTerm (offs : List (ℕ × ℕ)) : STerm → Option (List UInt8)
  | .jump l => (offs.lookup l).map fun o => push2 o ++ [0x56]
  | .jumpi t e => do
    let a ← offs.lookup t
    let b ← offs.lookup e
    pure (push2 a ++ [0x57] ++ push2 b ++ [0x56])
  | .halts => some [0x00]

theorem encodeTerm_length {offs : List (ℕ × ℕ)} {t : STerm} {bs : List UInt8}
    (h : encodeTerm offs t = some bs) : bs.length = stermSize t := by
  cases t with
  | jump l =>
    simp only [encodeTerm, Option.map_eq_some_iff] at h
    obtain ⟨o, _, rfl⟩ := h; simp [push2, stermSize]
  | jumpi t e =>
    simp only [encodeTerm, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨a, _, b, _, rfl⟩ := h; simp [push2, stermSize]
  | halts => simp only [encodeTerm, Option.some.injEq] at h; subst h; rfl

/-- The bytes of one block: `JUMPDEST`, the code (asserts jump to the revert block at `r`), the
terminator. -/
def encodeBlock (offs : List (ℕ × ℕ)) (r : ℕ) (b : SBlock) : Option (List UInt8) :=
  (encodeTerm offs b.term).map fun t => 0x5b :: b.code.flatMap (encodeS r) ++ t

/-- **Each block occupies exactly `sblockSize` bytes**, so the offsets of `blockOffsets` are where
the blocks' `JUMPDEST`s really are. -/
theorem encodeBlock_length {offs : List (ℕ × ℕ)} {r : ℕ} {b : SBlock} {bs : List UInt8}
    (h : encodeBlock offs r b = some bs) : bs.length = sblockSize b := by
  simp only [encodeBlock, Option.map_eq_some_iff] at h
  obtain ⟨t, ht, rfl⟩ := h
  have hc : (b.code.flatMap (encodeS r)).length = (b.code.map asmSizeS).sum := by
    simp [List.length_flatMap, encodeS_length]
  simp [sblockSize, hc, encodeTerm_length ht]
  omega

/-- Bytecode of a stack function: the blocks in order (the first must be the entry, where
execution starts), then the shared revert block. `none` if the first block is not the entry, a
jump target is unknown, or an offset does not fit `PUSH2`. -/
def assembleCfg (sf : SFunc) : Option ByteArray :=
  match sf.blocks with
  | [] => none
  | b₀ :: _ =>
    if b₀.label ≠ sf.entry then none else
    let offs := blockOffsets 0 sf.blocks
    let r := (sf.blocks.map sblockSize).sum
    if 65536 ≤ r then none else
    (sf.blocks.mapM (encodeBlock offs r)).map fun parts => ⟨(parts.flatten ++ revertBlock).toArray⟩

/-! ## Reference model of the primitive effects -/

/-- Machine state of the reference model. -/
structure Ref where
  /-- Storage (all slots `0` initially unless set). -/
  storage : ℕ → ℕ
  /-- Storage at the start of the transaction (EIP-2200's *original* value). -/
  original : ℕ → ℕ
  /-- Slots accessed so far (EIP-2929's accessed storage keys of the contract; initially none). -/
  warm : List ℕ
  /-- Byte-addressed memory. -/
  mem : ℕ → UInt8
  /-- Active memory size in 32-byte words (`μᵢ`). -/
  words : ℕ
  /-- Call data. -/
  calldata : List UInt8
  /-- Call value. -/
  callvalue : ℕ

/-- Initial reference state. -/
def Ref.init (kvs : List (ℕ × ℕ)) (data : List UInt8) (value : ℕ) : Ref :=
  { storage := fun k => (kvs.lookup k).getD 0, original := fun k => (kvs.lookup k).getD 0,
    warm := [], mem := fun _ => 0, words := 0,
    calldata := data, callvalue := value }

/-- Memory cost of `a` active words (YP (326)): `G_memory · a + a² / 512`. -/
def memCost (a : ℕ) : ℕ := Gmemory * a + a * a / 512

/-- Active words after touching `[ofs, ofs + len)` (`len > 0`). -/
def wordsAfter (w ofs len : ℕ) : ℕ := if len = 0 then w else max w ((ofs + len + 31) / 32)

/-- Big-endian value of 32 bytes read by `f` from `ofs`. -/
def read32 (f : ℕ → UInt8) (ofs : ℕ) : ℕ :=
  (List.range 32).foldl (fun acc i => acc * 256 + (f (ofs + i)).toNat) 0

/-- Byte `j` of the call data, `0` beyond its end. -/
def Ref.cdByte (s : Ref) (j : ℕ) : UInt8 := s.calldata.getD j 0

/-- Memory after writing the 32 big-endian bytes of `v` at `ofs`. -/
def write32 (f : ℕ → UInt8) (ofs : ℕ) (v : UInt256) : ℕ → UInt8 :=
  fun j => if ofs ≤ j ∧ j < ofs + 32 then (bytes32 v).getD (j - ofs) 0 else f j

/-- The reference effects. -/
def refApply (e : Eff) (s : Ref) (vs : List UInt256) : UInt256 × Ref :=
  let a := (vs.getD 0 default).toNat
  let b := vs.getD 1 default
  match e with
  | .callvalue => (word s.callvalue, s)
  | .calldatasize => (word s.calldata.length, s)
  | .calldataload => (word (read32 s.cdByte a), s)
  | .sload => (word (s.storage a), { s with warm := a :: s.warm })
  | .sstore => (word 0, { s with storage := fun k => if k = a then b.toNat else s.storage k,
                                 warm := a :: s.warm })
  | .mload => (word (read32 s.mem a), { s with words := wordsAfter s.words a 32 })
  | .mstore => (word 0, { s with mem := write32 s.mem a b, words := wordsAfter s.words a 32 })

/-- EIP-2929 surcharge of touching slot `a`: `G_coldsload` on the first access, else `0`. -/
def Ref.coldCost (s : Ref) (a : ℕ) : ℕ := if a ∈ s.warm then 0 else Gcoldsload

/-- EIP-2200 (with EIP-2929's prices) `SSTORE` cost of writing `new` to slot `a`, without the cold
surcharge: a no-op write or a write to an already dirty slot costs `G_warmaccess`; the first change
of a clean slot costs `G_sset` from zero and `G_sreset` otherwise. -/
def Ref.sstoreCost (s : Ref) (a new : ℕ) : ℕ :=
  if s.storage a = new then Gwarmaccess
  else if s.original a = s.storage a then (if s.original a = 0 then Gsset else Gsreset)
  else Gwarmaccess

/-- The reference gas of an effect. -/
def refCost (e : Eff) (s : Ref) (vs : List UInt256) : ℕ :=
  let a := (vs.getD 0 default).toNat
  match e with
  | .callvalue | .calldatasize => Gbase
  | .calldataload => Gverylow
  | .sload => s.coldCost a + (if a ∈ s.warm then Gwarmaccess else 0)
  | .sstore => s.coldCost a + s.sstoreCost a (vs.getD 1 default).toNat
  | .mload | .mstore => Gverylow + (memCost (wordsAfter s.words a 32) - memCost s.words)

/-- The reference gas of a terminator: memory expansion of `return`/`revert`. -/
def refHaltCost (h : Halt) (s : Ref) (vs : List UInt256) : ℕ :=
  match h with
  | .stop => 0
  | _ => memCost (wordsAfter s.words (vs.getD 0 default).toNat (vs.getD 1 default).toNat) -
         memCost s.words

/-- The reference model as `Prims`. -/
def refPrims : Prims Ref := ⟨refApply, refCost, refHaltCost⟩

/-- The output bytes of a result: memory `[ofs, ofs + len)` for `return`/`revert`. -/
def Final.output (f : Final Ref) : List UInt8 :=
  match f.data with
  | [o, l] => (List.range l.toNat).map fun i => f.state.mem (o.toNat + i)
  | _ => []

/-- Does the program neither read nor write storage? (Reported by the coverage line of the
tests, so that the share of programs exercising the storage gas is visible.) -/
def storageFree (p : Program) : Bool :=
  p.all fun
    | .eff _ .sload _ | .eff _ .sstore _ => false
    | _ => true

/-! ## Running on `Θ` -/

/-- Run bytecode on `Θ` with initial storage `kvs`, call data and call value. -/
def onTheta (code : ByteArray) (kvs : List (ℕ × ℕ)) (data : List UInt8) (value : ℕ) :
    Option Vyper.Run :=
  Vyper.execute code kvs ⟨data.toArray⟩ value

/-- The `Θ` frame outcome that a Venom outcome corresponds to. -/
def Outcome.frame : Outcome → EVM.FrameOutcome
  | .stopped | .returned => .success
  | .reverted => .revert

end EvmYul.Venom
