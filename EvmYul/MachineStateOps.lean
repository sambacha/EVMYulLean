module


public import EvmYul.FFI.Primitives
public import EvmYul.MachineState

public import EvmYul.SpongeHash.Keccak256

/-!
# Operations on the machine state

Memory reads and writes, memory expansion (`M`), return data, and the gas and storage helpers on
`MachineState`.
-/

public section

namespace EvmYul

@[expose] def writeBytes
  (source : ByteArray)
  (sourceAddr : ℕ)
  (self : MachineState)
  (destAddr len : ℕ)
 : MachineState :=
  { self with
      memory := source.write sourceAddr self.memory destAddr len
  }

namespace MachineState


-- Appendix H, (320)
@[expose] def M (s f l : ℕ) : ℕ :=
  match l with
  | 0 => s
  | l =>
    -- ⌈ (f + l) ÷ 32 ⌉
    -- The addition is not subject to s²⁵⁶ division (at least that's what MSTORE suggests)
    max s ((f + l + 31) / 32)

@[expose] def writeWord (self : MachineState) (addr val : UInt256) : MachineState :=
  let numOctets := 32
  let source : ByteArray := val.toByteArray
  writeBytes source 0 self addr.toNat numOctets

@[expose] def lookupMemory (self : MachineState) (addr : UInt256) : UInt256 :=
  if addr.toNat ≥ self.memory.size ∨ addr ≥ self.activeWords * ⟨32⟩ then ⟨0⟩ else
    let bytes := self.memory.readWithPadding addr.toNat 32
    let val := fromByteArrayBigEndian bytes
    .ofNat val

@[expose] def msize (self : MachineState) : UInt256 :=
  self.activeWords * ⟨32⟩

@[expose] def mload (self : MachineState) (spos : UInt256) : UInt256 × MachineState :=
  let val := self.lookupMemory spos
  let self :=
    { self with
      activeWords := .ofNat (MachineState.M self.activeWords.toNat spos.toNat 32)
    }
  (val, self)

@[expose] def mstore (self : MachineState) (spos sval : UInt256) : MachineState :=
  let self := self.writeWord spos sval
  { self with
    activeWords := .ofNat (MachineState.M self.activeWords.toNat spos.toNat 32)
  }

@[expose] def mstore8 (self : MachineState) (spos sval : UInt256) : MachineState :=
  let self := writeBytes ⟨#[UInt8.ofNat sval.toNat]⟩ 0 self spos.toNat 1
  { self with
    activeWords := .ofNat (MachineState.M self.activeWords.toNat spos.toNat 1)
  }

@[expose] def mcopy (self : MachineState) (writeStart readStart s : UInt256) : MachineState :=
  let self := writeBytes self.memory readStart.toNat self writeStart.toNat s.toNat
  { self with
    activeWords :=
      .ofNat (MachineState.M self.activeWords.toNat (max writeStart.toNat readStart.toNat) s.toNat)
  }

@[expose] def gas (self : MachineState) : UInt256 :=
  self.gasAvailable

section ReturnData

@[expose] def setReturnData (self : MachineState) (r : ByteArray) : MachineState :=
  { self with returnData := r }

@[expose] def setHReturn (self : MachineState) (r : ByteArray) : MachineState :=
  { self with H_return := r }

@[expose] def returndatasize (self : MachineState) : UInt256 :=
  .ofNat self.returnData.size

@[expose] def returndataat (self : MachineState) (pos : UInt256) : UInt8 :=
  self.returnData.data.getD pos.toNat 0

@[expose] def returndatacopy (self : MachineState) (mstart rstart size : UInt256) : MachineState :=
  let self := writeBytes self.returnData rstart.toNat self mstart.toNat size.toNat
  { self with
    activeWords :=
      .ofNat (MachineState.M self.activeWords.toNat mstart.toNat size.toNat)
  }


@[expose] def evmReturn (self : MachineState) (mstart s : UInt256) : MachineState :=
  { self with
    H_return := self.memory.readWithPadding mstart.toNat s.toNat
    activeWords :=
      .ofNat <| MachineState.M self.activeWords.toNat mstart.toNat s.toNat
  }

@[expose] def evmRevert (self : MachineState) (mstart s : UInt256) : MachineState :=
  let self := self.evmReturn mstart s
  { self with
    activeWords :=
      .ofNat <| MachineState.M self.activeWords.toNat mstart.toNat s.toNat
  }

end ReturnData

@[expose] def keccak256 (self : MachineState) (mstart s : UInt256) : UInt256 × MachineState :=
  let bytes := self.memory.readWithPadding mstart.toNat s.toNat
  let kec := ffi.KEC bytes
  let newMachineState :=
    { self with activeWords := .ofNat (M self.activeWords.toNat mstart.toNat s.toNat) }
  (.ofNat (fromByteArrayBigEndian kec), newMachineState)

section Gas

@[expose] def mkNewWithGas (gas : ℕ) : MachineState :=
  let init : MachineState := default
  { init with gasAvailable := .ofNat gas }

end Gas

section Storage

end Storage

end MachineState

end EvmYul
