module

public import EvmYul.PerformIO
public import EvmYul.Wheels

/-!
# Precompile `RIPEMD-160` (address 0x03)

The RIPEMD-160 hash, computed by the Python helper through `totallySafePerformIO`.
-/

public section

def blobRIP160 (d : String) : String :=
  totallySafePerformIO ∘ IO.Process.run <|
    pythonCommandOfInput d
  where pythonCommandOfInput (d : String) : IO.Process.SpawnArgs := {
    cmd := "python3",
    args := #["python/EllipticCurvesPy/rip160.py", d]
  }

def RIP160 (d : ByteArray) : Except String ByteArray :=
  ByteArray.ofBlob <| blobRIP160 (toHex d)
