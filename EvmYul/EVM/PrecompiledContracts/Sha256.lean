module

public import EvmYul.PerformIO
public import EvmYul.Wheels

/-!
# Precompile `SHA2-256` (address 0x02)

The SHA-256 hash, computed by the Python helper through `totallySafePerformIO`.
-/

public section

def blobSHA256 (d : String) : String :=
  dbg_trace s!"python/EllipticCurvesPy/sha256.py"
  totallySafePerformIO ∘ IO.Process.run <|
    pythonCommandOfInput d
  where pythonCommandOfInput (d : String) : IO.Process.SpawnArgs := {
    cmd := "python3",
    args := #["python/EllipticCurvesPy/sha256.py", d]
  }

def SHA256 (d : ByteArray) : Except String ByteArray :=
  ByteArray.ofBlob <| blobSHA256 (toHex d)
