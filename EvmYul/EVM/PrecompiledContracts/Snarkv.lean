module

public import EvmYul.Wheels
public import EvmYul.PerformIO

/-!
# Precompile `SNARKV` (address 0x08)

The alt_bn128 pairing check of EIP-197, computed by the Python helper through
`totallySafePerformIO`.
-/

public section

def blobSNARKV (data : String) : String :=
  totallySafePerformIO ∘ IO.Process.run <|
    pythonCommandOfInput data
  where pythonCommandOfInput (data : String) : IO.Process.SpawnArgs := {
    cmd := "python3",
    args := #["python/EllipticCurvesPy/snarkv.py", data]
  }

def SNARKV (data : ByteArray) : Except String ByteArray :=
  match blobSNARKV (toHex data) with
    | "error" => .error "SNARKV failed"
    | s => ByteArray.ofBlob s
