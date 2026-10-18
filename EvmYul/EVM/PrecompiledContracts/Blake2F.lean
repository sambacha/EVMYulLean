module

public import EvmYul.Wheels
public import EvmYul.PerformIO

/-!
# Precompile `BLAKE2_F` (address 0x09)

The `BLAKE2` compression function of EIP-152, computed by the Python helper through
`totallySafePerformIO`.
-/

public section

def blobBLAKE2_F (data : String) : String :=
  totallySafePerformIO ∘ IO.Process.run <|
    pythonCommandOfInput data
  where pythonCommandOfInput (data : String) : IO.Process.SpawnArgs := {
    cmd := "python3",
    args := #["python/EllipticCurvesPy/blake2_f.py", data]
  }

def BLAKE2_F (data : ByteArray) : Except String ByteArray :=
  match blobBLAKE2_F (toHex data) with
    | "error" => .error "BLAKE2_F failed"
    | s => ByteArray.ofBlob s
