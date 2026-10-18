module

public import EvmYul.Wheels
public import EvmYul.PerformIO

/-!
# Precompile `POINT_EVALUATION` (address 0x0a)

The KZG point-evaluation check of EIP-4844, computed by the Python helper through
`totallySafePerformIO`.
-/

public section

def blobPointEval (data : String) : String :=
  totallySafePerformIO ∘ IO.Process.run <|
    pythonCommandOfInput data
  where pythonCommandOfInput (data : String) : IO.Process.SpawnArgs := {
    cmd := "python3",
    args := #["python/EllipticCurvesPy/point_evaluation.py", data]
  }

def PointEval (data : ByteArray) : Except String ByteArray :=
  match blobPointEval (toHex data) with
    | "error" => .error "PointEval failed"
    | s => ByteArray.ofBlob s
