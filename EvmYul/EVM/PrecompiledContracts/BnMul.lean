module

public import EvmYul.Wheels
public import EvmYul.PerformIO

/-!
# Precompile `BN_MUL` (address 0x07)

Scalar multiplication on the alt_bn128 curve (EIP-196), computed by the Python helper through
`totallySafePerformIO`.
-/

public section

def blobBN_MUL (x₀ y₀ n : String) : String :=
  totallySafePerformIO ∘ IO.Process.run <|
    pythonCommandOfInput x₀ y₀ n
  where pythonCommandOfInput (x₀ y₀ n : String) : IO.Process.SpawnArgs := {
    cmd := "python3",
    args := #["python/EllipticCurvesPy/bn_mul.py", x₀, y₀, n]
  }

def BN_MUL (x₀ y₀ n : ByteArray) : Except String ByteArray :=
  match blobBN_MUL (toHex x₀) (toHex y₀) (toHex n) with
    | "error" => .error "BN_MUL failed"
    | s => ByteArray.ofBlob s
