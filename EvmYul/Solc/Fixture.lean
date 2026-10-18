module

public section

/-!
# The shape of a solc Yul-lowering fixture (`docs/SOLC_VYPER_PLAN.md`, Steps 2–3)

A *cell* is one compilation: a pinned solc binary, one program of the corpus
(`tools/solc/corpus/*.yul`, compiled with `--strict-assembly`), the optimizer off or on, and a code
generator. The cells are generated into `EvmYul/Solc/Fixtures.lean` by
`tools/solc/gen_solc_fixtures.py`; this module only fixes their type, so that the generated file
holds data and nothing else.
-/

namespace EvmYul.Solc

@[expose] section

/-- solc's code generators for Yul. `legacy` is the default; `ssaCfg` is the experimental
`--via-ssa-cfg` generator of the latest compiler. -/
inductive Codegen where
  /-- The default Yul → EVM code transform. -/
  | legacy
  /-- The experimental SSA-CFG code generator (`--experimental --via-ssa-cfg`). -/
  | ssaCfg
  deriving DecidableEq, Repr

end

@[expose] instance : ToString Codegen where
  toString | .legacy => "legacy" | .ssaCfg => "ssa-cfg"

/-- One run replayed on py-evm (an EVM implementation independent of this project) when the
fixtures were generated, with what py-evm observed. Storage starts empty. -/
structure OraclePoint where
  /-- The calldata, as 32-byte words. -/
  args : List Nat
  /-- Did the run succeed (no exceptional halt)? -/
  success : Bool
  /-- Execution gas consumed (message call, no intrinsic gas, no refund). -/
  gasUsed : Nat
  /-- Storage slots `0` and `1` after the run (`oracleSlots`). -/
  slots : List Nat

/-- One compiled program, as recorded by the generator. -/
structure Cell where
  /-- Compiler version, e.g. `"0.8.37"`. -/
  solc : String
  /-- Compiler commit reported by `solc --version`. -/
  commit : String
  /-- sha256 of the compiler binary that was verified before use. -/
  binarySha256 : String
  /-- `--evm-version` used (the newest target of this compiler that the project's EVM runs). -/
  evmVersion : String
  /-- Was `--optimize` given? -/
  optimize : Bool
  /-- Code generator used. -/
  codegen : Codegen
  /-- Corpus program (file stem in `tools/solc/corpus`). -/
  program : String
  /-- sha256 of the program source that was compiled. -/
  sourceSha256 : String
  /-- The bytecode, lower-case hex without `0x`. -/
  runtimeHex : String
  /-- Runs replayed on py-evm with their observed results. -/
  oracle : List OraclePoint

/-- A short name for messages: `program@version/opt/codegen`. -/
def Cell.name (c : Cell) : String :=
  s!"{c.program}@{c.solc}/{if c.optimize then "opt" else "noopt"}/{c.codegen}"

end EvmYul.Solc
