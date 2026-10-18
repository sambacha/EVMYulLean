module

public section

/-!
# The shape of a Vyper bytecode fixture (V1, `docs/VYPER_V1_PLAN.md`)

A *cell* is one compilation: a pinned Vyper compiler, one contract of the corpus
(`tools/vyper/corpus/*.vy`) and one code generator. The cells themselves are generated into
`EvmYul/Vyper/Fixtures.lean` by `tools/vyper/gen_vyper_fixtures.py`; this module only fixes their
type, so that the generated file holds data and nothing else.
-/

namespace EvmYul.Vyper

@[expose] section

/-- Vyper's two code generators. `legacy` is the default in 0.4.x; `venom` is the SSA pipeline
behind `--experimental-codegen`. -/
inductive Codegen where
  /-- The default s-expression IR code generator. -/
  | legacy
  /-- The Venom (SSA) code generator, `--experimental-codegen`. -/
  | venom
  deriving DecidableEq, Repr

end

@[expose] instance : ToString Codegen where
  toString | .legacy => "legacy" | .venom => "venom"

/-- One call replayed on py-evm (an EVM implementation independent of this project) when the
fixtures were generated, with what py-evm observed. -/
structure OraclePoint where
  /-- ABI signature of the called function. -/
  sig : String
  /-- `uint256` arguments. -/
  args : List Nat
  /-- Initial value of the contract's first storage variable. -/
  x0 : Nat
  /-- Call value (wei). -/
  value : Nat
  /-- Did the call succeed (no revert, no exceptional halt)? -/
  success : Bool
  /-- Execution gas consumed (message call, no intrinsic gas, no refund). -/
  gasUsed : Nat
  /-- The first storage variable after the call. -/
  slotAfter : Nat
  /-- Return data, lower-case hex. -/
  outputHex : String

/-- One compiled contract, as recorded by the generator. -/
structure Cell where
  /-- Compiler version, e.g. `"0.4.3"`. -/
  vyper : String
  /-- Compiler commit reported by `vyper --version`. -/
  commit : String
  /-- sha256 of the compiler wheel that was verified before installation. -/
  wheelSha256 : String
  /-- Code generator used. -/
  codegen : Codegen
  /-- Corpus contract (file stem in `tools/vyper/corpus`). -/
  contract : String
  /-- sha256 of the contract source that was compiled. -/
  sourceSha256 : String
  /-- The `bound=` of the contract's single bounded loop, if it has one. -/
  loopBound : Option Nat
  /-- ABI signature ↦ 4-byte selector (`-f method_identifiers`). -/
  selectors : List (String × Nat)
  /-- Function name ↦ Vyper's static gas estimate (`--show-gas-estimates`). -/
  gasEstimates : List (String × Nat)
  /-- Storage variable ↦ slot (`-f layout`). -/
  storageSlots : List (String × Nat)
  /-- Runtime bytecode, lower-case hex without `0x`. -/
  runtimeHex : String
  /-- Calls replayed on py-evm with their observed results (the independent-EVM oracle). -/
  oracle : List OraclePoint

/-- A short name for messages: `contract@version/codegen`. -/
def Cell.name (c : Cell) : String := s!"{c.contract}@{c.vyper}/{c.codegen}"

end EvmYul.Vyper
