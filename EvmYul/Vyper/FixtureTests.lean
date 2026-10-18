module

public import EvmYul.FFI.Primitives
public meta import EvmYul.FFI.Primitives
public import EvmYul.Vyper.Harness
public meta import EvmYul.Vyper.Harness
public import EvmYul.Vyper.Fixtures
public meta import EvmYul.Vyper.Fixtures
public import EvmYul.Vyper.Reference
public meta import EvmYul.Vyper.Reference
public import EvmYul.Testing.EvmFixtures
public meta import EvmYul.Testing.EvmFixtures
@[expose] public meta section

/-!
# Vyper V1: compiled contracts executed on this project's EVM (`docs/VYPER_V1_PLAN.md`)

Every cell of `EvmYul/Vyper/Fixtures.lean` is runtime bytecode emitted by a pinned Vyper compiler
(0.4.0 and the latest stable 0.4.3; legacy and Venom code generators; `--evm-version cancun`). This
file runs that bytecode on `Θ` and checks what a user of the contract relies on. It is built by
`lake build EvmYulGasTests`; any failed check fails the build.

* **§0 Matrix and provenance (TESTING.md 0.3, D2).** The cells are exactly *pinned compilers ×
  corpus contracts × code generators*, read from `tools/vyper/vyper-matrix.lock` and
  `tools/vyper/corpus/` at build time; every wheel hash matches the lock; every source hash matches
  the corpus file (so editing a contract without regenerating fails the build, offline); the hex
  round-trips; every selector equals `keccak256(signature)[0:4]`, recomputed here.
* **§1 Business assertions, exhaustive (F1).** Storage, return data and revert behaviour agree with
  the reference models of `Reference.lean` on every trip count `0 … bound + 2`, from storage values
  that include the overflow boundary, and on a boundary grid for the straight-line contract. The
  ABI guards hold: a call with value, an unknown selector or truncated calldata reverts and leaves
  storage unchanged.
* **§2 K16, Vyper's gas estimate (F3).** For every successful call in the sweep, execution gas is
  at most `--show-gas-estimates`; by `estimateSound_of_sweep` the passing sweep *is* the statement
  `EstimateSound`. The estimate does **not** bound the gas of a whole transaction: the intrinsic
  `21000 + calldata` is outside it, and a concrete witness (`set(1)` on `store.vy`) is kept as an
  expected refutation (G1).
* **§3 Gas structure and golden values (D1, D3).** Gas is non-decreasing in the trip count, and
  constant per iteration once storage is warm. The **rules** are relations derived from EIP-2929 /
  EIP-2200 that every cell must satisfy whatever its numbers (`storageGasRules`): the first storage
  write of `loop_if` costs one warm iteration plus the cold-read and fresh-set surcharges, storing a
  non-zero total in `sum_squares` costs one iteration plus the fresh-set surcharge, and `store`'s
  writes differ by `G_sset − G_warmaccess` / `G_sreset − G_warmaccess`; they are checked on `Θ` and
  on the py-evm records, with a canary. The per-cell numbers are a **regression snapshot** only, and
  each row must equal the same measurement on the independent py-evm records (provenance), so no
  pinned number comes from `Θ` alone. Every run satisfies `Θ_gasLeft_le` and never errors.
* **§4 Legacy vs Venom (D3).** Both code generators produce the same observable behaviour on every
  input; gas has no fixed order between them (a witness where Venom costs more is pinned).
* **§5 Property tests (A2, counted).** Random 256-bit storage, arguments and trip counts (Plausible,
  fixed seed, `CountedTesting` counts), each with a canary that must be refuted.
* **§6 Mutation tests (E1).** A changed loop bound, an unreachable selector, swapped bytecode and an
  estimate one gas below the measured maximum are each caught.
* **§7 Independent EVM (D1).** Every call recorded on py-evm (an EVM implementation independent of
  this project, pinned in `tools/vyper/oracle.lock`) when the fixtures were generated agrees with
  `Θ` exactly: success, execution gas, storage and return data. That is a second route for the
  project's gas semantics on real compiler output. Canary: another cell's bytecode does not match
  the record.
-/

namespace EvmYul.Vyper.FixtureTests

open EvmYul.Vyper Plausible EvmYul.Testing.EvmFixtures GasConstants

/-! ## Helpers -/

/-- Fail with all collected messages (at most ten shown). -/
def failIf (what : String) (errs : List String) : IO Unit :=
  unless errs.isEmpty do
    throw <| IO.userError s!"{what}: {errs.length} failure(s):\n{String.intercalate "\n" (errs.take 10)}"

/-- The cells of one corpus contract. -/
def cellsOf (contract : String) : List Cell := fixtures.filter (·.contract == contract)

/-- Call `sig` of cell `c`, but on the bytecode `code` (used by the mutation tests). -/
def callOn (code : ByteArray) (c : Cell) (sig : String) (args : List ℕ) (kvs : List (ℕ × ℕ))
    (value : ℕ := 0) : Option Run := do
  let sel ← c.selector? sig
  execute code kvs (calldata sel args) value

/-- Compare one run with the expected effect: `some v` = success with storage slot `slot` equal to
`v` (and, if `ret`, return data equal to the ABI word of `v`); `none` = revert with storage still
`x0`. -/
def checkRun (what : String) (r? : Option Run) (expect : Option ℕ) (slot x0 : ℕ) (ret : Bool) :
    List String :=
  match r? with
  | none => [s!"{what}: Θ returned an error"]
  | some r =>
    match expect with
    | some v =>
      (if r.ok then [] else [s!"{what}: expected success, got {repr r.outcome}"]) ++
      (if r.slot slot == v then [] else [s!"{what}: storage {r.slot slot}, expected {v}"]) ++
      (if ret then (if r.output.toList == word v then [] else
          [s!"{what}: returned 0x{hexOf r.output}, expected the word of {v}"])
        else (if r.output.size == 0 then [] else [s!"{what}: unexpected return data"]))
    | none =>
      (if r.outcome == .revert then [] else [s!"{what}: expected revert, got {repr r.outcome}"]) ++
      (if r.slot slot == x0 then [] else [s!"{what}: storage changed by a reverted call"])

/-- The boundary grid for 256-bit arguments and storage (TESTING.md B1). -/
def boundary : List ℕ := [0, 1, 2, 255, 256, 2 ^ 128, 2 ^ 255, 2 ^ 256 - 2, 2 ^ 256 - 1]

/-- Initial values of `x` for `loop_if`: empty, ordinary, close enough to `2^256` that the loop
overflows from `n = 16` on (`Σ_{4 ≤ i < 16} i = 114 > 100`), and the maximum. -/
def loopX0s : List ℕ := [0, 1000, 2 ^ 256 - 100, 2 ^ 256 - 1]

/-- Initial values of `total` for `sum_squares` (it is overwritten, never read). -/
def sumT0s : List ℕ := [0, 12345]

/-! ## §1 Business laws, parametric in the bytecode (so §6 can run them on mutants) -/

/-- `loop_if.vy` on `code`, against `loopIfRef`: every trip count `n ≤ bound + 2` (descending, so a
lowered bound fails on the first calls) from `x = 0` and from `x = 2^256 − 100`; the other
`loopX0s` at the trip counts where behaviour changes; the getter `x()` for every `x0`. With `stop`,
return at the first failure (used by the mutation tests). -/
def loopIfLaw (code : ByteArray) (c : Cell) (stop : Bool := false) : List String := Id.run do
  let some bound := c.loopBound | return [s!"{c.name}: no loop bound recorded"]
  let some slot := c.slot? "x" | return [s!"{c.name}: no slot for x"]
  let full := (List.range (bound + 3)).reverse
  let spots := [0, 4, 5, 16, bound, bound + 1]
  let mut errs := []
  for x0 in loopX0s do
    let ns := if x0 == 0 || x0 == 2 ^ 256 - 100 then full else spots
    for n in ns do
      errs := errs ++ checkRun s!"{c.name} f({n}) from x = {x0}"
        (callOn code c "f(uint256)" [n] [(slot, x0)]) (loopIfRef bound x0 n) slot x0 false
      if stop && !errs.isEmpty then return errs
    errs := errs ++ checkRun s!"{c.name} x() with x = {x0}" (callOn code c "x()" [] [(slot, x0)])
      (some x0) slot x0 true
  return errs

/-- Number of calls made by `loopIfLaw` (for the printed counts). -/
def loopIfLawCalls (bound : ℕ) : ℕ := 2 * (bound + 3) + 2 * 6 + loopX0s.length

/-- `sum_squares.vy` on `code`: every `t0 ∈ sumT0s`, every `n ≤ bound + 2`, against `sumSqRef`
(stored **and** returned); plus the getter `total()`. -/
def sumSquaresLaw (code : ByteArray) (c : Cell) (stop : Bool := false) : List String := Id.run do
  let some bound := c.loopBound | return [s!"{c.name}: no loop bound recorded"]
  let some slot := c.slot? "total" | return [s!"{c.name}: no slot for total"]
  let mut errs := []
  for t0 in sumT0s do
    for n in List.range (bound + 3) do
      errs := errs ++ checkRun s!"{c.name} run({n}) from total = {t0}"
        (callOn code c "run(uint256)" [n] [(slot, t0)]) (sumSqRef bound n) slot t0 true
      if stop && !errs.isEmpty then return errs
    errs := errs ++ checkRun s!"{c.name} total() = {t0}"
      (callOn code c "total()" [] [(slot, t0)]) (some t0) slot t0 true
  return errs

/-- `store.vy` on `code`: `set(v)` and `bump(d)` on the boundary grid, against `v` and `bumpRef`. -/
def storeLaw (code : ByteArray) (c : Cell) (stop : Bool := false) : List String := Id.run do
  let some slot := c.slot? "x" | return [s!"{c.name}: no slot for x"]
  let mut errs := []
  for x0 in boundary do
    for v in boundary do
      errs := errs ++ checkRun s!"{c.name} set({v}) from x = {x0}"
        (callOn code c "set(uint256)" [v] [(slot, x0)]) (some v) slot x0 false
      errs := errs ++ checkRun s!"{c.name} bump({v}) from x = {x0}"
        (callOn code c "bump(uint256)" [v] [(slot, x0)]) (bumpRef x0 v) slot x0 false
      if stop && !errs.isEmpty then return errs
    errs := errs ++ checkRun s!"{c.name} x() = {x0}" (callOn code c "x()" [] [(slot, x0)])
      (some x0) slot x0 true
  return errs

/-- The business law of a cell's contract (`stop`: return at the first failure). -/
def lawOf (c : Cell) (stop : Bool := false) : ByteArray → List String :=
  match c.contract with
  | "loop_if" => (loopIfLaw · c stop)
  | "sum_squares" => (sumSquaresLaw · c stop)
  | "store" => (storeLaw · c stop)
  | other => fun _ => [s!"{c.name}: no business law for corpus contract {other}"]

/-- The ABI guards of every external function: a call with value (all functions are
non-payable), an unknown selector, or calldata one byte short must revert without touching storage. -/
def guardLaw (c : Cell) (code : ByteArray) : List String := Id.run do
  let some (_, slot) := c.storageSlots.head? | return [s!"{c.name}: no storage variable"]
  let kvs := [(slot, 5)]
  let mut errs := []
  for (sig, sel) in c.selectors do
    let args := if (sig.splitOn "(uint256)").length > 1 then [7] else []
    errs := errs ++ checkRun s!"{c.name} {sig} with value 1"
      (execute code kvs (calldata sel args) 1) none slot 5 false
    let bad := if c.selectors.any (·.2 == sel ^^^ 1) then sel ^^^ 2 else sel ^^^ 1
    errs := errs ++ checkRun s!"{c.name} unknown selector next to {sig}"
      (execute code kvs (calldata bad args)) none slot 5 false
    unless args.isEmpty do
      let d := calldata sel args
      errs := errs ++ checkRun s!"{c.name} {sig} with calldata one byte short"
        (execute code kvs (d.extract 0 (d.size - 1))) none slot 5 false
  return errs

/-! ## §2 K16 -/

/-- The external functions with an estimate, their signature, and the arguments of the sweep. -/
def k16Plan (c : Cell) : List (String × String × List ℕ × List (List (ℕ × ℕ))) :=
  match c.contract, c.loopBound with
  | "loop_if", some b => [("f(uint256)", "f", List.range (b + 1), [[], [(0, 1)]])]
  | "sum_squares", some b => [("run(uint256)", "run", List.range (b + 1), [[], [(0, 1)]])]
  | "store", _ => [("set(uint256)", "set", boundary, [[], [(0, 9)]]),
                   ("bump(uint256)", "bump", boundary, [[], [(0, 9)]])]
  | _, _ => []

/-- Maximum execution gas of successful calls over a sweep, with the storage and argument where it
is reached. -/
def maxGas (c : Cell) (sig : String) (args : List ℕ) (kvss : List (List (ℕ × ℕ))) :
    ℕ × List (ℕ × ℕ) × ℕ :=
  kvss.foldl (fun acc kvs => args.foldl (fun acc n =>
    match c.call? sig [n] kvs with
    | some r => if r.ok && acc.1 < r.gasUsed then (r.gasUsed, kvs, n) else acc
    | none => acc) acc) (0, [], 0)

/-- The K16 gate on one storage: `allUpTo bound (gasWithin …)` for a loop contract (by
`estimateSound_of_sweep` this is `EstimateSound … bound`), the boundary grid otherwise. -/
def k16Gate (c : Cell) (sig fn : String) (args : List ℕ) (kvs : List (ℕ × ℕ)) : Bool :=
  match c.loopBound with
  | some b => allUpTo b (gasWithin c sig fn kvs)
  | none => args.all (gasWithin c sig fn kvs)

/-! ## §3 Golden values: a regression snapshot whose every number has an independent source

The table below is a **regression snapshot** (TESTING.md D3): it catches a change of the compiled
code or of `Θ` between two versions, and is not where any rule comes from. Its numbers are not
"what `Θ` printed once": every row is required to equal the same measurement taken from the py-evm
records of the cell (`measureWith (oracleGas c)`), an EVM implementation independent of this
project. The rules the gas must obey are checked separately, as relations derived from EIP-2929 /
EIP-2200 that hold for every cell whatever its numbers (`storageGasRules`). -/

/-- Golden gas per cell `(version, codegen, contract)`:
* `loop_if`: `[f(0), f(bound), per-iteration gas while i ≤ 3 (after the first iteration, which also
  pays the loop entry), per-iteration gas once x is warm (i ≥ 5)]`;
* `sum_squares`: `[run(0), run(bound), per-iteration gas from n = 2 on]`;
* `store`: `[set(0) on 0, set(1) on 0, set(1) on 9, bump(1) on 9]`.

All measured points are calls that py-evm recorded (value 0), so each row has an independent
counterpart. -/
def golden : List ((String × Codegen × String) × List ℕ) :=
  [(("0.4.0", .legacy, "loop_if"), [163, 36818, 64, 315]),
   (("0.4.0", .venom, "loop_if"), [202, 37514, 81, 328]),
   (("0.4.3", .legacy, "loop_if"), [163, 36818, 64, 315]),
   (("0.4.3", .venom, "loop_if"), [169, 36079, 64, 299]),
   (("0.4.0", .legacy, "sum_squares"), [2394, 26683, 219]),
   (("0.4.0", .venom, "sum_squares"), [2433, 26799, 223]),
   (("0.4.3", .legacy, "sum_squares"), [2394, 26683, 219]),
   (("0.4.3", .venom, "sum_squares"), [2403, 25103, 140]),
   (("0.4.0", .legacy, "store"), [2317, 22217, 5117, 5160]),
   (("0.4.0", .venom, "store"), [2326, 22226, 5126, 5165]),
   (("0.4.3", .legacy, "store"), [2317, 22217, 5117, 5160]),
   (("0.4.3", .venom, "store"), [2317, 22217, 5117, 5152])]

/-- Gas of a successful call on `code` (`none` if it fails or reverts). -/
def okGas (code : ByteArray) (c : Cell) (sig : String) (args : List ℕ) (kvs : List (ℕ × ℕ)) :
    Option ℕ := do
  let r ← callOn code c sig args kvs
  if r.ok then pure r.gasUsed else none

/-- A source of execution gas for a successful call `sig(args)` from storage value `x0` (value 0):
`Θ` on some bytecode, or the py-evm record. -/
abbrev GasSource := String → List ℕ → ℕ → Option ℕ

/-- The golden measurement of cell `c`, taken from the gas source `g`. -/
def measureWith (g : GasSource) (c : Cell) : Option (List ℕ) := do
  match c.contract with
  | "loop_if" =>
    let b ← c.loopBound
    let f := fun n => g "f(uint256)" [n] 0
    pure [← f 0, ← f b, (← f 2) - (← f 1), (← f 7) - (← f 6)]
  | "sum_squares" =>
    let b ← c.loopBound
    let f := fun n => g "run(uint256)" [n] 0
    pure [← f 0, ← f b, (← f 3) - (← f 2)]
  | "store" =>
    pure [← g "set(uint256)" [0] 0, ← g "set(uint256)" [1] 0, ← g "set(uint256)" [1] 9,
          ← g "bump(uint256)" [1] 9]
  | _ => none

/-- `Θ` on `code` as a gas source. -/
def thetaGas (code : ByteArray) (c : Cell) : GasSource := fun sig args x0 =>
  okGas code c sig args (if x0 = 0 then [] else [(0, x0)])

/-- The py-evm record of cell `c` as a gas source (`none` if the call was not recorded or
failed). -/
def oracleGas (c : Cell) : GasSource := fun sig args x0 => do
  let p ← c.oracle.find? fun p => p.sig == sig && p.args == args && p.x0 == x0 && p.value == 0
  if p.success then pure p.gasUsed else none

/-- The measured counterpart of `golden` for cell `c`, run on `code`. -/
def measure (code : ByteArray) (c : Cell) : Option (List ℕ) := measureWith (thetaGas code c) c

/-- **Storage-gas rules** (EIP-2929, EIP-2200), as relations every cell must satisfy whatever its
numbers; the gas source `g` is `Θ` or py-evm. Each relation compares two calls whose executions
differ **only** in their storage accesses, so the difference is fixed by the EIPs:

* `loop_if` from `x = 0`: iteration `i = 4` is the first with `i > 3`. It reads `x` cold (EIP-2929:
  `G_coldsload` instead of `G_warmaccess`) and changes the clean zero slot (EIP-2200: `G_sset`
  instead of the dirty-slot price `G_warmaccess`); every later iteration reads warm and writes
  dirty. So `f(5) − f(4) = (f(7) − f(6)) + (G_coldsload − G_warmaccess) + (G_sset − G_warmaccess)`.
* `sum_squares` from `total = 0`: `run(1)` ends by storing `0` (a no-op write), `run(2)` by storing
  `1` (a fresh set), and has one more iteration. So
  `run(2) − run(1) = (run(3) − run(2)) + (G_sset − G_warmaccess)`.
* `store`: `set(1)` and `set(0)` on a zero slot differ by `G_sset − G_warmaccess`; `set(1)` on 9 and
  `set(0)` on 0 by `G_sreset − G_warmaccess`; a no-op write costs the same at any value (`0` and
  `2^256 − 1`).

Every call used is one py-evm recorded, so the same relations are checked on both EVMs.

Returns the violated relations (empty when all hold). -/
def storageGasRules (g : GasSource) (c : Cell) : List String :=
  let bad := fun (what : String) (ok : Option Bool) =>
    if ok == some true then [] else [s!"{c.name}: {what}"]
  match c.contract with
  | "loop_if" =>
    let f := fun n => g "f(uint256)" [n] 0
    bad "first write = warm iteration + cold-read and fresh-set surcharges" (do
      pure ((← f 5) - (← f 4) ==
        ((← f 7) - (← f 6)) + (Gcoldsload - Gwarmaccess) + (Gsset - Gwarmaccess)))
  | "sum_squares" =>
    let f := fun n => g "run(uint256)" [n] 0
    bad "storing a non-zero total = one iteration + fresh-set surcharge" (do
      pure ((← f 2) - (← f 1) == ((← f 3) - (← f 2)) + (Gsset - Gwarmaccess)))
  | "store" =>
    let set := fun v x0 => g "set(uint256)" [v] x0
    bad "fresh set − no-op write = G_sset − G_warmaccess" (do
        pure ((← set 1 0) - (← set 0 0) == Gsset - Gwarmaccess)) ++
      bad "reset − no-op write = G_sreset − G_warmaccess" (do
        pure ((← set 1 9) - (← set 0 0) == Gsreset - Gwarmaccess)) ++
      bad "a no-op write costs the same at any value" (do
        pure ((← set (2 ^ 256 - 1) (2 ^ 256 - 1)) == (← set 0 0)))
  | _ => []

/-- Gas is non-decreasing in the trip count, and the increment `gas(n + 1) − gas(n)` is constant
for `n` in each given range `[lo, hi)`. For `loop_if` the ranges are `[1, 4)` (iterations `i ≤ 3`,
no storage access; `n = 0 → 1` differs because it also enters the loop) and `[5, bound)` (warm
`SLOAD` + dirty `SSTORE`); `n = 4 → 5` is the first, cold, write. For `sum_squares` the range is
`[2, bound)`: from `n = 2` on the final `SSTORE` always writes a non-zero total. -/
def gasShapeLaw (c : Cell) : List String := Id.run do
  let (sig, ranges) := match c.contract with
    | "loop_if" => ("f(uint256)", [(1, 4), (5, c.loopBound.getD 0)])
    | "sum_squares" => ("run(uint256)", [(2, c.loopBound.getD 0)])
    | _ => ("", [])
  if sig.isEmpty then return []
  let some code := c.code? | return [s!"{c.name}: bad hex"]
  let some b := c.loopBound | return [s!"{c.name}: no bound"]
  let gs := (List.range (b + 1)).map fun n => okGas code c sig [n] []
  let mut errs := []
  for n in List.range b do
    match gs[n]?.join, gs[n + 1]?.join with
    | some a, some a' =>
      unless a ≤ a' do errs := errs ++ [s!"{c.name}: gas drops from n = {n} ({a}) to {n + 1} ({a'})"]
    | _, _ => errs := errs ++ [s!"{c.name}: n = {n} or {n + 1} did not succeed"]
  for (lo, hi) in ranges do
    let d := fun n => match gs[n]?.join, gs[n + 1]?.join with
      | some a, some a' => some (a' - a)
      | _, _ => none
    for n in (List.range hi).filter (lo ≤ ·) do
      unless d n == d lo do
        errs := errs ++ [s!"{c.name}: increment at n = {n} is {d n}, at n = {lo} it is {d lo}"]
  return errs

/-! ## §5 Properties (stated over all cells of a contract) -/

/-- `loop_if` agrees with `loopIfRef` from storage `x0`, trip count `n mod (bound + 3)`. -/
def loopIfAgrees (ref : ℕ → ℕ → ℕ → Option ℕ) (x0 : UInt256) (n : ℕ) : Bool :=
  (cellsOf "loop_if").all fun c =>
    match c.code?, c.loopBound with
    | some code, some b =>
      let k := n % (b + 3)
      (checkRun "" (callOn code c "f(uint256)" [k] [(0, x0.toNat)]) (ref b x0.toNat k) 0 x0.toNat
        false).isEmpty
    | _, _ => false

/-- `sum_squares` agrees with `sumSqRef` from storage `t0`, trip count `n mod (bound + 3)`. -/
def sumSquaresAgrees (t0 : UInt256) (n : ℕ) : Bool :=
  (cellsOf "sum_squares").all fun c =>
    match c.code?, c.loopBound with
    | some code, some b =>
      let k := n % (b + 3)
      (checkRun "" (callOn code c "run(uint256)" [k] [(0, t0.toNat)]) (sumSqRef b k) 0 t0.toNat
        true).isEmpty
    | _, _ => false

/-- `store.set` then the getter: storage and `x()` both report `v`, from storage `x0`. -/
def setAgrees (store : ℕ → ℕ) (x0 v : UInt256) : Bool :=
  (cellsOf "store").all fun c =>
    match c.code? with
    | some code =>
      match callOn code c "set(uint256)" [v.toNat] [(0, x0.toNat)] with
      | some r =>
        r.ok && r.slot 0 == store v.toNat &&
          (checkRun "" (callOn code c "x()" [] [(0, r.slot 0)]) (some (store v.toNat)) 0
            (r.slot 0) true).isEmpty
      | none => false
    | none => false

/-- `store.bump` agrees with a reference for `bump`. -/
def bumpAgrees (ref : ℕ → ℕ → Option ℕ) (x0 d : UInt256) : Bool :=
  (cellsOf "store").all fun c =>
    match c.code? with
    | some code =>
      (checkRun "" (callOn code c "bump(uint256)" [d.toNat] [(0, x0.toNat)]) (ref x0.toNat d.toNat)
        0 x0.toNat false).isEmpty
    | none => false

/-- A plausible implementation bug: the `if i > 3` guard forgotten (`x += i` for every `i`). -/
def loopNoGuardRef (bound x n : ℕ) : Option ℕ :=
  if n ≤ bound ∧ x + n * (n - 1) / 2 < wordSize then some (x + n * (n - 1) / 2) else none

/-! ## §6 Mutation helpers -/

/-- Replace the first occurrence of `pat` in `s` (`none` if absent). -/
def replaceFirst (s pat rep : String) : Option String :=
  match s.splitOn pat with
  | a :: rest@(_ :: _) => some (a ++ rep ++ pat.intercalate rest)
  | _ => none

/-- Two hex digits of a byte. -/
def hex2 (n : ℕ) : String := hexOf ⟨#[n.toUInt8]⟩

/-! ## §7 Independent EVM -/

/-- Replay one py-evm point on `Θ` with bytecode `code`; `none` if every observable agrees
(success, execution gas, storage after the call, return data), otherwise a description. -/
def oracleDiff (code : ByteArray) (c : Cell) (p : OraclePoint) : Option String := do
  let slot := (c.storageSlots.head?.map (·.2)).getD 0
  let what := s!"{c.name} {p.sig} {p.args} from {p.x0} value {p.value}"
  match callOn code c p.sig p.args [(slot, p.x0)] p.value with
  | none => some s!"{what}: Θ error"
  | some r =>
    if r.ok == p.success && r.gasUsed == p.gasUsed && r.slot slot == p.slotAfter &&
        hexOf r.output == p.outputHex then none
    else some s!"{what}: Θ (ok {r.ok}, gas {r.gasUsed}, slot {r.slot slot}, out {hexOf r.output}) \
      vs py-evm (ok {p.success}, gas {p.gasUsed}, slot {p.slotAfter}, out {p.outputHex})"

/-! ## The suite -/

/-- Parse `tools/vyper/vyper-matrix.lock`: `(version, wheel sha256)` per non-comment line. -/
def readLock : IO (List (String × String)) := do
  let t ← IO.FS.readFile ("tools" / "vyper" / "vyper-matrix.lock")
  return (t.splitOn "\n").filterMap fun l =>
    match (l.splitOn " ").filter (· ≠ "") with
    | v :: _ :: sha :: _ => if v.startsWith "#" then none else some (v, sha)
    | _ => none

/-- Corpus contracts (file stems) and their sha256, read from `tools/vyper/corpus`. -/
def readCorpus : IO (List (String × String)) := do
  let mut out := []
  for e in ← ("tools" / "vyper" / "corpus" : System.FilePath).readDir do
    if e.path.extension == some "vy" then
      let bytes ← IO.FS.readBinFile e.path
      let sha ← IO.ofExcept (ffi.SHA256 bytes)
      out := (e.path.fileStem.getD "", hexOf sha) :: out
  return out

/-- All checks; throws on the first failing section. -/
def runAll : IO Unit := do
  -- §0 Matrix and provenance (0.3, D2)
  let lock ← readLock
  let corpus ← readCorpus
  let expected := lock.flatMap fun (v, _) => corpus.flatMap fun (k, _) =>
    [(v, Codegen.legacy, k), (v, Codegen.venom, k)]
  let actual := fixtures.map fun c => (c.vyper, c.codegen, c.contract)
  failIf "§0 matrix" <|
    (expected.filter (!actual.contains ·)).map (fun e => s!"missing cell {repr e}") ++
    (actual.filter (!expected.contains ·)).map (fun e => s!"cell not in lock × corpus {repr e}") ++
    (if actual.length == actual.eraseDups.length then [] else ["duplicate cells"]) ++
    (if lock.getLast?.map (·.1) == some pinnedLatest then [] else ["pinnedLatest is not the \
      last lock entry"])
  failIf "§0 provenance" <| fixtures.flatMap fun c =>
    (if lock.lookup c.vyper == some c.wheelSha256 then [] else
      [s!"{c.name}: wheel sha256 differs from the lock file"]) ++
    (if corpus.lookup c.contract == some c.sourceSha256 then [] else
      [s!"{c.name}: compiled from a different source than tools/vyper/corpus/{c.contract}.vy \
        (rerun the generator)"]) ++
    (match c.code? with
     | some b => if hexOf b == c.runtimeHex then [] else [s!"{c.name}: hex does not round-trip"]
     | none => [s!"{c.name}: runtime hex does not decode"]) ++
    (c.selectors.filterMap fun (sig, sel) =>
      let h := ffi.KEC sig.toUTF8
      if (h.extract 0 4).toList == bytesBE 4 sel then none
      else some s!"{c.name}: selector of {sig} is not keccak256(signature)[0:4]") ++
    ((k16Plan c).filterMap fun (_, fn, _, _) =>
      if (c.estimate? fn).isSome then none else some s!"{c.name}: no gas estimate for {fn}")
  let oracleLock ← IO.FS.readFile ("tools" / "vyper" / "oracle.lock")
  unless (oracleLock.splitOn oracleWheelSha256).length == 2 do
    throw <| IO.userError "§0 provenance: the py-evm wheel sha256 differs from tools/vyper/oracle.lock"
  IO.println s!"§0 matrix: {fixtures.length} cells = {lock.length} pinned compilers × \
    {corpus.length} corpus contracts × 2 code generators; wheel and source hashes, hex round trip \
    and keccak selectors checked on every cell"
  -- §1 Business assertions (F1) and ABI guards
  let mut runs := 0
  for c in fixtures do
    let some code := c.code? | throw <| IO.userError s!"{c.name}: bad hex"
    failIf s!"§1 business law {c.name}" (lawOf c false code)
    failIf s!"§1 ABI guards {c.name}" (guardLaw c code)
    runs := runs + match c.contract with
      | "loop_if" => loopIfLawCalls (c.loopBound.getD 0)
      | "sum_squares" => sumT0s.length * (c.loopBound.getD 0 + 4)
      | _ => boundary.length * (2 * boundary.length + 1)
  IO.println s!"§1 business assertions: {runs} calls on Θ agree with the reference models \
    (storage, return data, revert), every trip count 0 … bound + 2 and the 2^256 boundary; ABI \
    guards (value, unknown selector, short calldata) revert on every function of every cell"
  -- §2 K16 (F3): the sweep is `EstimateSound` by `estimateSound_of_sweep`
  let mut rows := #[]
  for c in fixtures do
    for (sig, fn, args, kvss) in k16Plan c do
      for kvs in kvss do
        unless k16Gate c sig fn args kvs do
          throw <| IO.userError s!"§2 K16 refuted: {c.name} {sig} from {kvs}: measured gas above \
            the estimate {c.estimate? fn}"
      let (m, _, _) := maxGas c sig args kvss
      let e := (c.estimate? fn).getD 0
      rows := rows.push s!"{c.name} {fn}: max {m} ≤ estimate {e} ({m * 1000 / max e 1}‰)"
  IO.println s!"§2 K16 holds on every swept call (execution gas ≤ --show-gas-estimates):\n  \
    {String.intercalate "\n  " rows.toList}"
  -- K16 does not extend to the transaction: intrinsic gas is outside the estimate (G1 witness).
  let mut witnesses := 0
  for c in cellsOf "store" do
    let some sel := c.selector? "set(uint256)" | throw <| IO.userError "no set selector"
    let some r := c.call? "set(uint256)" [1] [] | throw <| IO.userError "set(1) did not run"
    let tx := r.gasUsed + EVM.intrinsicGas (legacyTx (some contractAddr) (calldata sel [1]).toList)
    let e := (c.estimate? "set").getD 0
    unless r.ok && e < tx do
      throw <| IO.userError s!"§2 expected refutation of the transaction-level K16 lost on {c.name}"
    witnesses := witnesses + 1
    if witnesses == 1 then
      IO.println s!"§2 transaction-level K16 refuted (expected): {c.name} set(1) from x = 0 costs \
        {r.gasUsed} + intrinsic {tx - r.gasUsed} = {tx} > estimate {e}"
  -- §3 Golden values (provenance, then regression), gas shape, Θ invariants, storage-gas rules
  failIf "§3 golden provenance (py-evm)" <| fixtures.filterMap fun c =>
    let m := measureWith (oracleGas c) c
    match golden.lookup (c.vyper, c.codegen, c.contract) with
    | some g => if m == some g then none else some s!"{c.name}: py-evm gives {m}, pinned {g}"
    | none => some s!"{c.name}: no golden row (py-evm gives {m})"
  failIf "§3 golden gas" <| fixtures.filterMap fun c =>
    let m := c.code?.bind (measure · c)
    match golden.lookup (c.vyper, c.codegen, c.contract) with
    | some g => if m == some g then none else some s!"{c.name}: measured {m}, pinned {g}"
    | none => some s!"{c.name}: no golden row (measured {m})"
  failIf "§3 storage-gas rules on Θ" <| fixtures.flatMap fun c =>
    storageGasRules (thetaGas ((c.code?).getD .empty) c) c
  failIf "§3 storage-gas rules on py-evm" <| fixtures.flatMap fun c =>
    storageGasRules (oracleGas c) c
  -- Canary: the rules discriminate. With `G_sset` read as `G_sreset` (the pre-EIP-2200 confusion of
  -- a fresh set with a reset) the same relations fail on every cell that writes a fresh value.
  let wrongSset : GasSource → GasSource := fun g sig args x0 =>
    (g sig args x0).map fun gas => if gas ≥ Gsset then gas - (Gsset - Gsreset) else gas
  unless fixtures.all fun c => !(storageGasRules (wrongSset (oracleGas c)) c).isEmpty do
    throw <| IO.userError "§3 canary: the storage-gas rules accept a fresh set priced as a reset"
  for c in fixtures do
    failIf s!"§3 gas shape {c.name}" (gasShapeLaw c)
  IO.println s!"§3 golden gas matches on all {golden.length} cells, and every row equals the same \
    measurement on the py-evm records; EIP-2929/2200 storage-gas relations hold on Θ and on py-evm \
    for every cell (canary refuted); gas non-decreasing in the trip count with constant \
    per-iteration increments"
  failIf "§3 Θ invariants" <| fixtures.flatMap fun c =>
    (List.range ((c.loopBound.getD 3) + 3)).filterMap fun n =>
      let sig := (c.selectors.find? fun (s, _) => (s.splitOn "(uint256)").length > 1).map (·.1)
      match sig.bind fun s => c.call? s [n] [] with
      | some r => if r.gasLeft ≤ budget then none else some s!"{c.name} n = {n}: gasLeft > budget"
      | none => some s!"{c.name} n = {n}: Θ error or missing function"
  IO.println "§3 Θ_gasLeft_le executed on every swept call: no Θ error, gasLeft ≤ budget"
  -- §4 Legacy vs Venom: same behaviour, no fixed gas order
  let mut dearer : List String := []
  let mut cmp := 0
  for v in lock.map (·.1) do
    for (k, _) in corpus do
      let some l := fixtures.find? fun c => c.vyper == v && c.contract == k && c.codegen == .legacy
        | throw <| IO.userError "no legacy cell"
      let some w := fixtures.find? fun c => c.vyper == v && c.contract == k && c.codegen == .venom
        | throw <| IO.userError "no venom cell"
      let some (sig, _) := l.selectors.find? fun (s, _) => (s.splitOn "(uint256)").length > 1
        | throw <| IO.userError "no function with an argument"
      for n in List.range (l.loopBound.getD 9 + 3) do
        for kvs in [[], [(0, 1000)]] do
          match l.call? sig [n] kvs, w.call? sig [n] kvs with
          | some a, some b =>
            cmp := cmp + 1
            unless a.outcome == b.outcome && a.slot 0 == b.slot 0 && a.output == b.output do
              throw <| IO.userError s!"§4 legacy and venom disagree: {k}@{v} {sig} n = {n}"
            if a.ok && a.gasUsed < b.gasUsed then
              dearer := dearer ++ [s!"{k}@{v} {sig} n = {n}: legacy {a.gasUsed} < venom {b.gasUsed}"]
          | _, _ => throw <| IO.userError s!"§4 Θ error on {k}@{v}"
  if dearer.isEmpty then throw <| IO.userError "§4 expected a witness where venom costs more"
  -- Code size is no proxy for gas: Venom's runtime code is smaller on every 0.4.3 contract, but not
  -- on 0.4.0 `loop_if` (pinned fixture facts behind docs/CONJECTURES.md K17).
  let size := fun (v : String) (cg : Codegen) (k : String) =>
    (fixtures.find? fun c => c.vyper == v && c.codegen == cg && c.contract == k).map
      (·.runtimeHex.length / 2) |>.getD 0
  unless corpus.all (fun (k, _) => decide (size "0.4.3" .venom k < size "0.4.3" .legacy k)) &&
      decide (size "0.4.0" .legacy "loop_if" < size "0.4.0" .venom "loop_if") do
    throw <| IO.userError "§4 code-size facts behind K17 changed; review docs/CONJECTURES.md K17"
  IO.println s!"§4 legacy and venom agree on {cmp} paired calls (outcome, storage, return data); \
    'venom never costs more' refuted on {dearer.length} of them, e.g. {dearer.head!}"
  -- §5 Property tests (counted) and their canaries
  expectHolds "loop_if = loopIfRef (random 256-bit storage, trip count up to bound + 2)"
    (∀ x0 : UInt256, ∀ n : ℕ, loopIfAgrees loopIfRef x0 n = true)
  expectRefuted "canary: loop_if = the same loop without the `i > 3` guard"
    (∀ x0 : UInt256, ∀ n : ℕ, loopIfAgrees loopNoGuardRef x0 n = true)
  expectHolds "sum_squares = sumSqRef (random storage, trip count up to bound + 2)"
    (∀ t0 : UInt256, ∀ n : ℕ, sumSquaresAgrees t0 n = true)
  expectHolds "store.set(v) stores v and x() returns it (random 256-bit v and storage)"
    (∀ x0 v : UInt256, setAgrees id x0 v = true)
  expectRefuted "canary: store.set(v) stores v mod 2^128"
    (∀ x0 v : UInt256, setAgrees (· % 2 ^ 128) x0 v = true)
  expectHolds "store.bump(d) = bumpRef (checked addition, random 256-bit operands)"
    (∀ x0 d : UInt256, bumpAgrees bumpRef x0 d = true)
  expectRefuted "canary: store.bump never reverts (wrapping addition)"
    (∀ x0 d : UInt256, bumpAgrees (fun x d => some ((x + d) % wordSize)) x0 d = true)
  -- §6 Mutation tests (E1)
  let mut killed := 0
  for c in fixtures do
    let some code := c.code? | throw <| IO.userError s!"{c.name}: bad hex"
    -- M1: the loop bound constant `PUSH1 bound` lowered by one.
    if let some b := c.loopBound then
      let some h := replaceFirst c.runtimeHex ("60" ++ hex2 b) ("60" ++ hex2 (b - 1))
        | throw <| IO.userError s!"§6 {c.name}: PUSH1 bound not found"
      if (lawOf c true ((ofHex? h).getD .empty)).isEmpty then
        throw <| IO.userError s!"§6 M1 survived: {c.name} with bound {b - 1}"
      killed := killed + 1
    -- M2: the first function's selector constant changed, so it is unreachable.
    let some (sig, sel) := c.selectors.find? fun (s, _) => (s.splitOn "(uint256)").length > 1
      | throw <| IO.userError "no function with an argument"
    let some h := replaceFirst c.runtimeHex ("63" ++ hexOf ⟨(bytesBE 4 sel).toArray⟩)
        ("63" ++ hexOf ⟨(bytesBE 4 (sel ^^^ 1)).toArray⟩)
      | throw <| IO.userError s!"§6 {c.name}: PUSH4 selector of {sig} not found"
    if (lawOf c true ((ofHex? h).getD .empty)).isEmpty then
      throw <| IO.userError s!"§6 M2 survived: {c.name} with {sig} unreachable"
    killed := killed + 1
    -- M3: the other code generator's bytecode under this cell's golden values.
    if let some o := fixtures.find? fun o =>
        o.vyper == c.vyper && o.contract == c.contract && o.codegen != c.codegen then
      if measure ((o.code?).getD .empty) c == golden.lookup (c.vyper, c.codegen, c.contract) then
        throw <| IO.userError s!"§6 M3 survived: {o.name}'s bytecode passes {c.name}'s golden gas"
      killed := killed + 1
    -- M4: an estimate one gas below the measured maximum fails the K16 check at the maximising
    --     input, and an estimate equal to it passes there (the check is exact at the boundary).
    for (sig, fn, args, kvss) in k16Plan c do
      let (m, kvs, n) := maxGas c sig args kvss
      let atMax := { c with gasEstimates := [(fn, m)] }
      let below := { c with gasEstimates := [(fn, m - 1)] }
      unless gasWithin atMax sig fn kvs n && !gasWithin below sig fn kvs n do
        throw <| IO.userError s!"§6 M4: the K16 sweep is not exact at the boundary on {c.name} {fn}"
      killed := killed + 1
  -- §7 Independent EVM (D1): every call recorded on py-evm agrees with Θ exactly.
  let points := fixtures.foldl (fun n c => n + c.oracle.length) 0
  failIf s!"§7 Θ vs {oracleVersion}" <| fixtures.flatMap fun c =>
    match c.code? with
    | some code => c.oracle.filterMap (oracleDiff code c)
    | none => [s!"{c.name}: bad hex"]
  IO.println s!"§7 independent EVM: Θ and {oracleVersion} agree exactly (success, execution gas, \
    storage, return data) on all {points} recorded calls of the {fixtures.length} cells"
  -- Canary: the comparison discriminates; the other code generator's bytecode disagrees with this
  -- cell's py-evm record somewhere (gas differs between the code generators, §4).
  for c in fixtures do
    if let some o := fixtures.find? fun o =>
        o.vyper == c.vyper && o.contract == c.contract && o.codegen != c.codegen then
      let code := (o.code?).getD .empty
      if c.oracle.all fun p => (oracleDiff code c p).isNone then
        throw <| IO.userError s!"§7 canary: {o.name}'s bytecode matches {c.name}'s py-evm record"
      killed := killed + 1
  IO.println s!"§6 mutation: {killed} mutants killed (bound constant, unreachable selector, swapped \
    code generator under the golden values and under the py-evm record, estimate one below the \
    maximum), 0 survived"

#eval runAll

end EvmYul.Vyper.FixtureTests
