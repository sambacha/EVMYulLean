module

public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.SplitIfs

public section

/-!
# Reference semantics of the Vyper corpus (V1 business assertions)

Each corpus contract (`tools/vyper/corpus/*.vy`) has a small pure model here: what its external
functions must do to storage and return data, read off the Vyper source. The fixture tests
(`EvmYul/Vyper/FixtureTests.lean`) compare the compiled bytecode, executed on `Θ`, with these
models; a compiler or EVM-semantics bug shows up as a disagreement on a concrete input.

The models are stated the way the source reads (a loop, checked `+=`), and the theorems below
connect them to closed forms and to an overflow check done once at the end. The tests use the
iterative form and the theorems justify the closed forms used in golden values, so the two routes
are independent (TESTING.md D1):

* `loopIfSteps_eq`: Vyper checks overflow on **every** `self.x += i`; because every increment is
  non-negative, that is the same as checking the final sum once.
* `two_mul_loopIfSum`: `2 · Σ_{4 ≤ i < n} i = n (n − 1) − 12` for `n ≥ 4`.
* `six_mul_sumSq`: `6 · Σ_{i < n} i² = (n − 1) n (2n − 1)`.
* `loopIfRef_none_of_gt`, `sumSqRef_none_of_gt`: a trip count above the source `bound=` is
  rejected, whatever the storage.
-/

namespace EvmYul.Vyper

/-- The 256-bit word size. -/
abbrev wordSize : ℕ := 2 ^ 256

/-! ## `loop_if.vy`: `for i in range(n, bound=B): if i > 3: self.x += i` -/

/-- `Σ_{i < n, i > 3} i`, in loop order. -/
def loopIfSum : ℕ → ℕ
  | 0 => 0
  | n + 1 => loopIfSum n + if 3 < n then n else 0

/-- The loop as Vyper executes it: start from `x`, add `i` for every `i > 3`, and abort (`none`)
at the first addition that overflows 256 bits. -/
def loopIfSteps (x : ℕ) : ℕ → Option ℕ
  | 0 => some x
  | n + 1 => (loopIfSteps x n).bind fun y =>
    if 3 < n then (if y + n < wordSize then some (y + n) else none) else some y

/-- `f(n)` from storage `x`: the new `x`, or `none` if the call must revert (`n > bound`, or an
overflowing addition). -/
def loopIfRef (bound x n : ℕ) : Option ℕ :=
  if n ≤ bound then loopIfSteps x n else none

theorem loopIfSteps_eq {x : ℕ} (hx : x < wordSize) (n : ℕ) :
    loopIfSteps x n = if x + loopIfSum n < wordSize then some (x + loopIfSum n) else none := by
  induction n with
  | zero => simp [loopIfSteps, loopIfSum, hx]
  | succ n ih =>
    simp only [loopIfSteps, ih, loopIfSum]
    by_cases hs : x + loopIfSum n < wordSize
    · by_cases h3 : 3 < n
      · simp [hs, h3, Nat.add_assoc]
      · simp [hs, h3]
    · have : ¬ x + (loopIfSum n + if 3 < n then n else 0) < wordSize := by omega
      simp [hs, this]

theorem two_mul_loopIfSum {n : ℕ} (h : 4 ≤ n) : 2 * loopIfSum n = n * (n - 1) - 12 := by
  induction n, h using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    simp only [loopIfSum, show 3 < n by omega, if_true, Nat.add_sub_cancel, mul_add, ih]
    have : 12 ≤ n * (n - 1) := by
      have : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hn (by omega)
      omega
    cases n with
    | zero => omega
    | succ m => simp only [Nat.add_sub_cancel] at *; ring_nf; ring_nf at this; omega

theorem loopIfRef_none_of_gt {bound n : ℕ} (x : ℕ) (h : bound < n) : loopIfRef bound x n = none := by
  simp [loopIfRef, show ¬ n ≤ bound by omega]

/-! ## `sum_squares.vy`: `for i in range(n, bound=B): acc += self._sq(i)` -/

/-- `Σ_{i < n} i²`. -/
def sumSq : ℕ → ℕ
  | 0 => 0
  | n + 1 => sumSq n + n * n

/-- `run(n)`: the stored and returned total, or `none` if the call must revert. Every partial sum
is at most `sumSq bound`, far below `2^256` for the corpus bound, so no overflow case arises. -/
def sumSqRef (bound n : ℕ) : Option ℕ := if n ≤ bound then some (sumSq n) else none

theorem six_mul_sumSq_succ (n : ℕ) : 6 * sumSq (n + 1) = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [sumSq, mul_add, ih]
    ring

theorem six_mul_sumSq (n : ℕ) : 6 * sumSq n = (n - 1) * n * (2 * n - 1) := by
  cases n with
  | zero => rfl
  | succ m =>
    rw [six_mul_sumSq_succ, Nat.add_sub_cancel, show 2 * (m + 1) - 1 = 2 * m + 1 by omega]

theorem sumSqRef_none_of_gt {bound n : ℕ} (h : bound < n) : sumSqRef bound n = none := by
  simp [sumSqRef, show ¬ n ≤ bound by omega]

/-! ## `store.vy`: `set(v): self.x = v`, `bump(d): self.x += d` -/

/-- `bump(d)` from storage `x`: the new `x`, or `none` on overflow. -/
def bumpRef (x d : ℕ) : Option ℕ := if x + d < wordSize then some (x + d) else none

theorem bumpRef_eq_none_iff (x d : ℕ) : bumpRef x d = none ↔ wordSize ≤ x + d := by
  unfold bumpRef; split_ifs with h <;> simp <;> omega

end EvmYul.Vyper
