import Mathlib

/-!
# Elementary Collatz-style arithmetic

This file extracts the complete, reusable arithmetic core from
`M-RAMDHAN/discrete-algorithmic-physics`: Collatz-type steps, bit-count
helpers, and mod-4 facts about the `3n+1` map.
-/

namespace Nat

/-- The standard Collatz step: divide even inputs by two and send odd inputs to
`3n+1`. -/
def collatzStep (n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

/-- A generalized odd affine Collatz step. -/
def generalizedCollatzStep (a b n : ℕ) : ℕ :=
  if n % 2 = 0 then n / 2 else a * n + b

/-- The bounded Collatz trajectory until reaching `1`, `0`, or the step cap. -/
def collatzTrajectory (n maxSteps : ℕ) : List ℕ :=
  if n = 0 ∨ maxSteps = 0 then []
  else if n = 1 then [1]
  else n :: collatzTrajectory (collatzStep n) (maxSteps - 1)
termination_by maxSteps

/-- The population count of the binary expansion of a natural number. -/
def popcount : ℕ → ℕ
  | 0 => 0
  | n + 1 => (n + 1) % 2 + popcount ((n + 1) / 2)
termination_by n => n

/-- The number of trailing zero bits in a positive natural number, with
`countTrailingZeros 0 = 0`. -/
def countTrailingZeros : ℕ → ℕ
  | 0 => 0
  | n + 1 => if (n + 1) % 2 = 1 then 0 else 1 + countTrailingZeros ((n + 1) / 2)
termination_by n => n

/-- Check whether the bounded Collatz trajectory reaches `1`. -/
def reachesOne (n maxSteps : ℕ) : Bool :=
  if n = 1 ∨ maxSteps = 0 then n = 1
  else reachesOne (collatzStep n) (maxSteps - 1)
termination_by maxSteps

@[simp] lemma collatzStep_one : collatzStep 1 = 4 := rfl
@[simp] lemma collatzStep_two : collatzStep 2 = 1 := rfl
@[simp] lemma collatzStep_three : collatzStep 3 = 10 := rfl
@[simp] lemma collatzStep_four : collatzStep 4 = 2 := rfl
@[simp] lemma collatzStep_five : collatzStep 5 = 16 := rfl

@[simp] lemma popcount_one : popcount 1 = 1 := by native_decide
@[simp] lemma popcount_two : popcount 2 = 1 := by native_decide
@[simp] lemma popcount_four : popcount 4 = 1 := by native_decide
@[simp] lemma popcount_twentySeven : popcount 27 = 4 := by native_decide

@[simp] lemma countTrailingZeros_one : countTrailingZeros 1 = 0 := by native_decide
@[simp] lemma countTrailingZeros_two : countTrailingZeros 2 = 1 := by native_decide
@[simp] lemma countTrailingZeros_four : countTrailingZeros 4 = 2 := by native_decide
@[simp] lemma countTrailingZeros_eight : countTrailingZeros 8 = 3 := by native_decide
@[simp] lemma countTrailingZeros_sixteen : countTrailingZeros 16 = 4 := by native_decide

/-- If `n ≡ 1 (mod 4)`, then `3n+1` is divisible by four. -/
theorem three_mul_add_one_mod_four_eq_zero_of_mod_four_eq_one {n : ℕ}
    (hn : n % 4 = 1) :
    (3 * n + 1) % 4 = 0 := by
  omega

/-- If `n ≡ 3 (mod 4)`, then `3n+1 ≡ 2 (mod 4)`. -/
theorem three_mul_add_one_mod_four_eq_two_of_mod_four_eq_three {n : ℕ}
    (hn : n % 4 = 3) :
    (3 * n + 1) % 4 = 2 := by
  omega

end Nat
