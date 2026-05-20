import Mathlib

/-!
# Finite-index summation lemmas
-/

namespace Fin

/-- A value of a function on `Fin n` can be recovered as the difference between
the prefix sum through that index and the strict prefix sum before that index. -/
theorem eq_sum_le_sub_sum_lt {n : ℕ} (f : Fin n → ℝ) (i : Fin n) :
    f i = (∑ j ∈ Finset.univ.filter (· ≤ i), f j) -
      (∑ j ∈ Finset.univ.filter (· < i), f j) := by
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single i]
  · simp only [le_refl, if_true, lt_irrefl, if_false, sub_zero]
  · intro j _ hjne
    by_cases h : j ≤ i
    · have : j < i := lt_of_le_of_ne h hjne
      simp only [h, this, if_true, sub_self]
    · have : ¬j < i := fun hlt => h (le_of_lt hlt)
      simp only [h, this, if_false, sub_zero]
  · simp

end Fin
