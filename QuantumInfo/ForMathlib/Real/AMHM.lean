import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# AM-HM inequality

For a positive finite family of real numbers, `(∑ k, 1 / a k) * (∑ k, a k)`
is bounded below by the square of the number of terms.
-/

noncomputable section

namespace Real

/-- AM-HM inequality in the form `(∑ 1 / a k) * (∑ a k) ≥ n ^ 2`. -/
theorem sq_card_le_sum_inv_mul_sum {n : ℕ} (a : Fin n → ℝ) (ha : ∀ k, 0 < a k) :
    (n : ℝ) ^ 2 ≤ (∑ k : Fin n, 1 / a k) * (∑ k : Fin n, a k) := by
  let f : Fin n → ℝ := fun k => sqrt (1 / a k)
  let g : Fin n → ℝ := fun k => sqrt (a k)
  have h_cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f g
  have h_fg : ∀ k : Fin n, f k * g k = 1 := by
    intro k
    simp only [f, g]
    rw [← sqrt_mul (le_of_lt (div_pos one_pos (ha k))), one_div,
      inv_mul_cancel₀ (ne_of_gt (ha k)), sqrt_one]
  have h_fsq : ∀ k : Fin n, f k ^ 2 = 1 / a k := by
    intro k
    simp only [f]
    rw [sq_sqrt (le_of_lt (div_pos one_pos (ha k)))]
  have h_gsq : ∀ k : Fin n, g k ^ 2 = a k := by
    intro k
    simp only [g]
    rw [sq_sqrt (le_of_lt (ha k))]
  have h1 : ∑ k : Fin n, f k * g k = ∑ k : Fin n, (1 : ℝ) := by
    congr 1
    ext k
    exact h_fg k
  have h2 : ∑ k : Fin n, f k ^ 2 = ∑ k : Fin n, 1 / a k := by
    congr 1
    ext k
    exact h_fsq k
  have h3 : ∑ k : Fin n, g k ^ 2 = ∑ k : Fin n, a k := by
    congr 1
    ext k
    exact h_gsq k
  rw [h1, h2, h3] at h_cs
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at h_cs
  exact h_cs

end Real

end
