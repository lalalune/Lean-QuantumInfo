import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# Lemmas for complex exponentials

Small helper lemmas for phases of the form `Complex.exp (θ * Complex.I)`.
-/

namespace Complex

noncomputable section

/-- The squared norm of a purely imaginary exponential is one. -/
theorem normSq_exp_ofReal_mul_I (θ : ℝ) :
    normSq (exp ((θ : ℂ) * I)) = 1 := by
  rw [normSq_eq_norm_sq, norm_exp_ofReal_mul_I, one_pow]

/-- The squared norm of `exp (-I * a * t)` is one for real `a` and `t`. -/
theorem normSq_exp_neg_I_mul (a t : ℝ) :
    normSq (exp (-I * (a : ℂ) * (t : ℂ))) = 1 := by
  have h : -I * (a : ℂ) * (t : ℂ) = (↑(-(a * t)) : ℂ) * I := by
    push_cast
    ring
  rw [h, normSq_exp_ofReal_mul_I]

end

end Complex
