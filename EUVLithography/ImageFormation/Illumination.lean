import Mathlib.Data.Real.Basic

/-!
# EUV Lithography: Illumination Algebra

Formal algebra for partial coherence and illumination numerical aperture.
-/

noncomputable section

/-- Illumination NA: `NA_ill = sigma * NA_proj`. -/
def illuminationNA (sigma_coherence NA_proj : ℝ) : ℝ :=
  sigma_coherence * NA_proj

theorem illuminationNA_pos {sigma_coherence NA_proj : ℝ}
    (hsigma : 0 < sigma_coherence) (hNA : 0 < NA_proj) :
    0 < illuminationNA sigma_coherence NA_proj := by
  unfold illuminationNA
  exact mul_pos hsigma hNA

theorem illuminationNA_le_projection {sigma_coherence NA_proj : ℝ}
    (hsigma_le_one : sigma_coherence ≤ 1)
    (hNA_nonneg : 0 ≤ NA_proj) :
    illuminationNA sigma_coherence NA_proj ≤ NA_proj := by
  unfold illuminationNA
  exact mul_le_of_le_one_left hNA_nonneg hsigma_le_one

/-- A lower bound on partial coherence gives the corresponding lower bound on illumination NA. -/
theorem illuminationNA_ge_lower_fraction {sigma_coherence NA_proj sigma_min : ℝ}
    (hsigma : sigma_min ≤ sigma_coherence)
    (hNA_nonneg : 0 ≤ NA_proj) :
    sigma_min * NA_proj ≤ illuminationNA sigma_coherence NA_proj := by
  unfold illuminationNA
  exact mul_le_mul_of_nonneg_right hsigma hNA_nonneg

/-- If partial coherence lies in a design interval, illumination NA lies in the scaled interval. -/
theorem illuminationNA_in_coherence_window {sigma_coherence NA_proj sigma_min sigma_max : ℝ}
    (hsigma_min : sigma_min ≤ sigma_coherence)
    (hsigma_max : sigma_coherence ≤ sigma_max)
    (hNA_nonneg : 0 ≤ NA_proj) :
    sigma_min * NA_proj ≤ illuminationNA sigma_coherence NA_proj ∧
      illuminationNA sigma_coherence NA_proj ≤ sigma_max * NA_proj := by
  constructor
  · exact illuminationNA_ge_lower_fraction hsigma_min hNA_nonneg
  · unfold illuminationNA
    exact mul_le_mul_of_nonneg_right hsigma_max hNA_nonneg

end
