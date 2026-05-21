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

end
