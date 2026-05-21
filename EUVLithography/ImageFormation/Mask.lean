import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# EUV Lithography: Reflective Mask Algebra

Formal algebra for reflective-mask contrast, shadowing, grating order geometry,
and projection demagnification.
-/

noncomputable section

open Real

/-- Reflective mask contrast: `(R_ML - R_abs)/(R_ML + R_abs)`. -/
def maskContrast (R_ML R_abs : ℝ) : ℝ :=
  (R_ML - R_abs) / (R_ML + R_abs)

theorem maskContrast_pos {R_ML R_abs : ℝ} (habs : 0 < R_abs) (h : R_abs < R_ML) :
    0 < maskContrast R_ML R_abs := by
  unfold maskContrast
  exact div_pos (sub_pos.mpr h) (add_pos (lt_trans habs h) habs)

theorem maskContrast_lt_one {R_ML R_abs : ℝ} (habs : 0 < R_abs) (hML : 0 < R_ML) :
    maskContrast R_ML R_abs < 1 := by
  unfold maskContrast
  rw [div_lt_one (add_pos hML habs)]
  linarith

/-- Diffraction grating order condition. -/
def gratingOrderCondition (theta_m lambda p : ℝ) (m : ℤ) : Prop :=
  sin theta_m = m * lambda / p

/-- Mask shadow shift: `h_abs tan(theta_inc) / demag`. -/
def maskShadow (h_abs theta_inc demag : ℝ) : ℝ :=
  h_abs * tan theta_inc / demag

theorem maskShadow_pos {h_abs theta_inc demag : ℝ}
    (hh : 0 < h_abs) (htan : 0 < tan theta_inc) (hd : 0 < demag) :
    0 < maskShadow h_abs theta_inc demag := by
  unfold maskShadow
  positivity

theorem maskShadow_linear_in_absorber_height {h₁ h₂ theta_inc demag : ℝ}
    (hh : h₁ < h₂) (htan : 0 < tan theta_inc) (hd : 0 < demag) :
    maskShadow h₁ theta_inc demag < maskShadow h₂ theta_inc demag := by
  unfold maskShadow
  exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_right hh htan) hd

theorem maskShadow_decreases_with_demag {h_abs theta_inc d₁ d₂ : ℝ}
    (hh : 0 < h_abs) (htan : 0 < tan theta_inc) (hd₁ : 0 < d₁) (hd : d₁ < d₂) :
    maskShadow h_abs theta_inc d₂ < maskShadow h_abs theta_inc d₁ := by
  unfold maskShadow
  exact div_lt_div_of_pos_left (mul_pos hh htan) hd₁ hd

/-- Projection demagnification of a mask feature. -/
def waferFeatureWidth (w_mask demag : ℝ) : ℝ := w_mask / demag

theorem waferFeatureWidth_pos {w_mask demag : ℝ} (hw : 0 < w_mask) (hd : 0 < demag) :
    0 < waferFeatureWidth w_mask demag := by
  unfold waferFeatureWidth
  positivity

theorem fourX_demag (w_mask : ℝ) :
    waferFeatureWidth w_mask 4 = w_mask / 4 := rfl

theorem waferFeatureWidth_decreases_with_demag {w_mask d₁ d₂ : ℝ}
    (hw : 0 < w_mask) (hd₁ : 0 < d₁) (hd : d₁ < d₂) :
    waferFeatureWidth w_mask d₂ < waferFeatureWidth w_mask d₁ := by
  unfold waferFeatureWidth
  exact div_lt_div_of_pos_left hw hd₁ hd

end
