/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!

# EUV Lithography: Laser–Plasma Interaction Basics

Formalizes the CO₂ laser Gaussian beam optics and focused spot parameters
for the laser-produced plasma (LPP) EUV source.

## Main definitions

- `GaussianBeam` : Gaussian TEM₀₀ beam with waist w₀, wavelength `lam`
- `rayleighRange` : z_R = π w₀² / lam
- `beamRadius` : w(z) = w₀ √(1 + (z/z_R)²)
- `peakIntensity` : I₀ = 2P / (π w₀²)
- `intensity` : I(r,z) = I₀ (w₀/w(z))² exp(-2r²/w(z)²)
- `focusedWaist` : w₀' = lam × f / (π w₀)

## Main results

- `rayleighRange_pos`, `beamRadius_pos`, `beamRadius_ge_waist`
- `intensity_nonneg`, `intensity_peak`, `intensity_on_axis_decay`
- `focusedWaist_pos`, `focusPeakIntensity_pos`

-/

noncomputable section

open Real

/-- A Gaussian TEM₀₀ laser beam. Field `lam` is the wavelength (λ). -/
structure GaussianBeam where
  /-- Wavelength in meters (named `lam` to avoid conflict with Lean's λ keyword) -/
  lam : ℝ
  lam_pos : 0 < lam
  /-- Beam waist radius at z = 0 -/
  w₀ : ℝ
  w₀_pos : 0 < w₀
  /-- Total power (W) -/
  P : ℝ
  P_pos : 0 < P

namespace GaussianBeam

variable (b : GaussianBeam)

/-- Rayleigh range: z_R = π w₀² / lam -/
def rayleighRange : ℝ := π * b.w₀ ^ 2 / b.lam

theorem rayleighRange_pos : 0 < b.rayleighRange :=
  div_pos (mul_pos pi_pos (sq_pos_of_pos b.w₀_pos)) b.lam_pos

/-- Longer wavelength shortens the Rayleigh range at fixed waist. -/
theorem rayleighRange_decreases_with_wavelength {lam₁ lam₂ w₀ P : ℝ}
    (hlam₁ : 0 < lam₁) (hlam : lam₁ < lam₂) (hw : 0 < w₀) (hP : 0 < P) :
    (GaussianBeam.mk lam₂ (lt_trans hlam₁ hlam) w₀ hw P hP).rayleighRange <
      (GaussianBeam.mk lam₁ hlam₁ w₀ hw P hP).rayleighRange := by
  unfold rayleighRange
  exact div_lt_div_of_pos_left (mul_pos pi_pos (sq_pos_of_pos hw)) hlam₁ hlam

/-- Larger beam waist increases the Rayleigh range at fixed wavelength. -/
theorem rayleighRange_increases_with_waist {w₁ w₂ lam P : ℝ}
    (hw₁ : 0 < w₁) (hw : w₁ < w₂) (hlam : 0 < lam) (hP : 0 < P) :
    (GaussianBeam.mk lam hlam w₁ hw₁ P hP).rayleighRange <
      (GaussianBeam.mk lam hlam w₂ (lt_trans hw₁ hw) P hP).rayleighRange := by
  unfold rayleighRange
  apply div_lt_div_of_pos_right _ hlam
  exact mul_lt_mul_of_pos_left (by nlinarith) pi_pos

/-- Beam radius at position z: w(z) = w₀ √(1 + (z/z_R)²) -/
def beamRadius (z : ℝ) : ℝ :=
  b.w₀ * sqrt (1 + (z / b.rayleighRange) ^ 2)

theorem beamRadius_pos (z : ℝ) : 0 < b.beamRadius z := by
  unfold beamRadius
  apply mul_pos b.w₀_pos
  apply sqrt_pos_of_pos
  have := sq_nonneg (z / b.rayleighRange)
  linarith

theorem beamRadius_waist : b.beamRadius 0 = b.w₀ := by
  simp [beamRadius, rayleighRange]

/-- Beam radius is minimized at the waist: w(z) ≥ w₀ -/
theorem beamRadius_ge_waist (z : ℝ) : b.w₀ ≤ b.beamRadius z := by
  unfold beamRadius
  calc b.w₀
      = b.w₀ * 1 := by ring
    _ ≤ b.w₀ * sqrt (1 + (z / b.rayleighRange) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt b.w₀_pos)
      have hA : 0 ≤ 1 + (z / b.rayleighRange) ^ 2 := by
        linarith [sq_nonneg (z / b.rayleighRange)]
      nlinarith [sq_sqrt hA, sqrt_nonneg (1 + (z / b.rayleighRange) ^ 2),
        sq_nonneg (z / b.rayleighRange)]

/-- Real-beam radius with beam-quality factor `M²`:
    `w(z) = w₀ sqrt(1 + (M² z / z_R)^2)`. -/
def beamRadiusM2 (M2 z : ℝ) : ℝ :=
  b.w₀ * sqrt (1 + (M2 * z / b.rayleighRange) ^ 2)

theorem beamRadiusM2_pos {M2 z : ℝ} :
    0 < b.beamRadiusM2 M2 z := by
  unfold beamRadiusM2
  apply mul_pos b.w₀_pos
  apply sqrt_pos_of_pos
  linarith [sq_nonneg (M2 * z / b.rayleighRange)]

theorem beamRadiusM2_ideal (z : ℝ) :
    b.beamRadiusM2 1 z = b.beamRadius z := by
  unfold beamRadiusM2 beamRadius
  ring_nf

theorem beamRadiusM2_waist (M2 : ℝ) :
    b.beamRadiusM2 M2 0 = b.w₀ := by
  simp [beamRadiusM2]

/-- Real-beam radius is still minimized at the waist. -/
theorem beamRadiusM2_ge_waist (M2 z : ℝ) : b.w₀ ≤ b.beamRadiusM2 M2 z := by
  unfold beamRadiusM2
  calc b.w₀
      = b.w₀ * 1 := by ring
    _ ≤ b.w₀ * sqrt (1 + (M2 * z / b.rayleighRange) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (le_of_lt b.w₀_pos)
      have hA : 0 ≤ 1 + (M2 * z / b.rayleighRange) ^ 2 := by
        linarith [sq_nonneg (M2 * z / b.rayleighRange)]
      nlinarith [sq_sqrt hA, sqrt_nonneg (1 + (M2 * z / b.rayleighRange) ^ 2),
        sq_nonneg (M2 * z / b.rayleighRange)]

/-- Peak intensity at the waist: I₀ = 2P / (π w₀²) -/
def peakIntensity : ℝ := 2 * b.P / (π * b.w₀ ^ 2)

theorem peakIntensity_pos : 0 < b.peakIntensity :=
  div_pos (mul_pos two_pos b.P_pos) (mul_pos pi_pos (sq_pos_of_pos b.w₀_pos))

/-- Higher laser power raises waist peak intensity at fixed beam geometry. -/
theorem peakIntensity_increases_with_power {P₁ P₂ lam w₀ : ℝ}
    (hP₁ : 0 < P₁) (hP : P₁ < P₂) (hlam : 0 < lam) (hw : 0 < w₀) :
    (GaussianBeam.mk lam hlam w₀ hw P₁ hP₁).peakIntensity <
      (GaussianBeam.mk lam hlam w₀ hw P₂ (lt_trans hP₁ hP)).peakIntensity := by
  unfold peakIntensity
  exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hP two_pos)
    (mul_pos pi_pos (sq_pos_of_pos hw))

/-- Larger waist lowers waist peak intensity at fixed power. -/
theorem peakIntensity_decreases_with_waist {w₁ w₂ lam P : ℝ}
    (hw₁ : 0 < w₁) (hw : w₁ < w₂) (hlam : 0 < lam) (hP : 0 < P) :
    (GaussianBeam.mk lam hlam w₂ (lt_trans hw₁ hw) P hP).peakIntensity <
      (GaussianBeam.mk lam hlam w₁ hw₁ P hP).peakIntensity := by
  unfold peakIntensity
  apply div_lt_div_of_pos_left (mul_pos two_pos hP)
  · exact mul_pos pi_pos (sq_pos_of_pos hw₁)
  exact mul_lt_mul_of_pos_left (by nlinarith) pi_pos

/-- The radial Gaussian area factor at the beam waist:
    `∫₀∞ 2πr exp(-2r²/w₀²) dr = πw₀²/2`. -/
def waistGaussianAreaFactor : ℝ := π * b.w₀ ^ 2 / 2

theorem waistGaussianAreaFactor_pos : 0 < b.waistGaussianAreaFactor :=
  div_pos (mul_pos pi_pos (sq_pos_of_pos b.w₀_pos)) two_pos

/-- Algebraic power normalization after evaluating the radial Gaussian integral. -/
theorem waistPowerNormalization :
    b.peakIntensity * b.waistGaussianAreaFactor = b.P := by
  unfold peakIntensity waistGaussianAreaFactor
  field_simp [pi_ne_zero, ne_of_gt b.w₀_pos]

/-- Fraction of Gaussian beam power inside radius `R` at the waist. -/
def encircledPowerFraction (R : ℝ) : ℝ :=
  1 - exp (-(2 * R ^ 2 / b.w₀ ^ 2))

theorem encircledPowerFraction_nonneg (R : ℝ) :
    0 ≤ b.encircledPowerFraction R := by
  unfold encircledPowerFraction
  apply sub_nonneg.mpr
  rw [exp_le_one_iff]
  exact neg_nonpos.mpr (div_nonneg
    (mul_nonneg (by norm_num) (sq_nonneg R)) (sq_nonneg b.w₀))

theorem encircledPowerFraction_lt_one (R : ℝ) :
    b.encircledPowerFraction R < 1 := by
  unfold encircledPowerFraction
  linarith [exp_pos (-(2 * R ^ 2 / b.w₀ ^ 2))]

theorem encircledPowerFraction_zero :
    b.encircledPowerFraction 0 = 0 := by
  simp [encircledPowerFraction]

/-- Intensity profile: I(r,z) = I₀ (w₀/w(z))² exp(-2r²/w(z)²) -/
def intensity (r z : ℝ) : ℝ :=
  b.peakIntensity * (b.w₀ / b.beamRadius z) ^ 2 * exp (-2 * r ^ 2 / b.beamRadius z ^ 2)

theorem intensity_nonneg (r z : ℝ) : 0 ≤ b.intensity r z :=
  mul_nonneg (mul_nonneg (le_of_lt b.peakIntensity_pos) (sq_nonneg _)) (le_of_lt (exp_pos _))

/-- On-axis intensity: I(0,z) = I₀ (w₀/w(z))² -/
theorem intensity_on_axis (z : ℝ) :
    b.intensity 0 z = b.peakIntensity * (b.w₀ / b.beamRadius z) ^ 2 := by
  simp [intensity]

/-- At z = 0, intensity = I₀ -/
theorem intensity_peak : b.intensity 0 0 = b.peakIntensity := by
  simp [intensity, beamRadius_waist, div_self (ne_of_gt b.w₀_pos)]

/-- On-axis intensity decays as 1/(1 + (z/z_R)²) -/
theorem intensity_on_axis_decay (z : ℝ) :
    b.intensity 0 z = b.peakIntensity / (1 + (z / b.rayleighRange) ^ 2) := by
  rw [intensity_on_axis]
  unfold beamRadius
  have hw0 : b.w₀ ≠ 0 := ne_of_gt b.w₀_pos
  have harg_nonneg : 0 ≤ 1 + (z / b.rayleighRange) ^ 2 := by
    linarith [sq_nonneg (z / b.rayleighRange)]
  have hs : sqrt (1 + (z / b.rayleighRange) ^ 2) ≠ 0 := by
    exact ne_of_gt (sqrt_pos_of_pos (by linarith [sq_nonneg (z / b.rayleighRange)]))
  field_simp [hw0, hs, sq_sqrt harg_nonneg]
  rw [sq_sqrt (by positivity)]

/-- Far-field divergence angle: θ_∞ = lam / (π w₀) -/
def farFieldDivergence : ℝ := b.lam / (π * b.w₀)

theorem farFieldDivergence_pos : 0 < b.farFieldDivergence :=
  div_pos b.lam_pos (mul_pos pi_pos b.w₀_pos)

/-- Larger beam waist reduces far-field divergence at fixed wavelength. -/
theorem farFieldDivergence_decreases_with_waist {w₁ w₂ lam P : ℝ}
    (hw₁ : 0 < w₁) (hw : w₁ < w₂) (hlam : 0 < lam) (hP : 0 < P) :
    (GaussianBeam.mk lam hlam w₂ (lt_trans hw₁ hw) P hP).farFieldDivergence <
      (GaussianBeam.mk lam hlam w₁ hw₁ P hP).farFieldDivergence := by
  unfold farFieldDivergence
  exact div_lt_div_of_pos_left hlam (mul_pos pi_pos hw₁)
    (mul_lt_mul_of_pos_left hw pi_pos)

/-- Longer wavelength increases far-field divergence at fixed waist. -/
theorem farFieldDivergence_increases_with_wavelength {lam₁ lam₂ w₀ P : ℝ}
    (hlam₁ : 0 < lam₁) (hlam : lam₁ < lam₂) (hw : 0 < w₀) (hP : 0 < P) :
    (GaussianBeam.mk lam₁ hlam₁ w₀ hw P hP).farFieldDivergence <
      (GaussianBeam.mk lam₂ (lt_trans hlam₁ hlam) w₀ hw P hP).farFieldDivergence := by
  unfold farFieldDivergence
  exact div_lt_div_of_pos_right hlam (mul_pos pi_pos hw)

/-- Focused beam waist: w₀' = lam × f / (π w₀) -/
def focusedWaist (f : ℝ) : ℝ := b.lam * f / (π * b.w₀)

theorem focusedWaist_pos {f : ℝ} (hf : 0 < f) : 0 < b.focusedWaist f :=
  div_pos (mul_pos b.lam_pos hf) (mul_pos pi_pos b.w₀_pos)

/-- Real-beam focused waist including beam-quality factor `M²`. -/
def focusedWaistM2 (M2 f : ℝ) : ℝ := M2 * b.lam * f / (π * b.w₀)

theorem focusedWaistM2_pos {M2 f : ℝ} (hM2 : 0 < M2) (hf : 0 < f) :
    0 < b.focusedWaistM2 M2 f :=
  div_pos (mul_pos (mul_pos hM2 b.lam_pos) hf) (mul_pos pi_pos b.w₀_pos)

theorem focusedWaistM2_ideal (f : ℝ) :
    b.focusedWaistM2 1 f = b.focusedWaist f := by
  unfold focusedWaistM2 focusedWaist
  ring

theorem focusedWaistM2_increases_with_quality_factor {M2a M2b f : ℝ}
    (hM2 : M2a < M2b) (hf : 0 < f) :
    b.focusedWaistM2 M2a f < b.focusedWaistM2 M2b f := by
  unfold focusedWaistM2
  apply div_lt_div_of_pos_right _ (mul_pos pi_pos b.w₀_pos)
  exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hM2 b.lam_pos) hf

/-- Larger collimated input beam radius gives a smaller focused waist. -/
theorem focusedWaistM2_decreases_with_input_waist {w₁ w₂ lam P M2 f : ℝ}
    (hw₁ : 0 < w₁) (hw : w₁ < w₂) (hlam : 0 < lam) (hP : 0 < P)
    (hM2 : 0 < M2) (hf : 0 < f) :
    (GaussianBeam.mk lam hlam w₂ (lt_trans hw₁ hw) P hP).focusedWaistM2 M2 f <
      (GaussianBeam.mk lam hlam w₁ hw₁ P hP).focusedWaistM2 M2 f := by
  unfold focusedWaistM2
  have hnum : 0 < M2 * lam * f := mul_pos (mul_pos hM2 hlam) hf
  exact div_lt_div_of_pos_left hnum (mul_pos pi_pos hw₁)
    (mul_lt_mul_of_pos_left hw pi_pos)

/-- Peak intensity at focus: I_focus = 2P / (π w₀'²) -/
def focusPeakIntensity (f : ℝ) : ℝ :=
  2 * b.P / (π * b.focusedWaist f ^ 2)

theorem focusPeakIntensity_pos {f : ℝ} (hf : 0 < f) : 0 < b.focusPeakIntensity f :=
  div_pos (mul_pos two_pos b.P_pos) (mul_pos pi_pos (sq_pos_of_pos (b.focusedWaist_pos hf)))

/-- Higher laser power raises focused peak intensity when the focused waist is fixed. -/
theorem focusPeakIntensity_increases_with_power {P₁ P₂ lam w₀ f : ℝ}
    (hP₁ : 0 < P₁) (hP : P₁ < P₂) (hlam : 0 < lam) (hw : 0 < w₀) (hf : 0 < f) :
    (GaussianBeam.mk lam hlam w₀ hw P₁ hP₁).focusPeakIntensity f <
      (GaussianBeam.mk lam hlam w₀ hw P₂ (lt_trans hP₁ hP)).focusPeakIntensity f := by
  unfold focusPeakIntensity focusedWaist
  apply div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hP two_pos)
  exact mul_pos pi_pos (sq_pos_of_pos (div_pos (mul_pos hlam hf) (mul_pos pi_pos hw)))

/-- Longer focal length makes a larger focused waist and lowers peak intensity. -/
theorem focusPeakIntensity_decreases_with_focal_length {f₁ f₂ : ℝ}
    (hf₁ : 0 < f₁) (hf : f₁ < f₂) :
    b.focusPeakIntensity f₂ < b.focusPeakIntensity f₁ := by
  unfold focusPeakIntensity focusedWaist
  have hwa : 0 < b.lam * f₁ / (π * b.w₀) :=
    div_pos (mul_pos b.lam_pos hf₁) (mul_pos pi_pos b.w₀_pos)
  have hw : b.lam * f₁ / (π * b.w₀) < b.lam * f₂ / (π * b.w₀) := by
    exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hf b.lam_pos)
      (mul_pos pi_pos b.w₀_pos)
  have hden_pos : 0 < π * (b.lam * f₁ / (π * b.w₀)) ^ 2 :=
    mul_pos pi_pos (sq_pos_of_pos hwa)
  have hden : π * (b.lam * f₁ / (π * b.w₀)) ^ 2 <
      π * (b.lam * f₂ / (π * b.w₀)) ^ 2 := by
    apply mul_lt_mul_of_pos_left _ pi_pos
    nlinarith
  exact div_lt_div_of_pos_left (mul_pos two_pos b.P_pos) hden_pos hden

/-- Real-beam peak intensity at focus using the `M²` waist. -/
def focusPeakIntensityM2 (M2 f : ℝ) : ℝ :=
  2 * b.P / (π * b.focusedWaistM2 M2 f ^ 2)

theorem focusPeakIntensityM2_pos {M2 f : ℝ} (hM2 : 0 < M2) (hf : 0 < f) :
    0 < b.focusPeakIntensityM2 M2 f :=
  div_pos (mul_pos two_pos b.P_pos)
    (mul_pos pi_pos (sq_pos_of_pos (b.focusedWaistM2_pos hM2 hf)))

theorem focusPeakIntensityM2_ideal (f : ℝ) :
    b.focusPeakIntensityM2 1 f = b.focusPeakIntensity f := by
  unfold focusPeakIntensityM2 focusPeakIntensity
  rw [focusedWaistM2_ideal]

/-- Increasing `M²` increases the focused waist and therefore reduces peak intensity. -/
theorem focusPeakIntensityM2_decreases_with_quality_factor {M2a M2b f : ℝ}
    (hM2a : 0 < M2a) (hM2 : M2a < M2b) (hf : 0 < f) :
    b.focusPeakIntensityM2 M2b f < b.focusPeakIntensityM2 M2a f := by
  unfold focusPeakIntensityM2
  have hwa_pos : 0 < b.focusedWaistM2 M2a f := b.focusedWaistM2_pos hM2a hf
  have hwb_pos : 0 < b.focusedWaistM2 M2b f :=
    b.focusedWaistM2_pos (lt_trans hM2a hM2) hf
  have hw : b.focusedWaistM2 M2a f < b.focusedWaistM2 M2b f :=
    b.focusedWaistM2_increases_with_quality_factor hM2 hf
  have hden_pos : 0 < π * b.focusedWaistM2 M2a f ^ 2 :=
    mul_pos pi_pos (sq_pos_of_pos hwa_pos)
  have hden :
      π * b.focusedWaistM2 M2a f ^ 2 < π * b.focusedWaistM2 M2b f ^ 2 := by
    apply mul_lt_mul_of_pos_left _ pi_pos
    nlinarith
  exact div_lt_div_of_pos_left (mul_pos two_pos b.P_pos) hden_pos hden

end GaussianBeam

end
