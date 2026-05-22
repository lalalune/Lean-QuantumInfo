/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.BigOperators

/-!

# EUV Lithography: Projection Optics — Resolution, Depth of Focus, and Strehl Ratio

Formalizes the resolution limit, depth of focus, and Strehl ratio for
EUV projection optics with 4–6 aspheric mirrors.

## Main definitions

- `ProjectionSystem` : EUV scanner projection optics parameters
- `rayleighResolution` : R = k₁ λ / NA
- `abbeLimit` : d_min = λ / (2 NA)
- `depthOfFocus` : DoF = k₂ λ / NA²
- `strehlRatio` : S = exp(-(2π W_rms/λ)²)
- `maskNA` : NA_mask = NA_wafer / demag

## Main results

- `rayleighResolution_pos`, `abbeLimit_pos`, `depthOfFocus_pos`
- `higher_NA_better_resolution`, `shorter_lambda_better_resolution`
- `doF_scales_as_NA_squared`, `doF_resolution_product`
- `strehlRatio_le_one`, `strehlRatio_one_iff_perfect`
- `euv_strehl_gt_98` : W_rms < λ/60 implies Strehl > 0.98

-/

noncomputable section

open Real
open scoped BigOperators

/-- Parameters for an EUV projection optical system.
    Field `lambda` holds the wavelength (avoiding Lean's `λ` keyword). -/
structure ProjectionSystem where
  /-- EUV wavelength (m), ≈ 13.5e-9 -/
  lambda : ℝ
  lambda_pos : 0 < lambda
  /-- Numerical aperture (0 < NA < 1 in vacuum) -/
  NA : ℝ
  NA_pos : 0 < NA
  NA_lt_one : NA < 1
  /-- k₁ process factor (0.25 ≤ k₁ ≤ 0.8 typically) -/
  k₁ : ℝ
  k₁_pos : 0 < k₁
  /-- k₂ process factor (≈ 1 for coherent illumination) -/
  k₂ : ℝ
  k₂_pos : 0 < k₂
  /-- RMS wavefront error (m) -/
  W_rms : ℝ
  W_rms_nonneg : 0 ≤ W_rms

namespace ProjectionSystem

variable (ps : ProjectionSystem)

/-- Rayleigh resolution: R = k₁ λ / NA -/
def rayleighResolution : ℝ := ps.k₁ * ps.lambda / ps.NA

theorem rayleighResolution_pos : 0 < ps.rayleighResolution :=
  div_pos (mul_pos ps.k₁_pos ps.lambda_pos) ps.NA_pos

/-- Abbe diffraction limit: d_min = λ / (2 NA) -/
def abbeLimit : ℝ := ps.lambda / (2 * ps.NA)

theorem abbeLimit_pos : 0 < ps.abbeLimit :=
  div_pos ps.lambda_pos (mul_pos two_pos ps.NA_pos)

/-- Rayleigh resolution = 2 k₁ × Abbe limit -/
theorem rayleigh_vs_abbe : ps.rayleighResolution = 2 * ps.k₁ * ps.abbeLimit := by
  unfold rayleighResolution abbeLimit; field_simp

/-- Higher NA lowers the Abbe diffraction limit at fixed wavelength. -/
theorem abbeLimit_decreases_with_NA {NA₁ NA₂ : ℝ} (hNA₁ : 0 < NA₁)
    (hNA : NA₁ < NA₂)
    (ps₁ ps₂ : ProjectionSystem)
    (h_lam : ps₁.lambda = ps₂.lambda)
    (h_NA₁ : ps₁.NA = NA₁) (h_NA₂ : ps₂.NA = NA₂) :
    ps₂.abbeLimit < ps₁.abbeLimit := by
  unfold abbeLimit
  rw [h_NA₁, h_NA₂, h_lam]
  apply div_lt_div_of_pos_left ps₂.lambda_pos
  · exact mul_pos two_pos hNA₁
  exact mul_lt_mul_of_pos_left hNA two_pos

/-- Shorter wavelength lowers the Abbe diffraction limit at fixed NA. -/
theorem abbeLimit_decreases_with_wavelength {lam₁ lam₂ : ℝ}
    (hlam : lam₁ < lam₂)
    (ps₁ ps₂ : ProjectionSystem)
    (h_NA : ps₁.NA = ps₂.NA)
    (h_lam₁ : ps₁.lambda = lam₁) (h_lam₂ : ps₂.lambda = lam₂) :
    ps₁.abbeLimit < ps₂.abbeLimit := by
  unfold abbeLimit
  rw [h_NA, h_lam₁, h_lam₂]
  exact div_lt_div_of_pos_right hlam (mul_pos two_pos ps₂.NA_pos)

/-- Higher NA → better (smaller) resolution -/
theorem higher_NA_better_resolution {NA₁ NA₂ : ℝ} (hNA₁ : 0 < NA₁)
    (hlt : NA₁ < NA₂)
    (ps₁ ps₂ : ProjectionSystem)
    (h_lam : ps₁.lambda = ps₂.lambda)
    (h_k₁ : ps₁.k₁ = ps₂.k₁)
    (h_NA₁ : ps₁.NA = NA₁) (h_NA₂ : ps₂.NA = NA₂) :
    ps₂.rayleighResolution < ps₁.rayleighResolution := by
  unfold rayleighResolution
  rw [h_NA₁, h_NA₂, h_lam, h_k₁]
  exact div_lt_div_of_pos_left (mul_pos ps₂.k₁_pos ps₂.lambda_pos) hNA₁ hlt

/-- Shorter wavelength → better resolution (same NA, k₁) -/
theorem shorter_lambda_better_resolution {lam₁ lam₂ : ℝ}
    (hlt : lam₁ < lam₂)
    (ps₁ ps₂ : ProjectionSystem)
    (h_NA : ps₁.NA = ps₂.NA)
    (h_k₁ : ps₁.k₁ = ps₂.k₁)
    (h_lam₁ : ps₁.lambda = lam₁) (h_lam₂ : ps₂.lambda = lam₂) :
    ps₁.rayleighResolution < ps₂.rayleighResolution := by
  unfold rayleighResolution
  rw [h_NA, h_k₁, h_lam₁, h_lam₂]
  exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hlt ps₂.k₁_pos) ps₂.NA_pos

/-- Depth of focus: DoF = k₂ λ / NA² -/
def depthOfFocus : ℝ := ps.k₂ * ps.lambda / ps.NA ^ 2

theorem depthOfFocus_pos : 0 < ps.depthOfFocus :=
  div_pos (mul_pos ps.k₂_pos ps.lambda_pos) (sq_pos_of_pos ps.NA_pos)

/-- DoF–Resolution product: DoF × R = k₁ k₂ λ² / NA³ -/
theorem doF_resolution_product :
    ps.depthOfFocus * ps.rayleighResolution = ps.k₂ * ps.k₁ * ps.lambda ^ 2 / ps.NA ^ 3 := by
  unfold depthOfFocus rayleighResolution; field_simp

/-- DoF scales as NA⁻² -/
theorem doF_scales_as_NA_squared {NA₁ NA₂ : ℝ} (hNA₁ : 0 < NA₁) (hNA₂ : 0 < NA₂)
    (ps₁ ps₂ : ProjectionSystem)
    (h_lam : ps₁.lambda = ps₂.lambda) (h_k₂ : ps₁.k₂ = ps₂.k₂)
    (h_NA₁ : ps₁.NA = NA₁) (h_NA₂ : ps₂.NA = NA₂) :
    ps₁.depthOfFocus / ps₂.depthOfFocus = (NA₂ / NA₁) ^ 2 := by
  unfold depthOfFocus
  rw [h_NA₁, h_NA₂, h_lam, h_k₂]
  field_simp [ne_of_gt hNA₁, ne_of_gt hNA₂, ne_of_gt ps₂.k₂_pos, ne_of_gt ps₂.lambda_pos]

/-- Higher NA reduces depth of focus at fixed wavelength and k₂. -/
theorem higher_NA_smaller_depthOfFocus {NA₁ NA₂ : ℝ} (hNA₁ : 0 < NA₁)
    (hNA : NA₁ < NA₂)
    (ps₁ ps₂ : ProjectionSystem)
    (h_lam : ps₁.lambda = ps₂.lambda)
    (h_k₂ : ps₁.k₂ = ps₂.k₂)
    (h_NA₁ : ps₁.NA = NA₁) (h_NA₂ : ps₂.NA = NA₂) :
    ps₂.depthOfFocus < ps₁.depthOfFocus := by
  unfold depthOfFocus
  rw [h_NA₁, h_NA₂, h_lam, h_k₂]
  apply div_lt_div_of_pos_left (mul_pos ps₂.k₂_pos ps₂.lambda_pos)
  · exact sq_pos_of_pos hNA₁
  nlinarith [mul_pos hNA₁ hNA₁, mul_lt_mul_of_pos_left hNA hNA₁,
    mul_lt_mul_of_pos_right hNA (lt_trans hNA₁ hNA)]

/-- Strehl ratio: S = exp(-(2π W_rms/λ)²) — Maréchal approximation -/
def strehlRatio : ℝ := exp (-(2 * π * ps.W_rms / ps.lambda) ^ 2)

theorem strehlRatio_pos : 0 < ps.strehlRatio := exp_pos _

theorem strehlRatio_le_one : ps.strehlRatio ≤ 1 := by
  unfold strehlRatio
  rw [← exp_zero]
  exact exp_le_exp.mpr (neg_nonpos.mpr (sq_nonneg _))

/-- The exponential Maréchal Strehl is bounded below by its first-order approximation. -/
theorem marechal_first_order_lower_bound :
    1 - (2 * π * ps.W_rms / ps.lambda) ^ 2 ≤ ps.strehlRatio := by
  unfold strehlRatio
  have h := add_one_le_exp (-(2 * π * ps.W_rms / ps.lambda) ^ 2)
  nlinarith

/-- Strehl = 1 iff wavefront is perfect -/
theorem strehlRatio_one_iff_perfect : ps.strehlRatio = 1 ↔ ps.W_rms = 0 := by
  constructor
  · intro h
    unfold strehlRatio at h
    have heq : -(2 * π * ps.W_rms / ps.lambda) ^ 2 = 0 :=
      exp_injective (by simpa [exp_zero] using h)
    by_contra hW
    have hpos : 0 < ps.W_rms := lt_of_le_of_ne ps.W_rms_nonneg (Ne.symm hW)
    have : 0 < (2 * π * ps.W_rms / ps.lambda) ^ 2 :=
      sq_pos_of_pos (div_pos (mul_pos (mul_pos two_pos pi_pos) hpos) ps.lambda_pos)
    linarith
  · intro h; simp [strehlRatio, h]

/-- EUV wavefront requirement: W_rms < λ/60 -/
def euvWavefrontReq : Prop := ps.W_rms < ps.lambda / 60

/-- If W_rms < λ/60, the Maréchal approximation gives Strehl ratio > 0.98.
    The common informal `> 0.993` estimate is not valid at the endpoint λ/60:
    `exp(-(2π/60)^2) ≈ 0.989`. -/
theorem euv_strehl_gt_98 (h : ps.euvWavefrontReq) : ps.strehlRatio > 0.98 := by
  unfold strehlRatio euvWavefrontReq at *
  let x := (2 * π * ps.W_rms / ps.lambda) ^ 2
  have hW60 : 60 * ps.W_rms < ps.lambda := by nlinarith [h]
  have ha_nonneg : 0 ≤ 2 * π * ps.W_rms / ps.lambda :=
    div_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt pi_pos)) ps.W_rms_nonneg)
      (le_of_lt ps.lambda_pos)
  have ha_lt : 2 * π * ps.W_rms / ps.lambda < π / 30 := by
    rw [div_lt_iff₀ ps.lambda_pos]
    nlinarith [mul_lt_mul_of_pos_left hW60 pi_pos]
  have hx_lt_pi : x < (π / 30) ^ 2 := by
    have hdiff : 0 < (π / 30 - 2 * π * ps.W_rms / ps.lambda) *
        (π / 30 + 2 * π * ps.W_rms / ps.lambda) :=
      mul_pos (sub_pos.mpr ha_lt) (add_pos_of_pos_of_nonneg (div_pos pi_pos (by norm_num)) ha_nonneg)
    unfold x; nlinarith
  have hpi_bound : (π / 30) ^ 2 < (0.02 : ℝ) := by nlinarith [pi_pos, pi_le_four]
  have hx_lt : x < (0.02 : ℝ) := lt_trans hx_lt_pi hpi_bound
  have hexp_lower : 1 + (-x) ≤ exp (-x) := by simpa [add_comm] using add_one_le_exp (-x)
  have : (0.98 : ℝ) < exp (-x) := by nlinarith
  simpa [x] using this

/-- Mask-side NA: NA_mask = NA_wafer / demag -/
def maskNA (demag : ℝ) : ℝ := ps.NA / demag

theorem maskNA_pos {demag : ℝ} (hd : 0 < demag) : 0 < ps.maskNA demag :=
  div_pos ps.NA_pos hd

/-- Larger demagnification lowers mask-side NA for a fixed wafer-side NA. -/
theorem maskNA_decreases_with_demag {d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd : d₁ < d₂) :
    ps.maskNA d₂ < ps.maskNA d₁ := by
  unfold maskNA
  exact div_lt_div_of_pos_left ps.NA_pos hd₁ hd

/-- Four-times reduction optics place mask-side NA at one quarter of wafer-side NA. -/
theorem maskNA_fourX : ps.maskNA 4 = ps.NA / 4 := rfl

end ProjectionSystem

/-- Numerical aperture in a medium: `NA = n sin θ`. -/
def numericalAperture (n θ : ℝ) : ℝ := n * sin θ

theorem numericalAperture_pos {n θ : ℝ} (hn : 0 < n) (hsin : 0 < sin θ) :
    0 < numericalAperture n θ :=
  mul_pos hn hsin

/-- Abbe sine-condition algebra: if image-side NA is `m` times object-side NA,
    then object-side NA is image-side NA divided by magnification. -/
theorem abbeSine_NA_object_eq_image_div_magnification {NA_object NA_image m : ℝ}
    (hm : m ≠ 0) (h : NA_image = m * NA_object) :
    NA_object = NA_image / m := by
  rw [h]
  field_simp [hm]

/-- Coherent aerial-image intensity is the squared field magnitude. -/
def coherentIntensity (field : ℂ) : ℝ := ‖field‖ ^ 2

theorem coherentIntensity_nonneg (field : ℂ) :
    0 ≤ coherentIntensity field :=
  sq_nonneg _

theorem coherentIntensity_eq_zero_iff (field : ℂ) :
    coherentIntensity field = 0 ↔ field = 0 := by
  unfold coherentIntensity
  rw [sq_eq_zero_iff, norm_eq_zero]

/-- Finite-mode Zernike wavefront expansion `W = Σ c_nm Z_nm`. -/
def zernikeWavefront {ι : Type*} [Fintype ι] (coeff zernikeMode : ι → ℝ) : ℝ :=
  ∑ i, coeff i * zernikeMode i

theorem zernikeWavefront_zero_coeff {ι : Type*} [Fintype ι] (zernikeMode : ι → ℝ) :
    zernikeWavefront (fun _ : ι => 0) zernikeMode = 0 := by
  simp [zernikeWavefront]

theorem zernikeWavefront_add_coeff {ι : Type*} [Fintype ι]
    (c₁ c₂ zernikeMode : ι → ℝ) :
    zernikeWavefront (fun i => c₁ i + c₂ i) zernikeMode =
      zernikeWavefront c₁ zernikeMode + zernikeWavefront c₂ zernikeMode := by
  simp [zernikeWavefront, add_mul, Finset.sum_add_distrib]

/-- Finite-pupil coherent amplitude: a Riemann-sum analogue of `∫ U(f) e^{iφ(f)} df`. -/
def coherentPupilAmplitude {ι : Type*} [Fintype ι]
    (field phase weight : ι → ℂ) : ℂ :=
  ∑ f, weight f * field f * phase f

/-- Coherent aerial intensity from a finite pupil discretization. -/
def coherentPupilIntensity {ι : Type*} [Fintype ι]
    (field phase weight : ι → ℂ) : ℝ :=
  coherentIntensity (coherentPupilAmplitude field phase weight)

theorem coherentPupilIntensity_nonneg {ι : Type*} [Fintype ι]
    (field phase weight : ι → ℂ) :
    0 ≤ coherentPupilIntensity field phase weight :=
  coherentIntensity_nonneg _

theorem coherentPupilIntensity_zero_field {ι : Type*} [Fintype ι]
    (phase weight : ι → ℂ) :
    coherentPupilIntensity (fun _ : ι => 0) phase weight = 0 := by
  simp [coherentPupilIntensity, coherentPupilAmplitude, coherentIntensity]

end
