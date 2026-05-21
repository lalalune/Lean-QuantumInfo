/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!

# EUV Lithography: Acid Diffusion in Chemically Amplified Resist

Formalizes the Fickian diffusion of photo-generated acid during post-exposure
bake (PEB), including the diffusion length, Gaussian blur kernel, and the
effect of diffusion on image contrast.

## Main definitions

- `AcidDiffusionParams` : PEB diffusion parameters
- `diffusionLength` : σ = √(2 D t_PEB) — Gaussian blur radius
- `gaussianKernel` : G(x) = (4πDt)^(-1/2) exp(-x²/(4Dt))
- `contrastAttenuation` : exp(-2π² σ² / p²) — Gaussian OTF at pitch p

## Main results

- `diffusionLength_pos`, `diffusionLength_mono`, `diffusionLength_sq`
- `gaussianKernel_pos`
- `contrastAttenuation_pos`, `contrastAttenuation_le_one`
- `contrastAttenuation_mono_in_sigma` : larger σ → worse contrast

-/

noncomputable section

open Real

/-- Parameters for acid diffusion during post-exposure bake -/
structure AcidDiffusionParams where
  /-- Acid diffusion coefficient (m²/s), typically 10–50 nm²/s -/
  D : ℝ
  D_pos : 0 < D
  /-- PEB time (s), typically 60–120 s -/
  t_PEB : ℝ
  t_PEB_pos : 0 < t_PEB

namespace AcidDiffusionParams

variable (p : AcidDiffusionParams)

/-- Diffusion length (Gaussian 1σ blur radius): σ = √(2 D t_PEB) -/
def diffusionLength : ℝ := sqrt (2 * p.D * p.t_PEB)

theorem diffusionLength_pos : 0 < p.diffusionLength := by
  unfold diffusionLength
  exact Real.sqrt_pos.mpr (mul_pos (mul_pos two_pos p.D_pos) p.t_PEB_pos)

theorem diffusionLength_nonneg : 0 ≤ p.diffusionLength :=
  le_of_lt p.diffusionLength_pos

theorem diffusionLength_sq : p.diffusionLength ^ 2 = 2 * p.D * p.t_PEB := by
  unfold diffusionLength
  rw [sq_sqrt (le_of_lt (mul_pos (mul_pos two_pos p.D_pos) p.t_PEB_pos))]

/-- Longer PEB → larger diffusion length -/
theorem diffusionLength_mono {t₁ t₂ : ℝ} (ht₁ : 0 < t₁) (ht : t₁ < t₂)
    (p₁ p₂ : AcidDiffusionParams)
    (hD : p₁.D = p₂.D) (ht₁' : p₁.t_PEB = t₁) (ht₂' : p₂.t_PEB = t₂) :
    p₁.diffusionLength < p₂.diffusionLength := by
  unfold diffusionLength
  rw [ht₁', ht₂', hD]
  apply Real.sqrt_lt_sqrt
  · exact le_of_lt (mul_pos (mul_pos two_pos p₂.D_pos) ht₁)
  · exact mul_lt_mul_of_pos_left ht (mul_pos two_pos p₂.D_pos)

/-- Higher diffusivity → larger diffusion length -/
theorem diffusionLength_mono_D {D₁ D₂ : ℝ} (hD₁ : 0 < D₁) (hD : D₁ < D₂)
    (p₁ p₂ : AcidDiffusionParams)
    (ht : p₁.t_PEB = p₂.t_PEB) (hD₁' : p₁.D = D₁) (hD₂' : p₂.D = D₂) :
    p₁.diffusionLength < p₂.diffusionLength := by
  unfold diffusionLength
  rw [hD₁', hD₂', ht]
  apply Real.sqrt_lt_sqrt
  · exact le_of_lt (mul_pos (mul_pos two_pos hD₁) p₂.t_PEB_pos)
  · exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hD two_pos) p₂.t_PEB_pos

/-- Gaussian PSF kernel at position x: G(x) = (4πDt)^(-1/2) exp(-x²/(4Dt)) -/
def gaussianKernel (x : ℝ) : ℝ :=
  (1 / sqrt (4 * π * p.D * p.t_PEB)) * exp (-(x ^ 2 / (4 * p.D * p.t_PEB)))

theorem gaussianKernel_pos (x : ℝ) : 0 < p.gaussianKernel x := by
  unfold gaussianKernel
  apply mul_pos
  · apply div_pos one_pos
    exact Real.sqrt_pos.mpr
      (mul_pos (mul_pos (mul_pos (by norm_num) pi_pos) p.D_pos) p.t_PEB_pos)
  · exact exp_pos _

/-- Three-dimensional point-source Gaussian acid cloud:
    `N₀/(4πDt)^(3/2) * exp(-r²/(4Dt))`. -/
def gaussianPointSource3D (N₀ r : ℝ) : ℝ :=
  N₀ / (4 * π * p.D * p.t_PEB) ^ (3 / 2 : ℝ) *
    exp (-(r ^ 2 / (4 * p.D * p.t_PEB)))

theorem gaussianPointSource3D_pos {N₀ r : ℝ} (hN₀ : 0 < N₀) :
    0 < p.gaussianPointSource3D N₀ r := by
  unfold gaussianPointSource3D
  apply mul_pos
  · apply div_pos hN₀
    apply Real.rpow_pos_of_pos
    exact mul_pos (mul_pos (mul_pos (by norm_num) pi_pos) p.D_pos) p.t_PEB_pos
  · exact exp_pos _

theorem gaussianPointSource3D_linear_in_source {N₁ N₂ r : ℝ}
    (hN : N₁ < N₂) :
    p.gaussianPointSource3D N₁ r < p.gaussianPointSource3D N₂ r := by
  unfold gaussianPointSource3D
  apply mul_lt_mul_of_pos_right _ (exp_pos _)
  apply div_lt_div_of_pos_right
  · exact hN
  · apply Real.rpow_pos_of_pos
    exact mul_pos (mul_pos (mul_pos (by norm_num) pi_pos) p.D_pos) p.t_PEB_pos

/-- Contrast attenuation (Gaussian OTF) at pitch p: exp(-2π²σ²/p²) -/
def contrastAttenuation (pitch : ℝ) : ℝ :=
  exp (-(2 * π ^ 2 * p.diffusionLength ^ 2 / pitch ^ 2))

theorem contrastAttenuation_pos (pitch : ℝ) : 0 < p.contrastAttenuation pitch :=
  exp_pos _

theorem contrastAttenuation_le_one (pitch : ℝ) :
    p.contrastAttenuation pitch ≤ 1 := by
  unfold contrastAttenuation
  rw [← exp_zero]
  apply exp_le_exp.mpr
  apply neg_nonpos.mpr
  apply div_nonneg
  · exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  · exact sq_nonneg _

/-- Larger diffusion length → weaker contrast at fixed pitch -/
theorem contrastAttenuation_mono_in_sigma {σ₁ σ₂ pitch : ℝ}
    (hσ₁ : 0 < σ₁) (hσ : σ₁ < σ₂) (hpitch : 0 < pitch) :
    exp (-(2 * π ^ 2 * σ₂ ^ 2 / pitch ^ 2)) < exp (-(2 * π ^ 2 * σ₁ ^ 2 / pitch ^ 2)) := by
  apply exp_lt_exp.mpr
  apply neg_lt_neg
  apply div_lt_div_of_pos_right _ (sq_pos_of_pos hpitch)
  apply mul_lt_mul_of_pos_left _ (mul_pos two_pos (sq_pos_of_pos pi_pos))
  exact sq_lt_sq' (by linarith) hσ

end AcidDiffusionParams

end
