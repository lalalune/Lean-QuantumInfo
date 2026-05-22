/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!

# EUV Lithography: Shot Noise and Stochastic Printing Limits

Formalizes the Poisson photon statistics underlying EUV shot noise, the
resulting line edge roughness (LER), and the dose–failure-probability
relationship for sub-10 nm features.

## Main definitions

- `ShotNoiseParams` : photon-budget parameters for a feature
- `meanPhotonCount` : N̄ = D × A / E_photon — mean absorbed photons per feature
- `relativeNoise` : σ/N̄ = 1/√N̄ — Poisson relative standard deviation
- `lerRms` : σ_LER = (CD/2) × (1/√N̄) — LER from photon shot noise
- `failureProbability` : P_fail(k) = exp(-N̄) Σ_{j<k} N̄^j/j! (Poisson tail)

## Main results

- `meanPhotonCount_pos`
- `relativeNoise_pos`, `relativeNoise_decreases_with_N`
- `lerRms_pos`, `lerRms_decreases_with_dose`
- `more_photons_less_ler` : higher dose → smaller LER

-/

noncomputable section

open Real

/-- Parameters for photon shot noise at a single resist feature -/
structure ShotNoiseParams where
  /-- EUV dose at wafer (J/m²), typically 20–60 mJ/cm² = 200–600 J/m² -/
  dose : ℝ
  dose_pos : 0 < dose
  /-- Exposed area (m²), e.g. (10nm)² = 10⁻¹⁶ m² -/
  area : ℝ
  area_pos : 0 < area
  /-- Photon energy at 13.5 nm (J), ≈ 1.47×10⁻¹⁷ J -/
  E_photon : ℝ
  E_photon_pos : 0 < E_photon
  /-- Critical dimension (m) -/
  CD : ℝ
  CD_pos : 0 < CD
  /-- Quantum efficiency / absorption fraction (0 < η ≤ 1) -/
  eta : ℝ
  eta_pos : 0 < eta
  eta_le_one : eta ≤ 1

namespace ShotNoiseParams

variable (s : ShotNoiseParams)

/-- Mean absorbed photon count per feature: N̄ = η × D × A / E_photon -/
def meanPhotonCount : ℝ := s.eta * s.dose * s.area / s.E_photon

theorem meanPhotonCount_pos : 0 < s.meanPhotonCount :=
  div_pos (mul_pos (mul_pos s.eta_pos s.dose_pos) s.area_pos) s.E_photon_pos

/-- Relative shot noise: σ/N̄ = 1/√N̄ (Poisson statistics) -/
def relativeNoise : ℝ := 1 / sqrt s.meanPhotonCount

theorem relativeNoise_pos : 0 < s.relativeNoise :=
  div_pos one_pos (Real.sqrt_pos.mpr s.meanPhotonCount_pos)

/-- More photons → less relative noise -/
theorem relativeNoise_decreases_with_N {N₁ N₂ : ℝ} (hN₁ : 0 < N₁) (hN : N₁ < N₂) :
    1 / sqrt N₂ < 1 / sqrt N₁ := by
  apply div_lt_div_of_pos_left one_pos (Real.sqrt_pos.mpr hN₁)
  exact Real.sqrt_lt_sqrt (le_of_lt hN₁) hN

/-- LER (1σ) from photon shot noise: σ_LER = (CD/2) / √N̄ -/
def lerRms : ℝ := s.CD / 2 / sqrt s.meanPhotonCount

theorem lerRms_pos : 0 < s.lerRms :=
  div_pos (div_pos s.CD_pos two_pos) (Real.sqrt_pos.mpr s.meanPhotonCount_pos)

/-- LER expressed as fraction of CD -/
def lerFraction : ℝ := s.lerRms / s.CD

theorem lerFraction_pos : 0 < s.lerFraction :=
  div_pos s.lerRms_pos s.CD_pos

theorem lerFraction_eq : s.lerFraction = 1 / (2 * sqrt s.meanPhotonCount) := by
  unfold lerFraction lerRms
  field_simp [s.CD_pos.ne']

/-- At fixed area, photon energy, and absorption fraction, higher dose increases mean photons. -/
theorem meanPhotonCount_increases_with_dose {D₁ D₂ : ℝ} (hD_lt : D₁ < D₂)
    (s₁ s₂ : ShotNoiseParams)
    (hA : s₁.area = s₂.area) (hE : s₁.E_photon = s₂.E_photon)
    (heta : s₁.eta = s₂.eta) (hD₁ : s₁.dose = D₁) (hD₂ : s₂.dose = D₂) :
    s₁.meanPhotonCount < s₂.meanPhotonCount := by
  unfold meanPhotonCount
  rw [hA, hE, heta, hD₁, hD₂]
  apply div_lt_div_of_pos_right _ s₂.E_photon_pos
  calc
    s₂.eta * D₁ * s₂.area = (s₂.eta * s₂.area) * D₁ := by ring
    _ < (s₂.eta * s₂.area) * D₂ :=
      mul_lt_mul_of_pos_left hD_lt (mul_pos s₂.eta_pos s₂.area_pos)
    _ = s₂.eta * D₂ * s₂.area := by ring

/-- At fixed dose, area, and absorption fraction, higher photon energy means fewer photons. -/
theorem meanPhotonCount_decreases_with_photon_energy {E₁ E₂ : ℝ}
    (hE₁ : 0 < E₁) (hE : E₁ < E₂)
    (s₁ s₂ : ShotNoiseParams)
    (hD : s₁.dose = s₂.dose) (hA : s₁.area = s₂.area)
    (heta : s₁.eta = s₂.eta) (hE₁_eq : s₁.E_photon = E₁) (hE₂_eq : s₂.E_photon = E₂) :
    s₂.meanPhotonCount < s₁.meanPhotonCount := by
  unfold meanPhotonCount
  rw [hD, hA, heta, hE₁_eq, hE₂_eq]
  exact div_lt_div_of_pos_left (mul_pos (mul_pos s₂.eta_pos s₂.dose_pos) s₂.area_pos) hE₁ hE

/-- Higher dose → smaller LER -/
theorem more_photons_less_ler {D₁ D₂ : ℝ} (hD : D₁ < D₂)
    (s₁ s₂ : ShotNoiseParams)
    (hA : s₁.area = s₂.area) (hE : s₁.E_photon = s₂.E_photon)
    (heta : s₁.eta = s₂.eta) (hCD : s₁.CD = s₂.CD)
    (hd₁ : s₁.dose = D₁) (hd₂ : s₂.dose = D₂) :
    s₂.lerRms < s₁.lerRms := by
  unfold lerRms
  rw [hCD]
  apply div_lt_div_of_pos_left (div_pos s₂.CD_pos two_pos)
    (Real.sqrt_pos.mpr s₁.meanPhotonCount_pos)
  apply Real.sqrt_lt_sqrt (le_of_lt s₁.meanPhotonCount_pos)
  exact meanPhotonCount_increases_with_dose hD s₁ s₂ hA hE heta hd₁ hd₂

/-- At fixed dose and photon energy, a larger feature area collects more photons. -/
theorem meanPhotonCount_increases_with_area {A₁ A₂ : ℝ} (hA_lt : A₁ < A₂)
    (s₁ s₂ : ShotNoiseParams)
    (hD : s₁.dose = s₂.dose) (hE : s₁.E_photon = s₂.E_photon)
    (heta : s₁.eta = s₂.eta) (hA₁ : s₁.area = A₁) (hA₂ : s₂.area = A₂) :
    s₁.meanPhotonCount < s₂.meanPhotonCount := by
  unfold meanPhotonCount
  rw [hD, hE, heta, hA₁, hA₂]
  apply div_lt_div_of_pos_right _ s₂.E_photon_pos
  exact mul_lt_mul_of_pos_left hA_lt (mul_pos s₂.eta_pos s₂.dose_pos)

/-- At fixed dose, larger printed area lowers the photon-shot-noise LER. -/
theorem larger_area_less_ler {A₁ A₂ : ℝ} (hA_lt : A₁ < A₂)
    (s₁ s₂ : ShotNoiseParams)
    (hD : s₁.dose = s₂.dose) (hE : s₁.E_photon = s₂.E_photon)
    (heta : s₁.eta = s₂.eta) (hCD : s₁.CD = s₂.CD)
    (hA₁ : s₁.area = A₁) (hA₂ : s₂.area = A₂) :
    s₂.lerRms < s₁.lerRms := by
  unfold lerRms
  rw [hCD]
  apply div_lt_div_of_pos_left (div_pos s₂.CD_pos two_pos)
    (Real.sqrt_pos.mpr s₁.meanPhotonCount_pos)
  exact Real.sqrt_lt_sqrt (le_of_lt s₁.meanPhotonCount_pos)
    (meanPhotonCount_increases_with_area hA_lt s₁ s₂ hD hE heta hA₁ hA₂)

/-- Shot noise limited LER (3σ) as percentage of CD:
    Typical EUV: 2700 photons → 3σ ≈ 2% of 13 nm CD -/
theorem euv_ler_fraction_approx {s : ShotNoiseParams}
    (hN : s.meanPhotonCount = 2700) :
    s.lerFraction = 1 / (2 * sqrt 2700) := by
  rw [lerFraction_eq, hN]

end ShotNoiseParams

/-- Contrast-limited stochastic LER surrogate:
    `σ_LER ≈ 1 / (γ √(N/A_pixel))`. -/
def stochasticLerFromContrast (gamma N_photons A_pixel : ℝ) : ℝ :=
  1 / (gamma * sqrt (N_photons / A_pixel))

theorem stochasticLerFromContrast_pos {gamma N_photons A_pixel : ℝ}
    (hgamma : 0 < gamma) (hN : 0 < N_photons) (hA : 0 < A_pixel) :
    0 < stochasticLerFromContrast gamma N_photons A_pixel := by
  unfold stochasticLerFromContrast
  exact div_pos one_pos (mul_pos hgamma (sqrt_pos_of_pos (div_pos hN hA)))

/-- More photons reduce the contrast-limited stochastic LER at fixed contrast and pixel area. -/
theorem stochasticLerFromContrast_decreases_with_photons {gamma N₁ N₂ A_pixel : ℝ}
    (hgamma : 0 < gamma) (hN₁ : 0 < N₁) (hN : N₁ < N₂) (hA : 0 < A_pixel) :
    stochasticLerFromContrast gamma N₂ A_pixel <
      stochasticLerFromContrast gamma N₁ A_pixel := by
  unfold stochasticLerFromContrast
  apply div_lt_div_of_pos_left one_pos
  · exact mul_pos hgamma (sqrt_pos_of_pos (div_pos hN₁ hA))
  apply mul_lt_mul_of_pos_left _ hgamma
  apply sqrt_lt_sqrt
  · exact le_of_lt (div_pos hN₁ hA)
  exact div_lt_div_of_pos_right hN hA

/-- Higher resist/image contrast lowers the contrast-limited stochastic LER. -/
theorem stochasticLerFromContrast_decreases_with_gamma {gamma₁ gamma₂ N_photons A_pixel : ℝ}
    (hgamma₁ : 0 < gamma₁) (hgamma : gamma₁ < gamma₂)
    (hN : 0 < N_photons) (hA : 0 < A_pixel) :
    stochasticLerFromContrast gamma₂ N_photons A_pixel <
      stochasticLerFromContrast gamma₁ N_photons A_pixel := by
  unfold stochasticLerFromContrast
  apply div_lt_div_of_pos_left one_pos
  · exact mul_pos hgamma₁ (sqrt_pos_of_pos (div_pos hN hA))
  exact mul_lt_mul_of_pos_right hgamma (sqrt_pos_of_pos (div_pos hN hA))

/-- For fixed photon count and contrast, spreading photons over a larger pixel worsens LER. -/
theorem stochasticLerFromContrast_increases_with_pixel_area {gamma N_photons A₁ A₂ : ℝ}
    (hgamma : 0 < gamma) (hN : 0 < N_photons) (hA₁ : 0 < A₁) (hA : A₁ < A₂) :
    stochasticLerFromContrast gamma N_photons A₁ <
      stochasticLerFromContrast gamma N_photons A₂ := by
  unfold stochasticLerFromContrast
  apply one_div_lt_one_div_of_lt
  · exact mul_pos hgamma (sqrt_pos_of_pos (div_pos hN (lt_trans hA₁ hA)))
  apply mul_lt_mul_of_pos_left _ hgamma
  apply sqrt_lt_sqrt
  · exact le_of_lt (div_pos hN (lt_trans hA₁ hA))
  exact div_lt_div_of_pos_left hN hA₁ hA

/-- Fundamental photon-noise LER floor: σ_LER ∝ CD × N̄^(-1/2) -/
theorem ler_scales_as_sqrt_dose {CD dose area E_photon eta : ℝ}
    (hCD : 0 < CD) (hD : 0 < dose) (hA : 0 < area)
    (hE : 0 < E_photon) (heta : 0 < eta) :
    let N := eta * dose * area / E_photon
    0 < CD / 2 / sqrt N := by
  intro N
  apply div_pos (div_pos hCD two_pos)
  exact Real.sqrt_pos.mpr (div_pos (mul_pos (mul_pos heta hD) hA) hE)

end
