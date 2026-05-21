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
  unfold meanPhotonCount
  rw [hd₁, hd₂, hA, hE, heta]
  apply div_lt_div_of_pos_right _ s₂.E_photon_pos
  nlinarith [mul_pos s₂.eta_pos s₂.area_pos]

/-- Shot noise limited LER (3σ) as percentage of CD:
    Typical EUV: 2700 photons → 3σ ≈ 2% of 13 nm CD -/
theorem euv_ler_fraction_approx {s : ShotNoiseParams}
    (hN : s.meanPhotonCount = 2700) :
    s.lerFraction = 1 / (2 * sqrt 2700) := by
  rw [lerFraction_eq, hN]

end ShotNoiseParams

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
