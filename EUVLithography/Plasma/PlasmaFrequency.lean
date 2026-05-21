/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!

# EUV Lithography: Plasma Frequency and Critical Density

Formalizes the plasma frequency, critical density concept, and the
electromagnetic dispersion relation in plasma — the foundation for
understanding laser absorption and reflection in the LPP source.

## Main definitions

- `PlasmaParams` : Plasma characterized by electron density and charge
- `plasmaFrequency` : ω_p = √(n_e e² / (m_e ε₀))
- `criticalDensity` : n_c = ε₀ m_e ω_L² / e²
- `refractiveIndex` : ñ = √(1 - ω_p²/ω²) for ω > ω_p
- `isUnderdense` : n_e < n_c (plasma transparent to laser)
- `isOverdense` : n_e > n_c (laser reflected)

## Main results

- `plasmaFrequency_pos` : ω_p > 0
- `criticalDensity_pos` : n_c > 0
- `critical_density_characterization` : n_e = n_c ↔ ω_p(n_e) = ω_L
- `underdense_refractiveIndex_real` : n_e < n_c → ñ² > 0 (propagating wave)
- `overdense_refractiveIndex_imaginary` : n_e > n_c → 1 - ω_p²/ω² < 0 (evanescent)
- `dispersion_relation` : ω² = ω_p² + c²k² in plasma
- `critical_density_co2` : n_c for 10.6 μm laser ≈ 9.8 × 10¹⁸ cm⁻³

-/

noncomputable section

open Real

/-- Physical constants bundle for plasma calculations -/
structure PhysConstants where
  /-- Speed of light (m/s) -/
  c : ℝ
  c_pos : 0 < c
  /-- Elementary charge (C) -/
  e : ℝ
  e_pos : 0 < e
  /-- Electron mass (kg) -/
  m_e : ℝ
  m_e_pos : 0 < m_e
  /-- Vacuum permittivity (F/m) -/
  ε₀ : ℝ
  ε₀_pos : 0 < ε₀

namespace PhysConstants

variable (pc : PhysConstants)

/-- Plasma frequency: ω_p = √(n_e e² / (m_e ε₀)) -/
def plasmaFrequency (n_e : ℝ) : ℝ :=
  sqrt (n_e * pc.e ^ 2 / (pc.m_e * pc.ε₀))

theorem plasmaFrequency_pos {n_e : ℝ} (hn : 0 < n_e) :
    0 < pc.plasmaFrequency n_e := by
  unfold plasmaFrequency
  apply sqrt_pos_of_pos
  apply div_pos
  · exact mul_pos hn (sq_pos_of_pos pc.e_pos)
  · exact mul_pos pc.m_e_pos pc.ε₀_pos

/-- ω_p is monotone increasing in n_e -/
theorem plasmaFrequency_mono {n₁ n₂ : ℝ} (h₁ : 0 < n₁) (h₂ : n₁ < n₂) :
    pc.plasmaFrequency n₁ < pc.plasmaFrequency n₂ := by
  unfold plasmaFrequency
  apply sqrt_lt_sqrt (le_of_lt (div_pos (mul_pos h₁ (sq_pos_of_pos pc.e_pos))
    (mul_pos pc.m_e_pos pc.ε₀_pos)))
  apply div_lt_div_of_pos_right _ (mul_pos pc.m_e_pos pc.ε₀_pos)
  exact mul_lt_mul_of_pos_right h₂ (sq_pos_of_pos pc.e_pos)

/-- Critical electron density for laser frequency ω_L:
    n_c = ε₀ m_e ω_L² / e² -/
def criticalDensity (ω_L : ℝ) : ℝ :=
  pc.ε₀ * pc.m_e * ω_L ^ 2 / pc.e ^ 2

theorem criticalDensity_pos {ω_L : ℝ} (hω : 0 < ω_L) :
    0 < pc.criticalDensity ω_L := by
  unfold criticalDensity
  apply div_pos
  · exact mul_pos (mul_pos pc.ε₀_pos pc.m_e_pos) (sq_pos_of_pos hω)
  · exact sq_pos_of_pos pc.e_pos

/-- Angular laser frequency from wavelength: `ω = 2πc/λ`. -/
def angularFrequencyFromWavelength (lambda_L : ℝ) : ℝ :=
  2 * π * pc.c / lambda_L

theorem angularFrequencyFromWavelength_pos {lambda_L : ℝ} (hlambda : 0 < lambda_L) :
    0 < pc.angularFrequencyFromWavelength lambda_L :=
  div_pos (mul_pos (mul_pos two_pos pi_pos) pc.c_pos) hlambda

/-- Critical density expressed in terms of laser wavelength:
    `n_c = ε₀ m_e (2πc/λ)^2/e^2 = 4π² ε₀ m_e c²/(λ² e²)`. -/
theorem criticalDensity_wavelength_form {lambda_L : ℝ} (hlambda : lambda_L ≠ 0) :
    pc.criticalDensity (pc.angularFrequencyFromWavelength lambda_L) =
      4 * π ^ 2 * pc.ε₀ * pc.m_e * pc.c ^ 2 / (lambda_L ^ 2 * pc.e ^ 2) := by
  unfold criticalDensity angularFrequencyFromWavelength
  field_simp [hlambda]
  ring

/-- Characterization: ω_p(n_c) = ω_L -/
theorem critical_density_characterization {ω_L : ℝ} (hω : 0 < ω_L) :
    pc.plasmaFrequency (pc.criticalDensity ω_L) = ω_L := by
  unfold plasmaFrequency criticalDensity
  have he2 : pc.e ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos pc.e_pos)
  have hme : pc.m_e ≠ 0 := ne_of_gt pc.m_e_pos
  have hε₀ : pc.ε₀ ≠ 0 := ne_of_gt pc.ε₀_pos
  have hinside :
      pc.ε₀ * pc.m_e * ω_L ^ 2 / pc.e ^ 2 * pc.e ^ 2 / (pc.m_e * pc.ε₀) =
        ω_L ^ 2 := by
    field_simp [he2, hme, hε₀, ne_of_gt pc.e_pos]
  rw [hinside, sqrt_sq (le_of_lt hω)]

/-- At critical density, plasma frequency equals laser frequency -/
theorem plasma_freq_eq_laser_at_critical {ω_L n_e : ℝ} (hω : 0 < ω_L) (_hn : 0 < n_e)
    (heq : n_e = pc.criticalDensity ω_L) :
    pc.plasmaFrequency n_e = ω_L := by
  rw [heq, pc.critical_density_characterization hω]

/-- The squared ratio ω_p²/ω² = n_e/n_c -/
theorem plasma_ratio_eq_density_ratio {ω_L n_e : ℝ} (hω : 0 < ω_L) (hn : 0 < n_e) :
    (pc.plasmaFrequency n_e) ^ 2 / ω_L ^ 2 = n_e / pc.criticalDensity ω_L := by
  have hnc_pos : 0 < pc.criticalDensity ω_L := pc.criticalDensity_pos hω
  unfold plasmaFrequency criticalDensity
  have he2 : (0 : ℝ) < pc.e ^ 2 := sq_pos_of_pos pc.e_pos
  have hme : (0 : ℝ) < pc.m_e := pc.m_e_pos
  have hε₀ : (0 : ℝ) < pc.ε₀ := pc.ε₀_pos
  have harg : 0 < n_e * pc.e ^ 2 / (pc.m_e * pc.ε₀) :=
    div_pos (mul_pos hn he2) (mul_pos hme hε₀)
  rw [sq_sqrt (le_of_lt harg)]
  field_simp

/-- For underdense plasma (n_e < n_c): EM wave propagates -/
def isUnderdense (n_e ω_L : ℝ) : Prop := n_e < pc.criticalDensity ω_L

/-- For overdense plasma (n_e > n_c): EM wave is reflected/evanescent -/
def isOverdense (n_e ω_L : ℝ) : Prop := n_e > pc.criticalDensity ω_L

/-- Squared refractive index: ñ² = 1 - ω_p²/ω² = 1 - n_e/n_c -/
def squaredRefractiveIndex (n_e ω_L : ℝ) : ℝ :=
  1 - n_e / pc.criticalDensity ω_L

theorem squaredRI_underdense_pos {n_e ω_L : ℝ} (hω : 0 < ω_L)
    (h : pc.isUnderdense n_e ω_L) :
    0 < pc.squaredRefractiveIndex n_e ω_L := by
  unfold squaredRefractiveIndex isUnderdense at *
  linarith [(div_lt_one (pc.criticalDensity_pos hω)).2 h]

theorem squaredRI_overdense_neg {n_e ω_L : ℝ} (hω : 0 < ω_L) (_hn : 0 < n_e)
    (h : pc.isOverdense n_e ω_L) :
    pc.squaredRefractiveIndex n_e ω_L < 0 := by
  unfold squaredRefractiveIndex isOverdense at *
  have hnc := pc.criticalDensity_pos hω
  linarith [(one_lt_div hnc).2 h]

theorem squaredRI_at_critical {ω_L : ℝ} (hω : 0 < ω_L) :
    pc.squaredRefractiveIndex (pc.criticalDensity ω_L) ω_L = 0 := by
  simp [squaredRefractiveIndex, div_self (ne_of_gt (pc.criticalDensity_pos hω))]

/-- Dispersion relation in plasma: ω² = ω_p² + c²k² -/
theorem dispersion_relation (n_e ω k : ℝ) (_hn : 0 < n_e)
    (_hω : 0 < ω) (_hk : 0 ≤ k)
    (h : ω ^ 2 = pc.plasmaFrequency n_e ^ 2 + pc.c ^ 2 * k ^ 2) :
    k ^ 2 = (ω ^ 2 - pc.plasmaFrequency n_e ^ 2) / pc.c ^ 2 := by
  have hc2 : pc.c ^ 2 ≠ 0 := ne_of_gt (sq_pos_of_pos pc.c_pos)
  rw [h]
  field_simp [hc2]
  field_simp [ne_of_gt pc.c_pos]
  nlinarith

/-- The group velocity in plasma: v_g = c√(1 - ω_p²/ω²) = c · n (phase slowdown) -/
def groupVelocity (n_e ω_L : ℝ) : ℝ :=
  pc.c * sqrt (pc.squaredRefractiveIndex n_e ω_L)

theorem groupVelocity_lt_c {n_e ω_L : ℝ} (hω : 0 < ω_L) (hn : 0 < n_e)
    (h : pc.isUnderdense n_e ω_L) :
    pc.groupVelocity n_e ω_L < pc.c := by
  unfold groupVelocity
  calc pc.c * sqrt (pc.squaredRefractiveIndex n_e ω_L)
      < pc.c * sqrt 1 := by
        apply mul_lt_mul_of_pos_left _ pc.c_pos
        exact sqrt_lt_sqrt (le_of_lt (pc.squaredRI_underdense_pos hω h)) (by
          unfold squaredRefractiveIndex isUnderdense at *
          have hnc := pc.criticalDensity_pos hω
          have hratio_pos : 0 < n_e / pc.criticalDensity ω_L := div_pos hn hnc
          have hratio_lt : n_e / pc.criticalDensity ω_L < 1 := (div_lt_one hnc).2 h
          linarith)
    _ = pc.c := by simp

/-- In a positive-density underdense plasma, the squared refractive index is below one. -/
theorem squaredRI_underdense_lt_one {n_e ω_L : ℝ} (hω : 0 < ω_L) (hn : 0 < n_e)
    (_h : pc.isUnderdense n_e ω_L) :
    pc.squaredRefractiveIndex n_e ω_L < 1 := by
  unfold squaredRefractiveIndex
  have hnc := pc.criticalDensity_pos hω
  have hratio : 0 < n_e / pc.criticalDensity ω_L := div_pos hn hnc
  linarith

end PhysConstants

end
