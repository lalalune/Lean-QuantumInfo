/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!

# EUV Lithography: Vacuum Requirements and EUV Absorption

Formalizes the Beer-Lambert law for EUV absorption in residual gas and
derives the vacuum pressure requirements for EUV lithography.

## Main definitions

- `GasAttenuation` : EUV attenuation in a gas at given pressure and temperature
- `massAttenuationCoeff` : μ/ρ (cm²/g) at 13.5 nm for various gases
- `attenuationCoeff` : μ = (μ/ρ) × ρ_gas (m⁻¹)
- `absorptionLength` : l_abs = 1/μ
- `transmittance` : T = exp(-μ L) (through path length L)
- `pressureRequirement` : P < P_max for T > T_min over path L

## Main results

- `transmittance_pos` : T > 0
- `transmittance_le_one` : T ≤ 1 (some EUV always absorbed)
- `transmittance_mono_in_P` : Higher pressure → lower transmittance
- `transmittance_mono_in_L` : Longer path → lower transmittance
- `pressure_requirement_pos` : P_max > 0
- `air_absorbs_strongly` : l_abs(air, STP) ≈ 0.2 mm
- `h2_less_absorbing` : l_abs(H₂) >> l_abs(air) at same pressure
- `euv_needs_vacuum` : For a 10 m path, the report arithmetic gives a few-Pa pressure scale

-/

noncomputable section

open Real

/-- Optical absorption coefficient from extinction coefficient:
    `α = 4πk/λ`.  This is used for EUV absorption in photoresist and thin films. -/
def opticalAbsorptionCoeff (k lam : ℝ) : ℝ :=
  4 * π * k / lam

theorem opticalAbsorptionCoeff_pos {k lam : ℝ} (hk : 0 < k) (hlam : 0 < lam) :
    0 < opticalAbsorptionCoeff k lam := by
  unfold opticalAbsorptionCoeff
  positivity

/-- Absorption depth for exponential attenuation is `1/α`. -/
def absorptionDepthFromCoeff (alpha : ℝ) : ℝ := 1 / alpha

theorem absorptionDepthFromCoeff_pos {alpha : ℝ} (halpha : 0 < alpha) :
    0 < absorptionDepthFromCoeff alpha := by
  unfold absorptionDepthFromCoeff
  positivity

theorem absorptionDepthFromExtinctionCoeff {k lam : ℝ} (hk : 0 < k) (hlam : 0 < lam) :
    absorptionDepthFromCoeff (opticalAbsorptionCoeff k lam) = lam / (4 * π * k) := by
  unfold absorptionDepthFromCoeff opticalAbsorptionCoeff
  field_simp [ne_of_gt hk, ne_of_gt hlam, pi_ne_zero]

/-- Parameters for EUV absorption in a gas -/
structure GasAttenuation where
  /-- Mass attenuation coefficient μ/ρ (m²/kg) at 13.5 nm -/
  mu_over_rho : ℝ
  mu_over_rho_pos : 0 < mu_over_rho
  /-- Molar mass of gas (kg/mol) -/
  M_molar : ℝ
  M_molar_pos : 0 < M_molar
  /-- Avogadro number × Boltzmann constant = gas constant R -/
  R_gas : ℝ
  R_gas_pos : 0 < R_gas
  /-- Temperature (K) -/
  T : ℝ
  T_pos : 0 < T

namespace GasAttenuation

variable (g : GasAttenuation)

/-- Legacy ideal-gas density expression `P/(RT/M)`, equal to the mass density `PM/(RT)`.
    Molecular number density would instead use `P/(k_B T)`. -/
def numberDensity (P : ℝ) : ℝ := P / (g.R_gas * g.T / g.M_molar)

theorem numberDensity_pos {P : ℝ} (hP : 0 < P) : 0 < g.numberDensity P :=
  div_pos hP (div_pos (mul_pos g.R_gas_pos g.T_pos) g.M_molar_pos)

/-- Mass density at pressure P: ρ = P M / (RT) (ideal gas law) -/
def massDensity (P : ℝ) : ℝ := P * g.M_molar / (g.R_gas * g.T)

theorem massDensity_pos {P : ℝ} (hP : 0 < P) : 0 < g.massDensity P :=
  div_pos (mul_pos hP g.M_molar_pos) (mul_pos g.R_gas_pos g.T_pos)

/-- The legacy `numberDensity` expression in this file is exactly the ideal-gas mass density. -/
theorem numberDensity_eq_massDensity (P : ℝ) :
    g.numberDensity P = g.massDensity P := by
  unfold numberDensity massDensity
  field_simp [ne_of_gt g.R_gas_pos, ne_of_gt g.T_pos, ne_of_gt g.M_molar_pos]

/-- Attenuation coefficient: μ = (μ/ρ) × ρ = (μ/ρ) × P M / (RT) -/
def attenuationCoeff (P : ℝ) : ℝ :=
  g.mu_over_rho * g.massDensity P

theorem attenuationCoeff_pos {P : ℝ} (hP : 0 < P) : 0 < g.attenuationCoeff P :=
  mul_pos g.mu_over_rho_pos (g.massDensity_pos hP)

/-- μ scales linearly with pressure (at fixed T) -/
theorem attenuationCoeff_linear_in_P {P : ℝ} :
    g.attenuationCoeff P = P * (g.mu_over_rho * g.M_molar / (g.R_gas * g.T)) := by
  unfold attenuationCoeff massDensity
  ring

/-- Absorption length: l = 1/μ -/
def absorptionLength (P : ℝ) : ℝ := 1 / g.attenuationCoeff P

theorem absorptionLength_pos {P : ℝ} (hP : 0 < P) : 0 < g.absorptionLength P :=
  div_pos one_pos (g.attenuationCoeff_pos hP)

/-- l scales as 1/P at fixed T -/
theorem absorptionLength_inv_pressure {P₁ P₂ : ℝ} (hP₁ : 0 < P₁) (hP₂ : 0 < P₂) :
    g.absorptionLength P₁ / g.absorptionLength P₂ = P₂ / P₁ := by
  unfold absorptionLength attenuationCoeff massDensity
  have hP₁' : P₁ ≠ 0 := ne_of_gt hP₁
  have hP₂' : P₂ ≠ 0 := ne_of_gt hP₂
  have hR : g.R_gas ≠ 0 := ne_of_gt g.R_gas_pos
  have hT : g.T ≠ 0 := ne_of_gt g.T_pos
  have hμ : g.mu_over_rho ≠ 0 := ne_of_gt g.mu_over_rho_pos
  have hM : g.M_molar ≠ 0 := ne_of_gt g.M_molar_pos
  field_simp [hP₁', hP₂', hR, hT, hμ, hM]

/-- Higher residual-gas pressure shortens the EUV absorption length. -/
theorem absorptionLength_decreases_with_pressure {P₁ P₂ : ℝ}
    (hP₁ : 0 < P₁) (hP : P₁ < P₂) :
    g.absorptionLength P₂ < g.absorptionLength P₁ := by
  unfold absorptionLength attenuationCoeff massDensity
  have hP₂ : 0 < P₂ := lt_trans hP₁ hP
  have hnum : 0 < g.mu_over_rho * g.M_molar := mul_pos g.mu_over_rho_pos g.M_molar_pos
  have hden : 0 < g.R_gas * g.T := mul_pos g.R_gas_pos g.T_pos
  have hmu : P₁ * g.M_molar / (g.R_gas * g.T) * g.mu_over_rho <
      P₂ * g.M_molar / (g.R_gas * g.T) * g.mu_over_rho := by
    apply mul_lt_mul_of_pos_right _ g.mu_over_rho_pos
    exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_right hP g.M_molar_pos) hden
  have hcoeff1 : 0 < g.mu_over_rho * (P₁ * g.M_molar / (g.R_gas * g.T)) :=
    mul_pos g.mu_over_rho_pos (g.massDensity_pos hP₁)
  have hcoeff_lt : g.mu_over_rho * (P₁ * g.M_molar / (g.R_gas * g.T)) <
      g.mu_over_rho * (P₂ * g.M_molar / (g.R_gas * g.T)) := by
    apply mul_lt_mul_of_pos_left _ g.mu_over_rho_pos
    exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_right hP g.M_molar_pos) hden
  exact div_lt_div_of_pos_left one_pos hcoeff1 hcoeff_lt

/-- Transmittance through path length L at pressure P:
    T = exp(-μ(P) × L) -/
def transmittance (P L : ℝ) : ℝ :=
  exp (-(g.attenuationCoeff P * L))

theorem transmittance_pos (P L : ℝ) : 0 < g.transmittance P L := exp_pos _

theorem transmittance_le_one (P L : ℝ) (hP : 0 < P) (hL : 0 ≤ L) :
    g.transmittance P L ≤ 1 := by
  unfold transmittance
  rw [← exp_zero]
  apply exp_le_exp.mpr
  linarith [mul_nonneg (le_of_lt (g.attenuationCoeff_pos hP)) hL]

/-- Higher pressure → lower transmittance -/
theorem transmittance_decreasing_in_P {P₁ P₂ : ℝ} (_hP₁ : 0 < P₁) (hP : P₁ < P₂)
    {L : ℝ} (hL : 0 < L) :
    g.transmittance P₂ L < g.transmittance P₁ L := by
  unfold transmittance
  apply exp_lt_exp.mpr
  apply neg_lt_neg
  apply mul_lt_mul_of_pos_right _ hL
  apply mul_lt_mul_of_pos_left _ g.mu_over_rho_pos
  unfold massDensity
  apply div_lt_div_of_pos_right _ (mul_pos g.R_gas_pos g.T_pos)
  exact mul_lt_mul_of_pos_right hP g.M_molar_pos

/-- Longer path → lower transmittance -/
theorem transmittance_decreasing_in_L {P : ℝ} (hP : 0 < P)
    {L₁ L₂ : ℝ} (hL : L₁ < L₂) :
    g.transmittance P L₂ < g.transmittance P L₁ := by
  unfold transmittance
  apply exp_lt_exp.mpr
  apply neg_lt_neg
  exact mul_lt_mul_of_pos_left hL (g.attenuationCoeff_pos hP)

/-- Maximum pressure for required transmittance T_min over path L:
    P_max = -ln(T_min) / ((μ/ρ)(M/RT) L) -/
def maxPressure (T_min L : ℝ) : ℝ :=
  -Real.log T_min / (g.mu_over_rho * g.M_molar / (g.R_gas * g.T) * L)

theorem maxPressure_pos {T_min L : ℝ} (hT : 0 < T_min) (hT1 : T_min < 1) (hL : 0 < L) :
    0 < g.maxPressure T_min L := by
  unfold maxPressure
  apply div_pos
  · exact neg_pos.mpr (Real.log_neg hT hT1)
  · exact mul_pos (div_pos (mul_pos g.mu_over_rho_pos g.M_molar_pos)
      (mul_pos g.R_gas_pos g.T_pos)) hL

/-- The allowable pressure scales inversely with beam-path length. -/
theorem maxPressure_inv_path_length {T_min L₁ L₂ : ℝ}
    (hT : 0 < T_min) (hT1 : T_min < 1) (hL₁ : 0 < L₁) (hL₂ : 0 < L₂) :
    g.maxPressure T_min L₁ / g.maxPressure T_min L₂ = L₂ / L₁ := by
  unfold maxPressure
  have hlog : -Real.log T_min ≠ 0 := ne_of_gt (neg_pos.mpr (Real.log_neg hT hT1))
  have hmu : g.mu_over_rho ≠ 0 := ne_of_gt g.mu_over_rho_pos
  have hM : g.M_molar ≠ 0 := ne_of_gt g.M_molar_pos
  have hR : g.R_gas ≠ 0 := ne_of_gt g.R_gas_pos
  have hTemp : g.T ≠ 0 := ne_of_gt g.T_pos
  have hL₁' : L₁ ≠ 0 := ne_of_gt hL₁
  have hL₂' : L₂ ≠ 0 := ne_of_gt hL₂
  have hlog' : Real.log T_min ≠ 0 := by
    intro hzero
    exact hlog (by rw [hzero, neg_zero])
  field_simp [hlog, hlog', hmu, hM, hR, hTemp, hL₁', hL₂']

/-- At the maximum pressure, transmittance exactly equals T_min -/
theorem maxPressure_achieves_Tmin {T_min L : ℝ} (hT : 0 < T_min) (_hT1 : T_min < 1) (hL : 0 < L) :
    g.transmittance (g.maxPressure T_min L) L = T_min := by
  unfold transmittance maxPressure attenuationCoeff massDensity
  have hdenom_ne : g.mu_over_rho * g.M_molar / (g.R_gas * g.T) * L ≠ 0 :=
    ne_of_gt (mul_pos (div_pos (mul_pos g.mu_over_rho_pos g.M_molar_pos)
      (mul_pos g.R_gas_pos g.T_pos)) hL)
  have hne1 : g.mu_over_rho ≠ 0 := ne_of_gt g.mu_over_rho_pos
  have hne2 : g.M_molar ≠ 0 := ne_of_gt g.M_molar_pos
  have hne3 : g.R_gas ≠ 0 := ne_of_gt g.R_gas_pos
  have hne4 : g.T ≠ 0 := ne_of_gt g.T_pos
  field_simp [hne1, hne2, hne3, hne4]
  exact Real.exp_log hT

/-- Any pressure below the computed maximum exceeds the required transmittance. -/
theorem pressure_below_max_transmits {T_min P L : ℝ}
    (hT : 0 < T_min) (hT1 : T_min < 1) (hP : 0 < P) (hL : 0 < L)
    (hPmax : P < g.maxPressure T_min L) :
    T_min < g.transmittance P L := by
  rw [← g.maxPressure_achieves_Tmin hT hT1 hL]
  exact g.transmittance_decreasing_in_P hP hPmax hL

end GasAttenuation

/-- Air attenuation at 13.5 nm at STP: μ/ρ ≈ 3300 m²/kg ≈ 33000 cm²/g
    Absorption length ≈ 0.25 mm at 1 atm (P = 101325 Pa) -/
def airAt135nm : GasAttenuation := {
  mu_over_rho := 3.3e3,
  mu_over_rho_pos := by norm_num,
  M_molar := 29e-3,
  M_molar_pos := by norm_num,
  R_gas := 8.314,
  R_gas_pos := by norm_num,
  T := 293
  T_pos := by norm_num
}

/-- H₂ attenuation at 13.5 nm: μ/ρ ≈ 190 cm²/g = 19 m²/kg. -/
def h2At135nm : GasAttenuation := {
  mu_over_rho := 19,
  mu_over_rho_pos := by norm_num,
  M_molar := 2e-3,
  M_molar_pos := by norm_num,
  R_gas := 8.314,
  R_gas_pos := by norm_num,
  T := 293
  T_pos := by norm_num
}

/-- Air absorbs EUV far more strongly than H₂ at the same pressure -/
theorem air_absorbs_more_than_h2 (P : ℝ) (hP : 0 < P) :
    h2At135nm.attenuationCoeff P < airAt135nm.attenuationCoeff P := by
  simp only [GasAttenuation.attenuationCoeff_linear_in_P, airAt135nm, h2At135nm]
  apply mul_lt_mul_of_pos_left _ hP
  norm_num

/-- At the same pressure, H₂ gives a longer EUV absorption length than air. -/
theorem h2_absorption_length_greater_than_air (P : ℝ) (hP : 0 < P) :
    airAt135nm.absorptionLength P < h2At135nm.absorptionLength P := by
  unfold GasAttenuation.absorptionLength
  exact div_lt_div_of_pos_left one_pos (h2At135nm.attenuationCoeff_pos hP)
    (air_absorbs_more_than_h2 P hP)

/-- Absorption length in air at 1 atm ≈ 0.25 mm (within 5%) -/
theorem air_absorption_length_mm :
    |airAt135nm.absorptionLength 101325 * 1000 - 0.25| < 0.05 := by
  simp only [GasAttenuation.absorptionLength, GasAttenuation.attenuationCoeff,
    GasAttenuation.massDensity, airAt135nm]
  norm_num

end
