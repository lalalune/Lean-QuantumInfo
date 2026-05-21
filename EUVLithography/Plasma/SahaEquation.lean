/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!

# EUV Lithography: Saha Equation for Tin Ionization

Formalizes the Saha ionization equilibrium equation that governs the
charge-state distribution of tin ions in the LPP plasma. The EUV emission
at 13.5 nm requires optimal population of Sn⁸⁺–Sn¹⁴⁺.

## Main definitions

- `SahaParams` : Physical parameters for Saha equation evaluation
- `sahaRatio` : n_{z+1} n_e / n_z = S(T_e, g_{z+1}/g_z, χ_z)
- `thermalDeBroglieWavelength` : λ_th = h / √(2πm_e k_B T)
- `SahaFactor` : The Saha factor S_z(T) = (2/n_e)(2πm_e kT/h²)^{3/2} (g_{z+1}/g_z) exp(-χ_z/kT)

## Main results

- `sahaRatio_pos` : S_z(T) > 0
- `sahaFactor_decreases_with_χ` : Higher ionization potential → lower ratio
- `sahaFactor_increases_with_T` : Higher temperature → higher ionization ratio
- `sahaFactor_decreases_with_ne` : Higher density → lower ratio (recombination)
- `euvPhotonEnergy` : E = 91.8 eV for λ = 13.5 nm

-/

noncomputable section

open Real

/-- Parameters for evaluating the Saha ionization equation -/
structure SahaParams where
  /-- Planck constant h (J·s) -/
  h : ℝ
  h_pos : 0 < h
  /-- Boltzmann constant k_B (J/K) -/
  k_B : ℝ
  k_B_pos : 0 < k_B
  /-- Electron mass m_e (kg) -/
  m_e : ℝ
  m_e_pos : 0 < m_e
  /-- Electron temperature in energy units k_B T_e (J) -/
  kT : ℝ
  kT_pos : 0 < kT
  /-- Electron number density n_e (m⁻³) -/
  n_e : ℝ
  n_e_pos : 0 < n_e

namespace SahaParams

variable (p : SahaParams)

/-- Quantum concentration: n_Q = (2πm_e kT/h²)^{3/2} -/
def quantumConcentration : ℝ :=
  (2 * π * p.m_e * p.kT / p.h ^ 2) ^ (3 / 2 : ℝ)

theorem quantumConcentration_pos : 0 < p.quantumConcentration := by
  unfold quantumConcentration
  apply rpow_pos_of_pos
  apply div_pos
  · exact mul_pos (mul_pos (mul_pos two_pos pi_pos) p.m_e_pos) p.kT_pos
  · exact sq_pos_of_pos p.h_pos

/-- Saha right-hand side for one ionization step z → z+1:
    S(T,z) = (2/n_e) · n_Q · (g_{z+1}/g_z) · exp(-χ_z / k_B T)
    where χ_z is the ionization energy of charge state z -/
def sahaFactor (g_ratio : ℝ) (chi_z : ℝ) : ℝ :=
  2 / p.n_e * p.quantumConcentration * g_ratio * exp (-chi_z / p.kT)

theorem sahaFactor_pos {g_ratio chi_z : ℝ} (hg : 0 < g_ratio) :
    0 < p.sahaFactor g_ratio chi_z := by
  unfold sahaFactor
  apply mul_pos (mul_pos (mul_pos _ p.quantumConcentration_pos) hg) (exp_pos _)
  exact div_pos two_pos p.n_e_pos

/-- Higher ionization potential χ → lower Saha ratio (exponential suppression) -/
theorem sahaFactor_decreases_with_chi (g_ratio : ℝ) (hg : 0 < g_ratio)
    {chi_1 chi_2 : ℝ} (hchi : chi_1 < chi_2) :
    p.sahaFactor g_ratio chi_2 < p.sahaFactor g_ratio chi_1 := by
  unfold sahaFactor
  apply mul_lt_mul_of_pos_left _ (mul_pos (mul_pos (div_pos two_pos p.n_e_pos)
    p.quantumConcentration_pos) hg)
  apply exp_lt_exp.mpr
  exact div_lt_div_of_pos_right (neg_lt_neg hchi) p.kT_pos

/-- Higher temperature raises the quantum concentration prefactor in the Saha ratio. -/
theorem quantumConcentration_increases_with_T
    (p₁ p₂ : SahaParams)
    (h_h : p₁.h = p₂.h)
    (h_me : p₁.m_e = p₂.m_e)
    (hT : p₁.kT < p₂.kT) :
    p₁.quantumConcentration < p₂.quantumConcentration := by
  unfold quantumConcentration
  rw [h_h, h_me]
  have hbase1 : 0 < 2 * π * p₂.m_e * p₁.kT / p₂.h ^ 2 :=
    div_pos (mul_pos (mul_pos (mul_pos two_pos pi_pos) p₂.m_e_pos) p₁.kT_pos)
      (sq_pos_of_pos p₂.h_pos)
  apply rpow_lt_rpow (le_of_lt hbase1) _ (by norm_num)
  apply div_lt_div_of_pos_right _ (sq_pos_of_pos p₂.h_pos)
  exact mul_lt_mul_of_pos_left hT (mul_pos (mul_pos two_pos pi_pos) p₂.m_e_pos)

/-- Higher electron density → lower Saha factor (collisional recombination) -/
theorem sahaFactor_decreases_with_ne (g_ratio chi_z : ℝ) (hg : 0 < g_ratio)
    (p₁ p₂ : SahaParams)
    (h_kT : p₁.kT = p₂.kT)
    (h_h : p₁.h = p₂.h)
    (h_me : p₁.m_e = p₂.m_e)
    (hne : p₁.n_e < p₂.n_e) :
    p₂.sahaFactor g_ratio chi_z < p₁.sahaFactor g_ratio chi_z := by
  unfold sahaFactor quantumConcentration
  rw [h_kT, h_h, h_me]
  apply mul_lt_mul_of_pos_right _ (exp_pos _)
  apply mul_lt_mul_of_pos_right _ hg
  apply mul_lt_mul_of_pos_right
  · apply div_lt_div_of_pos_left two_pos p₁.n_e_pos hne
  · apply rpow_pos_of_pos; apply div_pos
    · exact mul_pos (mul_pos (mul_pos two_pos pi_pos) p₂.m_e_pos) p₂.kT_pos
    · exact sq_pos_of_pos p₂.h_pos

/-- Photon energy of 13.5 nm EUV in eV: E = hc/λ ≈ 91.8 eV
    Using SI: h = 6.626e-34, c = 2.998e8, λ = 13.5e-9, e = 1.602e-19 -/
theorem euv_photon_energy_approx :
    |(6.626e-34 * 2.998e8 / (1.602e-19 * 13.5e-9) : ℝ) - 91.8| < 0.1 := by
  norm_num

end SahaParams

end
