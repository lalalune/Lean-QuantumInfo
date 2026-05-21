/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!

# EUV Lithography: Mirror Contamination and Cleaning Physics

Formalizes tin deposition, reflectivity degradation, hydrogen radical
cleaning, and carbon contamination for EUV collector and projection mirrors.

## Main definitions

- `SnDeposition` : Tin contamination model for collector mirror
- `tinFlux` : Φ_Sn = rate_Sn / (4π R²) (atoms/m²/s)
- `filmGrowthRate` : dh/dt = Φ_Sn × V_atom
- `reflectivity` : R(h) = R₀ exp(-4π k_Sn h/lam)
- `HydrogenCleaning` : Tin removal by H radicals (Sn + 4H → SnH₄↑)
- `steadyStateDensity` : n_ss = Phi_Sn / (k_clean × [H*]⁴)
- `hRadicalDensity` : [H*] = 2 σ_EUV I_EUV [H₂] / (k_rec + k_other)
- `carbonContaminationRate` : proportional to hydrocarbon partial pressure and EUV flux

## Main results

- `tinFlux_pos`, `tinFlux_inv_square_law`
- `reflectivity_at_zero`, `reflectivity_strictly_decreasing`
- `steadyState_balance`, `more_H_cleaner`
- `hRadicalDensity_pos`, `carbonContaminationRate_pos`

-/

noncomputable section

open Real

/-- Parameters for tin contamination of a mirror at distance R_dist from source -/
structure SnDeposition where
  /-- Mirror distance from plasma (m) -/
  R_dist : ℝ
  R_dist_pos : 0 < R_dist
  /-- Total Sn atom emission rate (atoms/s) -/
  rate_Sn : ℝ
  rate_Sn_pos : 0 < rate_Sn
  /-- Volume per Sn atom (m³) -/
  V_atom : ℝ
  V_atom_pos : 0 < V_atom
  /-- Extinction coefficient k_Sn of tin at the EUV wavelength -/
  k_Sn : ℝ
  k_Sn_pos : 0 < k_Sn
  /-- EUV wavelength (m) -/
  lam : ℝ
  lam_pos : 0 < lam
  /-- Mirror bare reflectivity R₀ -/
  R₀ : ℝ
  R₀_pos : 0 < R₀
  R₀_le_one : R₀ ≤ 1

namespace SnDeposition

variable (d : SnDeposition)

/-- Tin flux at mirror: Φ = rate_Sn / (4π R²) -/
def tinFlux : ℝ := d.rate_Sn / (4 * π * d.R_dist ^ 2)

theorem tinFlux_pos : 0 < d.tinFlux :=
  div_pos d.rate_Sn_pos (mul_pos (mul_pos (by norm_num) pi_pos) (sq_pos_of_pos d.R_dist_pos))

/-- Tin flux obeys inverse square law: Φ₁/Φ₂ = (R₂/R₁)² -/
theorem tinFlux_inv_square_law {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (hR₂ : 0 < R₂)
    (d₁ d₂ : SnDeposition)
    (hrate : d₁.rate_Sn = d₂.rate_Sn)
    (hd₁ : d₁.R_dist = R₁) (hd₂ : d₂.R_dist = R₂) :
    d₁.tinFlux / d₂.tinFlux = (R₂ / R₁) ^ 2 := by
  unfold tinFlux
  rw [hd₁, hd₂, hrate]
  field_simp [ne_of_gt hR₁, ne_of_gt hR₂, ne_of_gt d₂.rate_Sn_pos, pi_ne_zero]

/-- Film growth rate: dh/dt = Φ × V_atom -/
def filmGrowthRate : ℝ := d.tinFlux * d.V_atom

theorem filmGrowthRate_pos : 0 < d.filmGrowthRate :=
  mul_pos d.tinFlux_pos d.V_atom_pos

/-- Film thickness after starting from a clean mirror and growing at constant flux. -/
def filmThicknessFromClean (t : ℝ) : ℝ := d.filmGrowthRate * t

/-- The clean-start thickness model has derivative equal to the film growth rate. -/
theorem filmThicknessFromClean_derivative (t : ℝ) :
    HasDerivAt d.filmThicknessFromClean d.filmGrowthRate t := by
  unfold filmThicknessFromClean
  simpa using (hasDerivAt_id t).const_mul d.filmGrowthRate

/-- Reflectivity with Sn contamination layer of thickness h:
    R(h) = R₀ exp(-4π k_Sn h / lam) -/
def reflectivity (h : ℝ) : ℝ :=
  d.R₀ * exp (-(4 * π * d.k_Sn * h / d.lam))

theorem reflectivity_at_zero : d.reflectivity 0 = d.R₀ := by
  simp [reflectivity]

theorem reflectivity_pos (h : ℝ) : 0 < d.reflectivity h :=
  mul_pos d.R₀_pos (exp_pos _)

/-- The exponential tin-film reflectivity model satisfies `dR/dh = -α R`. -/
theorem reflectivity_derivative (h : ℝ) :
    HasDerivAt d.reflectivity
      (-(4 * π * d.k_Sn / d.lam) * d.reflectivity h) h := by
  unfold reflectivity
  convert (((hasDerivAt_id h).const_mul (-(4 * π * d.k_Sn / d.lam))).exp.const_mul
    d.R₀) using 1
  · funext y
    simp only [id_eq]
    ring_nf
  · simp only [id_eq]
    ring_nf

theorem reflectivity_le_bare {h : ℝ} (hh : 0 ≤ h) : d.reflectivity h ≤ d.R₀ := by
  unfold reflectivity
  apply mul_le_of_le_one_right (le_of_lt d.R₀_pos)
  rw [exp_le_one_iff]
  exact neg_nonpos.mpr (div_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt pi_pos))
      (le_of_lt d.k_Sn_pos)) hh) (le_of_lt d.lam_pos))

theorem reflectivity_strictly_decreasing {h₁ h₂ : ℝ} (hh : h₁ < h₂) :
    d.reflectivity h₂ < d.reflectivity h₁ := by
  unfold reflectivity
  apply mul_lt_mul_of_pos_left _ d.R₀_pos
  apply exp_lt_exp.mpr
  apply neg_lt_neg
  exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hh
    (mul_pos (mul_pos (by norm_num) pi_pos) d.k_Sn_pos)) d.lam_pos

end SnDeposition

/-- Parameters for hydrogen radical cleaning -/
structure HydrogenCleaning where
  /-- Hydrogen radical density (m⁻³) -/
  n_H : ℝ
  n_H_pos : 0 < n_H
  /-- Tin deposition flux (atoms/m²/s) -/
  Phi_Sn : ℝ
  Phi_Sn_pos : 0 < Phi_Sn
  /-- Cleaning rate constant (m¹²/s): Sn + 4H* → SnH₄ -/
  k_clean : ℝ
  k_clean_pos : 0 < k_clean

namespace HydrogenCleaning

variable (c : HydrogenCleaning)

/-- Cleaning rate: r = k_clean × [H*]⁴ × n_Sn -/
def cleaningRate (n_Sn : ℝ) : ℝ := c.k_clean * c.n_H ^ 4 * n_Sn

theorem cleaningRate_nonneg {n_Sn : ℝ} (hn : 0 ≤ n_Sn) : 0 ≤ c.cleaningRate n_Sn :=
  mul_nonneg (mul_nonneg (le_of_lt c.k_clean_pos) (le_of_lt (pow_pos c.n_H_pos 4))) hn

/-- Steady-state surface density: n_ss = Phi_Sn / (k_clean [H*]⁴) -/
def steadyStateDensity : ℝ := c.Phi_Sn / (c.k_clean * c.n_H ^ 4)

theorem steadyStateDensity_pos : 0 < c.steadyStateDensity :=
  div_pos c.Phi_Sn_pos (mul_pos c.k_clean_pos (pow_pos c.n_H_pos 4))

/-- At steady state, cleaning rate equals deposition rate -/
theorem steadyState_balance : c.cleaningRate c.steadyStateDensity = c.Phi_Sn := by
  unfold cleaningRate steadyStateDensity
  have h : c.k_clean * c.n_H ^ 4 ≠ 0 :=
    ne_of_gt (mul_pos c.k_clean_pos (pow_pos c.n_H_pos 4))
  field_simp [h, ne_of_gt c.k_clean_pos, ne_of_gt c.n_H_pos]

/-- Net tin surface-density balance: deposition minus hydrogen cleaning. -/
def surfaceDensityRHS (n_Sn : ℝ) : ℝ := c.Phi_Sn - c.cleaningRate n_Sn

/-- At steady state, the net tin surface-density RHS is zero. -/
theorem steadyState_rhs_zero : c.surfaceDensityRHS c.steadyStateDensity = 0 := by
  unfold surfaceDensityRHS
  rw [c.steadyState_balance]
  ring

/-- More H radicals → lower steady-state Sn density -/
theorem more_H_cleaner {c₁ c₂ : HydrogenCleaning}
    (hPhi : c₁.Phi_Sn = c₂.Phi_Sn)
    (hk : c₁.k_clean = c₂.k_clean)
    (hH : c₁.n_H < c₂.n_H) :
    c₂.steadyStateDensity < c₁.steadyStateDensity := by
  unfold steadyStateDensity
  rw [← hPhi, ← hk]
  apply div_lt_div_of_pos_left c₁.Phi_Sn_pos
  · exact mul_pos c₁.k_clean_pos (pow_pos c₁.n_H_pos 4)
  · apply mul_lt_mul_of_pos_left _ (by rw [hk]; exact c₂.k_clean_pos)
    exact pow_lt_pow_left₀ hH (le_of_lt c₁.n_H_pos) (by norm_num)

/-- SnH₄ boiling point is 252 K < 293 K (room temp) → volatile at room temp -/
theorem snH4_volatile_at_room_temp : (252 : ℝ) < 293 := by norm_num

end HydrogenCleaning

/-- Hydrogen radical density from EUV photolysis of H₂:
    [H*] = 2 σ_EUV I_EUV [H₂] / (k_rec + k_other) -/
def hRadicalDensity (sigma_EUV I_EUV H2 k_rec k_other : ℝ) : ℝ :=
  2 * sigma_EUV * I_EUV * H2 / (k_rec + k_other)

theorem hRadicalDensity_pos {sigma_EUV I_EUV H2 k_rec k_other : ℝ}
    (hsigma : 0 < sigma_EUV) (hI : 0 < I_EUV) (hH2 : 0 < H2)
    (hden : 0 < k_rec + k_other) :
    0 < hRadicalDensity sigma_EUV I_EUV H2 k_rec k_other := by
  unfold hRadicalDensity
  exact div_pos (mul_pos (mul_pos (mul_pos (by norm_num) hsigma) hI) hH2) hden

/-- Carbon contamination rate proportional to hydrocarbon partial pressure and EUV intensity -/
def carbonContaminationRate (P_HC I_EUV sigma_crack : ℝ) : ℝ :=
  P_HC * I_EUV * sigma_crack

theorem carbonContaminationRate_pos {P_HC I_EUV sigma_crack : ℝ}
    (hP : 0 < P_HC) (hI : 0 < I_EUV) (hsigma : 0 < sigma_crack) :
    0 < carbonContaminationRate P_HC I_EUV sigma_crack := by
  unfold carbonContaminationRate
  exact mul_pos (mul_pos hP hI) hsigma

/-- Atomic volume from molar mass, Avogadro number, and mass density. -/
def atomicVolume (molarMass avogadro density : ℝ) : ℝ :=
  molarMass / (avogadro * density)

theorem atomicVolume_pos {molarMass avogadro density : ℝ}
    (hM : 0 < molarMass) (hN : 0 < avogadro) (hρ : 0 < density) :
    0 < atomicVolume molarMass avogadro density :=
  div_pos hM (mul_pos hN hρ)

end
