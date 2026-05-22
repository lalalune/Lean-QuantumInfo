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

/-- Higher Sn emission rate gives higher tin flux at fixed mirror distance. -/
theorem tinFlux_increases_with_emission_rate {rate₁ rate₂ R : ℝ}
    (hrate : rate₁ < rate₂) (hR : 0 < R) :
    rate₁ / (4 * π * R ^ 2) < rate₂ / (4 * π * R ^ 2) :=
  div_lt_div_of_pos_right hrate
    (mul_pos (mul_pos (by norm_num) pi_pos) (sq_pos_of_pos hR))

/-- Tin flux obeys inverse square law: Φ₁/Φ₂ = (R₂/R₁)² -/
theorem tinFlux_inv_square_law {R₁ R₂ : ℝ} (hR₁ : 0 < R₁) (hR₂ : 0 < R₂)
    (d₁ d₂ : SnDeposition)
    (hrate : d₁.rate_Sn = d₂.rate_Sn)
    (hd₁ : d₁.R_dist = R₁) (hd₂ : d₂.R_dist = R₂) :
    d₁.tinFlux / d₂.tinFlux = (R₂ / R₁) ^ 2 := by
  unfold tinFlux
  rw [hd₁, hd₂, hrate]
  field_simp [ne_of_gt hR₁, ne_of_gt hR₂, ne_of_gt d₂.rate_Sn_pos, pi_ne_zero]

/-- Moving the mirror farther from the plasma lowers the tin flux by inverse-square spreading. -/
theorem tinFlux_decreases_with_distance {d₁ d₂ : SnDeposition}
    (hrate : d₁.rate_Sn = d₂.rate_Sn) (hR : d₁.R_dist < d₂.R_dist) :
    d₂.tinFlux < d₁.tinFlux := by
  unfold tinFlux
  rw [← hrate]
  have hR2sq : d₁.R_dist ^ 2 < d₂.R_dist ^ 2 := by
    nlinarith [mul_pos d₁.R_dist_pos d₁.R_dist_pos,
      mul_lt_mul_of_pos_left hR d₁.R_dist_pos,
      mul_lt_mul_of_pos_right hR (lt_trans d₁.R_dist_pos hR)]
  have hden1 : 0 < 4 * π * d₁.R_dist ^ 2 :=
    mul_pos (mul_pos (by norm_num) pi_pos) (sq_pos_of_pos d₁.R_dist_pos)
  have hden : 4 * π * d₁.R_dist ^ 2 < 4 * π * d₂.R_dist ^ 2 :=
    mul_lt_mul_of_pos_left hR2sq (mul_pos (by norm_num) pi_pos)
  exact div_lt_div_of_pos_left d₁.rate_Sn_pos hden1 hden

/-- Film growth rate: dh/dt = Φ × V_atom -/
def filmGrowthRate : ℝ := d.tinFlux * d.V_atom

theorem filmGrowthRate_pos : 0 < d.filmGrowthRate :=
  mul_pos d.tinFlux_pos d.V_atom_pos

/-- Higher tin flux gives a higher film growth rate for the same atomic volume. -/
theorem filmGrowthRate_increases_with_flux {Φ₁ Φ₂ V_atom : ℝ}
    (hΦ : Φ₁ < Φ₂) (hV : 0 < V_atom) :
    Φ₁ * V_atom < Φ₂ * V_atom :=
  mul_lt_mul_of_pos_right hΦ hV

/-- Larger atomic volume converts the same Sn flux into faster film growth. -/
theorem filmGrowthRate_increases_with_atomic_volume {Φ V₁ V₂ : ℝ}
    (hΦ : 0 < Φ) (hV : V₁ < V₂) :
    Φ * V₁ < Φ * V₂ :=
  mul_lt_mul_of_pos_left hV hΦ

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

/-- At fixed film thickness and wavelength, larger Sn extinction coefficient lowers reflectivity. -/
theorem reflectivityFactor_decreases_with_extinction {k₁ k₂ h lam : ℝ}
    (hk : k₁ < k₂) (hh : 0 < h) (hlam : 0 < lam) :
    exp (-(4 * π * k₂ * h / lam)) < exp (-(4 * π * k₁ * h / lam)) := by
  apply exp_lt_exp.mpr
  apply neg_lt_neg
  exact div_lt_div_of_pos_right
    (mul_lt_mul_of_pos_right
      (mul_lt_mul_of_pos_left hk (mul_pos (by norm_num) pi_pos)) hh) hlam

/-- At fixed film thickness and extinction coefficient, longer wavelength reduces optical depth. -/
theorem reflectivityFactor_increases_with_wavelength {k h lam₁ lam₂ : ℝ}
    (hk : 0 < k) (hh : 0 < h) (hlam₁ : 0 < lam₁) (hlam : lam₁ < lam₂) :
    exp (-(4 * π * k * h / lam₁)) < exp (-(4 * π * k * h / lam₂)) := by
  apply exp_lt_exp.mpr
  have hA : 0 < 4 * π * k * h :=
    mul_pos (mul_pos (mul_pos (by norm_num) pi_pos) hk) hh
  exact neg_lt_neg (div_lt_div_of_pos_left hA hlam₁ hlam)

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

/-- More surface tin gives a larger hydrogen-cleaning rate. -/
theorem cleaningRate_increases_with_surface_density {n₁ n₂ : ℝ} (hn : n₁ < n₂) :
    c.cleaningRate n₁ < c.cleaningRate n₂ := by
  unfold cleaningRate
  exact mul_lt_mul_of_pos_left hn (mul_pos c.k_clean_pos (pow_pos c.n_H_pos 4))

/-- More H radicals raise the fourth-order Sn cleaning rate. -/
theorem cleaningRate_increases_with_H_density {H₁ H₂ k_clean n_Sn : ℝ}
    (hH₁ : 0 < H₁) (hH : H₁ < H₂) (hk : 0 < k_clean) (hn : 0 < n_Sn) :
    k_clean * H₁ ^ 4 * n_Sn < k_clean * H₂ ^ 4 * n_Sn := by
  have hpow : H₁ ^ 4 < H₂ ^ 4 :=
    pow_lt_pow_left₀ hH (le_of_lt hH₁) (by norm_num)
  exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hpow hk) hn

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

/-- Higher Sn deposition flux requires a larger steady-state Sn surface density. -/
theorem steadyStateDensity_increases_with_flux {Phi₁ Phi₂ k_clean n_H : ℝ}
    (hPhi : Phi₁ < Phi₂) (hk : 0 < k_clean) (hH : 0 < n_H) :
    Phi₁ / (k_clean * n_H ^ 4) < Phi₂ / (k_clean * n_H ^ 4) :=
  div_lt_div_of_pos_right hPhi (mul_pos hk (pow_pos hH 4))

/-- A larger cleaning rate constant lowers the steady-state Sn surface density. -/
theorem steadyStateDensity_decreases_with_cleaning_constant {Phi k₁ k₂ n_H : ℝ}
    (hPhi : 0 < Phi) (hk₁ : 0 < k₁) (hk : k₁ < k₂) (hH : 0 < n_H) :
    Phi / (k₂ * n_H ^ 4) < Phi / (k₁ * n_H ^ 4) := by
  apply div_lt_div_of_pos_left hPhi
  · exact mul_pos hk₁ (pow_pos hH 4)
  · exact mul_lt_mul_of_pos_right hk (pow_pos hH 4)

/-- Net tin surface-density balance: deposition minus hydrogen cleaning. -/
def surfaceDensityRHS (n_Sn : ℝ) : ℝ := c.Phi_Sn - c.cleaningRate n_Sn

/-- At steady state, the net tin surface-density RHS is zero. -/
theorem steadyState_rhs_zero : c.surfaceDensityRHS c.steadyStateDensity = 0 := by
  unfold surfaceDensityRHS
  rw [c.steadyState_balance]
  ring

/-- Below steady state, tin deposition exceeds cleaning and surface tin grows. -/
theorem surfaceDensityRHS_pos_below_steady {n_Sn : ℝ}
    (hbelow : n_Sn < c.steadyStateDensity) :
    0 < c.surfaceDensityRHS n_Sn := by
  unfold steadyStateDensity at hbelow
  unfold surfaceDensityRHS cleaningRate
  have hcoeff : 0 < c.k_clean * c.n_H ^ 4 :=
    mul_pos c.k_clean_pos (pow_pos c.n_H_pos 4)
  rw [lt_div_iff₀ hcoeff] at hbelow
  nlinarith

/-- Above steady state, cleaning exceeds tin deposition and surface tin decays. -/
theorem surfaceDensityRHS_neg_above_steady {n_Sn : ℝ}
    (habove : c.steadyStateDensity < n_Sn) :
    c.surfaceDensityRHS n_Sn < 0 := by
  unfold steadyStateDensity at habove
  unfold surfaceDensityRHS cleaningRate
  have hcoeff : 0 < c.k_clean * c.n_H ^ 4 :=
    mul_pos c.k_clean_pos (pow_pos c.n_H_pos 4)
  rw [div_lt_iff₀ hcoeff] at habove
  nlinarith

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

theorem hRadicalDensity_increases_with_EUV_intensity {sigma_EUV I₁ I₂ H2 k_rec k_other : ℝ}
    (hsigma : 0 < sigma_EUV) (hI : I₁ < I₂) (hH2 : 0 < H2)
    (hden : 0 < k_rec + k_other) :
    hRadicalDensity sigma_EUV I₁ H2 k_rec k_other <
      hRadicalDensity sigma_EUV I₂ H2 k_rec k_other := by
  unfold hRadicalDensity
  apply div_lt_div_of_pos_right _ hden
  exact mul_lt_mul_of_pos_right
    (mul_lt_mul_of_pos_left hI (mul_pos (by norm_num) hsigma)) hH2

theorem hRadicalDensity_increases_with_H2 {sigma_EUV I_EUV H2₁ H2₂ k_rec k_other : ℝ}
    (hsigma : 0 < sigma_EUV) (hI : 0 < I_EUV) (hH2 : H2₁ < H2₂)
    (hden : 0 < k_rec + k_other) :
    hRadicalDensity sigma_EUV I_EUV H2₁ k_rec k_other <
      hRadicalDensity sigma_EUV I_EUV H2₂ k_rec k_other := by
  unfold hRadicalDensity
  apply div_lt_div_of_pos_right _ hden
  exact mul_lt_mul_of_pos_left hH2 (mul_pos (mul_pos (by norm_num) hsigma) hI)

/-- Larger aggregate H-loss/recombination rate lowers the H radical density. -/
theorem hRadicalDensity_decreases_with_loss_rate {sigma_EUV I_EUV H2 den₁ den₂ : ℝ}
    (hsigma : 0 < sigma_EUV) (hI : 0 < I_EUV) (hH2 : 0 < H2)
    (hden₁ : 0 < den₁) (hden : den₁ < den₂) :
    2 * sigma_EUV * I_EUV * H2 / den₂ <
      2 * sigma_EUV * I_EUV * H2 / den₁ :=
  div_lt_div_of_pos_left
    (mul_pos (mul_pos (mul_pos (by norm_num) hsigma) hI) hH2) hden₁ hden

/-- Carbon contamination rate proportional to hydrocarbon partial pressure and EUV intensity -/
def carbonContaminationRate (P_HC I_EUV sigma_crack : ℝ) : ℝ :=
  P_HC * I_EUV * sigma_crack

theorem carbonContaminationRate_pos {P_HC I_EUV sigma_crack : ℝ}
    (hP : 0 < P_HC) (hI : 0 < I_EUV) (hsigma : 0 < sigma_crack) :
    0 < carbonContaminationRate P_HC I_EUV sigma_crack := by
  unfold carbonContaminationRate
  exact mul_pos (mul_pos hP hI) hsigma

theorem carbonContaminationRate_increases_with_pressure {P₁ P₂ I_EUV sigma_crack : ℝ}
    (hP : P₁ < P₂) (hI : 0 < I_EUV) (hsigma : 0 < sigma_crack) :
    carbonContaminationRate P₁ I_EUV sigma_crack <
      carbonContaminationRate P₂ I_EUV sigma_crack := by
  unfold carbonContaminationRate
  exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hP hI) hsigma

theorem carbonContaminationRate_increases_with_EUV_intensity {P_HC I₁ I₂ sigma_crack : ℝ}
    (hP : 0 < P_HC) (hI : I₁ < I₂) (hsigma : 0 < sigma_crack) :
    carbonContaminationRate P_HC I₁ sigma_crack <
      carbonContaminationRate P_HC I₂ sigma_crack := by
  unfold carbonContaminationRate
  exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hI hP) hsigma

/-- Larger EUV cracking cross section raises hydrocarbon-driven carbon contamination. -/
theorem carbonContaminationRate_increases_with_cross_section {P_HC I_EUV sigma₁ sigma₂ : ℝ}
    (hP : 0 < P_HC) (hI : 0 < I_EUV) (hsigma : sigma₁ < sigma₂) :
    carbonContaminationRate P_HC I_EUV sigma₁ <
      carbonContaminationRate P_HC I_EUV sigma₂ := by
  unfold carbonContaminationRate
  exact mul_lt_mul_of_pos_left hsigma (mul_pos hP hI)

/-- Atomic volume from molar mass, Avogadro number, and mass density. -/
def atomicVolume (molarMass avogadro density : ℝ) : ℝ :=
  molarMass / (avogadro * density)

theorem atomicVolume_pos {molarMass avogadro density : ℝ}
    (hM : 0 < molarMass) (hN : 0 < avogadro) (hρ : 0 < density) :
    0 < atomicVolume molarMass avogadro density :=
  div_pos hM (mul_pos hN hρ)

/-- Atomic volume grows linearly with molar mass at fixed density and Avogadro number. -/
theorem atomicVolume_increases_with_molarMass {M₁ M₂ avogadro density : ℝ}
    (hM : M₁ < M₂) (hN : 0 < avogadro) (hρ : 0 < density) :
    atomicVolume M₁ avogadro density < atomicVolume M₂ avogadro density := by
  unfold atomicVolume
  exact div_lt_div_of_pos_right hM (mul_pos hN hρ)

/-- Atomic volume decreases with larger mass density at fixed molar mass. -/
theorem atomicVolume_decreases_with_density {molarMass avogadro ρ₁ ρ₂ : ℝ}
    (hM : 0 < molarMass) (hN : 0 < avogadro) (hρ₁ : 0 < ρ₁) (hρ : ρ₁ < ρ₂) :
    atomicVolume molarMass avogadro ρ₂ < atomicVolume molarMass avogadro ρ₁ := by
  unfold atomicVolume
  apply div_lt_div_of_pos_left hM
  · exact mul_pos hN hρ₁
  · exact mul_lt_mul_of_pos_left hρ hN

end
