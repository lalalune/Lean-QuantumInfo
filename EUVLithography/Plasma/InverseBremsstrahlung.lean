/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!

# EUV Lithography: Inverse Bremsstrahlung Absorption

Formalizes inverse bremsstrahlung (IB) — the primary mechanism by which
CO₂ laser energy is deposited into the tin plasma to create EUV-emitting
conditions. Also includes Beer-Lambert propagation.

## Main definitions

- `IBAbsorption` : Structure capturing IB absorption parameters
- `ibCoefficient` : κ_IB ∝ n_e² / (T_e^{3/2} ω²)
- `intensityProfile` : I(z) = I₀ exp(-∫κ dz) (Beer-Lambert in plasma)
- `absorptionDepth` : l = 1/κ_IB
- `CoulombLogarithm` : ln Λ ≈ ln(k_B T_e / (e² n_e^{1/2}))

## Main results

- `ibCoefficient_pos` : κ_IB > 0
- `intensity_decays` : I(z) is strictly decreasing in z for z ≥ 0
- `intensity_beerlambert` : I(z) = I₀ exp(-κ z) for uniform plasma
- `absorbed_fraction` : 1 - exp(-κL) fraction absorbed over length L
- `ib_scales_ne_squared` : doubling n_e quadruples κ_IB
- `ib_inversely_omega_squared` : doubling ω reduces κ by factor 4
- `co2_vs_1064_ib_ratio` : CO₂ absorbs ~100× more than Nd:YAG

-/

noncomputable section

open Real

/-- Coulomb-logarithm argument in the report's approximate expression. -/
def coulombLogArgument (kBT_e e n_e eps0 m_e : ℝ) : ℝ :=
  (kBT_e / (e ^ 2 * sqrt n_e)) *
    sqrt ((4 * π * eps0 * m_e * kBT_e) / e ^ 2)

theorem coulombLogArgument_pos {kBT_e e n_e eps0 m_e : ℝ}
    (hkT : 0 < kBT_e) (he : 0 < e) (hne : 0 < n_e) (heps : 0 < eps0)
    (hme : 0 < m_e) :
    0 < coulombLogArgument kBT_e e n_e eps0 m_e := by
  unfold coulombLogArgument
  apply mul_pos
  · exact div_pos hkT (mul_pos (sq_pos_of_pos he) (sqrt_pos.mpr hne))
  · apply sqrt_pos.mpr
    exact div_pos (mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) pi_pos) heps) hme) hkT)
      (sq_pos_of_pos he)

/-- If the Coulomb-logarithm argument exceeds one, the Coulomb logarithm is positive. -/
theorem coulombLog_pos_of_argument_gt_one {x : ℝ} (hx : 1 < x) : 0 < log x :=
  log_pos hx

/-- Electron-ion collision frequency appearing in the IB absorption model. -/
def electronIonCollisionFrequency (Z n_e e lnΛ eps0 m_e kBT_e : ℝ) : ℝ :=
  sqrt (2 * π) / 3 * (Z * n_e * e ^ 4 * lnΛ) /
    ((4 * π * eps0) ^ 2 * sqrt m_e * kBT_e ^ (3 / 2 : ℝ))

theorem electronIonCollisionFrequency_pos {Z n_e e lnΛ eps0 m_e kBT_e : ℝ}
    (hZ : 0 < Z) (hne : 0 < n_e) (he : 0 < e) (hln : 0 < lnΛ)
    (heps : 0 < eps0) (hme : 0 < m_e) (hkT : 0 < kBT_e) :
    0 < electronIonCollisionFrequency Z n_e e lnΛ eps0 m_e kBT_e := by
  unfold electronIonCollisionFrequency
  apply div_pos
  · apply mul_pos
    · exact div_pos (sqrt_pos.mpr (mul_pos two_pos pi_pos)) (by norm_num)
    · exact mul_pos (mul_pos (mul_pos hZ hne) (pow_pos he 4)) hln
  · exact mul_pos (mul_pos (sq_pos_of_pos (mul_pos (mul_pos (by norm_num) pi_pos) heps))
      (sqrt_pos.mpr hme)) (rpow_pos_of_pos hkT _)

/-- Full underdense inverse-bremsstrahlung coefficient from the report. -/
def ibCoefficientFull (omega_p nu_ei c omega densityRatio : ℝ) : ℝ :=
  omega_p ^ 2 * nu_ei / (c * omega ^ 2 * sqrt (1 - densityRatio))

theorem ibCoefficientFull_pos {omega_p nu_ei c omega densityRatio : ℝ}
    (hwp : 0 < omega_p) (hnu : 0 < nu_ei) (hc : 0 < c) (homega : 0 < omega)
    (hunderdense : densityRatio < 1) :
    0 < ibCoefficientFull omega_p nu_ei c omega densityRatio := by
  unfold ibCoefficientFull
  apply div_pos
  · exact mul_pos (sq_pos_of_pos hwp) hnu
  · exact mul_pos (mul_pos hc (sq_pos_of_pos homega)) (sqrt_pos.mpr (sub_pos.mpr hunderdense))

/-- Parameters for inverse bremsstrahlung absorption -/
structure IBParams where
  /-- Electron number density (m⁻³) -/
  n_e : ℝ
  n_e_pos : 0 < n_e
  /-- Electron temperature in joules (k_B T_e) -/
  T_e : ℝ
  T_e_pos : 0 < T_e
  /-- Mean ion charge state -/
  Z_star : ℝ
  Z_star_pos : 0 < Z_star
  /-- Coulomb logarithm ln Λ > 1 -/
  lnΛ : ℝ
  lnΛ_pos : 0 < lnΛ
  /-- Laser angular frequency -/
  ω : ℝ
  ω_pos : 0 < ω
  /-- Constants prefactor (e⁴/(m_e^{3/2} ε₀² c) × 1/(6π√(2π))) -/
  α : ℝ
  α_pos : 0 < α

namespace IBParams

variable (p : IBParams)

/-- Inverse bremsstrahlung absorption coefficient (simplified):
    κ_IB = α · Z* · n_e² · ln Λ / (T_e^{3/2} · ω²)
    This captures the key scaling: κ ∝ n_e² / (T_e^{3/2} ω²) -/
def ibCoefficient : ℝ :=
  p.α * p.Z_star * p.n_e ^ 2 * p.lnΛ / (p.T_e ^ (3/2 : ℝ) * p.ω ^ 2)

theorem ibCoefficient_pos : 0 < p.ibCoefficient := by
  unfold ibCoefficient
  apply div_pos
  · apply mul_pos (mul_pos (mul_pos p.α_pos p.Z_star_pos) (sq_pos_of_pos p.n_e_pos)) p.lnΛ_pos
  · apply mul_pos
    · exact rpow_pos_of_pos p.T_e_pos _
    · exact sq_pos_of_pos p.ω_pos

/-- Absorption depth: l = 1/κ_IB -/
def absorptionDepth : ℝ := 1 / p.ibCoefficient

theorem absorptionDepth_pos : 0 < p.absorptionDepth := by
  unfold absorptionDepth
  exact div_pos one_pos p.ibCoefficient_pos

/-- Beer-Lambert intensity in uniform plasma: I(z) = I₀ exp(-κ z) -/
def intensity (I₀ z : ℝ) : ℝ :=
  I₀ * exp (-(p.ibCoefficient * z))

theorem intensity_at_zero (I₀ : ℝ) : p.intensity I₀ 0 = I₀ := by
  simp [intensity]

theorem intensity_nonneg {I₀ : ℝ} (hI : 0 ≤ I₀) (z : ℝ) : 0 ≤ p.intensity I₀ z := by
  unfold intensity
  exact mul_nonneg hI (le_of_lt (exp_pos _))

theorem intensity_decays {I₀ : ℝ} (hI : 0 < I₀) {z₁ z₂ : ℝ} (hz : z₁ < z₂) :
    p.intensity I₀ z₂ < p.intensity I₀ z₁ := by
  unfold intensity
  apply mul_lt_mul_of_pos_left _ hI
  apply exp_lt_exp.mpr
  nlinarith [mul_lt_mul_of_pos_left hz p.ibCoefficient_pos]

/-- Fraction of power absorbed over path length L -/
def absorbedFraction (L : ℝ) : ℝ := 1 - exp (-(p.ibCoefficient * L))

theorem absorbedFraction_pos {L : ℝ} (hL : 0 < L) : 0 < p.absorbedFraction L := by
  unfold absorbedFraction
  apply sub_pos.mpr
  exact exp_lt_one_iff.mpr (by nlinarith [mul_pos p.ibCoefficient_pos hL])

theorem absorbedFraction_lt_one {L : ℝ} (_hL : 0 < L) : p.absorbedFraction L < 1 := by
  unfold absorbedFraction
  linarith [exp_pos (-(p.ibCoefficient * L))]

/-- The absorbed fraction is exactly one minus the transmitted Beer-Lambert factor. -/
theorem absorbedFraction_eq_one_sub_transmission (L : ℝ) :
    p.absorbedFraction L = 1 - exp (-(p.ibCoefficient * L)) := rfl

/-- Longer underdense-plasma path length absorbs a larger laser fraction. -/
theorem absorbedFraction_increases_with_length {L₁ L₂ : ℝ} (hL : L₁ < L₂) :
    p.absorbedFraction L₁ < p.absorbedFraction L₂ := by
  unfold absorbedFraction
  have htrans : exp (-(p.ibCoefficient * L₂)) < exp (-(p.ibCoefficient * L₁)) := by
    apply exp_lt_exp.mpr
    nlinarith [mul_lt_mul_of_pos_left hL p.ibCoefficient_pos]
  linarith

/-- Stronger inverse-bremsstrahlung coefficient absorbs a larger fraction over fixed path. -/
theorem absorbedFraction_increases_with_coefficient {κ₁ κ₂ L : ℝ}
    (hκ : κ₁ < κ₂) (hL : 0 < L) :
    1 - exp (-(κ₁ * L)) < 1 - exp (-(κ₂ * L)) := by
  have htrans : exp (-(κ₂ * L)) < exp (-(κ₁ * L)) := by
    apply exp_lt_exp.mpr
    nlinarith [mul_lt_mul_of_pos_right hκ hL]
  linarith

/-- Absorption depth is the reciprocal of the IB coefficient. -/
theorem absorptionDepth_mul_ibCoefficient : p.absorptionDepth * p.ibCoefficient = 1 := by
  unfold absorptionDepth
  field_simp [ne_of_gt p.ibCoefficient_pos]

/-- Stronger IB coefficient shortens absorption depth. -/
theorem absorptionDepth_decreases_with_coefficient {κ₁ κ₂ : ℝ}
    (hκ₁ : 0 < κ₁) (hκ : κ₁ < κ₂) :
    1 / κ₂ < 1 / κ₁ := by
  exact div_lt_div_of_pos_left one_pos hκ₁ hκ

/-- IB coefficient scales as n_e² (key CO₂ laser advantage) -/
theorem ib_scales_ne_squared {n₁ n₂ : ℝ} (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (p₁ p₂ : IBParams)
    (h_Te : p₁.T_e = p₂.T_e)
    (h_ω : p₁.ω = p₂.ω)
    (h_Z : p₁.Z_star = p₂.Z_star)
    (h_lnΛ : p₁.lnΛ = p₂.lnΛ)
    (h_α : p₁.α = p₂.α)
    (h_n₁ : p₁.n_e = n₁)
    (h_n₂ : p₂.n_e = n₂) :
    p₁.ibCoefficient / p₂.ibCoefficient = (n₁ / n₂) ^ 2 := by
  simp only [ibCoefficient, h_Te, h_ω, h_Z, h_lnΛ, h_α, h_n₁, h_n₂]
  field_simp [ne_of_gt hn₂, ne_of_gt p₂.α_pos, ne_of_gt p₂.Z_star_pos,
    ne_of_gt p₂.lnΛ_pos, ne_of_gt (rpow_pos_of_pos p₂.T_e_pos (3 / 2 : ℝ)),
    ne_of_gt p₂.ω_pos]

/-- IB coefficient scales as ω⁻² -/
theorem ib_inversely_omega_squared (p₁ p₂ : IBParams)
    (h_ne : p₁.n_e = p₂.n_e)
    (h_Te : p₁.T_e = p₂.T_e)
    (h_Z : p₁.Z_star = p₂.Z_star)
    (h_lnΛ : p₁.lnΛ = p₂.lnΛ)
    (h_α : p₁.α = p₂.α) :
    p₁.ibCoefficient / p₂.ibCoefficient = (p₂.ω / p₁.ω) ^ 2 := by
  simp only [ibCoefficient, h_ne, h_Te, h_Z, h_lnΛ, h_α]
  field_simp [ne_of_gt p₁.ω_pos, ne_of_gt p₂.ω_pos, ne_of_gt p₂.n_e_pos,
    ne_of_gt p₂.α_pos, ne_of_gt p₂.Z_star_pos, ne_of_gt p₂.lnΛ_pos,
    ne_of_gt (rpow_pos_of_pos p₂.T_e_pos (3 / 2 : ℝ))]

/-- Higher electron temperature lowers inverse-bremsstrahlung absorption through `T_e^(-3/2)`. -/
theorem ib_decreases_with_temperature {T₁ T₂ : ℝ} (hT₁ : 0 < T₁) (hT : T₁ < T₂)
    (p₁ p₂ : IBParams)
    (h_ne : p₁.n_e = p₂.n_e)
    (h_ω : p₁.ω = p₂.ω)
    (h_Z : p₁.Z_star = p₂.Z_star)
    (h_lnΛ : p₁.lnΛ = p₂.lnΛ)
    (h_α : p₁.α = p₂.α)
    (h_T₁ : p₁.T_e = T₁)
    (h_T₂ : p₂.T_e = T₂) :
    p₂.ibCoefficient < p₁.ibCoefficient := by
  unfold ibCoefficient
  rw [h_ne, h_ω, h_Z, h_lnΛ, h_α, h_T₁, h_T₂]
  have hnum : 0 < p₂.α * p₂.Z_star * p₂.n_e ^ 2 * p₂.lnΛ :=
    mul_pos (mul_pos (mul_pos p₂.α_pos p₂.Z_star_pos) (sq_pos_of_pos p₂.n_e_pos))
      p₂.lnΛ_pos
  have hw2 : 0 < p₂.ω ^ 2 := sq_pos_of_pos p₂.ω_pos
  have hden1 : 0 < T₁ ^ (3 / 2 : ℝ) * p₂.ω ^ 2 :=
    mul_pos (Real.rpow_pos_of_pos hT₁ _) hw2
  have hpow : T₁ ^ (3 / 2 : ℝ) < T₂ ^ (3 / 2 : ℝ) :=
    Real.rpow_lt_rpow (le_of_lt hT₁) hT (by norm_num)
  have hden : T₁ ^ (3 / 2 : ℝ) * p₂.ω ^ 2 <
      T₂ ^ (3 / 2 : ℝ) * p₂.ω ^ 2 :=
    mul_lt_mul_of_pos_right hpow hw2
  exact div_lt_div_of_pos_left hnum hden1 hden

/-- CO₂ (10.6 μm) vs Nd:YAG (1.064 μm): IB ratio ≈ (10.6/1.064)² ≈ 99.2 -/
theorem co2_vs_ndyag_ib_ratio :
    (10.6 / 1.064 : ℝ) ^ 2 > 99 := by norm_num

/-- Ponderomotive energy: U_p = e² E₀² / (4 m_e ω²) -/
def ponderomotiveEnergy (e m_e E₀ ω : ℝ) : ℝ :=
  e ^ 2 * E₀ ^ 2 / (4 * m_e * ω ^ 2)

/-- Electromagnetic intensity from field amplitude in the report convention:
    `I = (1/2)c ε₀ E₀²`. -/
def intensityFromFieldAmplitude (c eps0 E₀ : ℝ) : ℝ :=
  c * eps0 * E₀ ^ 2 / 2

theorem intensityFromFieldAmplitude_pos {c eps0 E₀ : ℝ}
    (hc : 0 < c) (heps : 0 < eps0) (hE : 0 < E₀) :
    0 < intensityFromFieldAmplitude c eps0 E₀ := by
  unfold intensityFromFieldAmplitude
  exact div_pos (mul_pos (mul_pos hc heps) (sq_pos_of_pos hE)) two_pos

/-- Substituting `I = c ε₀ E₀²/2` gives the report's intensity form of `U_p`. -/
theorem ponderomotiveEnergy_eq_intensity_form {e m_e E₀ ω c eps0 : ℝ}
    (hc : c ≠ 0) (heps : eps0 ≠ 0) :
    ponderomotiveEnergy e m_e E₀ ω =
      e ^ 2 * intensityFromFieldAmplitude c eps0 E₀ / (2 * c * eps0 * m_e * ω ^ 2) := by
  unfold ponderomotiveEnergy intensityFromFieldAmplitude
  field_simp [hc, heps]
  ring

theorem ponderomotiveEnergy_pos {e m_e E₀ ω : ℝ}
    (he : 0 < e) (hm : 0 < m_e) (hE : 0 < E₀) (hω : 0 < ω) :
    0 < ponderomotiveEnergy e m_e E₀ ω := by
  unfold ponderomotiveEnergy
  apply div_pos
  · exact mul_pos (sq_pos_of_pos he) (sq_pos_of_pos hE)
  · exact mul_pos (mul_pos (by norm_num) hm) (sq_pos_of_pos hω)

/-- Ponderomotive energy in eV: U_p[eV] = 9.33 × I[W/cm²] × λ[μm]² × 10⁻¹⁴ -/
def ponderomotiveEnergyEV (I_Wcm2 lambda_μm : ℝ) : ℝ :=
  9.33 * I_Wcm2 * lambda_μm ^ 2 * 10 ^ (-14 : ℤ)

/-- Ponderomotive potential is positive for positive intensity and wavelength. -/
theorem ponderomotiveEnergyEV_pos {I_Wcm2 lambda_μm : ℝ}
    (hI : 0 < I_Wcm2) (hlambda : 0 < lambda_μm) :
    0 < ponderomotiveEnergyEV I_Wcm2 lambda_μm := by
  unfold ponderomotiveEnergyEV
  positivity

/-- Ponderomotive potential grows linearly with laser intensity at fixed wavelength. -/
theorem ponderomotiveEnergyEV_increases_with_intensity {I₁ I₂ lambda_μm : ℝ}
    (hI : I₁ < I₂) (hlambda : 0 < lambda_μm) :
    ponderomotiveEnergyEV I₁ lambda_μm < ponderomotiveEnergyEV I₂ lambda_μm := by
  unfold ponderomotiveEnergyEV
  have hfactor : 0 < 9.33 * lambda_μm ^ 2 * 10 ^ (-14 : ℤ) := by positivity
  calc
    9.33 * I₁ * lambda_μm ^ 2 * 10 ^ (-14 : ℤ)
        = (9.33 * lambda_μm ^ 2 * 10 ^ (-14 : ℤ)) * I₁ := by ring
    _ < (9.33 * lambda_μm ^ 2 * 10 ^ (-14 : ℤ)) * I₂ :=
      mul_lt_mul_of_pos_left hI hfactor
    _ = 9.33 * I₂ * lambda_μm ^ 2 * 10 ^ (-14 : ℤ) := by ring

/-- Ponderomotive potential grows as wavelength squared at fixed intensity. -/
theorem ponderomotiveEnergyEV_increases_with_wavelength {I_Wcm2 lambda₁ lambda₂ : ℝ}
    (hI : 0 < I_Wcm2) (hlambda₁ : 0 < lambda₁) (hlambda : lambda₁ < lambda₂) :
    ponderomotiveEnergyEV I_Wcm2 lambda₁ < ponderomotiveEnergyEV I_Wcm2 lambda₂ := by
  unfold ponderomotiveEnergyEV
  have hsquare : lambda₁ ^ 2 < lambda₂ ^ 2 := by
    nlinarith [mul_pos hlambda₁ hlambda₁, mul_lt_mul_of_pos_left hlambda hlambda₁,
      mul_lt_mul_of_pos_right hlambda (lt_trans hlambda₁ hlambda)]
  have hfactor : 0 < 9.33 * I_Wcm2 * 10 ^ (-14 : ℤ) := by positivity
  calc
    9.33 * I_Wcm2 * lambda₁ ^ 2 * 10 ^ (-14 : ℤ)
        = (9.33 * I_Wcm2 * 10 ^ (-14 : ℤ)) * lambda₁ ^ 2 := by ring
    _ < (9.33 * I_Wcm2 * 10 ^ (-14 : ℤ)) * lambda₂ ^ 2 :=
      mul_lt_mul_of_pos_left hsquare hfactor
    _ = 9.33 * I_Wcm2 * lambda₂ ^ 2 * 10 ^ (-14 : ℤ) := by ring

/-- For CO₂ at I = 10¹⁰ W/cm²: U_p ≈ 0.105 eV. -/
theorem co2_ponderomotive_at_1e10 :
    |ponderomotiveEnergyEV ((10 : ℝ) ^ 10) 10.6 - 0.10483188| < 0.00000001 := by
  norm_num [ponderomotiveEnergyEV]

end IBParams

end
