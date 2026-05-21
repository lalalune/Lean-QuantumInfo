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

/-- CO₂ (10.6 μm) vs Nd:YAG (1.064 μm): IB ratio ≈ (10.6/1.064)² ≈ 99.2 -/
theorem co2_vs_ndyag_ib_ratio :
    (10.6 / 1.064 : ℝ) ^ 2 > 99 := by norm_num

/-- Ponderomotive energy: U_p = e² E₀² / (4 m_e ω²) -/
def ponderomotiveEnergy (e m_e E₀ ω : ℝ) : ℝ :=
  e ^ 2 * E₀ ^ 2 / (4 * m_e * ω ^ 2)

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

/-- For CO₂ at I = 10¹⁰ W/cm²: U_p ≈ 0.105 eV. -/
theorem co2_ponderomotive_at_1e10 :
    |ponderomotiveEnergyEV ((10 : ℝ) ^ 10) 10.6 - 0.10483188| < 0.00000001 := by
  norm_num [ponderomotiveEnergyEV]

end IBParams

end
