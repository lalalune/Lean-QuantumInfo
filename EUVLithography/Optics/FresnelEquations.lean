/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!

# EUV Lithography: Fresnel Equations for EUV Optics

Formalizes the Fresnel reflection and transmission coefficients for EUV
light at interfaces between media with complex refractive indices.
At EUV wavelengths, all materials have complex ñ = 1 - δ - iβ with δ,β ≪ 1.

## Main definitions

- `EUVMedium` : Medium characterized by δ and β (EUV refractive index convention)
- `fresnelReflectanceNormal` : R = ((n₁-n₂)/(n₁+n₂))² at normal incidence
- `fresnelAmplitudeS` : rs at arbitrary angle for s-polarization
- `absorptionCoeff` : α = 4π β / λ
- `transmittance` : T = exp(-α d)

## Main results

- `fresnelReflectanceNormal_nonneg` : R ≥ 0
- `fresnelReflectanceNormal_lt_one` : R < 1 (for positive indices)
- `fresnelReflectanceNormal_symm` : R(n₁,n₂) = R(n₂,n₁)
- `absorptionCoeff_pos` : α > 0
- `transmittance_pos` : T > 0
- `transmittance_le_one` : T ≤ 1

-/

noncomputable section

open Real

/-- An optical medium at EUV wavelengths:
    ñ = 1 - δ - iβ where δ is the refractive decrement and β is absorption -/
structure EUVMedium where
  /-- Refractive index decrement δ (dimensionless, > 0 for most materials) -/
  δ : ℝ
  δ_nonneg : 0 ≤ δ
  /-- Extinction coefficient β (dimensionless, ≥ 0) -/
  β : ℝ
  β_nonneg : 0 ≤ β

/-- At normal incidence, Fresnel reflectance for s and p (degenerate):
    R = ((n₁ - n₂)/(n₁ + n₂))² -/
def fresnelReflectanceNormal (n₁ n₂ : ℝ) : ℝ :=
  ((n₁ - n₂) / (n₁ + n₂)) ^ 2

theorem fresnelReflectanceNormal_nonneg (n₁ n₂ : ℝ) :
    0 ≤ fresnelReflectanceNormal n₁ n₂ := sq_nonneg _

theorem fresnelReflectanceNormal_lt_one {n₁ n₂ : ℝ} (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) :
    fresnelReflectanceNormal n₁ n₂ < 1 := by
  unfold fresnelReflectanceNormal
  rw [sq_lt_one_iff_abs_lt_one]
  rw [abs_div, abs_of_pos (add_pos hn₁ hn₂)]
  exact (div_lt_one (add_pos hn₁ hn₂)).2 (abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩)

theorem fresnelReflectanceNormal_symm (n₁ n₂ : ℝ) :
    fresnelReflectanceNormal n₁ n₂ = fresnelReflectanceNormal n₂ n₁ := by
  unfold fresnelReflectanceNormal
  ring

/-- Mo/Si refractive indices at 13.5 nm -/
def moAt135nm : EUVMedium :=
  { δ := 0.077, β := 0.006, δ_nonneg := by norm_num, β_nonneg := by norm_num }

def siAt135nm : EUVMedium :=
  { δ := 0.001, β := 0.002, δ_nonneg := by norm_num, β_nonneg := by norm_num }

def ruAt135nm : EUVMedium :=
  { δ := 0.073, β := 0.015, δ_nonneg := by norm_num, β_nonneg := by norm_num }

/-- Single Mo/Si interface reflectance at normal incidence (real part approx):
    R ≈ ((δ_Mo - δ_Si)/(2 - (δ_Mo + δ_Si)))² ≈ 0.13% -/
theorem mo_si_interface_reflectance :
    let R := fresnelReflectanceNormal (1 - moAt135nm.δ) (1 - siAt135nm.δ)
    R < 0.002 := by
  simp [fresnelReflectanceNormal, moAt135nm, siAt135nm]
  norm_num

/-- Generalized Fresnel reflection amplitude for s-polarization -/
def fresnelAmplitudeS (n₁ n₂ θᵢ : ℝ) : ℝ :=
  let cosθt := sqrt (max 0 (1 - (n₁ * sin θᵢ / n₂) ^ 2))
  (n₁ * cos θᵢ - n₂ * cosθt) / (n₁ * cos θᵢ + n₂ * cosθt)

/-- Fresnel reflectance for s-polarization: R = |r|² -/
def fresnelReflectanceS (n₁ n₂ θᵢ : ℝ) : ℝ :=
  fresnelAmplitudeS n₁ n₂ θᵢ ^ 2

theorem fresnelReflectanceS_nonneg (n₁ n₂ θᵢ : ℝ) : 0 ≤ fresnelReflectanceS n₁ n₂ θᵢ :=
  sq_nonneg _

/-- Snell's law: n₁ sin θᵢ = n₂ sin θₜ -/
def snellsLaw (n₁ n₂ θᵢ θₜ : ℝ) : Prop :=
  n₁ * sin θᵢ = n₂ * sin θₜ

theorem snellsLaw_symm {n₁ n₂ θᵢ θₜ : ℝ} (h : snellsLaw n₁ n₂ θᵢ θₜ) :
    snellsLaw n₂ n₁ θₜ θᵢ := h.symm

/-- Critical angle for total external reflection:
    sin θ_c = n₂/n₁ for n₂ < n₁ (EUV grazing mirrors) -/
def criticalAngle (n₁ n₂ : ℝ) : ℝ := arcsin (n₂ / n₁)

/-- Beer-Lambert attenuation in absorbing medium:
    The imaginary part β of the refractive index gives absorption coefficient
    α = 4π β / lam  (lam = wavelength) -/
def absorptionCoeff (β lam : ℝ) : ℝ := 4 * π * β / lam

theorem absorptionCoeff_pos {β lam : ℝ} (hβ : 0 < β) (hlam : 0 < lam) :
    0 < absorptionCoeff β lam :=
  div_pos (mul_pos (mul_pos (by norm_num) pi_pos) hβ) hlam

/-- Intensity transmission after thickness d in absorbing medium:
    T = exp(-α d) -/
def transmittance (β lam d : ℝ) : ℝ :=
  exp (-(absorptionCoeff β lam * d))

theorem transmittance_pos (β lam d : ℝ) : 0 < transmittance β lam d :=
  exp_pos _

theorem transmittance_le_one (β lam d : ℝ) (hβ : 0 ≤ β) (hlam : 0 < lam) (hd : 0 ≤ d) :
    transmittance β lam d ≤ 1 := by
  unfold transmittance
  rw [← exp_zero]
  apply exp_le_exp.mpr
  apply neg_nonpos_of_nonneg
  exact mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt pi_pos)) hβ)
    (le_of_lt hlam)) hd

theorem transmittance_mono_d {β lam : ℝ} (hβ : 0 < β) (hlam : 0 < lam)
    {d₁ d₂ : ℝ} (hd : d₁ < d₂) :
    transmittance β lam d₂ < transmittance β lam d₁ := by
  unfold transmittance
  apply exp_lt_exp.mpr
  apply neg_lt_neg
  exact mul_lt_mul_of_pos_left hd (absorptionCoeff_pos hβ hlam)

end
