/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

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

namespace EUVMedium

/-- Real part of the EUV refractive index convention `ñ = 1 - δ - iβ`. -/
def realIndex (m : EUVMedium) : ℝ := 1 - m.δ

theorem realIndex_pos_of_delta_lt_one (m : EUVMedium) (hδ : m.δ < 1) :
    0 < m.realIndex := by
  unfold realIndex
  linarith

/-- Real part plus decrement reconstructs the EUV convention's unit baseline. -/
theorem realIndex_add_delta (m : EUVMedium) :
    m.realIndex + m.δ = 1 := by
  unfold realIndex
  ring

/-- Full complex EUV refractive index convention `ñ = 1 - δ - iβ`. -/
def complexIndex (m : EUVMedium) : ℂ :=
  ((1 - m.δ : ℝ) : ℂ) - Complex.I * (m.β : ℂ)

theorem complexIndex_re (m : EUVMedium) :
    m.complexIndex.re = 1 - m.δ := by
  simp [complexIndex]

theorem complexIndex_im (m : EUVMedium) :
    m.complexIndex.im = -m.β := by
  simp [complexIndex]

end EUVMedium

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

theorem mo_realIndex_pos : 0 < moAt135nm.realIndex := by
  norm_num [EUVMedium.realIndex, moAt135nm]

theorem si_realIndex_pos : 0 < siAt135nm.realIndex := by
  norm_num [EUVMedium.realIndex, siAt135nm]

theorem ru_realIndex_pos : 0 < ruAt135nm.realIndex := by
  norm_num [EUVMedium.realIndex, ruAt135nm]

theorem mo_realIndex_numeric : moAt135nm.realIndex = (0.923 : ℝ) := by
  norm_num [EUVMedium.realIndex, moAt135nm]

theorem si_realIndex_numeric : siAt135nm.realIndex = (0.999 : ℝ) := by
  norm_num [EUVMedium.realIndex, siAt135nm]

theorem ru_realIndex_numeric : ruAt135nm.realIndex = (0.927 : ℝ) := by
  norm_num [EUVMedium.realIndex, ruAt135nm]

theorem mo_complexIndex_re_numeric : moAt135nm.complexIndex.re = (0.923 : ℝ) := by
  norm_num [EUVMedium.complexIndex, moAt135nm]

theorem mo_complexIndex_im_numeric : moAt135nm.complexIndex.im = (-0.006 : ℝ) := by
  norm_num [EUVMedium.complexIndex, moAt135nm]

theorem si_complexIndex_re_numeric : siAt135nm.complexIndex.re = (0.999 : ℝ) := by
  norm_num [EUVMedium.complexIndex, siAt135nm]

theorem si_complexIndex_im_numeric : siAt135nm.complexIndex.im = (-0.002 : ℝ) := by
  norm_num [EUVMedium.complexIndex, siAt135nm]

theorem ru_complexIndex_re_numeric : ruAt135nm.complexIndex.re = (0.927 : ℝ) := by
  norm_num [EUVMedium.complexIndex, ruAt135nm]

theorem ru_complexIndex_im_numeric : ruAt135nm.complexIndex.im = (-0.015 : ℝ) := by
  norm_num [EUVMedium.complexIndex, ruAt135nm]

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

/-- Complex Fresnel reflection amplitude for s-polarization,
    parameterized by the complex cosines in the two media. -/
def fresnelAmplitudeSComplex (n₁ n₂ cosθi cosθt : ℂ) : ℂ :=
  (n₁ * cosθi - n₂ * cosθt) / (n₁ * cosθi + n₂ * cosθt)

theorem fresnelAmplitudeSComplex_normal_eq (n₁ n₂ : ℂ) :
    fresnelAmplitudeSComplex n₁ n₂ 1 1 = (n₁ - n₂) / (n₁ + n₂) := by
  simp [fresnelAmplitudeSComplex]

/-- Complex Fresnel reflectance is the squared modulus of the complex amplitude. -/
def fresnelReflectanceSComplex (n₁ n₂ cosθi cosθt : ℂ) : ℝ :=
  ‖fresnelAmplitudeSComplex n₁ n₂ cosθi cosθt‖ ^ 2

theorem fresnelReflectanceSComplex_nonneg (n₁ n₂ cosθi cosθt : ℂ) :
    0 ≤ fresnelReflectanceSComplex n₁ n₂ cosθi cosθt := by
  simp [fresnelReflectanceSComplex]

/-- Snell's law: n₁ sin θᵢ = n₂ sin θₜ -/
def snellsLaw (n₁ n₂ θᵢ θₜ : ℝ) : Prop :=
  n₁ * sin θᵢ = n₂ * sin θₜ

theorem snellsLaw_symm {n₁ n₂ θᵢ θₜ : ℝ} (h : snellsLaw n₁ n₂ θᵢ θₜ) :
    snellsLaw n₂ n₁ θₜ θᵢ := h.symm

/-- Complex-amplitude Snell relation, written in terms of complex sine values. -/
def snellsLawComplex (n₁ n₂ sinθi sinθt : ℂ) : Prop :=
  n₁ * sinθi = n₂ * sinθt

theorem snellsLawComplex_symm {n₁ n₂ sinθi sinθt : ℂ}
    (h : snellsLawComplex n₁ n₂ sinθi sinθt) :
    snellsLawComplex n₂ n₁ sinθt sinθi := h.symm

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

/-- Larger extinction coefficient β increases the EUV absorption coefficient. -/
theorem absorptionCoeff_increases_with_beta {β₁ β₂ lam : ℝ}
    (hβ : β₁ < β₂) (hlam : 0 < lam) :
    absorptionCoeff β₁ lam < absorptionCoeff β₂ lam := by
  unfold absorptionCoeff
  exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hβ (mul_pos (by norm_num) pi_pos))
    hlam

/-- Longer wavelength lowers the absorption coefficient for fixed β. -/
theorem absorptionCoeff_decreases_with_wavelength {β lam₁ lam₂ : ℝ}
    (hβ : 0 < β) (hlam₁ : 0 < lam₁) (hlam : lam₁ < lam₂) :
    absorptionCoeff β lam₂ < absorptionCoeff β lam₁ := by
  unfold absorptionCoeff
  exact div_lt_div_of_pos_left (mul_pos (mul_pos (by norm_num) pi_pos) hβ) hlam₁ hlam

theorem mo_absorptionCoeff_pos_at_135nm :
    0 < absorptionCoeff moAt135nm.β (13.5e-9) := by
  exact absorptionCoeff_pos (by norm_num [moAt135nm]) (by norm_num)

theorem si_absorptionCoeff_pos_at_135nm :
    0 < absorptionCoeff siAt135nm.β (13.5e-9) := by
  exact absorptionCoeff_pos (by norm_num [siAt135nm]) (by norm_num)

theorem ru_absorptionCoeff_pos_at_135nm :
    0 < absorptionCoeff ruAt135nm.β (13.5e-9) := by
  exact absorptionCoeff_pos (by norm_num [ruAt135nm]) (by norm_num)

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
