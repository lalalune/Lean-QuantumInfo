/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!

# EUV Lithography: Bragg Condition for Multilayer Mirrors

Formalizes the Bragg condition for constructive interference in Mo/Si
multilayer mirrors. At λ = 13.5 nm, the multilayer period is d ≈ 6.75 nm.

## Main definitions

- `MultilayerMirror` : Mo/Si multilayer stack geometry
- `braggCondition` : 2d cos θ = mλ (generalized for near-normal incidence)
- `optimalPeriod` : d_opt = mλ / (2 cos θ)
- `bilayerPeriod` : d = d_Mo + d_Si
- `debyeWallerFactor` : Γ = exp(-2(2π σ_r/λ)²) roughness reduction

## Main results

- `bragg_first_order` : m=1, θ≈0 gives d ≈ λ/2 = 6.75 nm
- `optimalPeriod_pos` : d_opt > 0
- `braggCondition_normal_incidence` : θ=0 → 2d = mλ
- `debyeWaller_le_one` : Γ ≤ 1 (roughness reduces reflectivity)
- `debyeWaller_one_at_zero` : Γ = 1 for perfect interfaces (σ_r = 0)
- `debyeWaller_lt_one_of_roughness` : Γ < 1 when σ_r > 0
- `relBandwidth_pos` : Δλ/λ > 0

-/

noncomputable section

open Real

/-- Parameters for a Mo/Si multilayer mirror.
    Note: wavelength is named `lam` to avoid conflict with Lean's `λ` keyword. -/
structure MultilayerMirror where
  /-- Target wavelength (m), ≈ 13.5e-9 -/
  lam : ℝ
  lam_pos : 0 < lam
  /-- Mo layer thickness (m), ≈ 2.8e-9 -/
  d_Mo : ℝ
  d_Mo_pos : 0 < d_Mo
  /-- Si layer thickness (m), ≈ 4.1e-9 -/
  d_Si : ℝ
  d_Si_pos : 0 < d_Si
  /-- Number of bilayers, typically 40 -/
  N : ℕ
  N_pos : 0 < N
  /-- Interface roughness σ_r (m), typically ~0.4e-9 -/
  σ_r : ℝ
  σ_r_nonneg : 0 ≤ σ_r

namespace MultilayerMirror

variable (m : MultilayerMirror)

/-- Total bilayer period -/
def period : ℝ := m.d_Mo + m.d_Si

theorem period_pos : 0 < m.period :=
  add_pos m.d_Mo_pos m.d_Si_pos

/-- The Mo/Si bilayer period is the sum of Mo and Si layer thicknesses. -/
theorem period_eq_mo_plus_si : m.period = m.d_Mo + m.d_Si := rfl

/-- Report arithmetic: `2.8 nm + 4.1 nm = 6.9 nm`, close to the 6.75 nm Bragg period. -/
theorem mo_si_nominal_period_numeric :
    (2.8 : ℝ) + 4.1 = 6.9 := by
  norm_num

/-- Bragg condition: 2d cos θ = n·λ (n = diffraction order) -/
def satisfiesBragg (θ : ℝ) (n : ℕ) : Prop :=
  2 * m.period * cos θ = n * m.lam

/-- For normal incidence (θ = 0), Bragg condition becomes 2d = n·λ -/
theorem bragg_normal_incidence (n : ℕ) :
    m.satisfiesBragg 0 n ↔ 2 * m.period = n * m.lam := by
  simp [satisfiesBragg, cos_zero]

/-- Optimal period for first-order Bragg at normal incidence: d = λ/2 -/
def optimalPeriodNormal : ℝ := m.lam / 2

theorem optimalPeriodNormal_pos : 0 < m.optimalPeriodNormal :=
  div_pos m.lam_pos two_pos

/-- First-order Bragg condition at normal incidence -/
theorem bragg_first_order_normal :
    2 * m.optimalPeriodNormal = 1 * m.lam := by
  simp [optimalPeriodNormal]; ring

/-- First-order normal-incidence Bragg condition is equivalent to `d = λ/2`. -/
theorem bragg_first_order_normal_iff :
    m.satisfiesBragg 0 1 ↔ m.period = m.lam / 2 := by
  rw [bragg_normal_incidence]
  constructor
  · intro h
    norm_num at h
    linarith
  · intro h
    rw [h]
    ring

/-- EUV mirror: period ≈ λ/2 = 6.75 nm for λ = 13.5 nm -/
theorem euv_period_approx : m.optimalPeriodNormal = m.lam / 2 := rfl

/-- Optimal period for order n at incidence angle θ -/
def optimalPeriod (θ : ℝ) (n : ℕ) (_hn : 0 < n) : ℝ :=
  n * m.lam / (2 * cos θ)

theorem optimalPeriod_pos {θ : ℝ} {n : ℕ} (hn : 0 < n) (hθ : cos θ > 0) :
    0 < m.optimalPeriod θ n hn :=
  div_pos (mul_pos (Nat.cast_pos.mpr hn) m.lam_pos) (mul_pos two_pos hθ)

/-- Bragg condition is satisfied at the optimal period -/
theorem optimal_period_satisfies_bragg {θ : ℝ} {n : ℕ} (hn : 0 < n) (hθ : cos θ ≠ 0) :
    2 * m.optimalPeriod θ n hn * cos θ = n * m.lam := by
  unfold optimalPeriod
  field_simp

/-- Debye-Waller roughness factor: Γ = exp(-2(2π σ_r/λ)²) -/
def debyeWallerFactor : ℝ :=
  exp (-2 * (2 * π * m.σ_r / m.lam) ^ 2)

theorem debyeWaller_pos : 0 < m.debyeWallerFactor :=
  exp_pos _

theorem debyeWaller_le_one : m.debyeWallerFactor ≤ 1 := by
  unfold debyeWallerFactor
  rw [← Real.exp_zero]
  apply exp_le_exp.mpr
  nlinarith [sq_nonneg (2 * π * m.σ_r / m.lam)]

/-- Perfect interfaces give Γ = 1 -/
theorem debyeWaller_one_at_zero (h : m.σ_r = 0) :
    m.debyeWallerFactor = 1 := by
  simp [debyeWallerFactor, h]

/-- Γ is strictly less than 1 when σ_r > 0 -/
theorem debyeWaller_lt_one_of_roughness (hσ : 0 < m.σ_r) :
    m.debyeWallerFactor < 1 := by
  unfold debyeWallerFactor
  rw [← Real.exp_zero]
  apply exp_lt_exp.mpr
  nlinarith [sq_pos_of_pos (div_pos (mul_pos (mul_pos two_pos pi_pos) hσ) m.lam_pos)]

/-- Larger interface roughness gives a smaller Debye-Waller reflectivity factor. -/
theorem debyeWaller_decreases_with_roughness {m₁ m₂ : MultilayerMirror}
    (hlam : m₁.lam = m₂.lam) (hσ₁ : 0 < m₁.σ_r) (hσ : m₁.σ_r < m₂.σ_r) :
    m₂.debyeWallerFactor < m₁.debyeWallerFactor := by
  unfold debyeWallerFactor
  rw [← hlam]
  apply exp_lt_exp.mpr
  have harg : 2 * π * m₁.σ_r / m₁.lam < 2 * π * m₂.σ_r / m₁.lam := by
    exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hσ (mul_pos two_pos pi_pos))
      m₁.lam_pos
  have harg_pos : 0 < 2 * π * m₁.σ_r / m₁.lam :=
    div_pos (mul_pos (mul_pos two_pos pi_pos) hσ₁) m₁.lam_pos
  have hsq : (2 * π * m₁.σ_r / m₁.lam) ^ 2 <
      (2 * π * m₂.σ_r / m₁.lam) ^ 2 :=
    sq_lt_sq' (by linarith [harg_pos, harg]) harg
  nlinarith

/-- Single-interface reflectance amplitude r₁₂ for Mo/Si -/
def interfaceReflectance (δ_Mo δ_Si : ℝ) : ℝ :=
  (δ_Mo - δ_Si) / (2 * (1 - (δ_Mo + δ_Si) / 2))

/-- Peak reflectivity estimate for N bilayers (tanh approximation):
    R_peak ≈ tanh²(N · |r₁₂|/2 · Γ)
    Since tanh < 1, we have R < 1. -/
def peakReflectivityArgument (r12 : ℝ) : ℝ :=
  m.N * (|r12| / 2) * m.debyeWallerFactor

def peakReflectivity (r12 : ℝ) : ℝ :=
  Real.tanh (m.peakReflectivityArgument r12) ^ 2

theorem peakReflectivity_argument_nonneg {r12 : ℝ} :
    0 ≤ m.peakReflectivityArgument r12 := by
  unfold peakReflectivityArgument
  exact
  mul_nonneg
    (mul_nonneg (Nat.cast_nonneg m.N) (div_nonneg (abs_nonneg r12) two_pos.le))
    m.debyeWaller_pos.le

/-- No interface contrast gives zero peak-reflectivity argument. -/
theorem peakReflectivityArgument_zero_of_no_contrast :
    m.peakReflectivityArgument 0 = 0 := by
  simp [peakReflectivityArgument]

/-- The peak-reflectivity argument is positive when there is nonzero interface contrast. -/
theorem peakReflectivityArgument_pos_of_contrast {r12 : ℝ} (hr : r12 ≠ 0) :
    0 < m.peakReflectivityArgument r12 := by
  unfold peakReflectivityArgument
  exact mul_pos
    (mul_pos (Nat.cast_pos.mpr m.N_pos) (div_pos (abs_pos.mpr hr) two_pos))
    m.debyeWaller_pos

/-- More bilayers increase the tanh-approximation stack-strength argument at fixed interface
contrast and roughness factor. -/
theorem peakReflectivityArgument_increases_with_bilayers {N₁ N₂ : ℕ} {r12 Γ : ℝ}
    (hN : N₁ < N₂) (hr : r12 ≠ 0) (hΓ : 0 < Γ) :
    (N₁ : ℝ) * (|r12| / 2) * Γ < (N₂ : ℝ) * (|r12| / 2) * Γ := by
  exact mul_lt_mul_of_pos_right
    (mul_lt_mul_of_pos_right (Nat.cast_lt.mpr hN) (div_pos (abs_pos.mpr hr) two_pos)) hΓ

/-- Rougher interfaces lower the tanh-approximation stack-strength argument through Γ. -/
theorem peakReflectivityArgument_decreases_with_roughness_factor {N : ℕ} {r12 Γ₁ Γ₂ : ℝ}
    (hN : 0 < N) (hr : r12 ≠ 0) (hΓ : Γ₁ < Γ₂) :
    (N : ℝ) * (|r12| / 2) * Γ₁ < (N : ℝ) * (|r12| / 2) * Γ₂ := by
  exact mul_lt_mul_of_pos_left hΓ
    (mul_pos (Nat.cast_pos.mpr hN) (div_pos (abs_pos.mpr hr) two_pos))

theorem peakReflectivity_nonneg {r12 : ℝ} :
    0 ≤ m.peakReflectivity r12 := sq_nonneg _

theorem peakReflectivity_lt_one {r12 : ℝ} :
    m.peakReflectivity r12 < 1 := by
  unfold peakReflectivity
  exact Real.tanh_sq_lt_one (m.peakReflectivityArgument r12)

/-- With no index contrast there is no Bragg-stack reflection in the tanh approximation. -/
theorem peakReflectivity_zero_of_no_contrast :
    m.peakReflectivity 0 = 0 := by
  simp [peakReflectivity, peakReflectivityArgument]

/-- Perfect interfaces remove the Debye-Waller roughness penalty in the peak-reflectivity estimate. -/
theorem peakReflectivity_perfect_interfaces {r12 : ℝ} (hσ : m.σ_r = 0) :
    m.peakReflectivity r12 = Real.tanh (m.N * (|r12| / 2)) ^ 2 := by
  simp [peakReflectivity, peakReflectivityArgument, debyeWallerFactor, hσ]

/-- Spectral bandwidth: Δλ/λ ≈ 1/(2N) -/
def relBandwidth : ℝ := 1 / (2 * m.N)

theorem relBandwidth_pos : 0 < m.relBandwidth :=
  div_pos one_pos (mul_pos two_pos (Nat.cast_pos.mpr m.N_pos))

theorem relBandwidth_halves_when_N_doubles {m₁ m₂ : MultilayerMirror}
    (hN : m₂.N = 2 * m₁.N) (hN₁ : 0 < m₁.N) :
    m₂.relBandwidth = m₁.relBandwidth / 2 := by
  simp [relBandwidth, hN]
  field_simp

end MultilayerMirror

end
