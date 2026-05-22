/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!

# EUV Lithography: Transfer Matrix Method for Multilayer Optics

Formalizes the 2×2 transfer matrix method for calculating EUV reflection
and transmission through multilayer mirror stacks.

## Main definitions

- `propagationPhase` : φ = 2π n d cosθ / lam (phase in layer)
- `transferMatrix` : M = [[cosφ, -sinφ/η], [-η sinφ, cosφ]]
- `stackMatrix` : Product of all layer matrices
- `reflectionAmplitude` : r from the total matrix

## Main results

- `transferMatrix_det_one` : det(M_j) = 1 (unimodularity, energy conservation)
- `stack_det_one` : det(M_stack) = 1
- `nBilayerStack_det_one` : det((M_Si M_Mo)^N) = 1
- `propagationPhase_linear_in_d` : Phase is additive for layers

-/

noncomputable section

open Real Matrix

/-- The propagation phase in a layer of thickness d with refractive index n at angle cosθ:
    φ = 2π n d cosθ / lam  (lam = wavelength) -/
def propagationPhase (n d cosθ lam : ℝ) : ℝ :=
  2 * π * n * d * cosθ / lam

theorem propagationPhase_pos {n d cosθ lam : ℝ}
    (hn : 0 < n) (hd : 0 < d) (hcosθ : 0 < cosθ) (hlam : 0 < lam) :
    0 < propagationPhase n d cosθ lam :=
  div_pos (mul_pos (mul_pos (mul_pos (mul_pos two_pos pi_pos) hn) hd) hcosθ) hlam

theorem propagationPhase_linear_in_d {n d₁ d₂ cosθ lam : ℝ} :
    propagationPhase n (d₁ + d₂) cosθ lam =
    propagationPhase n d₁ cosθ lam + propagationPhase n d₂ cosθ lam := by
  unfold propagationPhase; ring

theorem propagationPhase_monotone_in_d {n cosθ lam : ℝ} (hn : 0 < n) (hcosθ : 0 < cosθ)
    (hlam : 0 < lam) {d₁ d₂ : ℝ} (hd : d₁ < d₂) :
    propagationPhase n d₁ cosθ lam < propagationPhase n d₂ cosθ lam := by
  unfold propagationPhase
  apply div_lt_div_of_pos_right _ hlam
  nlinarith [mul_pos (mul_pos two_pos pi_pos) hn, mul_pos hcosθ (sub_pos.mpr hd)]

/-- Complex propagation phase used in absorbing EUV multilayers:
    `φ = 2π ñ d cosθ / λ`. -/
def propagationPhaseComplex (n cosθ : ℂ) (d lam : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * n * (d : ℂ) * cosθ) / (lam : ℂ)

theorem propagationPhaseComplex_eq_real_cast (n d cosθ lam : ℝ) :
    propagationPhaseComplex (n : ℂ) (cosθ : ℂ) d lam =
      (propagationPhase n d cosθ lam : ℂ) := by
  simp [propagationPhaseComplex, propagationPhase]

/-- S-polarization optical admittance surrogate: `η̃ = n cosθ / η₀`. -/
def layerAdmittanceS (n cosθ η₀ : ℝ) : ℝ :=
  n * cosθ / η₀

/-- Complex s-polarization optical admittance `η̃ = ñ cosθ / η₀`. -/
def layerAdmittanceSComplex (n cosθ η₀ : ℂ) : ℂ :=
  n * cosθ / η₀

theorem layerAdmittanceSComplex_eq_real_cast (n cosθ η₀ : ℝ) :
    layerAdmittanceSComplex (n : ℂ) (cosθ : ℂ) (η₀ : ℂ) =
      (layerAdmittanceS n cosθ η₀ : ℂ) := by
  simp [layerAdmittanceSComplex, layerAdmittanceS]

theorem layerAdmittanceS_pos {n cosθ η₀ : ℝ}
    (hn : 0 < n) (hcosθ : 0 < cosθ) (hη₀ : 0 < η₀) :
    0 < layerAdmittanceS n cosθ η₀ := by
  unfold layerAdmittanceS
  exact div_pos (mul_pos hn hcosθ) hη₀

theorem layerAdmittanceS_increases_with_index {n₁ n₂ cosθ η₀ : ℝ}
    (hn : n₁ < n₂) (hcosθ : 0 < cosθ) (hη₀ : 0 < η₀) :
    layerAdmittanceS n₁ cosθ η₀ < layerAdmittanceS n₂ cosθ η₀ := by
  unfold layerAdmittanceS
  exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_right hn hcosθ) hη₀

/-- The real-valued 2×2 transfer matrix surrogate for a single homogeneous layer.
    It uses the sign convention `[[cos φ, sin φ / η], [-η sin φ, cos φ]]`,
    whose determinant is one for nonzero admittance. The physical EUV formula in
    the report carries complex `-i` factors; this real surrogate captures the
    same unimodular algebra without complex amplitudes. -/
def transferMatrix (φ η : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![cos φ, sin φ / η;
     -(η * sin φ), cos φ]

/-- The transfer matrix has determinant 1 (unimodular = energy conservation) -/
theorem transferMatrix_det_one (φ η : ℝ) (hη : η ≠ 0) :
    (transferMatrix φ η).det = 1 := by
  simp [transferMatrix, det_fin_two]
  field_simp [hη]
  rw [← sin_sq_add_cos_sq φ]
  ring

/-- Complex-valued transfer matrix in the report convention:
    `[[cos φ, -i sin φ / η], [-i η sin φ, cos φ]]`. -/
def transferMatrixComplex (φ η : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.cos φ, -Complex.I * Complex.sin φ / η;
     -Complex.I * η * Complex.sin φ, Complex.cos φ]

/-- The report-form complex layer matrix is unimodular for nonzero admittance. -/
theorem transferMatrixComplex_det_one (φ η : ℂ) (hη : η ≠ 0) :
    (transferMatrixComplex φ η).det = 1 := by
  simp [transferMatrixComplex, det_fin_two]
  field_simp [hη]
  ring_nf
  simpa [pow_two, add_comm] using Complex.cos_sq_add_sin_sq φ

/-- Transfer matrix for a complex layer with zero phase is the identity. -/
theorem transferMatrixComplex_zero_phase (η : ℂ) :
    transferMatrixComplex 0 η = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [transferMatrixComplex]

/-- Product of two unimodular matrices is unimodular -/
theorem mul_unimodular {M N : Matrix (Fin 2) (Fin 2) ℝ}
    (hM : M.det = 1) (hN : N.det = 1) : (M * N).det = 1 := by
  rw [det_mul, hM, hN, mul_one]

/-- The identity matrix is unimodular -/
theorem one_unimodular : (1 : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := det_one

/-- Product of two complex unimodular matrices is unimodular. -/
theorem mul_unimodular_complex {M N : Matrix (Fin 2) (Fin 2) ℂ}
    (hM : M.det = 1) (hN : N.det = 1) : (M * N).det = 1 := by
  rw [det_mul, hM, hN, mul_one]

/-- The complex identity matrix is unimodular. -/
theorem one_unimodular_complex : (1 : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := det_one

/-- Ordered stack product of layer matrices. -/
def stackMatrix : List (Matrix (Fin 2) (Fin 2) ℝ) → Matrix (Fin 2) (Fin 2) ℝ
  | [] => 1
  | M :: Ms => M * stackMatrix Ms

/-- Ordered stack product of complex layer matrices. -/
def stackMatrixComplex : List (Matrix (Fin 2) (Fin 2) ℂ) → Matrix (Fin 2) (Fin 2) ℂ
  | [] => 1
  | M :: Ms => M * stackMatrixComplex Ms

/-- Stack of unimodular matrices has determinant 1. -/
theorem stack_det_one :
    ∀ layers : List (Matrix (Fin 2) (Fin 2) ℝ),
      (∀ M ∈ layers, M.det = 1) → (stackMatrix layers).det = 1
  | [], _ => by simp [stackMatrix, det_one]
  | M :: Ms, h => by
      simp [stackMatrix, det_mul, h M (by simp), stack_det_one Ms (by
        intro N hN
        exact h N (by simp [hN]))]

/-- Stack of complex unimodular matrices has determinant 1. -/
theorem stackComplex_det_one :
    ∀ layers : List (Matrix (Fin 2) (Fin 2) ℂ),
      (∀ M ∈ layers, M.det = 1) → (stackMatrixComplex layers).det = 1
  | [], _ => by simp [stackMatrixComplex, det_one]
  | M :: Ms, h => by
      simp [stackMatrixComplex, det_mul, h M (by simp), stackComplex_det_one Ms (by
        intro N hN
        exact h N (by simp [hN]))]

/-- Transfer matrix for a layer with zero phase = identity -/
theorem transferMatrix_zero_phase (η : ℝ) :
    transferMatrix 0 η = 1 := by
  simp [transferMatrix, Matrix.one_fin_two]

/-- Transfer matrix for N identical bilayers of Mo/Si -/
def nBilayerStack (φ_Mo φ_Si η_Mo η_Si : ℝ) (N : ℕ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  (transferMatrix φ_Si η_Si * transferMatrix φ_Mo η_Mo) ^ N

/-- Transfer matrix for `N` Mo/Si bilayers using the report's complex convention. -/
def nBilayerStackComplex (φ_Mo φ_Si η_Mo η_Si : ℂ) (N : ℕ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  (transferMatrixComplex φ_Si η_Si * transferMatrixComplex φ_Mo η_Mo) ^ N

/-- Full multilayer stack from cap, N Mo/Si bilayers, and substrate:
    `M_total = M_cap · (M_Si M_Mo)^N · M_sub`. -/
def cappedBilayerStack
    (M_cap M_Si M_Mo M_sub : Matrix (Fin 2) (Fin 2) ℝ) (N : ℕ) :
    Matrix (Fin 2) (Fin 2) ℝ :=
  M_cap * (M_Si * M_Mo) ^ N * M_sub

/-- Complex cap/bilayer/substrate stack:
    `M_total = M_cap · (M_Si M_Mo)^N · M_sub`. -/
def cappedBilayerStackComplex
    (M_cap M_Si M_Mo M_sub : Matrix (Fin 2) (Fin 2) ℂ) (N : ℕ) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  M_cap * (M_Si * M_Mo) ^ N * M_sub

/-- A cap/bilayer/substrate stack of unimodular layer matrices is unimodular. -/
theorem cappedBilayerStack_det_one
    (M_cap M_Si M_Mo M_sub : Matrix (Fin 2) (Fin 2) ℝ) (N : ℕ)
    (hcap : M_cap.det = 1) (hSi : M_Si.det = 1) (hMo : M_Mo.det = 1)
    (hsub : M_sub.det = 1) :
    (cappedBilayerStack M_cap M_Si M_Mo M_sub N).det = 1 := by
  unfold cappedBilayerStack
  rw [det_mul, det_mul, hcap, hsub, det_pow, det_mul, hSi, hMo]
  simp

/-- A complex cap/bilayer/substrate stack of unimodular layer matrices is unimodular. -/
theorem cappedBilayerStackComplex_det_one
    (M_cap M_Si M_Mo M_sub : Matrix (Fin 2) (Fin 2) ℂ) (N : ℕ)
    (hcap : M_cap.det = 1) (hSi : M_Si.det = 1) (hMo : M_Mo.det = 1)
    (hsub : M_sub.det = 1) :
    (cappedBilayerStackComplex M_cap M_Si M_Mo M_sub N).det = 1 := by
  unfold cappedBilayerStackComplex
  rw [det_mul, det_mul, hcap, hsub, det_pow, det_mul, hSi, hMo]
  simp

/-- With zero bilayers, the capped stack is just cap followed by substrate. -/
theorem cappedBilayerStack_zero
    (M_cap M_Si M_Mo M_sub : Matrix (Fin 2) (Fin 2) ℝ) :
    cappedBilayerStack M_cap M_Si M_Mo M_sub 0 = M_cap * M_sub := by
  simp [cappedBilayerStack]

theorem nBilayerStack_det_one (φ_Mo φ_Si η_Mo η_Si : ℝ) (N : ℕ) :
    η_Mo ≠ 0 → η_Si ≠ 0 →
    (nBilayerStack φ_Mo φ_Si η_Mo η_Si N).det = 1 := by
  intro hMo hSi
  unfold nBilayerStack
  rw [det_pow, mul_unimodular (transferMatrix_det_one _ _ hSi) (transferMatrix_det_one _ _ hMo)]
  simp

/-- The report-form complex `N`-bilayer stack is unimodular when both admittances are nonzero. -/
theorem nBilayerStackComplex_det_one (φ_Mo φ_Si η_Mo η_Si : ℂ) (N : ℕ) :
    η_Mo ≠ 0 → η_Si ≠ 0 →
    (nBilayerStackComplex φ_Mo φ_Si η_Mo η_Si N).det = 1 := by
  intro hMo hSi
  unfold nBilayerStackComplex
  rw [det_pow,
    mul_unimodular_complex (transferMatrixComplex_det_one _ _ hSi)
      (transferMatrixComplex_det_one _ _ hMo)]
  simp

/-- Approximate reflection amplitude from the total transfer matrix:
    Numerator = m₁₁ η_s + m₁₂ η_s η_inc - m₂₁ - m₂₂ η_inc
    Denominator = m₁₁ η_s - m₁₂ η_s η_inc + m₂₁ + m₂₂ η_inc -/
def reflectionAmplitude (M : Matrix (Fin 2) (Fin 2) ℝ) (η_inc η_s : ℝ) : ℝ :=
  let m₁₁ := M 0 0; let m₁₂ := M 0 1
  let m₂₁ := M 1 0; let m₂₂ := M 1 1
  (m₁₁ * η_s + m₁₂ * η_s * η_inc - m₂₁ - m₂₂ * η_inc) /
  (m₁₁ * η_s - m₁₂ * η_s * η_inc + m₂₁ + m₂₂ * η_inc)

/-- Reflectance R = r² -/
def reflectance (M : Matrix (Fin 2) (Fin 2) ℝ) (η_inc η_s : ℝ) : ℝ :=
  reflectionAmplitude M η_inc η_s ^ 2

theorem reflectance_nonneg (M : Matrix (Fin 2) (Fin 2) ℝ) (η_inc η_s : ℝ) :
    0 ≤ reflectance M η_inc η_s := sq_nonneg _

/-- An identity stack with matched incident/substrate admittance has no reflection. -/
theorem reflectionAmplitude_identity_matched (η : ℝ) :
    reflectionAmplitude (1 : Matrix (Fin 2) (Fin 2) ℝ) η η = 0 := by
  simp [reflectionAmplitude]

theorem reflectance_identity_matched (η : ℝ) :
    reflectance (1 : Matrix (Fin 2) (Fin 2) ℝ) η η = 0 := by
  simp [reflectance, reflectionAmplitude_identity_matched]

/-- Report-form reflection amplitude:
`r = (m₁₁ + m₁₂η_s - (m₂₁ + m₂₂η_s)/η_inc) /
     (m₁₁ + m₁₂η_s + (m₂₁ + m₂₂η_s)/η_inc)`. -/
def reflectionAmplitudeReport (M : Matrix (Fin 2) (Fin 2) ℝ) (η_inc η_s : ℝ) : ℝ :=
  let m₁₁ := M 0 0; let m₁₂ := M 0 1
  let m₂₁ := M 1 0; let m₂₂ := M 1 1
  (m₁₁ + m₁₂ * η_s - (m₂₁ + m₂₂ * η_s) / η_inc) /
  (m₁₁ + m₁₂ * η_s + (m₂₁ + m₂₂ * η_s) / η_inc)

/-- Report-form reflectance is the squared amplitude. -/
def reflectanceReport (M : Matrix (Fin 2) (Fin 2) ℝ) (η_inc η_s : ℝ) : ℝ :=
  reflectionAmplitudeReport M η_inc η_s ^ 2

theorem reflectanceReport_nonneg (M : Matrix (Fin 2) (Fin 2) ℝ) (η_inc η_s : ℝ) :
    0 ≤ reflectanceReport M η_inc η_s := sq_nonneg _

/-- Complex report-form reflection amplitude:
`r = (m₁₁ + m₁₂η_s - (m₂₁ + m₂₂η_s)/η_inc) /
     (m₁₁ + m₁₂η_s + (m₂₁ + m₂₂η_s)/η_inc)`. -/
def reflectionAmplitudeReportComplex (M : Matrix (Fin 2) (Fin 2) ℂ) (η_inc η_s : ℂ) : ℂ :=
  let m₁₁ := M 0 0; let m₁₂ := M 0 1
  let m₂₁ := M 1 0; let m₂₂ := M 1 1
  (m₁₁ + m₁₂ * η_s - (m₂₁ + m₂₂ * η_s) / η_inc) /
  (m₁₁ + m₁₂ * η_s + (m₂₁ + m₂₂ * η_s) / η_inc)

/-- Report-form physical reflectance is the squared complex modulus. -/
def reflectanceReportComplex (M : Matrix (Fin 2) (Fin 2) ℂ) (η_inc η_s : ℂ) : ℝ :=
  ‖reflectionAmplitudeReportComplex M η_inc η_s‖ ^ 2

theorem reflectanceReportComplex_nonneg (M : Matrix (Fin 2) (Fin 2) ℂ) (η_inc η_s : ℂ) :
    0 ≤ reflectanceReportComplex M η_inc η_s := by
  simp [reflectanceReportComplex]

/-- The report-form reflection amplitude gives no reflection for identity stack and matched admittance. -/
theorem reflectionAmplitudeReport_identity_matched {η : ℝ} (hη : η ≠ 0) :
    reflectionAmplitudeReport (1 : Matrix (Fin 2) (Fin 2) ℝ) η η = 0 := by
  simp [reflectionAmplitudeReport, hη]

theorem reflectanceReport_identity_matched {η : ℝ} (hη : η ≠ 0) :
    reflectanceReport (1 : Matrix (Fin 2) (Fin 2) ℝ) η η = 0 := by
  simp [reflectanceReport, reflectionAmplitudeReport_identity_matched hη]

/-- The complex report-form reflection amplitude gives no reflection for identity stack and matched admittance. -/
theorem reflectionAmplitudeReportComplex_identity_matched {η : ℂ} (hη : η ≠ 0) :
    reflectionAmplitudeReportComplex (1 : Matrix (Fin 2) (Fin 2) ℂ) η η = 0 := by
  simp [reflectionAmplitudeReportComplex, hη]

theorem reflectanceReportComplex_identity_matched {η : ℂ} (hη : η ≠ 0) :
    reflectanceReportComplex (1 : Matrix (Fin 2) (Fin 2) ℂ) η η = 0 := by
  simp [reflectanceReportComplex, reflectionAmplitudeReportComplex_identity_matched hη]

/-- Single-layer stack is just the single layer matrix -/
theorem nBilayerStack_one (φ_Mo φ_Si η_Mo η_Si : ℝ) :
    nBilayerStack φ_Mo φ_Si η_Mo η_Si 1 =
    transferMatrix φ_Si η_Si * transferMatrix φ_Mo η_Mo := by
  simp [nBilayerStack]

/-- Zero bilayers gives identity matrix -/
theorem nBilayerStack_zero (φ_Mo φ_Si η_Mo η_Si : ℝ) :
    nBilayerStack φ_Mo φ_Si η_Mo η_Si 0 = 1 := by
  simp [nBilayerStack]

end
