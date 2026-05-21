/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
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

/-- Product of two unimodular matrices is unimodular -/
theorem mul_unimodular {M N : Matrix (Fin 2) (Fin 2) ℝ}
    (hM : M.det = 1) (hN : N.det = 1) : (M * N).det = 1 := by
  rw [det_mul, hM, hN, mul_one]

/-- The identity matrix is unimodular -/
theorem one_unimodular : (1 : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := det_one

/-- Ordered stack product of layer matrices. -/
def stackMatrix : List (Matrix (Fin 2) (Fin 2) ℝ) → Matrix (Fin 2) (Fin 2) ℝ
  | [] => 1
  | M :: Ms => M * stackMatrix Ms

/-- Stack of unimodular matrices has determinant 1. -/
theorem stack_det_one :
    ∀ layers : List (Matrix (Fin 2) (Fin 2) ℝ),
      (∀ M ∈ layers, M.det = 1) → (stackMatrix layers).det = 1
  | [], _ => by simp [stackMatrix, det_one]
  | M :: Ms, h => by
      simp [stackMatrix, det_mul, h M (by simp), stack_det_one Ms (by
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

theorem nBilayerStack_det_one (φ_Mo φ_Si η_Mo η_Si : ℝ) (N : ℕ) :
    η_Mo ≠ 0 → η_Si ≠ 0 →
    (nBilayerStack φ_Mo φ_Si η_Mo η_Si N).det = 1 := by
  intro hMo hSi
  unfold nBilayerStack
  rw [det_pow, mul_unimodular (transferMatrix_det_one _ _ hSi) (transferMatrix_det_one _ _ hMo)]
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
