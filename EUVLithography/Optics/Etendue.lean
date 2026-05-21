/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!

# EUV Lithography: Étendue Conservation

Formalizes the optical invariant (étendue = AΩ) and its conservation
through lossless optical systems (Liouville's theorem).

## Main definitions

- `solidAngleCap` : Ω = 2π(1 - cos θ_max) for spherical cap
- `collectionEfficiency` : η = Ω / (4π)
- `etendue` : G = A × Ω
- `radiance` : L = P / (A × Ω)
- `throughput` : P_coll = P × η × R^N

## Main results

- `solidAngleCap_full_sphere` : Ω(π) = 4π
- `solidAngleCap_le_4pi` : Ω_cap ≤ 4π
- `collectionEfficiency_nonneg` : η ≥ 0
- `collectionEfficiency_lt_one` : η < 1 for θ_max < π
- `etendue_pos` : G > 0
- `throughput_pos` : P_coll > 0
- `more_mirrors_less_throughput` : P ↓ with more lossy mirrors

-/

noncomputable section

open Real

/-- Solid angle of a spherical cap up to polar angle θ_max:
    Ω = 2π(1 - cos θ_max) -/
def solidAngleCap (θ_max : ℝ) : ℝ :=
  2 * π * (1 - cos θ_max)

theorem solidAngleCap_nonneg (θ_max : ℝ) : 0 ≤ solidAngleCap θ_max := by
  unfold solidAngleCap
  apply mul_nonneg (mul_pos two_pos pi_pos).le
  linarith [cos_le_one θ_max]

theorem solidAngleCap_pos {θ_max : ℝ} (hθ : 0 < θ_max) (hθ_pi : θ_max < π) :
    0 < solidAngleCap θ_max := by
  unfold solidAngleCap
  apply mul_pos (mul_pos two_pos pi_pos)
  have hcos : cos θ_max < 1 := by
    have h := Real.strictAntiOn_cos
      (Set.mem_Icc.mpr ⟨le_refl 0, pi_pos.le⟩)
      (Set.mem_Icc.mpr ⟨hθ.le, hθ_pi.le⟩) hθ
    simp [cos_zero] at h; linarith
  linarith

theorem solidAngleCap_le_4pi (θ_max : ℝ) : solidAngleCap θ_max ≤ 4 * π := by
  unfold solidAngleCap
  nlinarith [neg_one_le_cos θ_max, pi_pos]

theorem solidAngleCap_full_sphere : solidAngleCap π = 4 * π := by
  simp [solidAngleCap, cos_pi]; ring

/-- Étendue: G = A × Ω -/
def etendue (A Ω : ℝ) : ℝ := A * Ω

theorem etendue_pos {A Ω : ℝ} (hA : 0 < A) (hΩ : 0 < Ω) : 0 < etendue A Ω :=
  mul_pos hA hΩ

/-- Collection efficiency: η = Ω_coll / (4π) -/
def collectionEfficiency (θ_max : ℝ) : ℝ :=
  solidAngleCap θ_max / (4 * π)

/-- Solid angle corresponding to a collection fraction of the full sphere. -/
def solidAngleFromFullSphereFraction (fraction : ℝ) : ℝ :=
  fraction * (4 * π)

theorem solidAngleFromFullSphereFraction_pos {fraction : ℝ} (hf : 0 < fraction) :
    0 < solidAngleFromFullSphereFraction fraction :=
  mul_pos hf (mul_pos (by norm_num) pi_pos)

theorem collectionFraction_of_solidAngleFromFullSphereFraction {fraction : ℝ} :
    solidAngleFromFullSphereFraction fraction / (4 * π) = fraction := by
  unfold solidAngleFromFullSphereFraction
  field_simp [pi_ne_zero]

theorem collectionEfficiency_nonneg (θ_max : ℝ) : 0 ≤ collectionEfficiency θ_max :=
  div_nonneg (solidAngleCap_nonneg θ_max) (mul_pos (by norm_num) pi_pos).le

theorem collectionEfficiency_lt_one {θ_max : ℝ} (hθ : 0 < θ_max) (hθ_pi : θ_max < π) :
    collectionEfficiency θ_max < 1 := by
  unfold collectionEfficiency
  rw [div_lt_one (mul_pos (by norm_num) pi_pos)]
  unfold solidAngleCap
  have hcos_pos : cos θ_max < 1 := by
    have h := Real.strictAntiOn_cos
      (Set.mem_Icc.mpr ⟨le_refl 0, pi_pos.le⟩)
      (Set.mem_Icc.mpr ⟨hθ.le, hθ_pi.le⟩) hθ
    simp [cos_zero] at h; linarith
  have hcos_neg : -1 < cos θ_max := by
    have h := Real.strictAntiOn_cos
      (Set.mem_Icc.mpr ⟨hθ.le, hθ_pi.le⟩)
      (Set.mem_Icc.mpr ⟨pi_pos.le, le_refl π⟩) hθ_pi
    simp [cos_pi] at h; linarith
  nlinarith [pi_pos]

/-- Étendue conservation (Liouville's theorem) -/
theorem etendue_conservation {A₁ Ω₁ A₂ Ω₂ : ℝ}
    (h : etendue A₁ Ω₁ = etendue A₂ Ω₂) :
    A₁ * Ω₁ = A₂ * Ω₂ := h

/-- Radiance (brightness): L = P / (A Ω) -/
def radiance (P A Ω : ℝ) : ℝ := P / (A * Ω)

theorem radiance_pos {P A Ω : ℝ} (hP : 0 < P) (hA : 0 < A) (hΩ : 0 < Ω) :
    0 < radiance P A Ω :=
  div_pos hP (mul_pos hA hΩ)

/-- In a lossless system, radiance is conserved -/
theorem radiance_conserved {P₁ P₂ A₁ Ω₁ A₂ Ω₂ : ℝ}
    (hP : P₁ = P₂) (hG : A₁ * Ω₁ = A₂ * Ω₂) :
    radiance P₁ A₁ Ω₁ = radiance P₂ A₂ Ω₂ := by
  unfold radiance; rw [hP, hG]

/-- Throughput formula: P_coll = P_EUV × η × R^N -/
def throughput (P_EUV η_coll R_mirror : ℝ) (N : ℕ) : ℝ :=
  P_EUV * η_coll * R_mirror ^ N

theorem throughput_pos {P_EUV η_coll R_mirror : ℝ} {N : ℕ}
    (hP : 0 < P_EUV) (hη : 0 < η_coll) (hR : 0 < R_mirror) :
    0 < throughput P_EUV η_coll R_mirror N :=
  mul_pos (mul_pos hP hη) (pow_pos hR N)

/-- More lossy mirrors reduce throughput -/
theorem more_mirrors_less_throughput {P_EUV η_coll R : ℝ} {N M : ℕ}
    (hP : 0 < P_EUV) (hη : 0 < η_coll) (hR : 0 < R) (hR1 : R < 1) (hNM : N < M) :
    throughput P_EUV η_coll R M < throughput P_EUV η_coll R N := by
  unfold throughput
  apply mul_lt_mul_of_pos_left _ (mul_pos hP hη)
  exact pow_lt_pow_right_of_lt_one₀ hR hR1 hNM

end
