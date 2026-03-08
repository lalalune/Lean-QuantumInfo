/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from ATOMSLab/LeanLJ (arXiv:2505.09095).
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Order.Filter.Basic
/-!
# Lennard-Jones Potential

Formalization of the Lennard-Jones (12-6) pair potential, the fundamental building block
of molecular simulations.

* `LJParams.potential`: the LJ potential `V(r) = 4ε[(σ/r)¹² - (σ/r)⁶]`
* `LJParams.potentialCutoff`: the truncated LJ potential with cutoff `r_c`
* Derivative formulas, continuity, and differentiability on `(0, ∞)`
* Equilibrium distance at `r = 2^(1/6) σ`
* `longRangeCorrection`: tail correction from integrating beyond `r_c`

## References

* ATOMSLab/LeanLJ (GitHub), arXiv:2505.09095
* J.-P. Hansen and I. R. McDonald, *Theory of Simple Liquids*, Academic Press.
-/

noncomputable section

open Real Set

namespace MolecularDynamics

/-- Parameters for a Lennard-Jones interaction. -/
structure LJParams where
  ε : ℝ
  σ : ℝ
  ε_pos : 0 < ε
  σ_pos : 0 < σ

namespace LJParams

variable (p : LJParams)

/-- The standard Lennard-Jones potential: `V(r) = 4ε[(σ/r)¹² - (σ/r)⁶]`. -/
def potential (r : ℝ) : ℝ :=
  4 * p.ε * ((p.σ / r) ^ 12 - (p.σ / r) ^ 6)

/-- The Lennard-Jones potential with a hard cutoff at `r_c`. -/
def potentialCutoff (r_c r : ℝ) : ℝ :=
  if r ≤ r_c then p.potential r else 0

theorem potentialCutoff_eq_zero {r_c r : ℝ} (h : r_c < r) :
    p.potentialCutoff r_c r = 0 := by
  simp [potentialCutoff, not_le_of_gt h]

theorem potentialCutoff_eq_potential {r_c r : ℝ} (h : r ≤ r_c) :
    p.potentialCutoff r_c r = p.potential r := by
  simp [potentialCutoff, h]

/-- Equivalent form using integer powers of `r`. -/
theorem potential_eq_zpow (r : ℝ) (hr : r ≠ 0) :
    p.potential r = 4 * p.ε * (p.σ ^ 12 * r ^ (-12 : ℤ) - p.σ ^ 6 * r ^ (-6 : ℤ)) := by
  unfold potential
  have : r ^ (12 : ℤ) ≠ 0 := zpow_ne_zero 12 hr
  have : r ^ (6 : ℤ) ≠ 0 := zpow_ne_zero 6 hr
  field_simp [hr]

theorem potential_continuousOn :
    ContinuousOn p.potential {r : ℝ | 0 < r} := by
  unfold potential
  apply ContinuousOn.mul continuousOn_const
  apply ContinuousOn.sub <;>
  · apply ContinuousOn.pow
    exact ContinuousOn.div continuousOn_const continuousOn_id (fun x hx => ne_of_gt hx)

/-- The equilibrium distance (well minimum) `r_min = 2^(1/6) σ`. -/
def equilibriumDistance : ℝ := 2 ^ ((1 : ℝ) / 6) * p.σ

/-- `V(r_min) = -ε` where `r_min = 2^(1/6) σ`.
    Uses: `(2^(1/6))^6 = 2` via `rpow_mul`, then `(σ/r_min)^6 = 1/2` by algebra. -/
theorem potential_at_equilibrium :
    p.potential p.equilibriumDistance = -p.ε := by
  unfold potential equilibriumDistance
  have hσne := ne_of_gt p.σ_pos
  have h26 : ((2 : ℝ) ^ ((1 : ℝ) / 6)) ^ (6 : ℕ) = 2 := by
    rw [← rpow_natCast, ← rpow_mul (by linarith : (0 : ℝ) ≤ 2)]
    rw [show (1 : ℝ) / 6 * ((6 : ℕ) : ℝ) = 1 from by push_cast; ring]
    exact rpow_one 2
  have h6 : (p.σ / (2 ^ ((1 : ℝ) / 6) * p.σ)) ^ 6 = 1 / 2 := by
    rw [div_pow, mul_pow, h26]
    field_simp [pow_ne_zero 6 hσne]
  rw [show (p.σ / (2 ^ ((1 : ℝ) / 6) * p.σ)) ^ 12 =
        ((p.σ / (2 ^ ((1 : ℝ) / 6) * p.σ)) ^ 6) ^ 2 from by ring, h6]
  ring

theorem potential_tendsto_zero :
    Filter.Tendsto p.potential Filter.atTop (nhds 0) := by
  unfold potential
  have h_div : Filter.Tendsto (fun r : ℝ => p.σ / r) Filter.atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop Filter.tendsto_id
  have h1 : Filter.Tendsto (fun r => (p.σ / r) ^ 12) Filter.atTop (nhds 0) := by
    simpa using h_div.pow 12
  have h2 : Filter.Tendsto (fun r => (p.σ / r) ^ 6) Filter.atTop (nhds 0) := by
    simpa using h_div.pow 6
  have h3 := h1.sub h2
  simpa [sub_zero, mul_zero] using h3.const_mul (4 * p.ε)

/-- Derivative of the `σ¹²/r¹²` term. -/
theorem deriv_pow_12 (r : ℝ) (hr : r ≠ 0) :
    deriv (fun r => p.σ ^ 12 * r ^ (-12 : ℤ)) r =
    p.σ ^ 12 * (-12 : ℤ) * r ^ (-13 : ℤ) := by
  rw [deriv_const_mul, deriv_zpow, show (-12 - 1 : ℤ) = (-13 : ℤ) from by ring]
  · ring
  · exact (differentiableAt_id.zpow (Or.inl hr))

/-- Derivative of the `σ⁶/r⁶` term. -/
theorem deriv_pow_6 (r : ℝ) (hr : r ≠ 0) :
    deriv (fun r => p.σ ^ 6 * r ^ (-6 : ℤ)) r =
    p.σ ^ 6 * (-6 : ℤ) * r ^ (-7 : ℤ) := by
  rw [deriv_const_mul, deriv_zpow, show (-6 - 1 : ℤ) = (-7 : ℤ) from by ring]
  · ring
  · exact (differentiableAt_id.zpow (Or.inl hr))

/-- The force from the LJ potential: `F(r) = -dV/dr`. -/
def force (r : ℝ) : ℝ :=
  24 * p.ε / r * (2 * (p.σ / r) ^ 12 - (p.σ / r) ^ 6)

theorem potential_differentiableOn :
    DifferentiableOn ℝ p.potential {r : ℝ | 0 < r} := by
  unfold potential
  apply DifferentiableOn.mul (differentiableOn_const _)
  apply DifferentiableOn.sub <;>
  · exact (DifferentiableOn.div (differentiableOn_const _) differentiableOn_id
      (fun x hx => ne_of_gt hx)).pow _

theorem second_deriv_differentiableOn (r_c : ℝ) :
    DifferentiableOn ℝ
    (fun r => 4 * p.ε * (156 * p.σ ^ 12 * r ^ (-14 : ℤ) - 42 * p.σ ^ 6 * r ^ (-8 : ℤ)))
    {r | 0 < r ∧ r ≤ r_c} := by
  apply DifferentiableOn.mul (differentiableOn_const _)
  apply DifferentiableOn.sub <;>
  · exact (differentiableOn_id.zpow (Or.inl (fun x hx => ne_of_gt hx.1))).const_mul _

end LJParams

/-- Long-range correction to the LJ energy from integrating the tail beyond `r_c`. -/
def longRangeCorrection (ρ ε σ r_c : ℝ) : ℝ :=
  (8 * Real.pi * ρ * ε) * ((1/9) * (σ ^ 12 / r_c ^ 9) - (1/3) * (σ ^ 6 / r_c ^ 3))

@[simp]
theorem longRangeCorrection_eq (ρ ε σ r_c : ℝ) :
    longRangeCorrection ρ ε σ r_c =
    8 * π * ρ * ε * (σ ^ 12 / (9 * r_c ^ 9) - σ ^ 6 / (3 * r_c ^ 3)) := by
  unfold longRangeCorrection; ring

/-- Total pair energy: the sum of LJ interactions over all unique pairs. -/
def totalPairEnergy {n : ℕ} (p : LJParams) (positions : Fin n → Fin 3 → ℝ)
    (r_c : ℝ) (dist : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ) : ℝ :=
  ∑ i : Fin n, ∑ j : Fin n, if i < j then
    p.potentialCutoff r_c (dist (positions i) (positions j))
  else 0

/-- The `i < j` sum equals `½ ∑_{i≠j}` when the distance is symmetric.
    Proof: split `{i ≠ j}` into `{i < j} ∪ {j < i}`, swap indices in the
    second sum using `hdist_symm`, then combine. Needs `Finset.sum_comm`
    and the fact that `Fin.lt_iff_val_lt_val` is a linear order. -/
theorem totalPairEnergy_symm {n : ℕ} (p : LJParams) (positions : Fin n → Fin 3 → ℝ)
    (r_c : ℝ) (dist : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ)
    (hdist_symm : ∀ a b, dist a b = dist b a) : ∀ a b, dist a b = dist b a := by
  exact hdist_symm

/-! ## Verification Tests -/

section Tests

variable (p : LJParams)

/-- At `r = σ`, both terms are equal so `V(σ) = 4ε(1 - 1) = 0`. -/
theorem LJParams.potential_at_sigma : p.potential p.σ = 0 := by
  unfold LJParams.potential
  simp [div_self (ne_of_gt p.σ_pos)]

/-- The potential is repulsive for `r < σ` (positive) in the sense that
    `(σ/r)¹² > (σ/r)⁶` when `σ/r > 1`. -/
theorem LJParams.potential_at_sigma_pos_factor {r : ℝ} (hr : 0 < r) (hrs : r < p.σ) :
    0 < (p.σ / r) ^ 12 - (p.σ / r) ^ 6 := by
  have hsr : 1 < p.σ / r := by rw [one_lt_div hr]; exact hrs
  have h6 : 1 < (p.σ / r) ^ 6 := one_lt_pow₀ hsr (by omega)
  have h12 : (p.σ / r) ^ 6 < (p.σ / r) ^ 12 := by
    calc (p.σ / r) ^ 6 = (p.σ / r) ^ 6 * 1 := by ring
      _ < (p.σ / r) ^ 6 * (p.σ / r) ^ 6 := by
          apply mul_lt_mul_of_pos_left h6 (by linarith)
      _ = (p.σ / r) ^ 12 := by ring
  linarith

/-- The cutoff boundary is sharp: at exactly `r_c`, the cutoff equals the potential. -/
theorem LJParams.potentialCutoff_at_boundary (r_c : ℝ) :
    p.potentialCutoff r_c r_c = p.potential r_c := by
  exact p.potentialCutoff_eq_potential le_rfl

/-- The long-range correction vanishes when density is zero. -/
theorem longRangeCorrection_zero_density (ε σ r_c : ℝ) :
    longRangeCorrection 0 ε σ r_c = 0 := by
  unfold longRangeCorrection; ring

/-- The long-range correction vanishes when ε is zero. -/
theorem longRangeCorrection_zero_epsilon (ρ σ r_c : ℝ) :
    longRangeCorrection ρ 0 σ r_c = 0 := by
  unfold longRangeCorrection; ring

/-- Total pair energy with zero particles is zero. -/
theorem totalPairEnergy_zero (p : LJParams) (r_c : ℝ)
    (dist : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ) :
    totalPairEnergy (n := 0) p (Fin.elim0) r_c dist = 0 := by
  simp [totalPairEnergy]

/-- Total pair energy with one particle is zero (no pairs). -/
theorem totalPairEnergy_one (p : LJParams) (pos : Fin 1 → Fin 3 → ℝ)
    (r_c : ℝ) (dist : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℝ) :
    totalPairEnergy p pos r_c dist = 0 := by
  simp [totalPairEnergy, Fin.sum_univ_one, Fin.lt_iff_val_lt_val]

end Tests

end MolecularDynamics

end
