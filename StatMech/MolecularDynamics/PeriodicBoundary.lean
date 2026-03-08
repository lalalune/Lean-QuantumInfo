/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from ATOMSLab/LeanLJ (arXiv:2505.09095).
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
/-!
# Periodic Boundary Conditions

Periodic boundary conditions (PBC) for molecular simulations.

* `pbc`: wrap a coordinate into `[-L/2, L/2)` via `x - L * round(x/L)`
* `minImageDistance`: minimum image convention distance
* `PeriodicConfiguration`: a configuration of particles in a periodic box

## References

* ATOMSLab/LeanLJ (GitHub), arXiv:2505.09095
* Allen & Tildesley, *Computer Simulation of Liquids*, Oxford University Press.
-/

noncomputable section

open Real

namespace MolecularDynamics

/-- Apply periodic boundary conditions: `pbc(x, L) = x - L · round(x/L)`. -/
def pbc (x L : ℝ) : ℝ := x - L * round (x / L)

theorem pbc_bounded (x L : ℝ) (hL : 0 < L) :
    |pbc x L| ≤ L / 2 := by
  unfold pbc
  have h : x - L * ↑(round (x / L)) = L * (x / L - ↑(round (x / L))) := by
    rw [mul_sub, mul_div_cancel₀ x (ne_of_gt hL)]
  rw [h, abs_mul, abs_of_pos hL]
  have := abs_sub_round (x / L)
  nlinarith [le_of_lt hL]

theorem pbc_idempotent (x L : ℝ) (hL : 0 < L) :
    pbc (pbc x L) L = pbc x L := by
  simp only [pbc]
  suffices h : round ((x - L * ↑(round (x / L))) / L) = (0 : ℤ) by
    simp [h]
  have : (x - L * ↑(round (x / L))) / L = x / L - ↑(round (x / L)) := by
    field_simp
  rw [this, round_sub_intCast, sub_self]

private theorem abs_sub_round_neg_eq (x : ℝ) :
    |(-x) - round (-x)| = |x - round x| := by
  rw [abs_sub_round_eq_min, abs_sub_round_eq_min]
  by_cases hx : Int.fract x = 0
  · have hneg : Int.fract (-x) = 0 := (Int.fract_neg_eq_zero).2 hx
    simp [hx, hneg]
  · rw [Int.fract_neg hx]
    ring_nf
    rw [min_comm]

private theorem pbc_sq_neg (x L : ℝ) (hL : 0 < L) :
    (pbc (-x) L) ^ 2 = (pbc x L) ^ 2 := by
  have h₁ : pbc (-x) L = L * ((-x / L) - ↑(round (-x / L))) := by
    unfold pbc
    rw [mul_sub, mul_div_cancel₀ (-x) (ne_of_gt hL)]
  have h₂ : pbc x L = L * (x / L - ↑(round (x / L))) := by
    unfold pbc
    rw [mul_sub, mul_div_cancel₀ x (ne_of_gt hL)]
  rw [h₁, h₂]
  set a : ℝ := (-x / L) - ↑(round (-x / L))
  set b : ℝ := x / L - ↑(round (x / L))
  have habs : |a| = |b| := by
    dsimp [a, b]
    simpa [neg_div] using abs_sub_round_neg_eq (x / L)
  have habs_sq : |a| ^ 2 = |b| ^ 2 := congrArg (fun t : ℝ => t ^ 2) habs
  have habs_sq' : a ^ 2 = b ^ 2 := by
    simpa [sq_abs] using habs_sq
  calc
    (L * a) ^ 2 = L ^ 2 * a ^ 2 := by ring
    _ = L ^ 2 * b ^ 2 := by rw [habs_sq']
    _ = (L * b) ^ 2 := by ring

/-- Squared minimum image distance between two particles in a periodic box. -/
def squaredMinImageDistance (posA posB boxLength : Fin 3 → ℝ) : ℝ :=
  let dx := pbc (posB 0 - posA 0) (boxLength 0)
  let dy := pbc (posB 1 - posA 1) (boxLength 1)
  let dz := pbc (posB 2 - posA 2) (boxLength 2)
  dx ^ 2 + dy ^ 2 + dz ^ 2

/-- Minimum image distance between two particles in a periodic box. -/
def minImageDistance (posA posB boxLength : Fin 3 → ℝ) : ℝ :=
  Real.sqrt (squaredMinImageDistance posA posB boxLength)

theorem squaredMinImageDistance_nonneg (posA posB boxLength : Fin 3 → ℝ) :
    0 ≤ squaredMinImageDistance posA posB boxLength := by
  unfold squaredMinImageDistance; positivity

theorem minImageDistance_nonneg (posA posB boxLength : Fin 3 → ℝ) :
    0 ≤ minImageDistance posA posB boxLength :=
  Real.sqrt_nonneg _

theorem minImageDistance_self (posA boxLength : Fin 3 → ℝ) :
    minImageDistance posA posA boxLength = 0 := by
  unfold minImageDistance squaredMinImageDistance pbc
  simp [sub_self, round_zero, mul_zero]

/-- Symmetry: `d(A,B) = d(B,A)`. Follows from `(pbc(-x,L))² = (pbc(x,L))²`, which
    holds because `round(z) + round(-z) ∈ {0,1}` forces both PBC images to have equal
    absolute value. Needs `round_add_round_neg` or a case split on half-integers. -/
theorem minImageDistance_symm (posA posB boxLength : Fin 3 → ℝ)
    (hbox : ∀ i, 0 < boxLength i) :
    minImageDistance posA posB boxLength = minImageDistance posB posA boxLength := by
  have h0 :
      (pbc (posA 0 - posB 0) (boxLength 0)) ^ 2 =
      (pbc (posB 0 - posA 0) (boxLength 0)) ^ 2 := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (pbc_sq_neg (x := posB 0 - posA 0) (L := boxLength 0) (hbox 0))
  have h1 :
      (pbc (posA 1 - posB 1) (boxLength 1)) ^ 2 =
      (pbc (posB 1 - posA 1) (boxLength 1)) ^ 2 := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (pbc_sq_neg (x := posB 1 - posA 1) (L := boxLength 1) (hbox 1))
  have h2 :
      (pbc (posA 2 - posB 2) (boxLength 2)) ^ 2 =
      (pbc (posB 2 - posA 2) (boxLength 2)) ^ 2 := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (pbc_sq_neg (x := posB 2 - posA 2) (L := boxLength 2) (hbox 2))
  unfold minImageDistance squaredMinImageDistance
  congr 1
  simp [h0, h1, h2]

/-- Configuration of `n` particles in a 3D periodic box. -/
structure PeriodicConfiguration (n : ℕ) where
  positions : Fin n → Fin 3 → ℝ
  boxLength : Fin 3 → ℝ
  box_pos : ∀ i, 0 < boxLength i

namespace PeriodicConfiguration

variable {n : ℕ} (config : PeriodicConfiguration n)

/-- Number density ρ = N/V. -/
def numberDensity : ℝ :=
  (n : ℝ) / (config.boxLength 0 * config.boxLength 1 * config.boxLength 2)

theorem numberDensity_nonneg : 0 ≤ config.numberDensity := by
  unfold numberDensity
  exact div_nonneg (Nat.cast_nonneg n)
    (mul_nonneg (mul_nonneg (le_of_lt (config.box_pos 0)) (le_of_lt (config.box_pos 1)))
      (le_of_lt (config.box_pos 2)))

def particleDistance (i j : Fin n) : ℝ :=
  minImageDistance (config.positions i) (config.positions j) config.boxLength

theorem particleDistance_symm (i j : Fin n) :
    config.particleDistance i j = config.particleDistance j i :=
  minImageDistance_symm _ _ _ config.box_pos

theorem particleDistance_self (i : Fin n) :
    config.particleDistance i i = 0 :=
  minImageDistance_self _ _

end PeriodicConfiguration

/-- Apply PBC to each coordinate of a position vector. -/
def wrapPosition (pos boxLength : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => pbc (pos i) (boxLength i)

/-! ## Verification Tests -/

section Tests

/-- PBC of zero is zero. -/
theorem pbc_zero (L : ℝ) (_hL : L ≠ 0) : pbc 0 L = 0 := by
  simp [pbc, zero_div, round_zero, mul_zero]

/-- Squared min-image distance is always non-negative. -/
example (a b box : Fin 3 → ℝ) :
    0 ≤ squaredMinImageDistance a b box :=
  squaredMinImageDistance_nonneg a b box

/-- Min-image distance of a point to itself is 0. -/
example (a box : Fin 3 → ℝ) :
    minImageDistance a a box = 0 :=
  minImageDistance_self a box

/-- Number density of an empty box is 0. -/
theorem PeriodicConfiguration.numberDensity_zero
    (config : PeriodicConfiguration 0) :
    config.numberDensity = 0 := by
  simp [PeriodicConfiguration.numberDensity]

/-- Particle distance is a proper pseudometric: self-distance is zero. -/
example {n : ℕ} (config : PeriodicConfiguration n) (i : Fin n) :
    config.particleDistance i i = 0 :=
  config.particleDistance_self i

/-- Particle distance is symmetric. -/
example {n : ℕ} (config : PeriodicConfiguration n) (i j : Fin n) :
    config.particleDistance i j = config.particleDistance j i :=
  config.particleDistance_symm i j

end Tests

end MolecularDynamics

end
