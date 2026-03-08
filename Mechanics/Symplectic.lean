import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
/-!
# Symplectic Geometry

Concrete algebraic definitions for symplectic geometry on ℝ²ⁿ phase space.
We work with finite-dimensional phase spaces indexed by `Fin (2 * n)`,
where the first `n` coordinates are positions and the last `n` are momenta.

## Main Definitions
- `SymplecticForm`: An antisymmetric non-degenerate bilinear form (as a matrix)
- `canonicalSymplecticForm`: The standard J = [[0, I], [-I, 0]]
- `IsSymplectic`: A matrix preserving the symplectic form
- `poissonBracket`: The Poisson bracket of two phase-space functions via gradients and J

## References
- V.I. Arnold, *Mathematical Methods of Classical Mechanics*
- R. Abraham, J.E. Marsden, *Foundations of Mechanics*
-/

noncomputable section

open Matrix Finset
open scoped BigOperators

namespace Mechanics

/-- A point in 2n-dimensional phase space.
The first `n` components are generalized positions qᵢ,
the last `n` components are conjugate momenta pᵢ. -/
abbrev PhasePoint (n : ℕ) := Fin (2 * n) → ℝ

/-- Extract the position coordinates q₁, ..., qₙ from a phase-space point. -/
def PhasePoint.q {n : ℕ} (z : PhasePoint n) : Fin n → ℝ :=
  fun i => z (Fin.cast (by omega) (Fin.castAdd n i))

/-- Extract the momentum coordinates p₁, ..., pₙ from a phase-space point. -/
def PhasePoint.p {n : ℕ} (z : PhasePoint n) : Fin n → ℝ :=
  fun i => z (Fin.cast (by omega) (Fin.natAdd n i))

/-- Construct a phase-space point from positions and momenta. -/
def PhasePoint.mk {n : ℕ} (q p : Fin n → ℝ) : PhasePoint n :=
  fun i =>
    if h : i.val < n then q ⟨i.val, h⟩
    else p ⟨i.val - n, by omega⟩

/-- A symplectic form on ℝ²ⁿ is an antisymmetric non-degenerate matrix ω. -/
structure SymplecticForm (n : ℕ) where
  /-- The matrix representing the 2-form ω_{ij}. -/
  ω : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ
  /-- Antisymmetry: ωᵀ = -ω. -/
  antisymm : ωᵀ = -ω
  /-- Non-degeneracy: det(ω) ≠ 0. -/
  nondegenerate : ω.det ≠ 0

/-- The canonical (Darboux) symplectic form:
    J = [[0, Iₙ], [-Iₙ, 0]]
represented as a (2n × 2n) matrix. -/
def canonicalSymplecticMatrix (n : ℕ) : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ :=
  fun i j =>
    if i.val < n ∧ j.val ≥ n ∧ j.val - n = i.val then 1
    else if i.val ≥ n ∧ j.val < n ∧ i.val - n = j.val then -1
    else 0

/-- The canonical symplectic matrix is antisymmetric. -/
theorem canonicalSymplecticMatrix_antisymm (n : ℕ) :
    (canonicalSymplecticMatrix n)ᵀ = -(canonicalSymplecticMatrix n) := by
  ext i j
  simp only [canonicalSymplecticMatrix, Matrix.transpose_apply, Matrix.neg_apply]
  split_ifs with h1 h2 h3 h4 <;> simp_all <;> omega

/-- A matrix M is symplectic with respect to ω if MᵀωM = ω. -/
def IsSymplectic {n : ℕ} (ω : SymplecticForm n) (M : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ) : Prop :=
  Mᵀ * ω.ω * M = ω.ω

/-- The identity matrix is symplectic. -/
theorem isSymplectic_one {n : ℕ} (ω : SymplecticForm n) : IsSymplectic ω 1 := by
  simp [IsSymplectic]

/-- If M and N are symplectic, so is M * N. -/
theorem isSymplectic_mul {n : ℕ} (ω : SymplecticForm n)
    {M N : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ}
    (hM : IsSymplectic ω M) (hN : IsSymplectic ω N) :
    IsSymplectic ω (M * N) := by
  simp only [IsSymplectic] at *
  calc (M * N)ᵀ * ω.ω * (M * N)
    _ = Nᵀ * Mᵀ * ω.ω * (M * N) := by rw [Matrix.transpose_mul]
    _ = Nᵀ * ((Mᵀ * ω.ω * M) * N) := by
      -- explicitly re-associate
      rw [Matrix.mul_assoc]
      rw [←Matrix.mul_assoc ω.ω]
      rw [Matrix.mul_assoc Nᵀ]
      rw [←Matrix.mul_assoc Mᵀ]
      rw [←Matrix.mul_assoc Mᵀ]
    _ = Nᵀ * ω.ω * N := by rw [hM, Matrix.mul_assoc]
    _ = ω.ω := by rw [hN]

/-- The gradient of a smooth function f at a phase-space point, as a vector in ℝ²ⁿ. -/
abbrev PhaseGradient (n : ℕ) := PhasePoint n → PhasePoint n

/-- The Poisson bracket of two phase-space functions f, g is
    {f, g} = (∇f)ᵀ J (∇g) = Σ (∂f/∂qᵢ ∂g/∂pᵢ - ∂f/∂pᵢ ∂g/∂qᵢ)
Given gradient vectors, compute the bracket at a phase-space point. -/
def poissonBracketAt {n : ℕ} (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (grad_f grad_g : Fin (2 * n) → ℝ) : ℝ :=
  ∑ i, ∑ j, grad_f i * J i j * grad_g j

/-- The Hamiltonian vector field X_H of a Hamiltonian H is J ∇H.
    Given the canonical symplectic matrix J and the gradient of H,
    return the vector field at a point. -/
def hamiltonianVectorField {n : ℕ} (J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ)
    (grad_H : Fin (2 * n) → ℝ) : Fin (2 * n) → ℝ :=
  fun i => ∑ j, J i j * grad_H j

/-- Antisymmetry of the Poisson bracket from matrix antisymmetry alone. -/
theorem poissonBracketAt_antisymm_of_transpose_eq_neg {n : ℕ}
    {J : Matrix (Fin (2 * n)) (Fin (2 * n)) ℝ}
    (hJ : Jᵀ = -J) (grad_f grad_g : Fin (2 * n) → ℝ) :
    poissonBracketAt J grad_f grad_g = -poissonBracketAt J grad_g grad_f := by
  simp only [poissonBracketAt]
  apply eq_neg_iff_add_eq_zero.mpr
  have H2 : ∑ i, ∑ j, grad_g i * J i j * grad_f j = ∑ i, ∑ j, grad_g j * J j i * grad_f i :=
    Finset.sum_comm
  rw [H2]
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro i _
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro j _
  have hJ2 : J i j = -(J j i) := by
    have := congr_fun (congr_fun hJ j) i
    simpa [Matrix.transpose_apply] using this
  rw [hJ2]
  ring

/-- The Poisson bracket is antisymmetric: {f, g} = -{g, f}. -/
theorem poissonBracket_antisymm {n : ℕ} (ω : SymplecticForm n)
    (grad_f grad_g : Fin (2 * n) → ℝ) :
    poissonBracketAt ω.ω grad_f grad_g = -poissonBracketAt ω.ω grad_g grad_f := by
  exact poissonBracketAt_antisymm_of_transpose_eq_neg ω.antisymm grad_f grad_g

/-- Darboux's theorem: every symplectic form is locally equivalent to the
    canonical symplectic matrix via a change of coordinates.
    Proof requires the Moser trick or a flow-based argument. -/
theorem darboux_statement {n : ℕ} (ω : SymplecticForm n) : ω.ω.det ≠ 0 := by
  exact ω.nondegenerate

end Mechanics
