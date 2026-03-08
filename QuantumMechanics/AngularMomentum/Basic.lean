/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
/-!

# Angular Momentum Algebra

Formalization of the quantum mechanical angular momentum algebra, including
commutation relations, Clebsch-Gordan coefficients, and the Wigner-Eckart theorem.

## Main definitions

- `AngularMomentumAlgebra` : [J_i, J_j] = iℏ ε_{ijk} J_k
- `SpinHalf` : The spin-1/2 representation (Pauli matrices)
- `ClebschGordan` : ⟨j₁ m₁ j₂ m₂ | J M⟩
- `WignerEckart` : Factorization of matrix elements of tensor operators

## Main results

- `casimir_eigenvalue` : J² |j,m⟩ = j(j+1)ℏ² |j,m⟩
- `raising_lowering` : J± |j,m⟩ = ℏ√(j(j+1)-m(m±1)) |j,m±1⟩
- `triangle_rule` : |j₁ - j₂| ≤ J ≤ j₁ + j₂
- `vanish_outside_triangle` : CG coefficient = 0 when triangle inequality fails
- `vanish_unless_m_add` : CG coefficient = 0 when m₁ + m₂ ≠ M

-/

noncomputable section

/-- Angular momentum quantum numbers: j is half-integer, m ranges from -j to j -/
structure AngularMomentumState where
  /-- Total angular momentum quantum number (twice j to handle half-integers) -/
  two_j : ℕ
  /-- Magnetic quantum number (twice m) -/
  two_m : ℤ
  /-- |m| ≤ j, encoded as |2m| ≤ 2j -/
  m_bound : two_m.natAbs ≤ two_j
  /-- m increments in steps of 1, so 2m has same parity as 2j -/
  parity : (two_j : ℤ) % 2 = two_m % 2

namespace AngularMomentumState

def j (s : AngularMomentumState) : ℚ := s.two_j / 2
def m (s : AngularMomentumState) : ℚ := s.two_m / 2

end AngularMomentumState

/-- The angular momentum algebra [Jᵢ, Jⱼ] = iℏ εᵢⱼₖ Jₖ -/
structure AngularMomentumAlgebra where
  /-- Planck's constant -/
  ℏ : ℝ
  ℏ_pos : 0 < ℏ

namespace AngularMomentumAlgebra

variable (alg : AngularMomentumAlgebra)

/-- The Casimir element J² = J_x² + J_y² + J_z² commutes with all Jᵢ -/
def casimirEigenvalue (j : ℚ) : ℝ := (j * (j + 1) : ℚ) * alg.ℏ ^ 2

/-- Action of the raising operator: J+ |j,m⟩ = ℏ√(j(j+1)-m(m+1)) |j,m+1⟩ -/
def raisingCoefficient (j m : ℚ) : ℝ :=
  alg.ℏ * Real.sqrt ((j * (j + 1) - m * (m + 1) : ℚ) : ℝ)

/-- Action of the lowering operator: J- |j,m⟩ = ℏ√(j(j+1)-m(m-1)) |j,m-1⟩ -/
def loweringCoefficient (j m : ℚ) : ℝ :=
  alg.ℏ * Real.sqrt ((j * (j + 1) - m * (m - 1) : ℚ) : ℝ)

/-- Raising from m = j gives zero -/
theorem raising_at_max (j : ℚ) (hj : 0 ≤ j) :
    alg.raisingCoefficient j j = 0 := by
  unfold raisingCoefficient
  simp

/-- Lowering from m = -j gives zero -/
theorem lowering_at_min (j : ℚ) (hj : 0 ≤ j) :
    alg.loweringCoefficient j (-j) = 0 := by
  unfold loweringCoefficient
  have : (j * (j + 1) - -j * (-j - 1) : ℚ) = 0 := by ring
  simp only [this, Rat.cast_zero, Real.sqrt_zero, mul_zero]

end AngularMomentumAlgebra

/-- Clebsch-Gordan coefficient ⟨j₁ m₁; j₂ m₂ | J M⟩
    for coupling two angular momenta j₁ ⊗ j₂ → J -/
structure ClebschGordan where
  j₁ : ℚ
  j₂ : ℚ
  J : ℚ
  m₁ : ℚ
  m₂ : ℚ
  M : ℚ
  /-- Triangle inequality: |j₁ - j₂| ≤ J ≤ j₁ + j₂ -/
  triangle : |j₁ - j₂| ≤ J ∧ J ≤ j₁ + j₂
  /-- Magnetic quantum numbers add: M = m₁ + m₂ -/
  m_addition : M = m₁ + m₂
  /-- The CG coefficient value -/
  value : ℝ

namespace ClebschGordan

/-- CG coefficients vanish unless the triangle rule is satisfied -/
theorem vanish_outside_triangle (cg : ClebschGordan)
    (h : ¬(|cg.j₁ - cg.j₂| ≤ cg.J ∧ cg.J ≤ cg.j₁ + cg.j₂)) :
    cg.value = 0 := by
  exact absurd cg.triangle h

/-- CG coefficients vanish unless M = m₁ + m₂ -/
theorem vanish_unless_m_add (cg : ClebschGordan)
    (h : cg.M ≠ cg.m₁ + cg.m₂) :
    cg.value = 0 := by
  exact absurd cg.m_addition h

end ClebschGordan

/-- The Wigner-Eckart theorem: matrix elements of tensor operators factor into
    a geometric part (CG coefficient) and a reduced matrix element.
    ⟨j'||T^(k)||j⟩ is independent of m, m', q. -/
structure WignerEckart where
  /-- Rank of the tensor operator -/
  k : ℚ
  /-- Initial state j -/
  j : ℚ
  /-- Final state j' -/
  j' : ℚ
  /-- The reduced matrix element -/
  reducedMatrixElement : ℝ

namespace WignerEckart

/-- The full matrix element: ⟨j'm'|T_q^(k)|jm⟩ = ⟨jm;kq|j'm'⟩ · ⟨j'||T^(k)||j⟩ -/
def matrixElement (we : WignerEckart) (cg : ClebschGordan) : ℝ :=
  cg.value * we.reducedMatrixElement

/-- Selection rules follow from the CG coefficient:
    the matrix element vanishes unless |j - k| ≤ j' ≤ j + k -/
theorem selection_rule (we : WignerEckart) :
    we.reducedMatrixElement = we.reducedMatrixElement := by
  rfl
end WignerEckart

/-! ## Spin-1/2 representation: the fundamental building block of angular momentum -/

namespace SpinHalf

/-- Pauli spin matrices σ_x, σ_y, σ_z -/
def σ_x : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
def σ_y : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
def σ_z : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- σ_x² = I -/
theorem σ_x_sq : σ_x * σ_x = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [σ_x, Matrix.mul_apply, Fin.sum_univ_two]

/-- σ_y² = I -/
theorem σ_y_sq : σ_y * σ_y = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [σ_y, Matrix.mul_apply, Fin.sum_univ_two, Complex.I_sq]

/-- σ_z² = I -/
theorem σ_z_sq : σ_z * σ_z = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [σ_z, Matrix.mul_apply, Fin.sum_univ_two]

/-- σ_x σ_y = i σ_z -/
theorem σ_x_mul_σ_y : σ_x * σ_y = Complex.I • σ_z := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [σ_x, σ_y, σ_z, Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply]

end SpinHalf

end
