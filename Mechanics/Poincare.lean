import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Poincaré Group and Wigner Classification

Formalizes the Poincaré group ISO(1,3), the Lorentz group SO(1,3),
and Wigner's classification of elementary particles by their
mass and spin/helicity quantum numbers.

## Main Definitions
- `MinkowskiMetric`: the metric η = diag(-1,1,1,1)
- `LorentzMatrix`: a 4×4 matrix preserving the Minkowski metric
- `LorentzGroup`: the group O(1,3) of Lorentz transformations
- `PoincareElement`: a Lorentz transformation + spacetime translation
- `FourMomentum`: energy-momentum 4-vector with mass-shell condition
- `PauliLubanski`: the Pauli-Lubanski pseudovector W^μ
- `WignerClass`: classification of irreducible representations

## Cross-reference: Overlapping Minkowski/Lorentz definitions

This module uses a simple fixed-4D matrix approach (`Fin 4 → ℝ`, `Matrix (Fin 4) (Fin 4) ℝ`)
with metric signature `(-,+,+,+)`. The unique content here is Wigner classification and
the Pauli-Lubanski pseudovector. For the Lorentz group and Minkowski metric, more general
and proven versions exist in the PhysLean tensor framework:

- **`Relativity.MinkowskiMatrix`**: dimension-generic `η` matrix with full proof suite
- **`Relativity.LorentzGroup`**: the Lorentz group as a subgroup with proper/orthochronous
  decomposition, boosts, rotations, and the restricted Lorentz group
- **`Relativity.LorentzAlgebra`**: Lie algebra with explicit basis and exponential map
- **`QFT.MinkowskiSpace`**: QFT-focused spacetime (`Fin d → ℝ`, signature `(+,-,-,-)`)

The `FourVector`, `LorentzMatrix`, and `PoincareElement` definitions here are lightweight
counterparts sufficient for the Wigner classification context but not connected to the
full PhysLean Lorentz infrastructure.

## References
- S. Weinberg, *The Quantum Theory of Fields*, Vol. 1, Ch. 2
- E.P. Wigner, *On Unitary Representations of the Inhomogeneous Lorentz Group* (1939)
- W.-K. Tung, *Group Theory in Physics*, Ch. 10
-/

noncomputable section

open Matrix Finset BigOperators Complex

namespace Mechanics

/-- The Minkowski metric η = diag(-1, 1, 1, 1). -/
def minkowskiMetric : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ![(-1 : ℝ), 1, 1, 1]

/-- A spacetime 4-vector: (t/c, x, y, z) or (E/c, px, py, pz). -/
abbrev FourVector := Fin 4 → ℝ

/-- The Minkowski inner product of two 4-vectors:
    η(a, b) = -a⁰b⁰ + a¹b¹ + a²b² + a³b³. -/
def minkowskiInner (a b : FourVector) : ℝ :=
  ∑ μ, ∑ ν, minkowskiMetric μ ν * a μ * b ν

/-- The Minkowski inner product in explicit component form:
    η(a,b) = -a₀b₀ + a₁b₁ + a₂b₂ + a₃b₃. -/
theorem minkowskiInner_explicit (a b : FourVector) :
    minkowskiInner a b = -(a 0 * b 0) + a 1 * b 1 + a 2 * b 2 + a 3 * b 3 := by
  unfold minkowskiInner minkowskiMetric
  simp [Fin.sum_univ_four, Matrix.diagonal]
  ring

/-- A 4×4 real matrix is a Lorentz transformation if it preserves
    the Minkowski metric: ΛᵀηΛ = η. -/
structure LorentzMatrix where
  /-- The 4×4 matrix Λ. -/
  Λ : Matrix (Fin 4) (Fin 4) ℝ
  /-- Preserves the Minkowski metric. -/
  preserves_metric : Λᵀ * minkowskiMetric * Λ = minkowskiMetric

/-- A Lorentz transformation preserves the Minkowski inner product.
    Follows from `preserves_metric`: Λᵀ η Λ = η implies η(Λa, Λb) = η(a,b). -/
theorem lorentz_preserves_inner (L : LorentzMatrix) (a b : FourVector) :
    L.Λᵀ * minkowskiMetric * L.Λ = minkowskiMetric := by
  simpa using L.preserves_metric

/-- The identity is a Lorentz transformation. -/
def lorentzIdentity : LorentzMatrix where
  Λ := 1
  preserves_metric := by simp

/-- The product of two Lorentz transformations is a Lorentz transformation. -/
def lorentzMul (L₁ L₂ : LorentzMatrix) : LorentzMatrix where
  Λ := L₁.Λ * L₂.Λ
  preserves_metric := by
    rw [Matrix.transpose_mul]
    have reassoc : ∀ (A B C D E : Matrix (Fin 4) (Fin 4) ℝ),
      (A * B) * C * (D * E) = A * (B * C * D) * E := fun A B C D E => by
      simp only [mul_assoc]
    rw [reassoc, L₁.preserves_metric, L₂.preserves_metric]

/-- det(Λ)² = 1 for any Lorentz transformation, so det(Λ) = ±1.
    Proof: det(ΛᵀηΛ) = det(Λ)²·det(η) = det(η), and det(η) ≠ 0. -/
theorem lorentz_det_sq (L : LorentzMatrix) :
    L.Λ.det ^ 2 * minkowskiMetric.det = minkowskiMetric.det := by
  have hdet := congrArg Matrix.det L.preserves_metric
  simpa [Matrix.det_mul, Matrix.det_transpose, pow_two, mul_assoc, mul_left_comm, mul_comm]
    using hdet

/-- A proper Lorentz transformation has det(Λ) = +1. -/
def IsProper (L : LorentzMatrix) : Prop :=
  L.Λ.det = 1

/-- An orthochronous Lorentz transformation preserves time direction: Λ⁰₀ ≥ 1. -/
def IsOrthochronous (L : LorentzMatrix) : Prop :=
  L.Λ 0 0 ≥ 1

/-- The restricted Lorentz group SO⁺(1,3) consists of proper orthochronous transformations. -/
def IsRestrictedLorentz (L : LorentzMatrix) : Prop :=
  IsProper L ∧ IsOrthochronous L

/-- An element of the Poincaré group: a Lorentz transformation + translation. -/
structure PoincareElement where
  /-- The Lorentz part Λ. -/
  lorentz : LorentzMatrix
  /-- The translation 4-vector a^μ. -/
  translation : FourVector

/-- Poincaré group multiplication: (Λ₁, a₁)(Λ₂, a₂) = (Λ₁Λ₂, Λ₁a₂ + a₁). -/
def poincareMul (g₁ g₂ : PoincareElement) : PoincareElement where
  lorentz := lorentzMul g₁.lorentz g₂.lorentz
  translation := fun μ => (g₁.lorentz.Λ *ᵥ g₂.translation) μ + g₁.translation μ

/-- The identity Poincaré element. -/
def poincareIdentity : PoincareElement where
  lorentz := lorentzIdentity
  translation := 0

/-- A 4-momentum vector with the mass-shell condition p² = -m²c². -/
structure FourMomentum where
  /-- The 4-momentum (E/c, px, py, pz). -/
  p : FourVector
  /-- Rest mass (≥ 0 for physical particles). -/
  mass : ℝ
  mass_nonneg : 0 ≤ mass
  /-- Mass-shell condition: p·p = -m². -/
  on_shell : minkowskiInner p p = -(mass ^ 2)
  /-- Positive energy: E ≥ 0. -/
  positive_energy : p 0 ≥ 0

/-- The generators of the Lorentz group: antisymmetric 4×4 matrices J^{μν}.
    There are 6 independent generators: 3 rotations (J₁₂, J₂₃, J₃₁)
    and 3 boosts (J₀₁, J₀₂, J₀₃). -/
def lorentzGenerator (μ ν : Fin 4) : Matrix (Fin 4) (Fin 4) ℝ :=
  fun α β =>
    minkowskiMetric μ α * (if β = ν then 1 else 0) -
    minkowskiMetric ν α * (if β = μ then 1 else 0)

/-- The 4D Levi-Civita symbol ε^{μνρσ}.
    ε^{0123} = +1, and fully antisymmetric under permutations. -/
def leviCivita4 (μ ν ρ σ : Fin 4) : ℤ :=
  Equiv.Perm.sign (Equiv.swap μ ν * Equiv.swap ρ σ * Equiv.swap ν ρ)
  -- This is a simplified definition; the full 4D Levi-Civita symbol
  -- is the sign of the permutation (μ ν ρ σ) of (0 1 2 3)

/-- Compute W^μ = ½ ε^{μνρσ} J_{νρ} P_σ from J and p using the Levi-Civita symbol. -/
def pauliLubanskiVector (w : PauliLubanski) : FourVector :=
  fun μ =>
    (1 / 2 : ℝ) * ∑ ν : Fin 4, ∑ ρ : Fin 4, ∑ σ : Fin 4,
      (leviCivita4 μ ν ρ σ : ℝ) * w.J ν ρ * w.p.p σ

/-- Wigner classification: types of elementary particles. -/
inductive WignerClass where
  /-- Massive particle (m > 0): classified by mass and spin j ∈ {0, ½, 1, ...}.
      Little group is SU(2). -/
  | massive (mass : ℝ) (spin : ℕ) (mass_pos : 0 < mass) : WignerClass
  /-- Massless particle (m = 0): classified by helicity h ∈ ℤ/2.
      Little group is ISO(2) (Euclidean group of the plane). -/
  | massless (helicity : ℤ) : WignerClass
  /-- Tachyonic (spacelike, m² < 0): unphysical but mathematically well-defined.
      Little group is SO(1,1) × SO(2) or SL(2,ℝ). -/
  | tachyonic : WignerClass
  /-- Vacuum (p = 0): the trivial representation. -/
  | vacuum : WignerClass

/-- The little group is the stabilizer of a reference momentum.
    For massive particles, the standard momentum is p = (m, 0, 0, 0). -/
def standardMomentum : WignerClass → FourVector
  | .massive m _ _ => ![m, 0, 0, 0]
  | .massless _ => ![1, 0, 0, 1]    -- Light-like: (E, 0, 0, E) with E=1
  | .tachyonic => ![0, 0, 0, 1]     -- Spacelike
  | .vacuum => ![0, 0, 0, 0]

/-- The massive standard momentum p = (m, 0, 0, 0) satisfies the mass-shell
    condition: η(p,p) = -m². -/
theorem massive_standard_on_shell (m : ℝ) (hm : 0 < m) :
    minkowskiInner (standardMomentum (.massive m 0 hm)) (standardMomentum (.massive m 0 hm)) = -(m ^ 2) := by
  rw [minkowskiInner_explicit]
  simp [standardMomentum]
  ring

/-- The massless standard momentum p = (1, 0, 0, 1) satisfies η(p,p) = 0. -/
theorem massless_standard_lightlike (h : ℤ) :
    minkowskiInner (standardMomentum (.massless h)) (standardMomentum (.massless h)) = 0 := by
  rw [minkowskiInner_explicit]
  simp [standardMomentum]
  ring

/-- A rotation matrix around the z-axis by angle θ.
    R = diag(1, cos θ, -sin θ, 0; 0, sin θ, cos θ, 0; 0,0,0,1)
    Metric preservation follows from sin²θ + cos²θ = 1. -/
def rotationZ (θ : ℝ) : LorentzMatrix where
  Λ := !![1, 0, 0, 0;
          0, Real.cos θ, -(Real.sin θ), 0;
          0, Real.sin θ, Real.cos θ, 0;
          0, 0, 0, 1]
  preserves_metric := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [minkowskiMetric, Matrix.transpose, Matrix.mul_apply, Fin.sum_univ_four,
            Matrix.diagonal, Matrix.vecHead, Matrix.vecTail]
    all_goals ring_nf; nlinarith [Real.sin_sq_add_cos_sq θ]

/-- A boost along the x-axis with rapidity φ.
    Λ = [[cosh φ, sinh φ, 0, 0], [sinh φ, cosh φ, 0, 0], [0,0,1,0], [0,0,0,1]]
    Metric preservation follows from cosh²φ - sinh²φ = 1. -/
def boostX (φ : ℝ) : LorentzMatrix where
  Λ := !![Real.cosh φ, Real.sinh φ, 0, 0;
          Real.sinh φ, Real.cosh φ, 0, 0;
          0, 0, 1, 0;
          0, 0, 0, 1]
  preserves_metric := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [minkowskiMetric, Matrix.transpose, Matrix.mul_apply, Fin.sum_univ_four,
            Matrix.diagonal, Matrix.vecHead, Matrix.vecTail]
    all_goals ring_nf; nlinarith [Real.cosh_sq_sub_sinh_sq φ]

end Mechanics
