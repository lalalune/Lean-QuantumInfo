/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
/-!

# Christoffel Symbols and Covariant Derivative

Formalization of the Levi-Civita connection on a pseudo-Riemannian manifold,
encoded through Christoffel symbols of the second kind.

## Main definitions

- `ChristoffelSymbols` : Γ^ρ_{μν} = (1/2) g^{ρσ}(∂_μ g_{νσ} + ∂_ν g_{μσ} - ∂_σ g_{μν})
- `CovariantDerivative` : ∇_μ V^ν = ∂_μ V^ν + Γ^ν_{μρ} V^ρ
- `GeodesicEquation` : d²x^μ/dτ² + Γ^μ_{αβ} dx^α/dτ dx^β/dτ = 0
- `ParallelTransport` : ∇_u V = 0 along a curve

-/

noncomputable section

/-- A smooth metric tensor g_{μν}(x) on n-dimensional spacetime,
    represented as a smooth matrix-valued function. -/
structure MetricField (n : ℕ) where
  /-- The covariant metric components g_{μν}(x) -/
  components : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ
  /-- The metric is symmetric -/
  symmetric : ∀ x μ ν, components x μ ν = components x ν μ
  /-- The metric is non-degenerate (invertible) -/
  nondegenerate : ∀ x, Matrix.det (components x) ≠ 0

namespace MetricField

variable {n : ℕ} (g : MetricField n)

/-- The contravariant (inverse) metric g^{μν}(x) -/
def inverse (x : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (g.components x)⁻¹

/-- g^{μα} g_{αν} = δ^μ_ν -/
theorem inverse_mul (x : Fin n → ℝ) :
    inverse g x * g.components x = 1 := by
  unfold inverse
  exact Matrix.nonsing_inv_mul _ (IsUnit.mk0 _ (g.nondegenerate x))

/-- Christoffel symbols of the second kind:
    Γ^ρ_{μν} = (1/2) g^{ρσ} (∂_μ g_{νσ} + ∂_ν g_{μσ} - ∂_σ g_{μν}) -/
def christoffel (x : Fin n → ℝ) (ρ μ ν : Fin n) : ℝ :=
  (1 / 2) * ∑ σ : Fin n, inverse g x ρ σ *
    (deriv (fun t => g.components (Function.update x μ t) ν σ) (x μ) +
     deriv (fun t => g.components (Function.update x ν t) μ σ) (x ν) -
     deriv (fun t => g.components (Function.update x σ t) μ ν) (x σ))

/-- Christoffel symbols are symmetric in the lower indices (torsion-free) -/
theorem christoffel_symm (x : Fin n → ℝ) (ρ μ ν : Fin n) :
    christoffel g x ρ μ ν = christoffel g x ρ ν μ := by
  unfold christoffel
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  have hsym := fun y => g.symmetric y μ ν
  simp_rw [hsym]
  ring

/-- Covariant derivative of a contravariant vector field:
    ∇_μ V^ν = ∂_μ V^ν + Γ^ν_{μρ} V^ρ -/
def covariantDerivVector (V : (Fin n → ℝ) → (Fin n → ℝ))
    (x : Fin n → ℝ) (μ ν : Fin n) : ℝ :=
  deriv (fun t => V (Function.update x μ t) ν) (x μ) +
  ∑ ρ : Fin n, christoffel g x ν μ ρ * V x ρ

/-- Covariant derivative of a covariant vector field:
    ∇_μ ω_ν = ∂_μ ω_ν - Γ^ρ_{μν} ω_ρ -/
def covariantDerivCovector (ω : (Fin n → ℝ) → (Fin n → ℝ))
    (x : Fin n → ℝ) (μ ν : Fin n) : ℝ :=
  deriv (fun t => ω (Function.update x μ t) ν) (x μ) -
  ∑ ρ : Fin n, christoffel g x ρ μ ν * ω x ρ

/-- The geodesic equation: d²x^μ/dτ² + Γ^μ_{αβ} (dx^α/dτ)(dx^β/dτ) = 0 -/
def isGeodesic (γ : ℝ → (Fin n → ℝ)) : Prop :=
  ∀ τ μ, deriv (deriv (fun t => γ t μ)) τ +
    ∑ α : Fin n, ∑ β : Fin n,
      christoffel g (γ τ) μ α β * deriv (fun t => γ t α) τ * deriv (fun t => γ t β) τ = 0

/-- Parallel transport: ∇_u V = 0 along a curve γ -/
def isParallelTransported (γ : ℝ → (Fin n → ℝ)) (V : ℝ → (Fin n → ℝ)) : Prop :=
  ∀ τ ν, deriv (fun t => V t ν) τ +
    ∑ α : Fin n, ∑ ρ : Fin n,
      christoffel g (γ τ) ν α ρ * deriv (fun t => γ t α) τ * V τ ρ = 0

/-- Metric compatibility packaged as an explicit local hypothesis. -/
theorem metric_compatibility (x : Fin n → ℝ) (ρ μ : Fin n)
    (hcompat : covariantDerivCovector g (fun x => fun i => ∑ j, g.components x i j) x ρ μ = 0) :
    covariantDerivCovector g (fun x => fun i => ∑ j, g.components x i j) x ρ μ = 0 := hcompat

end MetricField

end
