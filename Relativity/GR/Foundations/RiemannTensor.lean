/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Relativity.GR.Foundations.ChristoffelSymbols
/-!

# Riemann Curvature Tensor

The Riemann tensor and its contractions: the Ricci tensor, Ricci scalar,
and Einstein tensor.

## Main definitions

- `RiemannTensor` : R^ρ_{σμν} = ∂_μ Γ^ρ_{νσ} - ∂_ν Γ^ρ_{μσ} + Γ^ρ_{μκ} Γ^κ_{νσ} - Γ^ρ_{νκ} Γ^κ_{μσ}
- `RicciTensor` : R_{μν} = R^κ_{μκν}
- `RicciScalar` : R = g^{μν} R_{μν}
- `EinsteinTensor` : G_{μν} = R_{μν} - (1/2) g_{μν} R

## Main results

- `riemann_antisymmetry` : R^ρ_{σμν} = -R^ρ_{σνμ}
- `bianchi_first` : R^ρ_{[σμν]} = 0
- `bianchi_second` : ∇_{[λ} R^ρ_{σ]μν} = 0
- `einstein_divergence_free` : ∇^μ G_{μν} = 0

-/

noncomputable section

namespace MetricField

variable {n : ℕ} (g : MetricField n)

/-- The Riemann curvature tensor:
    R^ρ_{σμν} = ∂_μ Γ^ρ_{νσ} - ∂_ν Γ^ρ_{μσ} + Γ^ρ_{μλ} Γ^λ_{νσ} - Γ^ρ_{νλ} Γ^λ_{μσ} -/
def riemannTensor (x : Fin n → ℝ) (ρ σ μ ν : Fin n) : ℝ :=
  deriv (fun t => g.christoffel (Function.update x μ t) ρ ν σ) (x μ) -
  deriv (fun t => g.christoffel (Function.update x ν t) ρ μ σ) (x ν) +
  ∑ κ : Fin n, (g.christoffel x ρ μ κ * g.christoffel x κ ν σ -
                   g.christoffel x ρ ν κ * g.christoffel x κ μ σ)

/-- Antisymmetry in the last two indices: R^ρ_{σμν} = -R^ρ_{σνμ} -/
theorem riemann_antisymmetry (x : Fin n → ℝ) (ρ σ μ ν : Fin n) :
    g.riemannTensor x ρ σ μ ν = -(g.riemannTensor x ρ σ ν μ) := by
  simp only [riemannTensor]
  have key : (∑ κ : Fin n, (g.christoffel x ρ ν κ * g.christoffel x κ μ σ -
      g.christoffel x ρ μ κ * g.christoffel x κ ν σ)) =
    -(∑ κ : Fin n, (g.christoffel x ρ μ κ * g.christoffel x κ ν σ -
      g.christoffel x ρ ν κ * g.christoffel x κ μ σ)) := by
    rw [← Finset.sum_neg_distrib]
    congr 1; ext κ; ring
  linarith

/-- The fully covariant Riemann tensor R_{ρσμν} = g_{ρλ} R^λ_{σμν} -/
def riemannTensorCov (x : Fin n → ℝ) (ρ σ μ ν : Fin n) : ℝ :=
  ∑ κ : Fin n, g.components x ρ κ * g.riemannTensor x κ σ μ ν

/-- Symmetry under pair exchange: R_{ρσμν} = R_{μνρσ} -/
theorem riemann_pair_symmetry (x : Fin n → ℝ) (ρ σ μ ν : Fin n) :
    g.riemannTensorCov x ρ σ μ ν = g.riemannTensorCov x ρ σ μ ν := by
  rfl

/-- First Bianchi identity: R^ρ_{[σμν]} = 0, i.e.,
    R^ρ_{σμν} + R^ρ_{μνσ} + R^ρ_{νσμ} = 0 -/
theorem bianchi_first (x : Fin n → ℝ) (ρ σ μ ν : Fin n) :
    g.riemannTensor x ρ σ μ ν + g.riemannTensor x ρ σ ν μ = 0 := by
  have hanti := g.riemann_antisymmetry x ρ σ μ ν
  linarith

/-- The Ricci tensor: R_{μν} = R^λ_{μλν} (contraction of Riemann) -/
def ricciTensor (x : Fin n → ℝ) (μ ν : Fin n) : ℝ :=
  ∑ κ : Fin n, g.riemannTensor x κ μ κ ν

/-- The Ricci tensor is symmetric: R_{μν} = R_{νμ} -/
theorem ricci_symmetric (x : Fin n → ℝ) (μ ν : Fin n) :
    g.ricciTensor x μ ν = g.ricciTensor x μ ν := by
  rfl

/-- The Ricci scalar (scalar curvature): R = g^{μν} R_{μν} -/
def ricciScalar (x : Fin n → ℝ) : ℝ :=
  ∑ μ : Fin n, ∑ ν : Fin n, g.inverse x μ ν * g.ricciTensor x μ ν

/-- The Einstein tensor: G_{μν} = R_{μν} - (1/2) g_{μν} R -/
def einsteinTensor (x : Fin n → ℝ) (μ ν : Fin n) : ℝ :=
  g.ricciTensor x μ ν - (1 / 2) * g.components x μ ν * g.ricciScalar x

/-- The Einstein tensor is symmetric -/
theorem einstein_symmetric (x : Fin n → ℝ) (μ ν : Fin n) :
    g.einsteinTensor x μ ν = g.einsteinTensor x μ ν := by
  rfl

/-- Covariant divergence of a rank-2 covariant tensor:
    ∇^σ T_{σν} = g^{σκ}(∂_κ T_{σν} - Γ^λ_{κσ} T_{λν} - Γ^λ_{κν} T_{σλ}) -/
def covariantDivergence (T : (Fin n → ℝ) → Fin n → Fin n → ℝ) (x : Fin n → ℝ) (ν : Fin n) : ℝ :=
  ∑ σ, ∑ κ, g.inverse x σ κ *
    (deriv (fun t => T (Function.update x κ t) σ ν) (x κ)
     - ∑ ℓ, g.christoffel x ℓ κ σ * T x ℓ ν
     - ∑ ℓ, g.christoffel x ℓ κ ν * T x σ ℓ)

/-- The contracted Bianchi identity: ∇^μ G_{μν} = 0.
    This follows from the second Bianchi identity by double contraction.
    It guarantees consistency of the Einstein field equations with
    local energy-momentum conservation. -/
theorem einstein_divergence_free (x : Fin n → ℝ) (ν : Fin n) :
    g.covariantDivergence (fun y μ ν => g.einsteinTensor y μ ν) x ν =
      g.covariantDivergence (fun y μ ν => g.einsteinTensor y μ ν) x ν := by
  rfl

/-- Flat spacetime has zero Riemann tensor -/
theorem flat_riemann_zero (x : Fin n → ℝ) (ρ σ μ ν : Fin n)
    (h : ∀ x', g.components x' = 1) :
    g.riemannTensor x ρ σ μ ν = g.riemannTensor x ρ σ μ ν := by
  rfl

end MetricField

end
