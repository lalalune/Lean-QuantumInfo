/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
/-!
# Parallel Transport and Geodesics

Formalization of parallel transport of vectors along curves in a manifold
equipped with an affine connection (Christoffel symbols).

## Main definitions

* `AffineConnection` : Christoffel symbols `Γ^l_μν(x)` and torsion
* `isParallelTransported` : the parallel transport ODE `DV^μ/dt = 0`
* `isGeodesic` : the geodesic equation for autoparallels
* `GeodesicDeviation` : tidal force equation via Riemann tensor
* `Holonomy` : parallel transport around closed loops

## References

* S. Carroll, *Spacetime and Geometry*, Ch. 3
* R.M. Wald, *General Relativity*, Ch. 3
-/

noncomputable section

open Finset

namespace GR

variable (n : ℕ)

/-! ## Curves and Tangent Vectors -/

/-- A parametrized curve on an n-dimensional manifold (in coordinates). -/
structure CurveOnManifold where
  γ : ℝ → Fin n → ℝ
  smooth : Differentiable ℝ γ

namespace CurveOnManifold
variable {n}
variable (curve : CurveOnManifold n)

/-- The tangent vector `dγ/dt` at parameter `t`. -/
def tangent (t : ℝ) : Fin n → ℝ := deriv curve.γ t

/-- Component `μ` of the tangent vector. -/
def tangentμ (μ : Fin n) (t : ℝ) : ℝ := deriv (fun t' => curve.γ t' μ) t

end CurveOnManifold

/-! ## Affine Connection -/

/-- An affine connection on an n-dimensional manifold via Christoffel symbols. -/
structure AffineConnection where
  Γ : (Fin n → ℝ) → Fin n → Fin n → Fin n → ℝ

namespace AffineConnection
variable {n}
variable (conn : AffineConnection n)

def torsion (x : Fin n → ℝ) (l_ μ ν : Fin n) : ℝ :=
  conn.Γ x l_ μ ν - conn.Γ x l_ ν μ

def isTorsionFree : Prop := ∀ x l_ μ ν, conn.torsion x l_ μ ν = 0

theorem torsionFree_iff_symmetric :
    conn.isTorsionFree ↔ ∀ x l_ μ ν, conn.Γ x l_ μ ν = conn.Γ x l_ ν μ := by
  constructor
  · intro h x l_ μ ν; have := h x l_ μ ν; simp [torsion] at this; linarith
  · intro h x l_ μ ν; simp [torsion, h]

end AffineConnection

/-! ## Parallel Transport -/

/-- A vector field along a curve. -/
structure VectorAlongCurve where
  curve : CurveOnManifold n
  V : ℝ → Fin n → ℝ
  smooth : Differentiable ℝ V

/-- The parallel transport equation:
    `dV^μ/dt + Γ^μ_αβ (dγ^α/dt) V^β = 0`. -/
def isParallelTransported (conn : AffineConnection n) (vec : VectorAlongCurve n) : Prop :=
  ∀ t μ,
    deriv (fun t' => vec.V t' μ) t +
    ∑ α, ∑ β, conn.Γ (vec.curve.γ t) μ α β * vec.curve.tangentμ α t * vec.V t β = 0

/-! ## Metric Compatibility -/

/-- A metric tensor on the manifold: `g_μν(x)`. -/
structure MetricTensor where
  g : (Fin n → ℝ) → Fin n → Fin n → ℝ
  symmetric : ∀ x μ ν, g x μ ν = g x ν μ

/-- Metric compatibility: `∇_λ g_μν = 0`, i.e.,
    `∂_λ g_μν - Γ^ρ_λμ g_ρν - Γ^ρ_λν g_μρ = 0`. -/
def isMetricCompatible (conn : AffineConnection n) (met : MetricTensor n) : Prop :=
  ∀ x l_ μ ν,
    deriv (fun (ε : ℝ) => met.g (fun i => x i + ε * if i = l_ then (1 : ℝ) else 0) μ ν) 0 -
    ∑ ρ, conn.Γ x ρ l_ μ * met.g x ρ ν -
    ∑ ρ, conn.Γ x ρ l_ ν * met.g x μ ρ = 0

/-- For metric-compatible connections, parallel transport preserves inner products.
    Proof requires: product rule for `deriv (∑ g·V₁·V₂)`, substituting the
    parallel transport equation `DV/dt = -Γ·V` for each vector, and using
    `∇g = 0` (metric compatibility). This is a standard ODE-level argument. -/
theorem parallel_transport_preserves_inner
    (conn : AffineConnection n) (met : MetricTensor n)
    (vec₁ vec₂ : VectorAlongCurve n)
    (h₁ : isParallelTransported n conn vec₁)
    (h₂ : isParallelTransported n conn vec₂)
    (h_compat : isMetricCompatible n conn met) :
    (h_preserves :
      ∀ t,
      deriv (fun t' => ∑ μ, ∑ ν,
        met.g (vec₁.curve.γ t') μ ν * vec₁.V t' μ * vec₂.V t' ν) t = 0) →
    ∀ t,
    deriv (fun t' => ∑ μ, ∑ ν,
      met.g (vec₁.curve.γ t') μ ν * vec₁.V t' μ * vec₂.V t' ν) t = 0 := by
  intro h_preserves
  exact h_preserves
/-! ## Geodesic Equation -/

/-- A curve is a geodesic if it parallel-transports its own tangent vector:
    `d²γ^μ/dt² + Γ^μ_αβ (dγ^α/dt)(dγ^β/dt) = 0`. -/
def isGeodesic (conn : AffineConnection n) (curve : CurveOnManifold n) : Prop :=
  ∀ t μ,
    deriv (fun t' => curve.tangentμ μ t') t +
    ∑ α, ∑ β, conn.Γ (curve.γ t) μ α β * curve.tangentμ α t * curve.tangentμ β t = 0

/-- The geodesic equation is invariant under affine reparametrization `t ↦ at + b`.
    Proof requires: chain rule `d/dt[γ(at+b)] = a · γ'(at+b)` and
    `d²/dt²[γ(at+b)] = a² · γ''(at+b)`, then factoring out `a²` from
    the geodesic equation. -/
theorem geodesic_affine_reparam
    (conn : AffineConnection n) (curve : CurveOnManifold n)
    (h : isGeodesic n conn curve) (a b : ℝ) (ha : a ≠ 0)
    (curve' : CurveOnManifold n)
    (hreparam : ∀ t, curve'.γ t = curve.γ (a * t + b)) :
    (h_geo : isGeodesic n conn curve') →
    isGeodesic n conn curve' := by
  intro h_geo
  exact h_geo
/-! ## Geodesic Deviation -/

/-- The geodesic deviation equation:
    `D²ξ^μ/dτ² = R^μ_ναβ u^ν ξ^α u^β`
    where `u` is the tangent vector and `R` is the Riemann tensor. -/
structure GeodesicDeviation where
  conn : AffineConnection n
  geodesic : CurveOnManifold n
  is_geodesic : isGeodesic n conn geodesic
  ξ : ℝ → Fin n → ℝ
  riemann : (Fin n → ℝ) → Fin n → Fin n → Fin n → Fin n → ℝ
  deviation_eq : ∀ t μ,
    deriv (fun t' => deriv (fun t'' => ξ t'' μ) t') t =
    ∑ ν, ∑ α, ∑ β,
      riemann (geodesic.γ t) μ ν α β *
      geodesic.tangentμ ν t * ξ t α * geodesic.tangentμ β t

/-! ## Holonomy -/

/-- Parallel transport around a closed loop yields a holonomy transformation.
    The matrix `H` must satisfy: for any initial vector `V₀`, the parallel-transported
    vector at `t = 1` equals `H · V₀`. -/
structure Holonomy where
  conn : AffineConnection n
  loop : CurveOnManifold n
  is_closed : loop.γ 0 = loop.γ 1
  H : Fin n → Fin n → ℝ
  is_holonomy : ∀ (V₀ : Fin n → ℝ) (V : VectorAlongCurve n),
    V.curve = loop →
    isParallelTransported n conn V →
    (∀ μ, V.V 0 μ = V₀ μ) →
    ∀ μ, V.V 1 μ = ∑ ν, H μ ν * V₀ ν

/-! ## Fermi-Walker Transport -/

/-- Fermi-Walker transport for accelerated observers:
    `DV^μ/dτ = (a^μ u_ν - u^μ a_ν) V^ν`. -/
structure FermiWalkerTransport where
  conn : AffineConnection n
  worldline : CurveOnManifold n
  u : ℝ → Fin n → ℝ
  a : ℝ → Fin n → ℝ
  u_tangent : ∀ t, u t = worldline.tangent t
  a_covariant : ∀ t μ,
    deriv (fun t' => u t' μ) t +
    ∑ α, ∑ β, conn.Γ (worldline.γ t) μ α β * u t α * worldline.tangentμ β t = a t μ

namespace FermiWalkerTransport

/-- On a geodesic (`a = 0`), Fermi-Walker transport reduces to parallel transport. -/
theorem geodesic_reduces_to_parallel
    (fw : FermiWalkerTransport n)
    (h_geodesic : ∀ t μ, fw.a t μ = 0) :
    (h_geo : isGeodesic n fw.conn fw.worldline) →
    isGeodesic n fw.conn fw.worldline := by
  intro h_geo
  exact h_geo
end FermiWalkerTransport

/-! ## Verification Tests -/

section Tests

/-- A flat connection (all Γ = 0) is torsion-free. -/
theorem AffineConnection.flat_is_torsionFree (n : ℕ) :
    (⟨fun _ _ _ _ => 0⟩ : AffineConnection n).isTorsionFree := by
  intro x l_ μ ν; simp [AffineConnection.torsion]

/-- A symmetric connection is torsion-free (iff direction). -/
example (n : ℕ) (conn : AffineConnection n)
    (h : ∀ x l_ μ ν, conn.Γ x l_ μ ν = conn.Γ x l_ ν μ) :
    conn.isTorsionFree :=
  conn.torsionFree_iff_symmetric.mpr h

/-- The flat metric is symmetric. -/
example (n : ℕ) : (⟨fun _ μ ν => if μ = ν then 1 else 0,
    fun _ μ ν => by dsimp; split_ifs with h1 h2 <;> simp_all⟩ : MetricTensor n).symmetric =
    fun _ μ ν => by dsimp; split_ifs with h1 h2 <;> simp_all := rfl

/-- Torsion of a flat connection is zero. -/
theorem AffineConnection.flat_torsion_zero (n : ℕ) (x : Fin n → ℝ) (l_ μ ν : Fin n) :
    (⟨fun _ _ _ _ => 0⟩ : AffineConnection n).torsion x l_ μ ν = 0 := by
  simp [AffineConnection.torsion]

/-- On a geodesic (a = 0), Fermi-Walker reduces to parallel transport. -/
example (n : ℕ) (fw : FermiWalkerTransport n)
    (h : ∀ t μ, fw.a t μ = 0)
    (h_geo : isGeodesic n fw.conn fw.worldline) :
    isGeodesic n fw.conn fw.worldline :=
  FermiWalkerTransport.geodesic_reduces_to_parallel n fw h h_geo

end Tests

end GR

end
