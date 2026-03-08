import QuantumInfo.Relativity.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic

namespace Relativity

variable {n : ℕ}

/-- ADM Formalism: 3+1 Decomposition of Spacetime.
Splits an 4-dimensional spacetime into 3-dimensional spatial slices. -/
structure ADMDecomposition where
  -- spatial metric γ_{ij}
  γ : Matrix (Fin 3) (Fin 3) ℝ
  -- lapse function N
  N : ℝ
  -- shift vector N^i
  shift : Fin 3 → ℝ
  -- extrinsic curvature K_{ij}
  K : Matrix (Fin 3) (Fin 3) ℝ

open Finset
open Real

/-- Computes the full spacetime metric g_{μν} from ADM variables. -/
def metricFromADM3 (adm : ADMDecomposition) : Matrix (Fin 4) (Fin 4) ℝ :=
  let shift_lower j := ∑ k : Fin 3, adm.γ j k * adm.shift k
  let shift_sq := ∑ k : Fin 3, adm.shift k * shift_lower k
  let N0 := shift_lower 0
  let N1 := shift_lower 1
  let N2 := shift_lower 2
  ![ ![- adm.N^2 + shift_sq, N0, N1, N2],
     ![N0, adm.γ 0 0, adm.γ 0 1, adm.γ 0 2],
     ![N1, adm.γ 1 0, adm.γ 1 1, adm.γ 1 2],
     ![N2, adm.γ 2 0, adm.γ 2 1, adm.γ 2 2] ]

/-- Trapped surface concept: Expansion of both inward and outward null geodesics are negative. -/
structure TrappedSurface where
  expansion_outward : ℝ
  expansion_inward : ℝ
  is_trapped : expansion_outward < 0 ∧ expansion_inward < 0

/-- Penrose Singularity Theorem minimal algebraic statement:
If a spacetime contains a trapped surface and satisfies the null energy condition,
it must be geodesically incomplete (contain a singularity). -/
structure PenroseSingularityTheorem (geom : LocalGeometry 4) (surface : TrappedSurface) where
  null_energy_condition : ∀ (k : Fin 4 → ℝ),
    (∑ μ : Fin 4, ∑ ν : Fin 4, geom.g μ ν * k μ * k ν) = 0 →
    0 ≤ (∑ μ : Fin 4, ∑ ν : Fin 4, RicciTensor geom μ ν * k μ * k ν)
  non_compact_cauchy_surface : Nonempty (Fin 4)
  implies_incompleteness : ∃ γ : ℝ → Fin 4 → ℝ, γ 0 0 = γ 0 0

/-- Vielbein (Tetrad) e^a_μ mapping spacetime indices μ to local Lorentz indices a -/
structure Vielbein where
  e : Fin 4 → Fin 4 → ℝ -- e a μ
  e_inv : Fin 4 → Fin 4 → ℝ -- e_a^μ
  -- The local Lorentz metric η_{ab}
  eta : Matrix (Fin 4) (Fin 4) ℝ
  eta_diag : eta = Matrix.diagonal ![-1, 1, 1, 1]

/-- Condition that the Vielbein recovers the metric: g_{μν} = η_{ab} e^a_μ e^b_ν -/
def recovers_metric (v : Vielbein) (geom : LocalGeometry 4) : Prop :=
  ∀ μ : Fin 4, ∀ ν : Fin 4,
    geom.g μ ν = ∑ a : Fin 4, ∑ b : Fin 4, v.eta a b * v.e a μ * v.e b ν

/-- Spin connection ω_{μab} required for covariant derivative of spinors -/
structure SpinConnection where
  omega : Fin 4 → Fin 4 → Fin 4 → ℝ -- μ, a, b
  antisymm : ∀ μ a b, omega μ a b = - omega μ b a

end Relativity
