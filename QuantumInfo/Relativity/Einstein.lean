import Mathlib
import QuantumInfo.Relativity.Basic

namespace Relativity

variable {n : ℕ}

/-- Einstein tensor: G_{μν} = R_{μν} - 1/2 R g_{μν} -/
noncomputable def EinsteinTensor (geom : LocalGeometry n) (μ ν : Fin n) : ℝ :=
  RicciTensor geom μ ν - (1/2 : ℝ) * RicciScalar geom * geom.g μ ν

/-- The Energy-Momentum tensor at a point. -/
structure StressEnergyTensor (n : ℕ) where
  T : Matrix (Fin n) (Fin n) ℝ
  symm : T.IsSymm

/-- Einstein Field Equations with Cosmological Constant: G_{μν} + Λ g_{μν} = 8πG T_{μν} -/
structure EinsteinFieldEquations (geom : LocalGeometry n) (T_tensor : StressEnergyTensor n) (Λ G : ℝ) : Prop where
  eq : ∀ μ ν, EinsteinTensor geom μ ν + Λ * geom.g μ ν = 8 * Real.pi * G * T_tensor.T μ ν

/-- Vacuum Field Equations: G_{μν} + Λ g_{μν} = 0 -/
structure VacuumFieldEquations (geom : LocalGeometry n) (Λ : ℝ) : Prop where
  eq : ∀ μ ν, EinsteinTensor geom μ ν + Λ * geom.g μ ν = 0

/-- Determinant of the metric -/
noncomputable def MetricDet (geom : LocalGeometry n) : ℝ :=
  Matrix.det geom.g

/-- Einstein-Hilbert Lagrangian density: L_EH = R √(-g) -/
noncomputable def HilbertLagrangianDensity (geom : LocalGeometry n) : ℝ :=
  RicciScalar geom * Real.sqrt (- MetricDet geom)

/-- Cosmological constant Lagrangian density: L_Λ = -2Λ √(-g) -/
noncomputable def CosmologicalLagrangianDensity (geom : LocalGeometry n) (Λ : ℝ) : ℝ :=
  -2 * Λ * Real.sqrt (- MetricDet geom)

/-- Matter Lagrangian density (abstract definition for variational principle) -/
noncomputable def MatterLagrangianDensity (geom : LocalGeometry n) (L_m : LocalGeometry n → ℝ) : ℝ :=
  L_m geom * Real.sqrt (- MetricDet geom)

end Relativity
