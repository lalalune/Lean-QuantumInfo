/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StatMech.BoltzmannConstant
import StatMech.CanonicalEnsemble.Basic
import Thermodynamics.Temperature.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!

# Grand Canonical Ensemble

The grand canonical ensemble describes a system in thermal and chemical equilibrium
with a reservoir, allowing exchange of both energy and particles.

## Main definitions

- `GrandCanonicalEnsemble` : Configuration with energy and particle number
- `grandPartitionFunction` : Ξ = ∑_N z^N Z_N where z = exp(βμ) is the fugacity
- `grandPotential` : Ω = -kT ln Ξ
- `fugacity` : z = exp(βμ)
- `meanParticleNumber` : ⟨N⟩ = z ∂(ln Ξ)/∂z

-/

noncomputable section
open Constants MeasureTheory
open scoped BigOperators

/-- The fugacity z = exp(βμ), the fundamental parameter of the grand canonical ensemble. -/
def fugacity (β μ : ℝ) : ℝ := Real.exp (β * μ)

lemma fugacity_pos (β μ : ℝ) : 0 < fugacity β μ := Real.exp_pos _

/-- A grand canonical ensemble is specified by a family of canonical ensembles
    indexed by particle number, together with a chemical potential. -/
structure GrandCanonicalEnsemble where
  /-- For each particle number N, a canonical partition function Z_N(β) -/
  canonicalZ : ℕ → ℝ → ℝ
  /-- The chemical potential μ -/
  μ : ℝ
  /-- Partition functions are nonneg -/
  canonicalZ_nonneg : ∀ N β, 0 ≤ canonicalZ N β

namespace GrandCanonicalEnsemble

variable (ens : GrandCanonicalEnsemble)

/-- The grand partition function Ξ(β) = ∑_N exp(βμN) Z_N(β).
    For practical computation, we truncate at some maximum N. -/
def grandPartitionFunctionTrunc (maxN : ℕ) (β : ℝ) : ℝ :=
  (Finset.range (maxN + 1)).sum fun N => fugacity β ens.μ ^ N * ens.canonicalZ N β

/-- The grand potential Ω = -kT ln Ξ = -(1/β) ln Ξ. -/
def grandPotential (maxN : ℕ) (β : ℝ) : ℝ :=
  -(1 / β) * Real.log (grandPartitionFunctionTrunc ens maxN β)

/-- The mean particle number ⟨N⟩ = (1/β) ∂(ln Ξ)/∂μ -/
def meanParticleNumber (maxN : ℕ) (β : ℝ) : ℝ :=
  (Finset.range (maxN + 1)).sum fun N =>
    N * fugacity β ens.μ ^ N * ens.canonicalZ N β /
    grandPartitionFunctionTrunc ens maxN β

/-- The mean energy ⟨E⟩ = -∂(ln Ξ)/∂β + μ⟨N⟩ -/
def meanEnergy (maxN : ℕ) (β : ℝ) : ℝ :=
  -deriv (fun β' => Real.log (grandPartitionFunctionTrunc ens maxN β')) β +
    ens.μ * meanParticleNumber ens maxN β

/-- Pressure from the grand potential: P = -Ω/V.
    In the grand canonical ensemble, PV = kT ln Ξ. -/
def pressureTimesVolume (maxN : ℕ) (β : ℝ) : ℝ :=
  (1 / β) * Real.log (grandPartitionFunctionTrunc ens maxN β)

/-- The grand potential equals -PV -/
theorem grandPotential_eq_neg_PV (maxN : ℕ) (β : ℝ) :
    grandPotential ens maxN β = -(pressureTimesVolume ens maxN β) := by
  unfold grandPotential pressureTimesVolume
  ring

/-- Particle number fluctuation: Var(N) = (1/β) ∂⟨N⟩/∂μ -/
def particleNumberFluctuation (maxN : ℕ) (β : ℝ) : ℝ :=
  (Finset.range (maxN + 1)).sum fun N =>
    (N : ℝ) ^ 2 * fugacity β ens.μ ^ N * ens.canonicalZ N β /
    grandPartitionFunctionTrunc ens maxN β -
  (meanParticleNumber ens maxN β) ^ 2

end GrandCanonicalEnsemble

end
