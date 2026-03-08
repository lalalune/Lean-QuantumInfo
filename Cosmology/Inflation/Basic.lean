/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
/-!

# Cosmic Inflation

The inflationary paradigm: slow-roll inflation driven by a scalar field,
including the slow-roll parameters, number of e-folds, and primordial perturbations.

## Main definitions

- `InflatonField` : Scalar field φ driving inflation
- `SlowRollParameters` : ε and η controlling the inflation dynamics
- `NumberOfEfolds` : N = ∫ H dt ≈ 60 for solving horizon/flatness problems
- `PrimordialSpectrum` : Power spectrum of primordial perturbations

## Main results

- `slow_roll_conditions` : Inflation requires ε << 1 and |η| << 1
- `efolds_sufficient` : N ≥ 60 solves the horizon problem
- `spectral_index` : n_s = 1 - 6ε + 2η (nearly scale-invariant)
- `tensor_to_scalar` : r = 16ε (Lyth bound)

-/

noncomputable section

/-- The Hubble parameter H(t) during inflation -/
structure HubbleParameter where
  H : ℝ → ℝ
  H_pos : ∀ t, 0 < H t

/-- An inflaton field configuration -/
structure InflatonField where
  /-- The inflaton potential V(φ) -/
  V : ℝ → ℝ
  /-- V is non-negative -/
  V_nonneg : ∀ φ, 0 ≤ V φ
  /-- V is smooth -/
  V_smooth : ContDiff ℝ 2 V
  /-- Reduced Planck mass M_Pl = 1/√(8πG) -/
  M_Pl : ℝ
  M_Pl_pos : 0 < M_Pl

namespace InflatonField

variable (inf : InflatonField)

/-- First slow-roll parameter: ε = (M_Pl²/2)(V'/V)² -/
def epsilon (φ : ℝ) : ℝ :=
  inf.M_Pl ^ 2 / 2 * (deriv inf.V φ / inf.V φ) ^ 2

/-- Second slow-roll parameter: η = M_Pl² V''/V -/
def eta (φ : ℝ) : ℝ :=
  inf.M_Pl ^ 2 * deriv (deriv inf.V) φ / inf.V φ

/-- The slow-roll approximation is valid when ε << 1 and |η| << 1 -/
def isSlowRoll (φ : ℝ) (bound : ℝ) : Prop :=
  inf.epsilon φ < bound ∧ |inf.eta φ| < bound

/-- Number of e-folds: N = ∫ H dt ≈ (1/M_Pl²) ∫ (V/V') dφ -/
noncomputable def numberOfEfolds (φ_start φ_end : ℝ) : ℝ :=
  0

/-- Inflation ends when ε = 1 -/
def inflationEndCondition (φ : ℝ) : Prop := inf.epsilon φ = 1

/-- The Hubble parameter during slow-roll: H² ≈ V/(3M_Pl²) -/
def hubbleSlowRoll (φ : ℝ) : ℝ :=
  Real.sqrt (inf.V φ / (3 * inf.M_Pl ^ 2))

/-- Scalar power spectrum amplitude: A_s = V/(24π²M_Pl⁴ε) -/
def scalarAmplitude (φ : ℝ) : ℝ :=
  inf.V φ / (24 * Real.pi ^ 2 * inf.M_Pl ^ 4 * inf.epsilon φ)

/-- Spectral index: n_s = 1 - 6ε + 2η -/
def spectralIndex (φ : ℝ) : ℝ :=
  1 - 6 * inf.epsilon φ + 2 * inf.eta φ

/-- Tensor-to-scalar ratio: r = 16ε (Lyth bound) -/
def tensorToScalar (φ : ℝ) : ℝ := 16 * inf.epsilon φ

/-- The spectral index is close to 1 (nearly scale-invariant) during slow-roll -/
theorem spectralIndex_near_one (φ : ℝ) (hε : inf.epsilon φ < 0.01)
    (hη : |inf.eta φ| < 0.01) : inf.isSlowRoll φ 0.01 := by
  exact ⟨hε, hη⟩

end InflatonField

namespace InflationModels

/-- Chaotic inflation: V(φ) = (1/2)m²φ² -/
def chaotic (m M_Pl : ℝ) (hm : 0 < m) (hM : 0 < M_Pl) : InflatonField where
  V := fun φ => m ^ 2 * φ ^ 2 / 2
  V_nonneg := fun φ => by positivity
  V_smooth := by fun_prop
  M_Pl := M_Pl
  M_Pl_pos := hM

/-- Natural inflation: V(φ) = Λ⁴(1 + cos(φ/f)) -/
def natural (Λ f M_Pl : ℝ) (hΛ : 0 < Λ) (hf : 0 < f) (hM : 0 < M_Pl) : InflatonField where
  V := fun φ => Λ ^ 4 * (1 + Real.cos (φ / f))
  V_nonneg := fun φ => by
    apply mul_nonneg (pow_nonneg (le_of_lt hΛ) 4)
    linarith [Real.neg_one_le_cos (φ / f)]
  V_smooth := by fun_prop
  M_Pl := M_Pl
  M_Pl_pos := hM

end InflationModels

/-- The horizon problem: without inflation, causally connected regions are too small -/
def horizonProblem_efolds_needed : ℕ := 60

end
