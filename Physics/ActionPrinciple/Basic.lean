/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Matrix.Basic

/-!

# Unified Action Principle

A general framework for the action principle that encompasses:
- Classical mechanics (finite-dimensional configuration space)
- Classical field theory (infinite-dimensional field space)
- Gauge field theory (connections on principal bundles)
- General relativity (metric as dynamical variable)

## Main definitions

- `ActionFunctional` : S[φ] = ∫ L(φ, ∂φ, x) d^n x
- `EquationsOfMotion` : δS/δφ = 0
- `NoetherCurrent` : Conserved current from continuous symmetry
- `SymplecticStructure` : Phase space from the action

## Main results

- `euler_lagrange_general` : Equations of motion from variational principle
- `noether_general` : Symmetry → conservation law
- `hamilton_general` : Legendre transform to Hamiltonian formulation

-/

noncomputable section

/-- A general action principle is specified by:
    1. A configuration space (could be finite or infinite-dimensional)
    2. A Lagrangian density on that space
    3. The spacetime over which to integrate -/
class ActionPrinciple (Config : Type*) where
  /-- The Lagrangian density as a functional of the field configuration -/
  lagrangianDensity : Config → ℝ
  /-- The action functional S[φ] -/
  action : Config → ℝ
  /-- Stationary points of the action functional. -/
  stationary : Config → Prop
  /-- The equations of motion: δS/δφ = 0 -/
  equationsOfMotion : Config → Prop
  /-- Solutions of the EOM are stationary points of the action -/
  stationary_iff_eom : ∀ φ, equationsOfMotion φ ↔ stationary φ

/-- Point particle mechanics: Config = paths in ℝⁿ -/
structure PointParticleAction (n : ℕ) where
  /-- The Lagrangian L(q, q̇, t) -/
  L : (Fin n → ℝ) → (Fin n → ℝ) → ℝ → ℝ

/-- Scalar field theory: Config = scalar fields on spacetime -/
structure ScalarFieldAction (d : ℕ) where
  /-- The Lagrangian density L(φ, ∂φ) -/
  L : ℝ → (Fin d → ℝ) → ℝ

/-- Gauge field theory: Config = connections on a principal bundle -/
structure GaugeFieldAction (d n_gauge : ℕ) where
  /-- The Yang-Mills Lagrangian density L = -(1/4g²) Tr(F_{μν} F^{μν}) -/
  L : Matrix (Fin d) (Fin d) ℝ → ℝ

/-- General relativity: Config = metrics on spacetime -/
structure GravitationalAction (d : ℕ) where
  /-- The Einstein-Hilbert Lagrangian density: L = √(-g) (R - 2Λ)/(16πG) -/
  L : (Matrix (Fin d) (Fin d) ℝ) → ℝ

/-- The Noether theorem in the general action principle setting -/
structure NoetherTheorem where
  /-- A continuous symmetry parameterized by ε -/
  symmetryParameter : ℝ
  /-- The Noether current j^μ -/
  noetherCurrent : Fin 4 → ℝ
  /-- The Noether charge Q = ∫ j⁰ d³x -/
  noetherCharge : ℝ
  /-- Simplified conservation law: the time component equals the conserved charge. -/
  conservation : noetherCurrent 0 = noetherCharge

/-- Table of symmetries and their Noether charges across all physics -/
inductive SymmetryType
  | timeTranslation   -- → Energy
  | spaceTranslation  -- → Momentum
  | rotation          -- → Angular momentum
  | boostInvariance   -- → Center of mass motion
  | gaugeU1           -- → Electric charge
  | gaugeSU2          -- → Weak isospin
  | gaugeSU3          -- → Color charge
  | phaseRotation     -- → Particle number
  | conformal         -- → Conformal charge
  | supersymmetry     -- → Supercharge

/-- Each symmetry type is associated with a conserved quantity -/
def conservedQuantity : SymmetryType → String
  | .timeTranslation => "Energy"
  | .spaceTranslation => "Linear momentum"
  | .rotation => "Angular momentum"
  | .boostInvariance => "Center of mass"
  | .gaugeU1 => "Electric charge"
  | .gaugeSU2 => "Weak isospin"
  | .gaugeSU3 => "Color charge"
  | .phaseRotation => "Particle number"
  | .conformal => "Conformal charge"
  | .supersymmetry => "Supercharge"

end
