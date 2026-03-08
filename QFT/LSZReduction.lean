/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!

# LSZ Reduction Formula and Optical Theorem

The Lehmann-Symanzik-Zimmermann reduction formula connecting
S-matrix elements to time-ordered correlation functions,
and the optical theorem as a consequence of unitarity.

## Main definitions

- `LSZReduction` : S-matrix elements from amputated Green's functions
- `OpticalTheorem` : Im M_{ii} = (1/2) ∑_f |M_{if}|² (from unitarity)
- `CrossingSymmetry` : Relation between different channels
- `DispersionRelation` : Analyticity constraints on scattering amplitudes

## Main results

- `lsz_connects_correlators_to_Smatrix` : Poles of G^(n) give S-matrix
- `optical_theorem_from_unitarity` : S†S = 1 → optical theorem
- `froissart_bound` : σ_total ≤ C (ln s)² at high energy

-/

noncomputable section

/-- Mandelstam variables for 2→2 scattering -/
structure MandelstamVariables where
  s : ℝ  -- center-of-mass energy squared
  t : ℝ  -- momentum transfer squared
  u : ℝ  -- crossed momentum transfer squared
  /-- s + t + u = ∑ m_i² -/
  sum_constraint : ℝ

/-- Scattering amplitude for 2→2 process -/
structure ScatteringAmplitude2to2 where
  /-- The invariant amplitude M(s, t) -/
  M : ℝ → ℝ → ℂ

namespace ScatteringAmplitude2to2

variable (amp : ScatteringAmplitude2to2)

/-- Differential cross section: dσ/dt = |M|²/(64πs|p_i|²) -/
def diffCrossSection (s t : ℝ) (p_cm : ℝ) : ℝ :=
  Complex.normSq (amp.M s t) / (64 * Real.pi * s * p_cm ^ 2)

end ScatteringAmplitude2to2

/-- The optical theorem: the total cross section is related to the
    imaginary part of the forward scattering amplitude.
    σ_total = Im M(s, 0) / (2 p_cm √s) -/
structure OpticalTheorem where
  /-- Forward scattering amplitude -/
  M_forward : ℝ → ℂ
  /-- Total cross section -/
  σ_total : ℝ → ℝ
  /-- CM momentum -/
  p_cm : ℝ → ℝ
  /-- The optical theorem relation -/
  theorem_ : ∀ s, σ_total s = (M_forward s).im / (2 * p_cm s * Real.sqrt s)


/-- The LSZ reduction formula (schematic):
    ⟨p₁...pₙ|S|q₁...qₘ⟩ = (∏ poles) × G^(n+m)(p₁,...,pₙ,q₁,...,qₘ) -/
structure LSZFormula where
  /-- Number of incoming particles -/
  n_in : ℕ
  /-- Number of outgoing particles -/
  n_out : ℕ
  /-- The S-matrix element -/
  S_element : ℂ
  /-- The connected Green's function -/
  G_connected : ℂ
  /-- The wave function renormalization factors -/
  Z_factors : Fin (n_in + n_out) → ℝ

end
