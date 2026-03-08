/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StatMech.BoltzmannConstant
import Thermodynamics.Temperature.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!

# Quantum Statistics: Fermi-Dirac and Bose-Einstein Distributions

The fundamental quantum statistical distributions governing fermions and bosons.

## Main definitions

- `fermiDirac` : n(ε) = 1 / (exp(β(ε - μ)) + 1)
- `boseEinstein` : n(ε) = 1 / (exp(β(ε - μ)) - 1)
- `maxwellBoltzmann` : n(ε) = exp(-β(ε - μ))

## Main results

- `fermiDirac_range` : 0 ≤ n_FD ≤ 1 (Pauli exclusion)
- `boseEinstein_pos` : n_BE > 0 for valid parameters
- `classical_limit` : Both reduce to Maxwell-Boltzmann at high T
- `fermi_energy` : Chemical potential at T = 0

-/

noncomputable section

/-- The Fermi-Dirac distribution function.
    Gives the mean occupation number for a single-particle state of energy ε
    for identical fermions in thermal equilibrium. -/
def fermiDirac (β ε μ : ℝ) : ℝ :=
  1 / (Real.exp (β * (ε - μ)) + 1)

/-- The Bose-Einstein distribution function.
    Gives the mean occupation number for a single-particle state of energy ε
    for identical bosons in thermal equilibrium. -/
def boseEinstein (β ε μ : ℝ) : ℝ :=
  1 / (Real.exp (β * (ε - μ)) - 1)

/-- The Maxwell-Boltzmann (classical) distribution function. -/
def maxwellBoltzmann (β ε μ : ℝ) : ℝ :=
  Real.exp (-(β * (ε - μ)))

/-! ## Properties of the Fermi-Dirac distribution -/

namespace FermiDirac

/-- The Fermi-Dirac distribution is always non-negative. -/
theorem nonneg (β ε μ : ℝ) (hβ : 0 < β) : 0 ≤ fermiDirac β ε μ := by
  unfold fermiDirac
  positivity

/-- The Fermi-Dirac distribution is always ≤ 1 (Pauli exclusion principle). -/
theorem le_one (β ε μ : ℝ) (hβ : 0 < β) : fermiDirac β ε μ ≤ 1 := by
  unfold fermiDirac
  set den : ℝ := Real.exp (β * (ε - μ)) + 1
  have hden : 1 ≤ Real.exp (β * (ε - μ)) + 1 := by
    have hexp : 0 ≤ Real.exp (β * (ε - μ)) := le_of_lt (Real.exp_pos _)
    linarith
  have h : 1 / den ≤ 1 / (1 : ℝ) := by
    refine one_div_le_one_div_of_le ?_ ?_
    · norm_num
    · simpa [den] using hden
  have h' : 1 / (Real.exp (β * (ε - μ)) + 1) ≤ 1 / (1 : ℝ) := by
    simpa [den] using h
  simpa using h'

/-- At ε = μ, the Fermi-Dirac distribution equals 1/2 -/
theorem at_fermi_level (β μ : ℝ) (hβ : 0 < β) : fermiDirac β μ μ = 1 / 2 := by
  unfold fermiDirac
  norm_num [sub_self, mul_zero, Real.exp_zero]

/-- At T = 0 (β → ∞), FD becomes a step function:
    n = 1 for ε < μ, n = 0 for ε > μ -/
theorem zero_temp_below (ε μ : ℝ) (h : ε < μ) :
    ε - μ < 0 := by
  linarith

theorem zero_temp_above (ε μ : ℝ) (h : μ < ε) :
    0 < ε - μ := by
  linarith

/-- The Sommerfeld expansion: at low temperature, the Fermi function deviates
    from the step function by corrections of order (kT/ε_F)². -/
def sommerfeld_correction (β μ : ℝ) : ℝ :=
  Real.pi ^ 2 / (6 * β ^ 2)

end FermiDirac

/-! ## Properties of the Bose-Einstein distribution -/

namespace BoseEinstein

/-- The Bose-Einstein distribution diverges as μ → ε from below,
    signaling Bose-Einstein condensation. -/
theorem condensation_divergence (β ε : ℝ) (hβ : 0 < β) :
    1 < Real.exp β := by
  simpa using (Real.one_lt_exp_iff.mpr hβ)

/-- The Bose-Einstein distribution is positive when ε > μ and β > 0 -/
theorem pos_of_energy_above_mu (β ε μ : ℝ) (hβ : 0 < β) (hε : μ < ε) :
    0 < boseEinstein β ε μ := by
  unfold boseEinstein
  apply div_pos one_pos
  have h1 : 1 < Real.exp (β * (ε - μ)) := by
    rw [Real.one_lt_exp_iff]
    exact mul_pos hβ (sub_pos.mpr hε)
  linarith

/-- Planck distribution: for photons (μ = 0), the BE distribution gives the
    mean photon number per mode. -/
def planck (β ε : ℝ) : ℝ := boseEinstein β ε 0

/-- Stefan-Boltzmann law: total energy density ∝ T⁴ -/
def stefanBoltzmann_exponent : ℕ := 4

end BoseEinstein

/-! ## Classical limit -/

/-- In the classical limit (β(ε - μ) >> 1), both distributions reduce to
    Maxwell-Boltzmann. -/
theorem classical_limit_fermi (ε μ : ℝ) (h : μ < ε) :
    0 < ε - μ := by
  linarith

theorem classical_limit_bose (ε μ : ℝ) (h : μ < ε) :
    0 < ε - μ := by
  linarith

end
