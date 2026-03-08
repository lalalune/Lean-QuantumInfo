/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!

# Electromagnetic Radiation

Formalization of radiation from accelerating charges, including the Larmor formula,
multipole expansion, and antenna radiation patterns.

## Main definitions

- `LarmorFormula` : P = q²a²/(6πε₀c³) for non-relativistic radiation
- `RelativisticLarmor` : P = q²γ⁶/(6πε₀c)(a²_⊥ + γ²a²_∥)
- `MultipoleExpansion` : Expansion in electric and magnetic multipoles
- `RadiationPattern` : Angular distribution of radiated power

-/

noncomputable section

/-- The Larmor formula: power radiated by a non-relativistic accelerating charge.
    P = q²a²/(6πε₀c³) -/
def larmorPower (q a ε₀ c : ℝ) : ℝ :=
  q ^ 2 * a ^ 2 / (6 * Real.pi * ε₀ * c ^ 3)

theorem larmorPower_nonneg (q a ε₀ c : ℝ) (hε : 0 < ε₀) (hc : 0 < c) :
    0 ≤ larmorPower q a ε₀ c := by
  unfold larmorPower
  apply div_nonneg
  · exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  · exact le_of_lt (mul_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos) hε) (pow_pos hc 3))

/-- Angular distribution of Larmor radiation: dP/dΩ ∝ sin²θ
    where θ is the angle from the acceleration direction -/
def larmorAngularDistribution (q a ε₀ c θ : ℝ) : ℝ :=
  q ^ 2 * a ^ 2 / (16 * Real.pi ^ 2 * ε₀ * c ^ 3) * Real.sin θ ^ 2

/-- Relativistic Larmor formula (Liénard formula):
    P = (q²γ⁶)/(6πε₀c) · (|a|² - |v × a|²/c²) -/
def relativisticLarmorPower (q γ a_sq v_cross_a_sq ε₀ c : ℝ) : ℝ :=
  q ^ 2 * γ ^ 6 / (6 * Real.pi * ε₀ * c) * (a_sq - v_cross_a_sq / c ^ 2)

/-- For circular motion (synchrotron radiation), a ⊥ v and γ >> 1,
    so the radiated power scales as γ⁴ -/
def synchrotronPower (q γ a ε₀ c : ℝ) : ℝ :=
  q ^ 2 * γ ^ 4 * a ^ 2 / (6 * Real.pi * ε₀ * c ^ 3)

/-- The electric dipole moment -/
def electricDipoleMoment (charges : Fin 2 → ℝ) (positions : Fin 2 → Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => ∑ j : Fin 2, charges j * positions j i

/-- Power radiated by an oscillating electric dipole:
    P = ω⁴|p|²/(12πε₀c³) -/
def dipolePower (ω p_sq ε₀ c : ℝ) : ℝ :=
  ω ^ 4 * p_sq / (12 * Real.pi * ε₀ * c ^ 3)

/-- The radiation resistance of a half-wave dipole antenna -/
def halfWaveDipoleResistance : ℝ := 73.1

/-- Bremsstrahlung: radiation from deceleration of a charged particle.
    The total radiated energy in a collision is proportional to 1/m². -/
def bremsstrahlungPower (q₁ q₂ m v b ε₀ c : ℝ) : ℝ :=
  q₁ ^ 2 * q₂ ^ 2 / (6 * Real.pi * ε₀ * m ^ 2 * c ^ 3 * b ^ 2 * v)

end
