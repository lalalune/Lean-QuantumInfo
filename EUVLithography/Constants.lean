/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!

# EUV Lithography: Physical Constants

Small positive-constant wrappers and light/quantum-energy identities used by
the EUV source and plasma calculations.  The positive-wrapper style follows the
useful constants pattern in `leanprover-community/physlib` for `ℏ`, `kB`, and
`SpeedOfLight`, while keeping this project independent of the full external
library.

-/

noncomputable section

open Real

namespace EUVConstants

/-- Reduced Planck constant `ℏ` as a positive real. -/
structure ReducedPlanckConstant where
  /-- Underlying value of `ℏ`. -/
  val : ℝ
  /-- Positivity of `ℏ`. -/
  pos : 0 < val

namespace ReducedPlanckConstant

instance : Coe ReducedPlanckConstant ℝ := ⟨ReducedPlanckConstant.val⟩

@[simp]
theorem val_pos (hbar : ReducedPlanckConstant) : 0 < (hbar : ℝ) := hbar.pos

@[simp]
theorem val_nonneg (hbar : ReducedPlanckConstant) : 0 ≤ (hbar : ℝ) := le_of_lt hbar.pos

@[simp]
theorem val_ne_zero (hbar : ReducedPlanckConstant) : (hbar : ℝ) ≠ 0 := ne_of_gt hbar.pos

/-- CODATA SI value of `ℏ`, in J s. -/
def si : ReducedPlanckConstant := ⟨1.054571817e-34, by norm_num⟩

end ReducedPlanckConstant

/-- Speed of light in vacuum as a positive real. -/
structure SpeedOfLight where
  /-- Underlying value of `c`. -/
  val : ℝ
  /-- Positivity of `c`. -/
  pos : 0 < val

namespace SpeedOfLight

instance : Coe SpeedOfLight ℝ := ⟨SpeedOfLight.val⟩

@[simp]
theorem val_pos (c : SpeedOfLight) : 0 < (c : ℝ) := c.pos

@[simp]
theorem val_nonneg (c : SpeedOfLight) : 0 ≤ (c : ℝ) := le_of_lt c.pos

@[simp]
theorem val_ne_zero (c : SpeedOfLight) : (c : ℝ) ≠ 0 := ne_of_gt c.pos

/-- Exact SI value of `c`, in m/s. -/
def si : SpeedOfLight := ⟨299792458, by norm_num⟩

end SpeedOfLight

/-- Boltzmann constant `k_B` as a positive real. -/
structure BoltzmannConstant where
  /-- Underlying value of `k_B`. -/
  val : ℝ
  /-- Positivity of `k_B`. -/
  pos : 0 < val

namespace BoltzmannConstant

instance : Coe BoltzmannConstant ℝ := ⟨BoltzmannConstant.val⟩

@[simp]
theorem val_pos (kB : BoltzmannConstant) : 0 < (kB : ℝ) := kB.pos

@[simp]
theorem val_nonneg (kB : BoltzmannConstant) : 0 ≤ (kB : ℝ) := le_of_lt kB.pos

@[simp]
theorem val_ne_zero (kB : BoltzmannConstant) : (kB : ℝ) ≠ 0 := ne_of_gt kB.pos

/-- Exact SI value of `k_B`, in J/K. -/
def si : BoltzmannConstant := ⟨1.380649e-23, by norm_num⟩

end BoltzmannConstant

/-- Planck constant generated from reduced Planck constant: `h = 2πℏ`. -/
def planckFromReduced (hbar : ReducedPlanckConstant) : ℝ :=
  2 * π * (hbar : ℝ)

theorem planckFromReduced_pos (hbar : ReducedPlanckConstant) :
    0 < planckFromReduced hbar := by
  unfold planckFromReduced
  exact mul_pos (mul_pos two_pos pi_pos) hbar.pos

/-- Optical angular frequency from wavelength: `ω = 2πc/λ`. -/
def angularFrequencyFromWavelength (c : SpeedOfLight) (lambda : ℝ) : ℝ :=
  2 * π * (c : ℝ) / lambda

theorem angularFrequencyFromWavelength_pos (c : SpeedOfLight) {lambda : ℝ}
    (hlambda : 0 < lambda) :
    0 < angularFrequencyFromWavelength c lambda := by
  unfold angularFrequencyFromWavelength
  exact div_pos (mul_pos (mul_pos two_pos pi_pos) c.pos) hlambda

/-- Photon energy in angular-frequency form. -/
def photonEnergyAngular (hbar : ReducedPlanckConstant) (omega : ℝ) : ℝ :=
  (hbar : ℝ) * omega

/-- The optical identity `ℏω = hc/λ` for `ω = 2πc/λ` and `h = 2πℏ`. -/
theorem hbar_omega_eq_hc_over_lambda (hbar : ReducedPlanckConstant) (c : SpeedOfLight)
    {lambda : ℝ} (hlambda : lambda ≠ 0) :
    photonEnergyAngular hbar (angularFrequencyFromWavelength c lambda) =
      planckFromReduced hbar * (c : ℝ) / lambda := by
  unfold photonEnergyAngular angularFrequencyFromWavelength planckFromReduced
  field_simp [hlambda]

end EUVConstants

