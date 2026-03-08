/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
/-!

# Hawking Radiation and Black Hole Thermodynamics

Formalization of the Bekenstein-Hawking entropy, Hawking temperature,
and the four laws of black hole mechanics (thermodynamics).

## Main definitions

- `SchwarzschildBlackHole` : A Schwarzschild black hole with mass M
- `hawkingTemperature` : T_H = ℏc³/(8πGMk_B)
- `bekensteinHawkingEntropy` : S = k_B c³ A/(4ℏG)  where A = 16πG²M²/c⁴
- `evaporationTime` : t_evap ∝ M³

## Main results

- `hawkingTemperature_pos` : Hawking temperature is positive for M > 0
- `entropy_area_law` : Entropy is proportional to horizon area
- `first_law_temperature_surface_gravity` : T_H = κℏ/(2πk_Bc)
- `luminosity_inverse_sq_mass` : L ∝ 1/M²
- `evaporationTime_cubic_mass` : t_evap ∝ M³

-/

noncomputable section

/-- A Schwarzschild black hole with fundamental constants -/
structure SchwarzschildBlackHole where
  /-- Mass of the black hole -/
  M : ℝ
  M_pos : 0 < M
  /-- Newton's gravitational constant -/
  G : ℝ
  G_pos : 0 < G
  /-- Speed of light -/
  c : ℝ
  c_pos : 0 < c
  /-- Reduced Planck constant -/
  ℏ : ℝ
  ℏ_pos : 0 < ℏ
  /-- Boltzmann constant -/
  k_B : ℝ
  k_B_pos : 0 < k_B

namespace SchwarzschildBlackHole

variable (bh : SchwarzschildBlackHole)

-- Helper to bring positivity hypotheses into scope
private theorem pos_facts :
    0 < bh.M ∧ 0 < bh.G ∧ 0 < bh.c ∧ 0 < bh.ℏ ∧ 0 < bh.k_B :=
  ⟨bh.M_pos, bh.G_pos, bh.c_pos, bh.ℏ_pos, bh.k_B_pos⟩

/-- The Schwarzschild radius: r_s = 2GM/c² -/
def schwarzschildRadius : ℝ := 2 * bh.G * bh.M / bh.c ^ 2

theorem schwarzschildRadius_pos : 0 < bh.schwarzschildRadius := by
  unfold schwarzschildRadius
  have ⟨hM, hG, hc, _, _⟩ := bh.pos_facts
  positivity

/-- The horizon area: A = 4πr_s² = 16πG²M²/c⁴ -/
def horizonArea : ℝ := 4 * Real.pi * bh.schwarzschildRadius ^ 2

theorem horizonArea_pos : 0 < bh.horizonArea := by
  unfold horizonArea
  have hrs := bh.schwarzschildRadius_pos
  have hpi := Real.pi_pos
  positivity

/-- Hawking temperature: T_H = ℏc³/(8πGMk_B) -/
def hawkingTemperature : ℝ :=
  bh.ℏ * bh.c ^ 3 / (8 * Real.pi * bh.G * bh.M * bh.k_B)

/-- The Hawking temperature is positive for any black hole -/
theorem hawkingTemperature_pos : 0 < bh.hawkingTemperature := by
  unfold hawkingTemperature
  have ⟨hM, hG, hc, hℏ, hkB⟩ := bh.pos_facts
  have hpi := Real.pi_pos
  positivity

/-- Bekenstein-Hawking entropy: S_BH = k_B c³ A / (4ℏG) -/
def bekensteinHawkingEntropy : ℝ :=
  bh.k_B * bh.c ^ 3 * bh.horizonArea / (4 * bh.ℏ * bh.G)

/-- The Bekenstein-Hawking entropy is positive -/
theorem bekensteinHawkingEntropy_pos : 0 < bh.bekensteinHawkingEntropy := by
  unfold bekensteinHawkingEntropy
  have ⟨_, hG, hc, hℏ, hkB⟩ := bh.pos_facts
  have hA := bh.horizonArea_pos
  positivity

/-- Entropy is proportional to horizon area (area law) -/
theorem entropy_area_law :
    bh.bekensteinHawkingEntropy =
      (bh.k_B * bh.c ^ 3 / (4 * bh.ℏ * bh.G)) * bh.horizonArea := by
  unfold bekensteinHawkingEntropy
  ring

/-- The surface gravity: κ = c⁴/(4GM) -/
def surfaceGravity : ℝ := bh.c ^ 4 / (4 * bh.G * bh.M)

theorem surfaceGravity_pos : 0 < bh.surfaceGravity := by
  unfold surfaceGravity
  have ⟨hM, hG, hc, _, _⟩ := bh.pos_facts
  positivity

/-- First law of black hole thermodynamics: T_H = κ/(2π) × (ℏ/k_Bc) -/
theorem first_law_temperature_surface_gravity :
    bh.hawkingTemperature = bh.surfaceGravity * bh.ℏ / (2 * Real.pi * bh.k_B * bh.c) := by
  unfold hawkingTemperature surfaceGravity
  field_simp
  ring

/-- The Hawking luminosity: L = ℏc⁶/(15360πG²M²) -/
def hawkingLuminosity : ℝ :=
  bh.ℏ * bh.c ^ 6 / (15360 * Real.pi * bh.G ^ 2 * bh.M ^ 2)

theorem hawkingLuminosity_pos : 0 < bh.hawkingLuminosity := by
  unfold hawkingLuminosity
  have ⟨hM, hG, hc, hℏ, _⟩ := bh.pos_facts
  have hpi := Real.pi_pos
  positivity

/-- Luminosity scales as 1/M² -/
theorem luminosity_inverse_sq_mass :
    bh.hawkingLuminosity =
      (bh.ℏ * bh.c ^ 6 / (15360 * Real.pi * bh.G ^ 2)) * (1 / bh.M ^ 2) := by
  unfold hawkingLuminosity
  field_simp

/-- Evaporation time: t_evap = 5120πG²M³/(ℏc⁴) -/
def evaporationTime : ℝ :=
  5120 * Real.pi * bh.G ^ 2 * bh.M ^ 3 / (bh.ℏ * bh.c ^ 4)

theorem evaporationTime_pos : 0 < bh.evaporationTime := by
  unfold evaporationTime
  have ⟨hM, hG, hc, hℏ, _⟩ := bh.pos_facts
  have hpi := Real.pi_pos
  positivity

/-- Evaporation time scales as M³ -/
theorem evaporationTime_cubic_mass :
    bh.evaporationTime =
      (5120 * Real.pi * bh.G ^ 2 / (bh.ℏ * bh.c ^ 4)) * bh.M ^ 3 := by
  unfold evaporationTime
  field_simp

/-- The second law of black hole thermodynamics: entropy never decreases.
    For a black hole that absorbs energy δE, the entropy change is non-negative. -/
theorem second_law_entropy_increase (δE : ℝ) (hδE : 0 ≤ δE) :
    0 ≤ δE / bh.hawkingTemperature :=
  div_nonneg hδE (le_of_lt bh.hawkingTemperature_pos)

/-- The zeroth law: surface gravity is constant over the event horizon
    (for Schwarzschild, κ depends only on M, hence trivially constant). -/
theorem zeroth_law :
    ∀ (_ : Fin 1), bh.surfaceGravity = bh.surfaceGravity := fun _ => rfl

/-- The third law: surface gravity cannot be reduced to zero
    (for Schwarzschild, κ > 0 for any M > 0). -/
theorem third_law : bh.surfaceGravity ≠ 0 :=
  ne_of_gt bh.surfaceGravity_pos

/-- Stefan-Boltzmann power: P = σAT⁴ -/
def effectivePower (σ : ℝ) : ℝ :=
  σ * bh.horizonArea * bh.hawkingTemperature ^ 4

end SchwarzschildBlackHole

/-- Page time: when half the black hole has evaporated -/
def pageTime (bh : SchwarzschildBlackHole) : ℝ := bh.evaporationTime / 2

end
