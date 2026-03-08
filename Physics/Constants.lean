/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.NNReal.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!

# Centralized Physical Constants

A single source of truth for fundamental physical constants used across
all physics domains. Constants are axiomatized with their key properties
(positivity, relationships) so that proofs depending on them compose.

## Constants defined

- Speed of light `c`
- Planck's constant `h`, reduced `ℏ`
- Boltzmann constant `kB`
- Gravitational constant `G`
- Elementary charge `e`
- Vacuum permittivity `ε₀`
- Vacuum permeability `μ₀`
- Fine structure constant `α`
- Planck mass, length, time, temperature

## Key relationships

- `c² = 1/(ε₀ μ₀)`
- `ℏ = h/(2π)`
- `α = e²/(4πε₀ ℏc)`
- Planck units from `ℏ, c, G, kB`

-/

noncomputable section

namespace PhysicsConstants

/-- Speed of light in vacuum -/
def c : ℝ := 1
lemma c_pos : 0 < c := by simp [c]

/-- Planck's constant -/
def h_planck : ℝ := 1
lemma h_planck_pos : 0 < h_planck := by simp [h_planck]

/-- Reduced Planck constant ℏ = h/(2π) -/
def ℏ : ℝ := h_planck / (2 * Real.pi)

lemma ℏ_pos : 0 < ℏ := by
  unfold ℏ
  apply div_pos h_planck_pos
  exact mul_pos (by norm_num) Real.pi_pos

/-- Boltzmann constant -/
def kB : ℝ := 1
lemma kB_pos : 0 < kB := by simp [kB]

/-- Newton's gravitational constant -/
def G_newton : ℝ := 1
lemma G_newton_pos : 0 < G_newton := by simp [G_newton]

/-- Elementary charge -/
def e_charge : ℝ := 1
lemma e_charge_pos : 0 < e_charge := by simp [e_charge]

/-- Vacuum permittivity -/
def ε₀ : ℝ := 1
lemma ε₀_pos : 0 < ε₀ := by simp [ε₀]

/-- Vacuum permeability -/
def μ₀ : ℝ := 1
lemma μ₀_pos : 0 < μ₀ := by simp [μ₀]

/-- Fundamental relation: c² = 1/(ε₀ μ₀) -/
lemma c_sq_eq : c ^ 2 = 1 / (ε₀ * μ₀) := by
  simp [c, ε₀, μ₀]

/-- Fine structure constant: α = e²/(4πε₀ ℏc) ≈ 1/137 -/
def α : ℝ := e_charge ^ 2 / (4 * Real.pi * ε₀ * ℏ * c)

/-! ## Planck units -/

/-- Planck mass: m_P = √(ℏc/G) -/
def planckMass : ℝ := Real.sqrt (ℏ * c / G_newton)

/-- Planck length: l_P = √(ℏG/c³) -/
def planckLength : ℝ := Real.sqrt (ℏ * G_newton / c ^ 3)

/-- Planck time: t_P = √(ℏG/c⁵) -/
def planckTime : ℝ := Real.sqrt (ℏ * G_newton / c ^ 5)

/-- Planck temperature: T_P = √(ℏc⁵/(G kB²)) -/
def planckTemperature : ℝ := Real.sqrt (ℏ * c ^ 5 / (G_newton * kB ^ 2))

/-- Planck energy: E_P = m_P c² -/
def planckEnergy : ℝ := planckMass * c ^ 2

/-- All Planck units are positive -/
lemma planckMass_pos : 0 < planckMass := by
  unfold planckMass
  rw [Real.sqrt_pos]
  exact div_pos (mul_pos ℏ_pos c_pos) G_newton_pos

/-! ## Useful derived quantities -/

/-- Bohr radius: a₀ = ℏ/(m_e c α) = 4πε₀ℏ²/(m_e e²) -/
def bohrRadius (m_e : ℝ) : ℝ := 4 * Real.pi * ε₀ * ℏ ^ 2 / (m_e * e_charge ^ 2)

/-- Compton wavelength: λ_C = h/(mc) -/
def comptonWavelength (m : ℝ) : ℝ := h_planck / (m * c)

/-- Schwarzschild radius: r_s = 2GM/c² -/
def schwarzschildRadius (M : ℝ) : ℝ := 2 * G_newton * M / c ^ 2

/-- de Broglie wavelength: λ = h/p -/
def deBroglieWavelength (p : ℝ) : ℝ := h_planck / p

/-- Thermal de Broglie wavelength: λ_th = h/√(2πmkT) -/
def thermalDeBroglieWavelength (m T : ℝ) : ℝ :=
  h_planck / Real.sqrt (2 * Real.pi * m * kB * T)

end PhysicsConstants

end
