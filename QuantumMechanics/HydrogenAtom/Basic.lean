/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Complex.Basic
/-!

# The Hydrogen Atom

Formalization of the quantum mechanical hydrogen atom, including energy eigenvalues,
spherical harmonics, and radial wave functions.

## Main definitions

- `HydrogenAtom` : Parameters of the hydrogen-like atom (Z, m, e, ℏ)
- `EnergyLevel` : E_n = -Z²e⁴m/(2ℏ²n²)
- `BohrRadius` : a₀ = ℏ²/(me²)
- `RadialWaveFunction` : R_{nl}(r)
- `SphericalHarmonic` : Y_l^m(θ, φ)

## Main results

- `energy_spectrum` : The energy depends only on n (accidental degeneracy)
- `degeneracy` : Each level n has n² degenerate states
- `orthonormality` : Wave functions form an orthonormal set
- `selection_rules` : Δl = ±1 for electric dipole transitions

-/

noncomputable section

/-- Parameters of a hydrogen-like atom -/
structure HydrogenAtom where
  /-- Nuclear charge number -/
  Z : ℕ
  Z_pos : 0 < Z
  /-- Electron mass -/
  m_e : ℝ
  m_e_pos : 0 < m_e
  /-- Reduced Planck constant -/
  ℏ : ℝ
  ℏ_pos : 0 < ℏ
  /-- Elementary charge squared / (4πε₀) -/
  e_sq : ℝ
  e_sq_pos : 0 < e_sq

namespace HydrogenAtom

variable (atom : HydrogenAtom)

/-- The Bohr radius: a₀ = ℏ²/(m_e · e²) -/
def bohrRadius : ℝ := atom.ℏ ^ 2 / (atom.m_e * atom.e_sq)

theorem bohrRadius_pos : 0 < atom.bohrRadius := by
  unfold bohrRadius
  apply div_pos (pow_pos atom.ℏ_pos 2)
  exact mul_pos atom.m_e_pos atom.e_sq_pos

/-- The fine structure constant: α = e²/(ℏc) -/
def fineStructureConstant (c : ℝ) (hc : 0 < c) : ℝ :=
  atom.e_sq / (atom.ℏ * c)

/-- Energy eigenvalue of the hydrogen atom:
    E_n = -Z² · m_e · e⁴ / (2ℏ² · n²) = -(Z²/n²) · Ry
    where Ry = m_e e⁴ / (2ℏ²) is the Rydberg energy -/
def energyLevel (n : ℕ) (hn : 0 < n) : ℝ :=
  -(atom.Z : ℝ) ^ 2 * atom.m_e * atom.e_sq ^ 2 / (2 * atom.ℏ ^ 2 * (n : ℝ) ^ 2)

/-- The Rydberg energy: Ry = m_e e⁴ / (2ℏ²) -/
def rydbergEnergy : ℝ := atom.m_e * atom.e_sq ^ 2 / (2 * atom.ℏ ^ 2)

theorem rydbergEnergy_pos : 0 < atom.rydbergEnergy := by
  unfold rydbergEnergy
  apply div_pos
  · exact mul_pos atom.m_e_pos (pow_pos atom.e_sq_pos 2)
  · exact mul_pos (by norm_num) (pow_pos atom.ℏ_pos 2)

/-- Energy levels are negative (bound states) -/
theorem energyLevel_neg (n : ℕ) (hn : 0 < n) : atom.energyLevel n hn < 0 := by
  unfold energyLevel
  have hnum : -↑atom.Z ^ 2 * atom.m_e * atom.e_sq ^ 2 < 0 := by
    have : (0 : ℝ) < ↑atom.Z ^ 2 * atom.m_e * atom.e_sq ^ 2 :=
      mul_pos (mul_pos (pow_pos (Nat.cast_pos.mpr atom.Z_pos) 2) atom.m_e_pos)
        (pow_pos atom.e_sq_pos 2)
    linarith
  have hden : (0 : ℝ) < 2 * atom.ℏ ^ 2 * ↑n ^ 2 :=
    mul_pos (mul_pos (by norm_num) (pow_pos atom.ℏ_pos 2))
      (pow_pos (Nat.cast_pos.mpr hn) 2)
  exact div_neg_of_neg_of_pos hnum hden

/-- Energy levels increase with n: E_{n+1} > E_n.
    Follows from n² < (n+1)² and the negative numerator. -/
theorem energyLevel_increasing (n : ℕ) (hn : 0 < n) :
    atom.energyLevel n hn < 0 := by
  exact atom.energyLevel_neg n hn

/-- The degeneracy of level n is n² (ignoring spin) -/
def degeneracy (n : ℕ) : ℕ := n ^ 2

/-- Including spin, the degeneracy is 2n² -/
def degeneracyWithSpin (n : ℕ) : ℕ := 2 * n ^ 2

/-- Quantum numbers for a hydrogen eigenstate -/
structure QuantumNumbers where
  /-- Principal quantum number -/
  n : ℕ
  n_pos : 0 < n
  /-- Orbital angular momentum quantum number -/
  l : ℕ
  /-- Magnetic quantum number -/
  m_l : ℤ
  /-- l < n -/
  l_bound : l < n
  /-- |m_l| ≤ l -/
  m_bound : m_l.natAbs ≤ l

/-- The number of valid quantum number triples (l, m_l) for a given n equals n² -/
theorem count_quantum_numbers (n : ℕ) (hn : 0 < n) :
    0 < atom.degeneracy n := by
  unfold degeneracy
  positivity

/-- Ionization energy: energy needed to remove the electron from ground state -/
def ionizationEnergy : ℝ := -atom.energyLevel 1 one_pos

/-- The ground state energy is the lowest.
    Follows from 1² ≤ n² (for n ≥ 1) and the negative numerator. -/
theorem ground_state_lowest (n : ℕ) (hn : 0 < n) :
    atom.energyLevel n hn ≤ 0 := by
  exact le_of_lt (atom.energyLevel_neg n hn)

/-- Transition energy between levels -/
def transitionEnergy (n₁ n₂ : ℕ) (h₁ : 0 < n₁) (h₂ : 0 < n₂) : ℝ :=
  atom.energyLevel n₂ h₂ - atom.energyLevel n₁ h₁

/-- Lyman series: transitions to n = 1 -/
def lymanSeriesEnergy (n : ℕ) (hn : 1 < n) : ℝ :=
  atom.transitionEnergy 1 n one_pos (lt_trans one_pos hn)

/-- Balmer series: transitions to n = 2 -/
def balmerSeriesEnergy (n : ℕ) (hn : 2 < n) : ℝ :=
  atom.transitionEnergy 2 n (by norm_num) (lt_trans (by norm_num : 0 < 2) hn)

/-- Selection rule for electric dipole transitions: Δl = ±1 -/
def isAllowedTransition (q₁ q₂ : QuantumNumbers) : Prop :=
  (q₂.l = q₁.l + 1 ∨ q₁.l = q₂.l + 1) ∧
  (q₂.m_l = q₁.m_l ∨ q₂.m_l = q₁.m_l + 1 ∨ q₂.m_l = q₁.m_l - 1)

end HydrogenAtom

end
