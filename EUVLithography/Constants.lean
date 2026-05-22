/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!

# EUV Lithography: Physical Constants

Small positive-constant wrappers and light/quantum-energy identities used by
the EUV source and plasma calculations.  The positive-wrapper style follows the
useful constants pattern in `leanprover-community/physlib` for `ℏ`, `kB`,
`SpeedOfLight`, `electronVolt`, and `standardAtmosphere`, while keeping this
project independent of the full external library.

-/

noncomputable section

open Real

namespace EUVConstants

/-- A positive real-valued physical constant used for table-level constants. -/
structure PositiveConstant where
  /-- Underlying SI value. -/
  val : ℝ
  /-- Positivity of the physical constant. -/
  pos : 0 < val

namespace PositiveConstant

instance : Coe PositiveConstant ℝ := ⟨PositiveConstant.val⟩

@[simp]
theorem val_pos (x : PositiveConstant) : 0 < (x : ℝ) := x.pos

@[simp]
theorem val_nonneg (x : PositiveConstant) : 0 ≤ (x : ℝ) := le_of_lt x.pos

@[simp]
theorem val_ne_zero (x : PositiveConstant) : (x : ℝ) ≠ 0 := ne_of_gt x.pos

end PositiveConstant

/-- Planck constant `h`, SI value in J s. -/
def planckConstantSI : PositiveConstant := ⟨6.62607015e-34, by norm_num⟩

/-- Elementary charge `e`, SI value in coulombs. -/
def elementaryChargeSI : PositiveConstant := ⟨1.602176634e-19, by norm_num⟩

/-- Electron rest mass `m_e`, SI value in kg. -/
def electronMassSI : PositiveConstant := ⟨9.1093837015e-31, by norm_num⟩

/-- Approximate mass of the 118Sn isotope used in the report, SI value in kg. -/
def tin118MassSI : PositiveConstant := ⟨1.975e-25, by norm_num⟩

/-- Vacuum permittivity `ε₀`, SI value in F/m. -/
def vacuumPermittivitySI : PositiveConstant := ⟨8.8541878128e-12, by norm_num⟩

/-- Vacuum permeability `μ₀`, SI value in H/m. -/
def vacuumPermeabilitySI : PositiveConstant := ⟨1.25663706212e-6, by norm_num⟩

/-- Avogadro number `N_A`, SI value in mol⁻¹. -/
def avogadroNumberSI : PositiveConstant := ⟨6.02214076e23, by norm_num⟩

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

/-- Electron volt as a positive number of joules.
    This mirrors physlib's `Units.WithDim.Energy.electronVolt` SI value. -/
structure ElectronVolt where
  /-- Underlying value of one eV in joules. -/
  val : ℝ
  /-- Positivity of the eV-to-joule conversion. -/
  pos : 0 < val

namespace ElectronVolt

instance : Coe ElectronVolt ℝ := ⟨ElectronVolt.val⟩

@[simp]
theorem val_pos (eV : ElectronVolt) : 0 < (eV : ℝ) := eV.pos

@[simp]
theorem val_nonneg (eV : ElectronVolt) : 0 ≤ (eV : ℝ) := le_of_lt eV.pos

@[simp]
theorem val_ne_zero (eV : ElectronVolt) : (eV : ℝ) ≠ 0 := ne_of_gt eV.pos

/-- Exact SI value of one electron volt, in joules. -/
def si : ElectronVolt := ⟨1.602176634e-19, by norm_num⟩

end ElectronVolt

/-- Standard atmosphere as a positive pressure in pascals.
    This mirrors physlib's `Units.WithDim.Pressure.standardAtmosphere` SI value. -/
structure StandardAtmosphere where
  /-- Underlying value of one atmosphere in pascals. -/
  val : ℝ
  /-- Positivity of atmospheric pressure. -/
  pos : 0 < val

namespace StandardAtmosphere

instance : Coe StandardAtmosphere ℝ := ⟨StandardAtmosphere.val⟩

@[simp]
theorem val_pos (atm : StandardAtmosphere) : 0 < (atm : ℝ) := atm.pos

@[simp]
theorem val_nonneg (atm : StandardAtmosphere) : 0 ≤ (atm : ℝ) := le_of_lt atm.pos

@[simp]
theorem val_ne_zero (atm : StandardAtmosphere) : (atm : ℝ) ≠ 0 := ne_of_gt atm.pos

/-- Exact SI value of a standard atmosphere, in Pa. -/
def si : StandardAtmosphere := ⟨101325, by norm_num⟩

end StandardAtmosphere

/-- Convert an energy in electron volts to joules. -/
def eVToJoule (eV : ElectronVolt) (energy_eV : ℝ) : ℝ :=
  energy_eV * (eV : ℝ)

theorem eVToJoule_pos (eV : ElectronVolt) {energy_eV : ℝ} (hE : 0 < energy_eV) :
    0 < eVToJoule eV energy_eV := by
  unfold eVToJoule
  exact mul_pos hE eV.pos

/-- Convert an energy in joules to electron volts. -/
def jouleToEV (eV : ElectronVolt) (energy_J : ℝ) : ℝ :=
  energy_J / (eV : ℝ)

theorem jouleToEV_pos (eV : ElectronVolt) {energy_J : ℝ} (hE : 0 < energy_J) :
    0 < jouleToEV eV energy_J := by
  unfold jouleToEV
  exact div_pos hE eV.pos

theorem jouleToEV_eVToJoule (eV : ElectronVolt) (energy_eV : ℝ) :
    jouleToEV eV (eVToJoule eV energy_eV) = energy_eV := by
  unfold jouleToEV eVToJoule
  field_simp [eV.val_ne_zero]

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

/-- Angular frequency decreases as wavelength increases. -/
theorem angularFrequency_decreases_with_wavelength (c : SpeedOfLight)
    {lambda₁ lambda₂ : ℝ} (hlambda₁ : 0 < lambda₁) (hlambda : lambda₁ < lambda₂) :
    angularFrequencyFromWavelength c lambda₂ <
      angularFrequencyFromWavelength c lambda₁ := by
  unfold angularFrequencyFromWavelength
  exact div_lt_div_of_pos_left (mul_pos (mul_pos two_pos pi_pos) c.pos) hlambda₁ hlambda

/-- Photon energy `E = hc/λ` decreases as wavelength increases. -/
theorem photonEnergy_decreases_with_wavelength (hbar : ReducedPlanckConstant)
    (c : SpeedOfLight) {lambda₁ lambda₂ : ℝ}
    (hlambda₁ : 0 < lambda₁) (hlambda : lambda₁ < lambda₂) :
    planckFromReduced hbar * (c : ℝ) / lambda₂ <
      planckFromReduced hbar * (c : ℝ) / lambda₁ := by
  exact div_lt_div_of_pos_left (mul_pos (planckFromReduced_pos hbar) c.pos) hlambda₁ hlambda

/-- Photon energy using direct Planck constant: `E = hc/λ`. -/
def photonEnergyFromWavelength (h c : PositiveConstant) (lambda : ℝ) : ℝ :=
  (h : ℝ) * (c : ℝ) / lambda

theorem photonEnergyFromWavelength_pos (h c : PositiveConstant) {lambda : ℝ}
    (hlambda : 0 < lambda) :
    0 < photonEnergyFromWavelength h c lambda := by
  unfold photonEnergyFromWavelength
  exact div_pos (mul_pos h.pos c.pos) hlambda

theorem photonEnergyFromWavelength_decreases_with_wavelength (h c : PositiveConstant)
    {lambda₁ lambda₂ : ℝ} (hlambda₁ : 0 < lambda₁) (hlambda : lambda₁ < lambda₂) :
    photonEnergyFromWavelength h c lambda₂ <
      photonEnergyFromWavelength h c lambda₁ := by
  unfold photonEnergyFromWavelength
  exact div_lt_div_of_pos_left (mul_pos h.pos c.pos) hlambda₁ hlambda

/-- The direct-`h` photon-energy formula agrees with the reduced-Planck formula when `h = 2πℏ`. -/
theorem photonEnergyFromWavelength_eq_reduced
    (h : PositiveConstant) (hbar : ReducedPlanckConstant) (c : SpeedOfLight) {lambda : ℝ}
    (hh : (h : ℝ) = planckFromReduced hbar) :
    photonEnergyFromWavelength h ⟨(c : ℝ), c.pos⟩ lambda =
      planckFromReduced hbar * (c : ℝ) / lambda := by
  unfold photonEnergyFromWavelength
  rw [hh]

end EUVConstants
