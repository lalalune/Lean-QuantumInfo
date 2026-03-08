/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Electromagnetic Wave Equation

Plane wave solutions of the electromagnetic wave equation, including
polarization states via Jones vectors and Stokes parameters.

## Main definitions

* `PlaneWave1D`, `PlaneWave3D` : monochromatic plane wave solutions
* `JonesVector` : polarization described by complex amplitudes
* `StokesParameters` : characterizing partially polarized light

## References

* J.D. Jackson, *Classical Electrodynamics*, Ch. 7
* D.J. Griffiths, *Introduction to Electrodynamics*, Ch. 9
-/

noncomputable section

open Real

namespace Electromagnetism

/-! ## Wave Equation -/

/-- Parameters for electromagnetic wave propagation in a medium. -/
structure MediumParameters where
  c : ℝ
  ε : ℝ
  μ : ℝ
  c_pos : 0 < c
  ε_pos : 0 < ε
  μ_pos : 0 < μ
  speed_relation : c ^ 2 = 1 / (ε * μ)

/-- The 1D wave equation: `∂²f/∂x² = (1/c²) ∂²f/∂t²`. -/
structure WaveEquation1D where
  f : ℝ → ℝ → ℝ
  c : ℝ
  c_pos : 0 < c
  wave_eq : ∀ x t,
    deriv (fun x' => deriv (fun x'' => f x'' t) x') x =
    (1 / c ^ 2) * deriv (fun t' => deriv (fun t'' => f x t'') t') t

/-! ## Plane Wave Solutions -/

/-- A monochromatic plane wave in 1D: `f(x,t) = A cos(kx - ωt + φ)`.
    This is a data carrier for the wave parameters. The proof that `waveFunction`
    satisfies `WaveEquation1D` when `ω = ck` is captured algebraically by
    `dispersion_algebraic` (showing `k² = ω²/c²`). A full derivative-level
    proof would additionally need `HasDerivAt` for composed `cos`. -/
structure PlaneWave1D where
  amplitude : ℝ
  waveNumber : ℝ
  angularFrequency : ℝ
  phase : ℝ
  amplitude_pos : 0 < amplitude

namespace PlaneWave1D

variable (pw : PlaneWave1D)

def waveFunction (x t : ℝ) : ℝ :=
  pw.amplitude * cos (pw.waveNumber * x - pw.angularFrequency * t + pw.phase)

def wavelength (hk : pw.waveNumber ≠ 0) : ℝ := 2 * π / |pw.waveNumber|
def period (hω : pw.angularFrequency ≠ 0) : ℝ := 2 * π / |pw.angularFrequency|
def frequency : ℝ := |pw.angularFrequency| / (2 * π)

def phaseVelocity (hk : pw.waveNumber ≠ 0) : ℝ :=
  pw.angularFrequency / pw.waveNumber

/-- The vacuum dispersion relation: `ω = ck`. -/
def satisfiesVacuumDispersion (c : ℝ) : Prop :=
  pw.angularFrequency = c * pw.waveNumber

theorem phaseVelocity_eq_c (c : ℝ) (hk : pw.waveNumber ≠ 0)
    (hdisp : pw.satisfiesVacuumDispersion c) :
    pw.phaseVelocity hk = c := by
  unfold phaseVelocity
  have h : pw.angularFrequency = c * pw.waveNumber := hdisp
  rw [h]; field_simp

/-- When ω = ck, the factors on both sides of the wave equation agree:
    `k² = ω²/c²`. This is the algebraic content of the dispersion relation. -/
theorem dispersion_algebraic (c : ℝ) (hc : c ≠ 0)
    (hdisp : pw.satisfiesVacuumDispersion c) :
    pw.waveNumber ^ 2 = pw.angularFrequency ^ 2 / c ^ 2 := by
  rw [hdisp]; field_simp

end PlaneWave1D

/-! ## 3D Plane Waves -/

/-- A monochromatic plane wave in 3D with transversality constraint. -/
structure PlaneWave3D where
  E₀ : Fin 3 → ℝ
  k : Fin 3 → ℝ
  ω : ℝ
  transverse : ∑ i, E₀ i * k i = 0

namespace PlaneWave3D

variable (pw : PlaneWave3D)

def electricField (x : Fin 3 → ℝ) (t : ℝ) : Fin 3 → ℝ :=
  fun i => pw.E₀ i * cos (∑ j, pw.k j * x j - pw.ω * t)

def kMagnitude : ℝ := Real.sqrt (∑ i, pw.k i ^ 2)

def vacuumDispersion (c : ℝ) : Prop := pw.ω ^ 2 = c ^ 2 * ∑ i, pw.k i ^ 2

def intensity (c ε₀ : ℝ) : ℝ := c * ε₀ / 2 * ∑ i, pw.E₀ i ^ 2

theorem intensity_nonneg (c ε₀ : ℝ) (hc : 0 < c) (hε₀ : 0 < ε₀) :
    0 ≤ pw.intensity c ε₀ := by
  unfold intensity
  apply mul_nonneg
  · exact div_nonneg (mul_nonneg (le_of_lt hc) (le_of_lt hε₀)) (by norm_num)
  · exact Finset.sum_nonneg fun i _ => sq_nonneg _

end PlaneWave3D

/-! ## Polarization (Jones Vectors) -/

/-- A polarization state described by Jones vector components (complex amplitudes). -/
structure JonesVector where
  Ex : ℂ
  Ey : ℂ

namespace JonesVector

def horizontal : JonesVector := ⟨1, 0⟩
def vertical : JonesVector := ⟨0, 1⟩
def rightCircular : JonesVector := ⟨1 / Real.sqrt 2, -Complex.I / Real.sqrt 2⟩
def leftCircular : JonesVector := ⟨1 / Real.sqrt 2, Complex.I / Real.sqrt 2⟩

def intensity (j : JonesVector) : ℝ := Complex.normSq j.Ex + Complex.normSq j.Ey

@[simp]
theorem horizontal_intensity : horizontal.intensity = 1 := by
  simp [horizontal, intensity, Complex.normSq]

@[simp]
theorem vertical_intensity : vertical.intensity = 1 := by
  simp [vertical, intensity, Complex.normSq]

end JonesVector

/-! ## Stokes Parameters -/

/-- Stokes parameters characterizing (partially) polarized light. -/
structure StokesParameters where
  S₀ : ℝ
  S₁ : ℝ
  S₂ : ℝ
  S₃ : ℝ
  S₀_nonneg : 0 ≤ S₀
  physical : S₁ ^ 2 + S₂ ^ 2 + S₃ ^ 2 ≤ S₀ ^ 2

namespace StokesParameters

variable (sp : StokesParameters)

/-- Degree of polarization `p = √(S₁² + S₂² + S₃²) / S₀`. -/
def degreeOfPolarization (h : sp.S₀ ≠ 0) : ℝ :=
  Real.sqrt (sp.S₁ ^ 2 + sp.S₂ ^ 2 + sp.S₃ ^ 2) / sp.S₀

theorem degreeOfPolarization_bounded (h : 0 < sp.S₀) :
    0 ≤ sp.degreeOfPolarization (ne_of_gt h) ∧
    sp.degreeOfPolarization (ne_of_gt h) ≤ 1 := by
  refine ⟨div_nonneg (Real.sqrt_nonneg _) (le_of_lt h), ?_⟩
  rw [degreeOfPolarization, div_le_one h]
  calc Real.sqrt (sp.S₁ ^ 2 + sp.S₂ ^ 2 + sp.S₃ ^ 2)
      ≤ Real.sqrt (sp.S₀ ^ 2) := Real.sqrt_le_sqrt (by linarith [sp.physical])
    _ = |sp.S₀| := Real.sqrt_sq_eq_abs sp.S₀
    _ = sp.S₀ := abs_of_nonneg (le_of_lt h)

def isFullyPolarized (h : sp.S₀ ≠ 0) : Prop := sp.degreeOfPolarization h = 1
def isUnpolarized : Prop := sp.S₁ = 0 ∧ sp.S₂ = 0 ∧ sp.S₃ = 0

end StokesParameters

/-! ## Verification Tests -/

section Tests

/-- The wavefunction at t=0, x=0 with zero phase equals the amplitude. -/
theorem PlaneWave1D.waveFunction_origin (pw : PlaneWave1D)
    (hφ : pw.phase = 0) :
    pw.waveFunction 0 0 = pw.amplitude := by
  simp [PlaneWave1D.waveFunction, hφ]

/-- A static wave (ω = 0) has zero frequency. -/
theorem PlaneWave1D.frequency_zero_omega (pw : PlaneWave1D) (hω : pw.angularFrequency = 0) :
    pw.frequency = 0 := by
  simp [PlaneWave1D.frequency, hω]

/-- Dispersion relation: for c=1 and k=ω, we get k² = ω². -/
example : ∀ (pw : PlaneWave1D),
    pw.satisfiesVacuumDispersion 1 → pw.angularFrequency = pw.waveNumber :=
  fun pw h => by simp [PlaneWave1D.satisfiesVacuumDispersion] at h; linarith

/-- Jones vector horizontal has unit intensity. -/
example : JonesVector.horizontal.intensity = 1 := JonesVector.horizontal_intensity

/-- Jones vector vertical has unit intensity. -/
example : JonesVector.vertical.intensity = 1 := JonesVector.vertical_intensity

/-- Jones vector intensity is non-negative. -/
theorem JonesVector.intensity_nonneg (j : JonesVector) : 0 ≤ j.intensity := by
  unfold intensity
  exact add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

/-- A 3D plane wave with E₀ = 0 has zero intensity. -/
theorem PlaneWave3D.intensity_zero_field (k : Fin 3 → ℝ) (ω c ε₀ : ℝ) :
    (⟨0, k, ω, by simp⟩ : PlaneWave3D).intensity c ε₀ = 0 := by
  simp [PlaneWave3D.intensity]

/-- Unpolarized light has zero degree of polarization. -/
theorem StokesParameters.unpolarized_degree_zero
    (sp : StokesParameters) (h : sp.isUnpolarized) (hS₀ : 0 < sp.S₀) :
    sp.degreeOfPolarization (ne_of_gt hS₀) = 0 := by
  obtain ⟨h1, h2, h3⟩ := h
  simp [degreeOfPolarization, h1, h2, h3]

/-- Stokes parameters: for S₁=S₂=S₃=0, the physical constraint is trivially satisfied. -/
example : (⟨1, 0, 0, 0, zero_le_one, by norm_num⟩ : StokesParameters).isUnpolarized :=
  ⟨rfl, rfl, rfl⟩

end Tests

end Electromagnetism

end
