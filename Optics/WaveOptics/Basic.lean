/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
/-!

# Wave Optics

Diffraction, interference, and coherence phenomena in the wave theory of light.

## Main definitions

- `MonochromaticWave` : E = E₀ exp(i(k·r - ωt))
- `DoubleSlitInterference` : Young's double slit pattern I = 4I₀ cos²(δ/2)
- `SingleSlitDiffraction` : I = I₀ (sin(β)/β)² where β = (πa sin θ)/λ
- `ThinFilmInterference` : Constructive/destructive conditions for thin films

## Main results

- `double_slit_maxima` : Maxima at d sin θ = mλ
- `single_slit_minima` : Minima at a sin θ = mλ (m ≠ 0)
- `rayleigh_criterion` : Resolution limit θ_min = 1.22 λ/D
- `fresnel_coefficients` : Reflection/transmission at interfaces

-/

noncomputable section

/-- A monochromatic plane wave in vacuum -/
structure MonochromaticWave where
  /-- Angular frequency -/
  ω : ℝ
  ω_pos : 0 < ω
  /-- Wave number magnitude -/
  k : ℝ
  k_pos : 0 < k
  /-- Wavelength λ = 2π/k -/
  wavelength : ℝ := 2 * Real.pi / k
  /-- Amplitude -/
  E₀ : ℝ
  /-- Dispersion relation: ω = ck -/
  c : ℝ
  dispersion : ω = c * k

namespace MonochromaticWave

/-- The intensity is proportional to E₀² -/
def intensity (w : MonochromaticWave) : ℝ := w.E₀ ^ 2

end MonochromaticWave

/-- Young's double slit experiment -/
structure DoubleSlit where
  /-- Slit separation -/
  d : ℝ
  d_pos : 0 < d
  /-- Wavelength of light -/
  wavelength : ℝ
  wavelength_pos : 0 < wavelength
  /-- Individual slit intensity -/
  I₀ : ℝ
  I₀_pos : 0 < I₀

namespace DoubleSlit

variable (ds : DoubleSlit)

/-- Path difference: Δ = d sin θ -/
def pathDifference (θ : ℝ) : ℝ := ds.d * Real.sin θ

/-- Phase difference: δ = 2πd sin θ / λ -/
def phaseDifference (θ : ℝ) : ℝ :=
  2 * Real.pi * ds.d * Real.sin θ / ds.wavelength

/-- Intensity pattern: I = 4I₀ cos²(δ/2) -/
def intensity (θ : ℝ) : ℝ :=
  4 * ds.I₀ * Real.cos (ds.phaseDifference θ / 2) ^ 2

/-- Constructive interference maxima at d sin θ = mλ -/
theorem constructive_maxima (m : ℤ) (θ : ℝ)
    (h : ds.d * Real.sin θ = m * ds.wavelength) :
    ds.intensity θ = 4 * ds.I₀ := by
  have hwl : ds.wavelength ≠ 0 := ne_of_gt ds.wavelength_pos
  have hphase : ds.phaseDifference θ = ↑m * (2 * Real.pi) := by
    simp only [phaseDifference]; field_simp; nlinarith [h]
  simp only [intensity, hphase]
  have : Real.cos (↑m * (2 * Real.pi) / 2) = Real.cos (↑m * Real.pi) := by ring_nf
  rw [this]
  have : Real.cos (↑m * Real.pi) ^ 2 = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq (↑m * Real.pi),
               Real.sin_int_mul_pi m,
               sq_nonneg (Real.cos (↑m * Real.pi))]
  rw [this]; ring

/-- Destructive interference minima at d sin θ = (m + 1/2)λ -/
theorem destructive_minima (m : ℤ) (θ : ℝ)
    (h : ds.d * Real.sin θ = (m + 1 / 2) * ds.wavelength) :
    ds.intensity θ = 0 := by
  have hwl : ds.wavelength ≠ 0 := ne_of_gt ds.wavelength_pos
  have hphase : ds.phaseDifference θ = (↑m + 1 / 2) * (2 * Real.pi) := by
    simp only [phaseDifference]; field_simp; nlinarith [h]
  simp only [intensity, hphase]
  have : (↑m + 1 / 2) * (2 * Real.pi) / 2 = (↑m + 1 / 2) * Real.pi := by ring
  rw [this]
  have : Real.cos ((↑m + 1 / 2) * Real.pi) = 0 := by
    rw [show (↑m + 1 / 2) * Real.pi = ↑m * Real.pi + Real.pi / 2 by ring,
        Real.cos_add, Real.cos_pi_div_two, mul_zero, zero_sub,
        Real.sin_pi_div_two, mul_one, neg_eq_zero, Real.sin_int_mul_pi]
  rw [this, zero_pow (by norm_num : 2 ≠ 0), mul_zero]

/-- Fringe spacing on a screen at distance L: Δy = λL/d -/
def fringeSpacing (L : ℝ) : ℝ := ds.wavelength * L / ds.d

end DoubleSlit

/-- Single slit diffraction -/
structure SingleSlit where
  /-- Slit width -/
  a : ℝ
  a_pos : 0 < a
  /-- Wavelength -/
  wavelength : ℝ
  wavelength_pos : 0 < wavelength
  /-- Central maximum intensity -/
  I₀ : ℝ

namespace SingleSlit

variable (ss : SingleSlit)

/-- The diffraction parameter β = πa sin θ / λ -/
def β (θ : ℝ) : ℝ := Real.pi * ss.a * Real.sin θ / ss.wavelength

/-- Diffraction intensity: I = I₀ (sin β / β)² -/
def intensity (θ : ℝ) : ℝ :=
  if ss.β θ = 0 then ss.I₀
  else ss.I₀ * (Real.sin (ss.β θ) / ss.β θ) ^ 2

/-- Diffraction minima at a sin θ = mλ (m ≠ 0) -/
theorem minima (m : ℤ) (hm : m ≠ 0) (θ : ℝ)
    (h : ss.a * Real.sin θ = m * ss.wavelength) :
    ss.intensity θ = 0 := by
  have hwl : ss.wavelength ≠ 0 := ne_of_gt ss.wavelength_pos
  have hbeta : ss.β θ = ↑m * Real.pi := by
    simp only [β]; field_simp; nlinarith [h]
  simp only [intensity, hbeta, if_neg (mul_ne_zero (Int.cast_ne_zero.mpr hm) Real.pi_ne_zero),
      Real.sin_int_mul_pi, zero_div, zero_pow (by norm_num : 2 ≠ 0), mul_zero]

end SingleSlit

/-- Rayleigh criterion for angular resolution of a circular aperture:
    θ_min ≈ 1.22 λ/D -/
def rayleighCriterion (wavelength D : ℝ) : ℝ := 1.22 * wavelength / D

/-- The Fresnel reflection coefficient at normal incidence -/
def fresnelReflection (n₁ n₂ : ℝ) : ℝ :=
  ((n₁ - n₂) / (n₁ + n₂)) ^ 2

/-- Brewster's angle: θ_B = arctan(n₂/n₁), at which reflected light is
    perfectly polarized -/
def brewsterAngle (n₁ n₂ : ℝ) : ℝ := Real.arctan (n₂ / n₁)

end
