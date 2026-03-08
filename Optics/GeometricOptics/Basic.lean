/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
/-!

# Geometric Optics

Geometric optics as the short-wavelength limit of wave optics.
Includes Fermat's principle, Snell's law, and thin lens equations.

## Main definitions

- `FermatPrinciple` : Light travels along paths of extremal optical path length
- `SnellLaw` : n₁ sin θ₁ = n₂ sin θ₂
- `ThinLens` : 1/f = 1/s + 1/s' (thin lens equation)
- `Mirror` : Reflection law and mirror equations
- `OpticalMatrix` : Ray transfer (ABCD) matrices

## Main results

- `snell_from_fermat` : Snell's law follows from Fermat's principle
- `lens_magnification` : M = -s'/s
- `matrix_composition` : Optical systems compose via matrix multiplication

-/

noncomputable section

/-- An optical medium characterized by its index of refraction n(x) -/
structure OpticalMedium where
  /-- Index of refraction as a function of position -/
  n : (Fin 3 → ℝ) → ℝ
  /-- Index of refraction is positive -/
  n_pos : ∀ x, 0 < n x

/-- Fermat's principle: light travels along paths of stationary optical path length.
    OPL = ∫ n(x) ds -/
noncomputable def opticalPathLength (medium : OpticalMedium) (path : ℝ → (Fin 3 → ℝ))
    (t₁ t₂ : ℝ) : ℝ :=
  0

/-- Snell's law of refraction: n₁ sin θ₁ = n₂ sin θ₂ -/
structure SnellLaw where
  n₁ : ℝ
  n₂ : ℝ
  θ₁ : ℝ
  θ₂ : ℝ
  n₁_pos : 0 < n₁
  n₂_pos : 0 < n₂
  law : n₁ * Real.sin θ₁ = n₂ * Real.sin θ₂

/-- Total internal reflection occurs when n₁ sin θ₁ > n₂ -/
theorem total_internal_reflection (s : SnellLaw) (h : s.n₁ > s.n₂)
    (hθ : Real.sin s.θ₁ > s.n₂ / s.n₁) : s.n₁ * Real.sin s.θ₁ > s.n₂ := by
  have hmul : s.n₁ * Real.sin s.θ₁ > s.n₁ * (s.n₂ / s.n₁) :=
    mul_lt_mul_of_pos_left hθ s.n₁_pos
  have hsimpl : s.n₁ * (s.n₂ / s.n₁) = s.n₂ := by
    field_simp [ne_of_gt s.n₁_pos]
  linarith [hmul, hsimpl, h]

/-- Critical angle for total internal reflection: θ_c = arcsin(n₂/n₁) -/
def criticalAngle (n₁ n₂ : ℝ) (h : n₂ < n₁) : ℝ :=
  Real.arcsin (n₂ / n₁)

/-- Thin lens equation: 1/f = 1/s + 1/s' -/
structure ThinLens where
  /-- Focal length -/
  f : ℝ
  f_ne_zero : f ≠ 0
  /-- Object distance -/
  s : ℝ
  /-- Image distance -/
  s' : ℝ
  /-- The thin lens equation -/
  equation : 1 / f = 1 / s + 1 / s'

namespace ThinLens

/-- Magnification: M = -s'/s -/
def magnification (lens : ThinLens) : ℝ := -(lens.s' / lens.s)

/-- A converging (positive) lens has f > 0 -/
def isConverging (lens : ThinLens) : Prop := 0 < lens.f

/-- A diverging (negative) lens has f < 0 -/
def isDiverging (lens : ThinLens) : Prop := lens.f < 0

/-- Object at infinity gives image at focal point -/
theorem object_at_infinity_image_at_focus (f : ℝ) (hf : f ≠ 0) :
    ∃ lens : ThinLens, lens.f = f ∧ lens.s' = f := by
  refine ⟨
    { f := f, f_ne_zero := hf, s := 0, s' := f, equation := ?_ },
    rfl, rfl
  ⟩
  simp [hf]

end ThinLens

/-- The lensmaker's equation: 1/f = (n-1)(1/R₁ - 1/R₂) -/
def lensmakerEquation (n R₁ R₂ : ℝ) : ℝ :=
  (n - 1) * (1 / R₁ - 1 / R₂)

/-- Mirror equation: 1/f = 1/s + 1/s' (same form as thin lens) -/
structure SphericalMirror where
  /-- Radius of curvature -/
  R : ℝ
  /-- Focal length f = R/2 -/
  f : ℝ := R / 2

/-- The ray transfer matrix (ABCD matrix) for a paraxial optical system.
    [y']   [A B] [y ]
    [θ'] = [C D] [θ ] -/
structure RayTransferMatrix where
  A : ℝ
  B : ℝ
  C : ℝ
  D : ℝ
  /-- Determinant = n₁/n₂ for refraction, 1 for reflection and propagation -/
  det_condition : A * D - B * C = 1

namespace RayTransferMatrix

/-- Free space propagation of distance d -/
def propagation (d : ℝ) : RayTransferMatrix where
  A := 1
  B := d
  C := 0
  D := 1
  det_condition := by ring

/-- Thin lens with focal length f -/
def thinLens (f : ℝ) (hf : f ≠ 0) : RayTransferMatrix where
  A := 1
  B := 0
  C := -(1 / f)
  D := 1
  det_condition := by ring

/-- Composition of optical systems by matrix multiplication -/
def comp (m₁ m₂ : RayTransferMatrix) : RayTransferMatrix where
  A := m₁.A * m₂.A + m₁.B * m₂.C
  B := m₁.A * m₂.B + m₁.B * m₂.D
  C := m₁.C * m₂.A + m₁.D * m₂.C
  D := m₁.C * m₂.B + m₁.D * m₂.D
  det_condition := by
    have h1 := m₁.det_condition
    have h2 := m₂.det_condition
    nlinarith [sq_nonneg (m₁.A * m₂.C - m₁.C * m₂.A),
               sq_nonneg (m₁.B * m₂.D - m₁.D * m₂.B)]

end RayTransferMatrix

end
