/-
Copyright (c) 2026. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg, Shaw Walters
-/
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Determinant

/-!
# Spacetime and Lorentz Group

This module provides the foundational spacetime structures for continuum QFT:
- Minkowski spacetime ℝ^{1,d-1}
- Minkowski metric η
- Lorentz group O(1,d-1) and proper orthochronous subgroup
- Poincaré group = Lorentz ⋉ Translations
- Test function space (abstract Schwartz-like space)
-/

namespace QFT

/-- Minkowski spacetime as ℝ^d with d = spacetime dimension (default 4). -/
def MinkowskiSpace (d : ℕ := 4) := Fin d → ℝ

instance (d : ℕ) : AddCommGroup (MinkowskiSpace d) :=
  inferInstanceAs (AddCommGroup (Fin d → ℝ))

noncomputable instance (d : ℕ) : Module ℝ (MinkowskiSpace d) :=
  inferInstanceAs (Module ℝ (Fin d → ℝ))

/-- The Minkowski metric signature (+,-,-,...,-).
    η(x,y) = x₀y₀ - x₁y₁ - ... - x_{d-1}y_{d-1}. -/
noncomputable def minkowskiMetric (d : ℕ) [NeZero d] (x y : MinkowskiSpace d) : ℝ :=
  x 0 * y 0 - Finset.univ.sum (fun i : Fin (d - 1) => x ⟨i.val + 1, by omega⟩ * y ⟨i.val + 1, by omega⟩)

/-- Minkowski norm squared: η(x,x). -/
noncomputable def minkowskiNormSq (d : ℕ) [NeZero d] (x : MinkowskiSpace d) : ℝ :=
  minkowskiMetric d x x

/-- A vector is timelike if η(x,x) > 0. -/
def IsTimelike (d : ℕ) [NeZero d] (x : MinkowskiSpace d) : Prop :=
  minkowskiNormSq d x > 0

/-- A vector is spacelike if η(x,x) < 0. -/
def IsSpacelike (d : ℕ) [NeZero d] (x : MinkowskiSpace d) : Prop :=
  minkowskiNormSq d x < 0

/-- A vector is lightlike (null) if η(x,x) = 0. -/
def IsLightlike (d : ℕ) [NeZero d] (x : MinkowskiSpace d) : Prop :=
  minkowskiNormSq d x = 0

/-- A vector is future-directed if its time component is positive. -/
def IsFutureDirected (d : ℕ) [NeZero d] (x : MinkowskiSpace d) : Prop :=
  x 0 > 0

/-- The forward light cone V₊ = {p : η(p,p) ≥ 0, p⁰ ≥ 0}. -/
def ForwardLightCone (d : ℕ) [NeZero d] : Set (MinkowskiSpace d) :=
  {p | minkowskiNormSq d p ≥ 0 ∧ p 0 ≥ 0}

/-- Two points are spacelike separated if (x-y) is spacelike. -/
def SpacelikeSeparated (d : ℕ) [NeZero d] (x y : MinkowskiSpace d) : Prop :=
  IsSpacelike d (x - y)

/-- A Lorentz transformation is a linear map preserving the Minkowski metric. -/
structure LorentzTransformation (d : ℕ) [NeZero d] where
  toLinearMap : MinkowskiSpace d →ₗ[ℝ] MinkowskiSpace d
  preserves_metric : ∀ x y : MinkowskiSpace d,
    minkowskiMetric d (toLinearMap x) (toLinearMap y) = minkowskiMetric d x y

/-- A Lorentz transformation is proper if det = +1. -/
def LorentzTransformation.IsProper {d : ℕ} [NeZero d] (_Λ : LorentzTransformation d) : Prop :=
  LinearMap.det _Λ.toLinearMap = 1

/-- A Lorentz transformation is orthochronous if it preserves time orientation. -/
def LorentzTransformation.IsOrthochronous {d : ℕ} [NeZero d] (Λ : LorentzTransformation d) : Prop :=
  ∀ x : MinkowskiSpace d, IsFutureDirected d x → IsFutureDirected d (Λ.toLinearMap x)

/-- The proper orthochronous Lorentz group SO⁺(1,d-1). -/
structure ProperLorentz (d : ℕ) [NeZero d] extends LorentzTransformation d where
  proper : toLorentzTransformation.IsProper
  orthochronous : toLorentzTransformation.IsOrthochronous

/-- The Poincaré group = Lorentz ⋉ Translations.
    An element (Λ, a) acts as x ↦ Λx + a. -/
structure PoincareTransformation (d : ℕ) [NeZero d] where
  lorentz : LorentzTransformation d
  translation : MinkowskiSpace d

/-- Action of a Poincaré transformation on a spacetime point. -/
def PoincareTransformation.act {d : ℕ} [NeZero d] (g : PoincareTransformation d) (x : MinkowskiSpace d) :
    MinkowskiSpace d :=
  g.lorentz.toLinearMap x + g.translation

/-- Abstract test function space for operator-valued distributions.
    In physics this is the Schwartz space S(ℝ^d). -/
structure TestFunctionSpace (d : ℕ) where
  carrier : Type
  instAddCommGroup : AddCommGroup carrier
  instModule : Module ℝ carrier
  instTopologicalSpace : TopologicalSpace carrier
  /-- The support of every test function is in spacetime -/
  support : carrier → Set (MinkowskiSpace d)

/-- A test function from a given test function space. -/
def TestFunction {d : ℕ} (S : TestFunctionSpace d) := S.carrier

/-- The closed forward light cone as a spectral condition set.
    This is exactly `ForwardLightCone` (both use the non-strict condition η(p,p) ≥ 0). -/
abbrev ClosedForwardLightCone (d : ℕ) [NeZero d] : Set (MinkowskiSpace d) :=
  ForwardLightCone d

/-- Parity transformation: (t, x⃗) ↦ (t, -x⃗). -/
noncomputable def parityTransformation (d : ℕ) [NeZero d] : MinkowskiSpace d → MinkowskiSpace d :=
  fun x => fun (i : Fin d) =>
    if i = 0 then x i else -(x i)

/-- Time reversal transformation: (t, x⃗) ↦ (-t, x⃗). -/
noncomputable def timeReversalTransformation (d : ℕ) [NeZero d] : MinkowskiSpace d → MinkowskiSpace d :=
  fun x => fun (i : Fin d) =>
    if i = 0 then -(x i) else x i

/-! ## Relationship to SpaceAndTime

This module's `MinkowskiSpace d` (total spacetime dimension d) corresponds to
`SpaceAndTime.SpaceTime (d-1)` (spatial dimension d-1). The reindexing is
`Fin d ≃ Fin 1 ⊕ Fin (d-1)` via `finSumFinEquiv`. A formal bridge requires
importing `SpaceAndTime.SpaceTime.Basic` and defining the equivalence. -/
end QFT
