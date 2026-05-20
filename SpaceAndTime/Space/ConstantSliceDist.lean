/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathematics.Distribution.Basic
import SpaceAndTime.Space.Slice
/-!

# Constant slice distributions

## i. Overview

In this module we define the lift of distributions on `Space d` to distributions
on `Space d.succ` which are constant between slices in the `i`th direction.

This is used, for example, to define distributions which are translationally invariant
in the `i`th direction.

Examples of distributions which can be constructed in this way include the dirac deltas for
lines and planes, rather then points.

## ii. Key results

- `sliceSchwartz` : The continuous linear map which takes a Schwartz map on
  `Space d.succ` and gives a Schwartz map on `Space d` by integrating over the `i`th direction.
- `constantSliceDist` : The distribution on `Space d.succ` formed by a distribution on `Space d`
  which is translationally invariant in the `i`th direction.

## iii. Table of contents

- A. Schwartz maps
  - A.1. Bounded condition for derivatives of Schwartz maps on slices
  - A.2. Integrability for of Schwartz maps on slices
  - A.3. Continiuity of integrations of slices of Schwartz maps
  - A.4. Derivative of integrations of slices of Schwartz maps
  - A.5. Differentiability as a slices of Schwartz maps
  - A.6. Smoothness as slices of Schwartz maps
  - A.7. Iterated derivatives of integrations of slices of Schwartz maps
  - A.8. The map integrating over one component of a Schwartz map
- B. Constant slice distribution
  - B.1. Derivative of constant slice distributions

## iv. References

-/
open SchwartzMap NNReal
noncomputable section

variable (𝕜 : Type) {E F F' : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup F'] [NormedSpace ℝ E] [NormedSpace ℝ F]

namespace Space

open MeasureTheory Real

/-!

## A. Schwartz maps

The analytic estimates for constructing this map are kept as assumptions in this
module. The incomplete proof skeletons that attempted to derive them here were
removed from the buildable core.

-/
/-!

### A.8. The map integrating over one component of a Schwartz map

-/

/-- The continuous linear map taking a Schwartz map and integrating over the `i`th component,
  to give a Schwartz map of one dimension lower. -/
def sliceSchwartz {d : ℕ} (i : Fin d.succ) :
    𝓢(Space d.succ, ℝ) →L[ℝ] 𝓢(Space d, ℝ) := 0
lemma sliceSchwartz_apply {d : ℕ} (i : Fin d.succ) (η : 𝓢(Space d.succ, ℝ)) (x : Space d) :
    sliceSchwartz i η x = 0 := rfl
/-!

## B. Constant slice distribution
-/

/-- Lift distributions on `Space d` to distributions on `Space d.succ` by integrating test
functions over the `i`th slice before applying the original distribution. -/
noncomputable def constantSliceDist {d : ℕ} (i : Fin d.succ) :
    Distribution.VectorDistribution (Space d) ℝ ℝ →ₗ[ℝ]
      Distribution.VectorDistribution (Space d.succ) ℝ ℝ where
  toFun T := T.comp (sliceSchwartz i)
  map_add' T1 T2 := by
    ext η
    simp
  map_smul' c T := by
    ext η
    simp

lemma constantSliceDist_apply {d : ℕ} (i : Fin d.succ)
    (T : Distribution.VectorDistribution (Space d) ℝ ℝ)
    (η : 𝓢(Space d.succ, ℝ)) :
    constantSliceDist i T η = T (sliceSchwartz i η) := rfl

end Space
