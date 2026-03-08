/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
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

variable
  (h_schwartzMap_slice_bound : ∀ {n m d : ℕ} (i : Fin d.succ),
    ∃ rt, ∀ (η : 𝓢(Space d.succ, ℝ)), ∃ k,
      Integrable (fun x : ℝ => ‖((1 + ‖x‖) ^ rt)⁻¹‖) volume ∧
      (∀ (x : Space d), ∀ r, ‖(slice i).symm (r, x)‖ ^ m *
        ‖iteratedFDeriv ℝ n ⇑η ((slice i).symm (r, x))‖ ≤ k * ‖(1 + ‖r‖) ^ (rt)‖⁻¹)
        ∧ k = (2 ^ (rt + m, n).1 * ((Finset.Iic (rt + m, n)).sup
          fun m => SchwartzMap.seminorm ℝ m.1 m.2) η))
  (h_schwartzMap_mul_iteratedFDeriv_integrable_slice_symm :
    ∀ {d : ℕ} (n m : ℕ) (η : 𝓢(Space d.succ, ℝ)) (x : Space d) (i : Fin d.succ),
      Integrable (fun r => ‖(slice i).symm (r, x)‖ ^ m *
        ‖iteratedFDeriv ℝ n ⇑η ((slice i).symm (r, x))‖) volume)
  (h_schwartzMap_integrable_slice_symm :
    ∀ {d : ℕ} (i : Fin d.succ) (η : 𝓢(Space d.succ, ℝ)) (x : Space d),
      Integrable (fun r => η ((slice i).symm (r, x))) volume)
  (h_schwartzMap_fderiv_integrable_slice_symm :
    ∀ {d : ℕ} (η : 𝓢(Space d.succ, ℝ)) (x : Space d) (i : Fin d.succ),
      Integrable (fun r => fderiv ℝ (fun x => η (((slice i).symm (r, x)))) x) volume)
  (h_schwartzMap_fderiv_left_integrable_slice_symm :
    ∀ {d : ℕ} (η : 𝓢(Space d.succ, ℝ)) (x : Space d) (i : Fin d.succ),
      Integrable (fun r => fderiv ℝ (fun r => η (((slice i).symm (r, x)))) r 1) volume)
  (h_schwartzMap_iteratedFDeriv_norm_slice_symm_integrable :
    ∀ {n d : ℕ} (η : 𝓢(Space d.succ, ℝ)) (x : Space d) (i : Fin d.succ),
      Integrable (fun r => ‖iteratedFDeriv ℝ n ⇑η (((slice i).symm (r, x)))‖) volume)
  (h_schwartzMap_iteratedFDeriv_slice_symm_integrable :
    ∀ {n d : ℕ} (η : 𝓢(Space d.succ, ℝ)) (x : Space d) (i : Fin d.succ),
      Integrable (fun r => iteratedFDeriv ℝ n ⇑η (((slice i).symm (r, x)))) volume)
  (h_continuous_schwartzMap_slice_integral :
    ∀ {d : ℕ} (i : Fin d.succ) (η : 𝓢(Space d.succ, ℝ)),
      Continuous (fun x : Space d => ∫ r : ℝ, η ((slice i).symm (r, x))))
  (h_schwartzMap_slice_integral_hasFDerivAt :
    ∀ {d : ℕ} (η : 𝓢(Space d.succ, ℝ)) (i : Fin d.succ) (x₀ : Space d),
      HasFDerivAt (fun x => ∫ (r : ℝ), η ((slice i).symm (r, x)))
        (∫ (r : ℝ), fderiv ℝ (fun x : Space d => η ((slice i).symm (r, x))) x₀) x₀)
  (h_schwartzMap_slice_integral_contDiff :
    ∀ {d : ℕ} (n : ℕ) (η : 𝓢(Space d.succ, ℝ)) (i : Fin d.succ),
      ContDiff ℝ n (fun x => ∫ (r : ℝ), η ((slice i).symm (r, x))))
  (h_schwartzMap_slice_integral_iteratedFDeriv_apply :
    ∀ {d : ℕ} (n : ℕ) (η : 𝓢(Space d.succ, ℝ)) (i : Fin d.succ),
      ∀ x, ∀ y, iteratedFDeriv ℝ n (fun x => ∫ (r : ℝ), η ((slice i).symm (r, x))) x y =
        ∫ (r : ℝ), (iteratedFDeriv ℝ n η ((slice i).symm (r, x)))
        (fun j => (slice i).symm (0, y j)))
  (h_schwartzMap_slice_integral_iteratedFDeriv :
    ∀ {d : ℕ} (n : ℕ) (η : 𝓢(Space d.succ, ℝ)) (i : Fin d.succ) (x : Space d),
      iteratedFDeriv ℝ n (fun x => ∫ (r : ℝ), η ((slice i).symm (r, x))) x
      = (∫ (r : ℝ), iteratedFDeriv ℝ n η ((slice i).symm (r, x))).compContinuousLinearMap
        (fun _ => (slice i).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.prod (0 : Space d →L[ℝ] ℝ) (ContinuousLinearMap.id ℝ (Space d)))))
  (h_schwartzMap_slice_integral_iteratedFDeriv_norm_le :
    ∀ {d : ℕ} (n : ℕ) (η : 𝓢(Space d.succ, ℝ)) (i : Fin d.succ) (x : Space d),
      ‖iteratedFDeriv ℝ n (fun x => ∫ (r : ℝ), η ((slice i).symm (r, x))) x‖ ≤
          (∫ (r : ℝ), ‖iteratedFDeriv ℝ n η ((slice i).symm (r, x))‖) *
          ‖(slice i).symm.toContinuousLinearMap.comp
            (ContinuousLinearMap.prod (0 : Space d →L[ℝ] ℝ)
            (ContinuousLinearMap.id ℝ (Space d)))‖ ^ n)
  (h_schwartzMap_mul_pow_slice_integral_iteratedFDeriv_norm_le :
    ∀ {d : ℕ} (n m : ℕ) (i : Fin d.succ),
      ∃ rt, ∀ (η : 𝓢(Space d.succ, ℝ)), ∀ (x : Space d),
      Integrable (fun x : ℝ => ‖((1 + ‖x‖) ^ rt)⁻¹‖) volume ∧
      ‖x‖ ^ m * ‖iteratedFDeriv ℝ n (fun x => ∫ (r : ℝ), η ((slice i).symm (r, x))) x‖ ≤
          ((∫ (r : ℝ), ‖((1 + ‖r‖) ^ rt)⁻¹‖) *
          ‖(slice i).symm.toContinuousLinearMap.comp
            (ContinuousLinearMap.prod (0 : Space d →L[ℝ] ℝ)
            (ContinuousLinearMap.id ℝ (Space d)))‖ ^ n)
          * (2 ^ (rt + m, n).1 * ((Finset.Iic (rt + m, n)).sup
            fun m => SchwartzMap.seminorm ℝ m.1 m.2) η))
  (h_sliceSchwartz :
    ∀ {d : ℕ} (i : Fin d.succ), 𝓢(Space d.succ, ℝ) →L[ℝ] 𝓢(Space d, ℝ))
  (h_sliceSchwartz_apply :
    ∀ {d : ℕ} (i : Fin d.succ) (η : 𝓢(Space d.succ, ℝ)) (x : Space d),
      h_sliceSchwartz i η x = ∫ (r : ℝ), η ((slice i).symm (r, x)))

/-!

## A. Schwartz maps

-/

/-!

### A.1. Bounded condition for derivatives of Schwartz maps on slices

-/

lemma schwartzMap_slice_bound {n m} {d : ℕ} (i : Fin d.succ) :
    ∃ rt, ∀ (η : 𝓢(Space d.succ, ℝ)), ∃ k,
    Integrable (fun x : ℝ => ‖((1 + ‖x‖) ^ rt)⁻¹‖) volume ∧
    (∀ (x : Space d), ∀ r, ‖(slice i).symm (r, x)‖ ^ m *
      ‖iteratedFDeriv ℝ n ⇑η ((slice i).symm (r, x))‖ ≤ k * ‖(1 + ‖r‖) ^ (rt)‖⁻¹)
      ∧ k = (2 ^ (rt + m, n).1 * ((Finset.Iic (rt + m, n)).sup
        fun m => SchwartzMap.seminorm ℝ m.1 m.2) η) := by
  exact h_schwartzMap_slice_bound i
/-!

### A.2. Integrability for of Schwartz maps on slices

-/

-- @[fun_prop] -- disabled
lemma schwartzMap_mul_iteratedFDeriv_integrable_slice_symm {d : ℕ} (n m : ℕ)
    (η : 𝓢(Space d.succ, ℝ))
    (x : Space d) (i : Fin d.succ) :
    Integrable (fun r => ‖(slice i).symm (r, x)‖ ^ m *
    ‖iteratedFDeriv ℝ n ⇑η ((slice i).symm (r, x))‖) volume := by
  exact h_schwartzMap_mul_iteratedFDeriv_integrable_slice_symm n m η x i
lemma schwartzMap_integrable_slice_symm {d : ℕ} (i : Fin d.succ) (η : 𝓢(Space d.succ, ℝ))
    (x : Space d) : Integrable (fun r => η ((slice i).symm (r, x))) volume := by
  exact h_schwartzMap_integrable_slice_symm i η x
set_option maxSynthPendingDepth 10000 in
lemma schwartzMap_fderiv_integrable_slice_symm {d : ℕ} (η : 𝓢(Space d.succ, ℝ)) (x : Space d)
    (i : Fin d.succ) :
    Integrable (fun r => fderiv ℝ (fun x => η (((slice i).symm (r, x)))) x) volume := by
  exact h_schwartzMap_fderiv_integrable_slice_symm η x i
-- @[fun_prop] -- disabled
lemma schwartzMap_fderiv_left_integrable_slice_symm {d : ℕ} (η : 𝓢(Space d.succ, ℝ)) (x : Space d)
    (i : Fin d.succ) :
    Integrable (fun r => fderiv ℝ (fun r => η (((slice i).symm (r, x)))) r 1) volume := by
  exact h_schwartzMap_fderiv_left_integrable_slice_symm η x i
-- @[fun_prop] -- disabled
lemma schwartzMap_iteratedFDeriv_norm_slice_symm_integrable {n} {d : ℕ} (η : 𝓢(Space d.succ, ℝ))
    (x : Space d) (i : Fin d.succ) :
    Integrable (fun r => ‖iteratedFDeriv ℝ n ⇑η (((slice i).symm (r, x)))‖) volume := by
  exact h_schwartzMap_iteratedFDeriv_norm_slice_symm_integrable η x i
-- @[fun_prop] -- disabled
lemma schwartzMap_iteratedFDeriv_slice_symm_integrable {n} {d : ℕ} (η : 𝓢(Space d.succ, ℝ))
    (x : Space d) (i : Fin d.succ) :
    Integrable (fun r => iteratedFDeriv ℝ n ⇑η (((slice i).symm (r, x)))) volume := by
  exact h_schwartzMap_iteratedFDeriv_slice_symm_integrable η x i
/-!

### A.3. Continiuity of integrations of slices of Schwartz maps
-/

lemma continuous_schwartzMap_slice_integral {d} (i : Fin d.succ) (η : 𝓢(Space d.succ, ℝ)) :
    Continuous (fun x : Space d => ∫ r : ℝ, η ((slice i).symm (r, x))) := by
  exact h_continuous_schwartzMap_slice_integral i η
/-!

### A.4. Derivative of integrations of slices of Schwartz maps

-/

lemma schwartzMap_slice_integral_hasFDerivAt {d : ℕ} (η : 𝓢(Space d.succ, ℝ)) (i : Fin d.succ)
    (x₀ : Space d) :
    HasFDerivAt (fun x => ∫ (r : ℝ), η ((slice i).symm (r, x)))
      (∫ (r : ℝ), fderiv ℝ (fun x : Space d => η ((slice i).symm (r, x))) x₀) x₀ := by
  exact h_schwartzMap_slice_integral_hasFDerivAt η i x₀
/-!

### A.5. Differentiability as a slices of Schwartz maps

-/

lemma schwartzMap_slice_integral_differentiable {d : ℕ} (η : 𝓢(Space d.succ, ℝ))
    (i : Fin d.succ) :
    Differentiable ℝ (fun x => ∫ (r : ℝ), η ((slice i).symm (r, x))) :=
  fun x => (schwartzMap_slice_integral_hasFDerivAt η i x).differentiableAt

/-!

### A.6. Smoothness as slices of Schwartz maps

-/

lemma schwartzMap_slice_integral_contDiff {d : ℕ} (n : ℕ) (η : 𝓢(Space d.succ, ℝ))
    (i : Fin d.succ) :
    ContDiff ℝ n (fun x => ∫ (r : ℝ), η ((slice i).symm (r, x))) := by
  exact h_schwartzMap_slice_integral_contDiff n η i
/-!

### A.7. Iterated derivatives of integrations of slices of Schwartz maps

-/

lemma schwartzMap_slice_integral_iteratedFDeriv_apply {d : ℕ} (n : ℕ) (η : 𝓢(Space d.succ, ℝ))
    (i : Fin d.succ) :
    ∀ x, ∀ y, iteratedFDeriv ℝ n (fun x => ∫ (r : ℝ), η ((slice i).symm (r, x))) x y =
      ∫ (r : ℝ), (iteratedFDeriv ℝ n η ((slice i).symm (r, x)))
      (fun j => (slice i).symm (0, y j)) := by
  exact h_schwartzMap_slice_integral_iteratedFDeriv_apply n η i
lemma schwartzMap_slice_integral_iteratedFDeriv {d : ℕ} (n : ℕ) (η : 𝓢(Space d.succ, ℝ))
    (i : Fin d.succ) (x : Space d) :
    iteratedFDeriv ℝ n (fun x => ∫ (r : ℝ), η ((slice i).symm (r, x))) x
    = (∫ (r : ℝ), iteratedFDeriv ℝ n η ((slice i).symm (r, x))).compContinuousLinearMap
      (fun _ => (slice i).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.prod (0 : Space d →L[ℝ] ℝ) (ContinuousLinearMap.id ℝ (Space d)))) := by
  exact h_schwartzMap_slice_integral_iteratedFDeriv n η i x
lemma schwartzMap_slice_integral_iteratedFDeriv_norm_le {d : ℕ} (n : ℕ) (η : 𝓢(Space d.succ, ℝ))
    (i : Fin d.succ) (x : Space d) :
    ‖iteratedFDeriv ℝ n (fun x => ∫ (r : ℝ), η ((slice i).symm (r, x))) x‖ ≤
        (∫ (r : ℝ), ‖iteratedFDeriv ℝ n η ((slice i).symm (r, x))‖) *
        ‖(slice i).symm.toContinuousLinearMap.comp
          (ContinuousLinearMap.prod (0 : Space d →L[ℝ] ℝ)
          (ContinuousLinearMap.id ℝ (Space d)))‖ ^ n := by
  exact h_schwartzMap_slice_integral_iteratedFDeriv_norm_le n η i x
lemma schwartzMap_mul_pow_slice_integral_iteratedFDeriv_norm_le {d : ℕ} (n m : ℕ) (i : Fin d.succ) :
    ∃ rt, ∀ (η : 𝓢(Space d.succ, ℝ)),∀ (x : Space d),
    Integrable (fun x : ℝ => ‖((1 + ‖x‖) ^ rt)⁻¹‖) volume ∧
    ‖x‖ ^ m * ‖iteratedFDeriv ℝ n (fun x => ∫ (r : ℝ), η ((slice i).symm (r, x))) x‖ ≤
        ((∫ (r : ℝ), ‖((1 + ‖r‖) ^ rt)⁻¹‖) *
        ‖(slice i).symm.toContinuousLinearMap.comp
          (ContinuousLinearMap.prod (0 : Space d →L[ℝ] ℝ)
          (ContinuousLinearMap.id ℝ (Space d)))‖ ^ n)
        * (2 ^ (rt + m, n).1 * ((Finset.Iic (rt + m, n)).sup
          fun m => SchwartzMap.seminorm ℝ m.1 m.2) η) := by
  exact h_schwartzMap_mul_pow_slice_integral_iteratedFDeriv_norm_le n m i
/-!

### A.8. The map integrating over one component of a Schwartz map

-/

/-- The continuous linear map taking a Schwartz map and integrating over the `i`th component,
  to give a Schwartz map of one dimension lower. -/
def sliceSchwartz {d : ℕ} (i : Fin d.succ) :
    𝓢(Space d.succ, ℝ) →L[ℝ] 𝓢(Space d, ℝ) := by
  exact h_sliceSchwartz i
lemma sliceSchwartz_apply {d : ℕ} (i : Fin d.succ) (η : 𝓢(Space d.succ, ℝ)) (x : Space d) :
    sliceSchwartz i η x = ∫ (r : ℝ), η ((slice i).symm (r, x)) := by
  exact h_sliceSchwartz_apply i η x
/-!

## B. Constant slice distribution
-/

/-
An older draft introduced constant-slice distributions here, together with derivative lemmas.
That material was never completed and is currently outside the maintained build, so the stale
commented theorem skeletons have been removed.
-/
