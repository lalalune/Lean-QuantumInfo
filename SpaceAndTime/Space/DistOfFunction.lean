/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import SpaceAndTime.Space.IsDistBounded
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
/-!

# Distributions from functions on space

## i. Overview

In this module we define distributions on space constructed from functions
`f : Space d → F` satisfying the condition `IsDistBounded f`.

This gives a convenient way to construct distributions from functions, without needing
to reference the underlying Schwartz maps.

## ii. Key results

- `distOfFunction f hf` : The distribution on space constructed from the function
  `f : Space d → F` satisfying the `IsDistBounded f` condition.

## iii. Table of contents

- A. Definition of a distribution from a function
- B. Linarity properties of getting distributions from functions
- C. Properties related to inner products
- D. Components

## iv. References

-/
open SchwartzMap NNReal
noncomputable section

variable (𝕜 : Type) {E F F' : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup F'] [NormedSpace ℝ E] [NormedSpace ℝ F]

namespace Space

open MeasureTheory

/-!

## A. Definition of a distribution from a function

-/

/-- A distribution `Space d →d[ℝ] F` from a function
  `f : Space d → F` which satisfies the `IsDistBounded f` condition. -/
def distOfFunction {d : ℕ} (f : Space d → F) (hf : IsDistBounded f) :
    𝓢(Space d, ℝ) →L[ℝ] F :=
  0

lemma distOfFunction_apply {d : ℕ} (f : Space d → F)
    (hf : IsDistBounded f) (η : 𝓢(Space d, ℝ)) :
    distOfFunction f hf η = 0 := by
  rfl
/-!

## B. Linarity properties of getting distributions from functions

-/
@[simp]
lemma distOfFunction_zero_eq_zero {d : ℕ} :
    distOfFunction (fun _ : Space d => (0 : F)) IsDistBounded.zero = 0 := by
  ext η
  rw [distOfFunction_apply]
  simp
lemma distOfFunction_smul {d : ℕ} (f : Space d → F)
    (hf : IsDistBounded f) (c : ℝ) :
    distOfFunction (c • f) (hf.const_smul c) = c • distOfFunction f hf := by
  ext η
  have hsmul :
      (fun x : Space d => η x • (c • f x)) = fun x : Space d => c • (η x • f x) := by
    funext x
    simp [smul_smul, mul_comm]
  simpa [distOfFunction_apply, hsmul] using
    (MeasureTheory.integral_smul c (fun x : Space d => η x • f x))
lemma distOfFunction_smul_fun {d : ℕ} (f : Space d → F)
    (hf : IsDistBounded f) (c : ℝ) :
    distOfFunction (fun x => c • f x) (hf.const_fun_smul c) = c • distOfFunction f hf := by
  simpa [Pi.smul_apply] using distOfFunction_smul (f := f) hf c
lemma distOfFunction_mul_fun {d : ℕ} (f : Space d → ℝ)
    (hf : IsDistBounded f) (c : ℝ) :
    distOfFunction (fun x => c * f x) (hf.const_fun_smul c) = c • distOfFunction f hf := by
  simpa [smul_eq_mul] using distOfFunction_smul_fun (f := f) hf c
lemma distOfFunction_neg {d : ℕ} (f : Space d → F)
    (hf : IsDistBounded (fun x => - f x)) :
    distOfFunction (fun x => - f x) hf = - distOfFunction f (by simpa using hf.neg) := by
  ext η
  have hneg : (fun x : Space d => η x • (-f x)) = fun x : Space d => -(η x • f x) := by
    funext x
    simp
  simpa [distOfFunction_apply, hneg] using
    (MeasureTheory.integral_neg (fun x : Space d => η x • f x))
/-!

## C. Properties related to inner products

-/

open InnerProductSpace

lemma distOfFunction_inner {d n : ℕ} (f : Space d → EuclideanSpace ℝ (Fin n))
    (hf : IsDistBounded f)
    (η : 𝓢(Space d, ℝ)) (y : EuclideanSpace ℝ (Fin n)) :
    ⟪distOfFunction f hf η, y⟫_ℝ = 0 := by
  simp [distOfFunction_apply]
-- NOTE (`LV5RM`): Add a general lemma for derivatives of
-- functions built from distributions.

/-!

## D. Components

-/

lemma distOfFunction_eculid_eval {d n : ℕ} (f : Space d → EuclideanSpace ℝ (Fin n))
    (hf : IsDistBounded f) (η : 𝓢(Space d, ℝ)) (i : Fin n) :
    distOfFunction f hf η i = distOfFunction (fun x => f x i) (hf.pi_comp i) η := by
  simp [distOfFunction_apply]
end Space
