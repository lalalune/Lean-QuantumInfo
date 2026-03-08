/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import SpaceAndTime.Space.Derivatives.Curl
/-!

# The constant distribution on space

## i. Overview

In this module we define the constant distribution from `Space d` to a module `M`.
That is the distribution which sends every Schwartz function to its
integral multiplied by a fixed element `m : M`.

We show that the derivatives of this constant distribution are zero.
## ii. Key results

- `distConst` : The constant distribution from `Space d` to a module `M`.

## iii. Table of contents

- A. The definition of the constant distribution
- B. Derivatives of the constant distribution

## iv. References

-/

namespace Space
open Distribution

/-!

## A. The definition of the constant distribution

-/

/-- The constant distribution from `Space d` to a module `M` associated with
  `m : M`. -/
noncomputable def distConst {M } [NormedAddCommGroup M] [NormedSpace ℝ M] (d : ℕ) (m : M) :
    (Space d) →d[ℝ] M := const ℝ (Space d) m

/-!

## B. Derivatives of the constant distribution

-/

@[simp]
lemma distDeriv_distConst {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (μ : Fin d) (m : M) :
    distDeriv μ (distConst d m) = 0 := by
  ext η
  rw [distDeriv_apply, Distribution.fderivD_apply]
  simp

@[simp]
lemma distGrad_distConst {d} (m : ℝ) :
    distGrad (distConst d m) = 0 := by
  ext η i
  rw [distGrad_apply]
  simpa using congrArg (fun g : (Space d) →d[ℝ] ℝ => g η)
    (distDeriv_distConst (d := d) (μ := i) (m := m))

@[simp]
lemma distDiv_distConst {d} (m : EuclideanSpace ℝ (Fin d)) :
    distDiv (distConst d m) = 0 := by
  ext η
  rw [distDiv_apply_eq_sum_distDeriv]
  simp [distDeriv_distConst]

@[simp]
lemma distCurl_distConst (m : EuclideanSpace ℝ (Fin 3)) :
    distCurl (distConst 3 m) = 0 := by
  ext η i
  fin_cases i <;> simp [distCurl, Distribution.fderivD_apply]

end Space
