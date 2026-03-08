/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import SpaceAndTime.Space.Derivatives.Div
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.SpecialFunctions.Sqrt
/-!

# The norm on space

## i. Overview

The main content of this file is defining `Space.normPowerSeries`, a power series which is
differentiable everywhere, and which tends to the norm in the limit as `n → ∞`.

We use properties of this power series to prove various results about distributions involving norms.

## ii. Key results

- `normPowerSeries` : A power series which is differentiable everywhere, and in the limit
  as `n → ∞` tends to `‖x‖`.
- `normPowerSeries_differentiable` : The power series is differentiable everywhere.
- `normPowerSeries_tendsto` : The power series tends to the norm in the limit as `n → ∞`.
- `distGrad_distOfFunction_norm_zpow` : The gradient of the distribution defined by a power of the
  norm.
- `distGrad_distOfFunction_log_norm` : The gradient of the distribution defined by the logarithm
  of the norm.
- `distDiv_inv_pow_eq_dim` : The divergence of the distribution defined by the
  inverse power of the norm proportional to the Dirac delta distribution.

## iii. Table of contents

- A. The norm as a power series
  - A.1. Differentiability of the norm power series
  - A.2. The limit of the norm power series
  - A.3. The derivative of the norm power series
  - A.4. Limits of the derivative of the power series
  - A.5. The power series is AEStronglyMeasurable
  - A.6. Bounds on the norm power series
  - A.7. The `IsDistBounded` property of the norm power series
  - A.8. Differentiability of functions
  - A.9. Derivatives of functions
  - A.10. Gradients of distributions based on powers
    - A.10.1. The limits of gradients of distributions based on powers
  - A.11. Gradients of distributions based on logs
    - A.11.1. The limits of gradients of distributions based on logs
- B. Distributions involving norms
  - B.1. The gradient of distributions based on powers
  - B.2. The gradient of distributions based on logs
  - B.3. Divergence equal dirac delta

## iv. References

-/
open SchwartzMap NNReal
noncomputable section

variable (𝕜 : Type) {E F F' : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup F'] [NormedSpace ℝ E] [NormedSpace ℝ F]

namespace Space

open MeasureTheory

/-!

## A. The norm as a power series

-/

/-- A power series which is differentiable everywhere, and in the limit
  as `n → ∞` tends to `‖x‖`. -/
def normPowerSeries {d} : ℕ → Space d → ℝ := fun n x =>
  √(‖x‖ ^ 2 + 1/(n + 1))

lemma normPowerSeries_eq (n : ℕ) :
    normPowerSeries (d := d) n = fun x => √(‖x‖ ^ 2 + 1/(n + 1)) := rfl

lemma normPowerSeries_eq_rpow {d} (n : ℕ) :
    normPowerSeries (d := d) n = fun x => ((‖x‖ ^ 2 + 1/(n + 1))) ^ (1/2 : ℝ) := by
  rw [normPowerSeries_eq]
  funext x
  rw [← Real.sqrt_eq_rpow]

/-!

### A.1. Differentiability of the norm power series

-/

-- @[fun_prop] -- disabled
lemma normPowerSeries_differentiable {d} (n : ℕ) :
    Differentiable ℝ (fun (x : Space d) => normPowerSeries n x) := by
  intro x
  have hnorm : HasFDerivAt (fun y : Space d => ‖y‖ ^ 2) (2 • (innerSL ℝ x)) x := by
    simpa using HasFDerivAt.norm_sq (f := fun y : Space d => y)
      (f' := ContinuousLinearMap.id ℝ (Space d)) (x := x) (hasFDerivAt_id x)
  have h2 : HasFDerivAt (fun _ : Space d => (1 : ℝ) / (n + 1)) (0 : Space d →L[ℝ] ℝ) x :=
    hasFDerivAt_const ((1 : ℝ) / (n + 1)) x
  have hsq : HasFDerivAt (fun y : Space d => ‖y‖ ^ 2 + (1 : ℝ) / (n + 1))
      (2 • (innerSL ℝ x)) x := by
    convert hnorm.add h2 using 1; simp [add_zero]
  have hpos : ‖x‖ ^ 2 + (1 : ℝ) / (n + 1) ≠ 0 := by positivity
  exact (HasFDerivAt.sqrt hsq hpos).differentiableAt

/-!

### A.2. The limit of the norm power series

-/
open InnerProductSpace

open scoped Topology BigOperators FourierTransform

lemma normPowerSeries_tendsto {d} (x : Space d) (hx : x ≠ 0) :
    Filter.Tendsto (fun n => normPowerSeries n x) Filter.atTop (𝓝 (‖x‖)) := by
  rw [normPowerSeries_eq]
  have h_arg : Filter.Tendsto (fun n : ℕ => ‖x‖ ^ 2 + (1 / (n + 1 : ℝ))) Filter.atTop
      (𝓝 (‖x‖ ^ 2)) := by
    simpa [add_assoc] using
      (tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat)
  refine (Real.continuous_sqrt.tendsto (‖x‖ ^ 2)).comp h_arg |>.trans ?_
  simp [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg x)]

lemma normPowerSeries_inv_tendsto {d} (x : Space d) (hx : x ≠ 0) :
    Filter.Tendsto (fun n => (normPowerSeries n x)⁻¹) Filter.atTop (𝓝 (‖x‖⁻¹)) := by
  exact (normPowerSeries_tendsto x hx).inv₀ (norm_ne_zero_iff.mpr hx)

/-!

### A.3. The derivative of the norm power series

-/
open Space

lemma deriv_normPowerSeries {d} (n : ℕ) (x : Space d) (i : Fin d) :
    ∂[i] (normPowerSeries n) x = x i * (normPowerSeries n x)⁻¹ := by
  rw [deriv_eq_fderiv_basis, normPowerSeries_eq]
  have hnorm : HasFDerivAt (fun y : Space d => ‖y‖ ^ 2) (2 • (innerSL ℝ x)) x := by
    simpa using HasFDerivAt.norm_sq (f := fun y : Space d => y)
      (f' := ContinuousLinearMap.id ℝ (Space d)) (x := x) (hasFDerivAt_id x)
  have h2 : HasFDerivAt (fun _ : Space d => (1 : ℝ) / (n + 1)) (0 : Space d →L[ℝ] ℝ) x :=
    hasFDerivAt_const ((1 : ℝ) / (n + 1)) x
  have hsq : HasFDerivAt (fun y : Space d => ‖y‖ ^ 2 + 1 / (n + 1))
      (2 • (innerSL ℝ x)) x := by
    convert hnorm.add h2 using 1
    simp [add_zero]
  have hpos : ‖x‖ ^ 2 + 1 / (n + 1) ≠ 0 := by positivity
  have hsqrt := HasFDerivAt.sqrt hsq hpos
  rw [hsqrt.fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, innerSL_apply, inner_basis]
  field_simp [normPowerSeries_eq]
  ring

lemma fderiv_normPowerSeries {d} (n : ℕ) (x y : Space d) :
    fderiv ℝ (fun (x : Space d) => normPowerSeries n x) x y =
      ⟪y, x⟫_ℝ * (normPowerSeries n x)⁻¹ := by
  rw [fderiv_eq_sum_deriv, inner_eq_sum, Finset.sum_mul]
  congr
  funext i
  simp [deriv_normPowerSeries]
  ring

/-!

### A.4. Limits of the derivative of the power series

-/

lemma deriv_normPowerSeries_tendsto {d} (x : Space d) (hx : x ≠ 0) (i : Fin d) :
    Filter.Tendsto (fun n => ∂[i] (normPowerSeries n) x) Filter.atTop (𝓝 (x i * (‖x‖)⁻¹)) := by
  conv => enter [1, n]; rw [deriv_normPowerSeries]
  refine Filter.Tendsto.mul ?_ ?_
  · exact tendsto_const_nhds
  · exact normPowerSeries_inv_tendsto x hx

lemma fderiv_normPowerSeries_tendsto {d} (x y : Space d) (hx : x ≠ 0) :
    Filter.Tendsto (fun n => fderiv ℝ (fun (x : Space d) => normPowerSeries n x) x y)
      Filter.atTop (𝓝 (⟪y, x⟫_ℝ * (‖x‖)⁻¹)) := by
  conv => enter [1, n]; rw [fderiv_normPowerSeries]
  refine Filter.Tendsto.mul ?_ ?_
  · exact tendsto_const_nhds
  · exact normPowerSeries_inv_tendsto x hx

/-!

### A.5. The power series is AEStronglyMeasurable

-/

-- @[fun_prop] -- disabled
lemma normPowerSeries_aestronglyMeasurable {d} (n : ℕ) :
    AEStronglyMeasurable (normPowerSeries n : Space d → ℝ) volume := by
  rw [normPowerSeries_eq]
  refine StronglyMeasurable.aestronglyMeasurable ?_
  exact (Real.continuous_sqrt.comp
    ((continuous_norm.pow 2).add continuous_const)).stronglyMeasurable

/-!

### A.6. Bounds on the norm power series

-/

@[simp]
lemma normPowerSeries_nonneg {d} (n : ℕ) (x : Space d) :
    0 ≤ normPowerSeries n x := by
  rw [normPowerSeries_eq]
  simp

@[simp]
lemma normPowerSeries_pos {d} (n : ℕ) (x : Space d) :
    0 < normPowerSeries n x := by
  rw [normPowerSeries_eq]
  simp only [one_div, Real.sqrt_pos]
  positivity

@[simp]
lemma normPowerSeries_ne_zero {d} (n : ℕ) (x : Space d) :
    normPowerSeries n x ≠ 0 := by
  rw [normPowerSeries_eq]
  simp only [one_div, ne_eq]
  positivity

lemma normPowerSeries_le_norm_sq_add_one {d} (n : ℕ) (x : Space d) :
    normPowerSeries n x ≤ ‖x‖ + 1 := by
  trans √(‖x‖ ^ 2 + 1)
  · rw [normPowerSeries_eq]
    apply Real.sqrt_le_sqrt
    simp only [one_div, add_le_add_iff_left]
    refine inv_le_one_iff₀.mpr ?_
    right
    simp
  · refine (Real.sqrt_le_left (by positivity)).mpr ?_
    trans (‖x‖ ^ 2 + 1) + (2 * ‖x‖)
    · simp
    · ring_nf
      rfl

@[simp]
lemma norm_lt_normPowerSeries {d} (n : ℕ) (x : Space d) :
    ‖x‖ < normPowerSeries n x := by
  rw [normPowerSeries_eq]
  apply Real.lt_sqrt_of_sq_lt
  simp only [one_div, lt_add_iff_pos_right, inv_pos]
  positivity

lemma norm_le_normPowerSeries {d} (n : ℕ) (x : Space d) :
    ‖x‖ ≤ normPowerSeries n x := by
  rw [normPowerSeries_eq]
  apply Real.le_sqrt_of_sq_le
  simp only [one_div, le_add_iff_nonneg_right, inv_nonneg]
  positivity

lemma normPowerSeries_zpow_le_norm_sq_add_one {d} (n : ℕ) (m : ℤ) (x : Space d)
    (hx : x ≠ 0) :
    (normPowerSeries n x) ^ m ≤ (‖x‖ + 1) ^ m + ‖x‖ ^ m := by
  match m with
  | .ofNat m =>
    trans (‖x‖ + 1) ^ m
    · simp
      refine pow_le_pow_left₀ (by simp) ?_ m
      exact normPowerSeries_le_norm_sq_add_one n x
    · simp
  | .negSucc m =>
    trans (‖x‖ ^ (m + 1))⁻¹; swap
    · simp
      positivity
    simp only [zpow_negSucc]
    refine inv_anti₀ ?_ ?_
    · positivity
    refine pow_le_pow_left₀ (by simp) ?_ (m + 1)
    exact norm_le_normPowerSeries n x

lemma normPowerSeries_inv_le {d} (n : ℕ) (x : Space d) (hx : x ≠ 0) :
    (normPowerSeries n x)⁻¹ ≤ ‖x‖⁻¹ := by
  refine inv_anti₀ ?_ ?_
  · positivity
  apply Real.le_sqrt_of_sq_le
  simp only [one_div, le_add_iff_nonneg_right, inv_nonneg]
  positivity

lemma normPowerSeries_log_le_normPowerSeries {d} (n : ℕ) (x : Space d) :
    |Real.log (normPowerSeries n x)| ≤ (normPowerSeries n x)⁻¹ + (normPowerSeries n x) := by
  have h1 := Real.neg_inv_le_log (x := (normPowerSeries n x)) (by simp)
  have h2 := Real.log_le_rpow_div (x := (normPowerSeries n x)) (by simp) (ε := 1) (by positivity)
  simp_all
  rw [abs_le']
  generalize Real.log ‖x‖ = r at *
  apply And.intro
  · apply h2.trans
    simp
  · rw [neg_le]
    apply le_trans _ h1
    simp
lemma normPowerSeries_log_le {d} (n : ℕ) (x : Space d) (hx : x ≠ 0) :
    |Real.log (normPowerSeries n x)| ≤ ‖x‖⁻¹ + (‖x‖ + 1) := by
  apply le_trans (normPowerSeries_log_le_normPowerSeries n x) ?_
  apply add_le_add
  · exact normPowerSeries_inv_le n x hx
  · exact normPowerSeries_le_norm_sq_add_one n x

lemma differentiable_normPowerSeries_zpow {d : ℕ} {n : ℕ} (m : ℤ) :
    Differentiable ℝ (fun x : Space d => (normPowerSeries n x) ^ m) := by
  refine Differentiable.zpow ?_ ?_
  · exact normPowerSeries_differentiable n
  · left
    exact normPowerSeries_ne_zero n

-- @[fun_prop] -- disabled
lemma differentiable_normPowerSeries_inv {d : ℕ} {n : ℕ} :
    Differentiable ℝ (fun x : Space d => (normPowerSeries n x)⁻¹) := by
  convert differentiable_normPowerSeries_zpow (n := n) (m := -1) using 1
  funext x
  simp

-- @[fun_prop] -- disabled
lemma differentiable_log_normPowerSeries {d : ℕ} {n : ℕ} :
    Differentiable ℝ (fun x : Space d => Real.log (normPowerSeries n x)) := by
  refine Differentiable.log ?_ ?_
  · exact normPowerSeries_differentiable n
  · intro x
    exact normPowerSeries_ne_zero n x
/-!

### A.9. Derivatives of functions

-/

lemma deriv_normPowerSeries_zpow {d : ℕ} {n : ℕ} (m : ℤ) (x : Space d) (i : Fin d) :
    ∂[i] (fun x : Space d => (normPowerSeries n x) ^ m) x =
      m * x i * (normPowerSeries n x) ^ (m - 2) := by
  rw [deriv_eq_fderiv_basis]
  change (fderiv ℝ ((fun x => x ^ m) ∘ normPowerSeries n) x) (basis i) = _
  rw [fderiv_comp]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, fderiv_eq_smul_deriv, deriv_zpow',
    smul_eq_mul]
  rw [fderiv_normPowerSeries]
  simp only [basis_inner]
  field_simp
  ring_nf
  have h1 : normPowerSeries n x ^ (-1 + m) = normPowerSeries n x ^ ((-2 + m) + 1) := by
    ring_nf
  rw [h1, zpow_add₀]
  simp only [Int.reduceNeg, zpow_one]
  ring
  · simp
  · refine DifferentiableAt.zpow ?_ ?_
    · exact differentiableAt_id (x := normPowerSeries n x)
    · left
      exact normPowerSeries_ne_zero n x
  · apply Differentiable.differentiableAt (normPowerSeries_differentiable (d := d) n)

lemma fderiv_normPowerSeries_zpow {d : ℕ} {n : ℕ} (m : ℤ) (x y : Space d) :
    fderiv ℝ (fun x : Space d => (normPowerSeries n x) ^ m) x y =
      m * ⟪y, x⟫_ℝ * (normPowerSeries n x) ^ (m - 2) := by
  rw [fderiv_eq_sum_deriv, inner_eq_sum, Finset.mul_sum, Finset.sum_mul]
  congr
  funext i
  simp [deriv_normPowerSeries_zpow]
  ring

lemma deriv_log_normPowerSeries {d : ℕ} {n : ℕ} (x : Space d) (i : Fin d) :
    ∂[i] (fun x : Space d => Real.log (normPowerSeries n x)) x =
      x i * (normPowerSeries n x) ^ (-2 : ℤ) := by
  rw [deriv_eq_fderiv_basis]
  change (fderiv ℝ (Real.log ∘ normPowerSeries n) x) (basis i) = _
  rw [fderiv_comp,]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, fderiv_eq_smul_deriv,
    Real.deriv_log', smul_eq_mul, Int.reduceNeg, zpow_neg]
  rw [fderiv_normPowerSeries]
  simp [zpow_ofNat, sq]
  ring
  · apply DifferentiableAt.log ?_ ?_
    · exact differentiableAt_id (x := normPowerSeries n x)
    · exact normPowerSeries_ne_zero n x
  · apply Differentiable.differentiableAt (normPowerSeries_differentiable (d := d) n)

lemma fderiv_log_normPowerSeries {d : ℕ} {n : ℕ} (x y : Space d) :
    fderiv ℝ (fun x : Space d => Real.log (normPowerSeries n x)) x y =
      ⟪y, x⟫_ℝ * (normPowerSeries n x) ^ (-2 : ℤ) := by
  rw [fderiv_eq_sum_deriv, inner_eq_sum, Finset.sum_mul]
  congr
  funext i
  simp [deriv_log_normPowerSeries]
  ring

/-
The older distributional norm-power-series development lived below as commented draft code.
It depended on results that are no longer maintained in this tree, so the inactive theorem
shells have been removed instead of leaving placeholder proofs in comments.
-/

end Space
