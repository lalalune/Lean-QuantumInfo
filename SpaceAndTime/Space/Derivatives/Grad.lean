/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong, Joseph Tooby-Smith, Lode Vermeulen
-/
import SpaceAndTime.Space.Derivatives.Basic
set_option maxHeartbeats 800000
/-!

# Gradient of functions and distributions on `Space d`

## i. Overview

This module defines and proves basic properties of the gradient operator
on functions from `Space d` to `ℝ` and on distributions from `Space d` to `ℝ`.

The gradient operator returns a vector field whose components are the partial derivatives
of the input function with respect to each spatial coordinate.

## ii. Key results

- `grad` : The gradient operator on functions from `Space d` to `ℝ`.
- `distGrad` : The gradient operator on distributions from `Space d` to `ℝ`.

## iii. Table of contents

- A. The gradient of functions on `Space d`
  - A.1. Gradient of the zero function
  - A.2. Gradient distributes over addition
  - A.3. Gradient of a constant function
  - A.4. Gradient distributes over scalar multiplication
  - A.5. Gradient distributes over negation
  - A.6. Expansion in terms of basis vectors
  - A.7. Components of the gradient
  - A.8. Inner product with a gradient
  - A.9. Gradient is equal to `gradient` from Mathlib
  - A.10. Value of gradient in the direction of the position vector
  - A.11. Gradient of the norm squared function
  - A.12. Gradient of the inner product function
  - A.13. Integrability with bounded functions
- B. Gradient of distributions
  - B.1. The definition
  - B.2. The gradient of inner products
  - B.3. The gradient as a sum over basis vectors
  - B.4. The underlying function of the gradient distribution
  - B.5. The gradient applied to a Schwartz function

## iv. References

-/

namespace Space

noncomputable instance {d : ℕ} : CompleteSpace (Space d) :=
  FiniteDimensional.complete ℝ (Space d)

/-!

## A. The gradient of functions on `Space d`

-/

/-- The vector calculus operator `grad`. -/
noncomputable def grad {d} (f : Space d → ℝ) :
  Space d → EuclideanSpace ℝ (Fin d) := fun x => WithLp.toLp 2 fun i => ∂[i] f x

@[inherit_doc grad]
scoped[Space] notation "∇" => grad

open InnerProductSpace

/-!

### A.1. Gradient of the zero function

-/

@[simp]
lemma grad_zero : ∇ (0 : Space d → ℝ) = 0 := by
  unfold grad Space.deriv
  simp only [fderiv_zero, Pi.zero_apply, ContinuousLinearMap.zero_apply]
  rfl

/-!

### A.2. Gradient distributes over addition

-/

lemma grad_add (f1 f2 : Space d → ℝ)
    (hf1 : Differentiable ℝ f1) (hf2 : Differentiable ℝ f2) :
    ∇ (f1 + f2) = ∇ f1 + ∇ f2 := by
  ext x i
  simpa [grad] using congrArg (fun g => g x) (deriv_add (u := i) f1 f2 hf1 hf2)

/-!

### A.3. Gradient of a constant function

-/

@[simp]
lemma grad_const : ∇ (fun _ : Space d => c) = 0 := by
  unfold grad Space.deriv
  simp only [fderiv_fun_const, Pi.ofNat_apply, ContinuousLinearMap.zero_apply]
  rfl

/-!

### A.4. Gradient distributes over scalar multiplication

-/

lemma grad_smul (f : Space d → ℝ) (k : ℝ)
    (hf : Differentiable ℝ f) :
    ∇ (k • f) = k • ∇ f := by
  ext x i
  simpa [grad, Pi.smul_apply] using congrArg (fun g => g x)
    (deriv_const_smul (u := i) (f := f) k hf)

/-!

### A.5. Gradient distributes over negation

-/

lemma grad_neg (f : Space d → ℝ) :
    ∇ (- f) = - ∇ f := by
  ext x i
  simpa [grad, deriv_eq, ContinuousLinearMap.neg_apply] using
    congrArg (fun L => L (basis i)) (fderiv_neg (f := f) (x := x) (𝕜 := ℝ))

/-!

### A.6. Expansion in terms of basis vectors

-/

lemma grad_eq_sum {d} (f : Space d → ℝ) (x : Space d) :
    ∇ f x = ∑ i, deriv i f x • EuclideanSpace.single i 1 := by
  symm
  simpa [grad, EuclideanSpace.basisFun_apply] using
    (OrthonormalBasis.sum_repr_symm (EuclideanSpace.basisFun (Fin d) ℝ) (∇ f x))

/-!

### A.7. Components of the gradient

-/

lemma grad_apply {d} (f : Space d → ℝ) (x : Space d) (i : Fin d) :
    (∇ f x) i = deriv i f x := by
  simp [grad]

/-!

### A.8. Inner product with a gradient

-/

open InnerProductSpace

lemma grad_inner_single {d} (f : Space d → ℝ) (x : Space d) (i : Fin d) :
    ⟪∇ f x, EuclideanSpace.single i 1⟫_ℝ = deriv i f x := by
  change ∑ j, ⟪(∇ f x) j, (EuclideanSpace.single i (1 : ℝ)) j⟫_ℝ = deriv i f x
  rw [Fintype.sum_eq_single i]
  · change (EuclideanSpace.single i (1 : ℝ)) i * (∇ f x) i = deriv i f x
    simp [grad]
  · intro j hj
    simp [hj]

lemma grad_inner_eq {d} (f : Space d → ℝ) (x : Space d) (y : EuclideanSpace ℝ (Fin d)) :
    ⟪∇ f x, y⟫_ℝ = ∑ i, y i * ∂[i] f x:= by
  have hy : y = ∑ i, y i • EuclideanSpace.basisFun (Fin d) ℝ i := by
      conv_lhs => rw [← OrthonormalBasis.sum_repr (EuclideanSpace.basisFun (Fin d) ℝ) y]
      dsimp [basis]
  conv_lhs => rw [hy, inner_sum]
  simp [inner_smul_right, grad_inner_single]

lemma inner_grad_eq {d} (f : Space d → ℝ) (x : EuclideanSpace ℝ (Fin d)) (y : Space d) :
    ⟪x, ∇ f y⟫_ℝ = ∑ i, x i * ∂[i] f y := by
  rw [← grad_inner_eq]
  exact real_inner_comm (∇ f y) x

lemma grad_inner_repr_eq {d} (f : Space d → ℝ) (x y : Space d) :
    ⟪∇ f x, (Space.basis).repr y⟫_ℝ = fderiv ℝ f x y := by
  rw [grad_inner_eq f x ((Space.basis).repr y), Space.fderiv_eq_sum_deriv]
  simp

lemma repr_grad_inner_eq {d} (f : Space d → ℝ) (x y : Space d) :
    ⟪(Space.basis).repr x, ∇ f y⟫_ℝ = fderiv ℝ f y x := by
  rw [← grad_inner_repr_eq f y x]
  exact real_inner_comm (∇ f y) ((Space.basis).repr x)

/-!

### A.9. Gradient is equal to `gradient` from Mathlib

-/

lemma grad_eq_gradiant {d} (f : Space d → ℝ) :
    ∇ f = basis.repr ∘ gradient f := by
  funext x
  ext i
  have hdual :
      ((toDual ℝ (Space d)) (gradient f x)) (basis i) = fderiv ℝ f x (basis i) := by
    simpa [gradient] using
      congrArg (fun L => L (basis i)) ((toDual ℝ (Space d)).apply_symm_apply (fderiv ℝ f x))
  simpa [grad, deriv_eq, basis_repr_apply, Space.inner_basis] using hdual.symm

lemma gradient_eq_grad {d} (f : Space d → ℝ) :
    gradient f = basis.repr.symm ∘ ∇ f := by
  funext x
  have h := congrArg (fun g => g x) (grad_eq_gradiant (f := f))
  simpa using (congrArg basis.repr.symm h).symm

lemma gradient_eq_sum {d} (f : Space d → ℝ) (x : Space d) :
    gradient f x = ∑ i, deriv i f x • basis i := by
  rw [gradient_eq_grad]
  change basis.repr.symm (∇ f x) = ∑ i, deriv i f x • basis i
  rw [grad_eq_sum]
  simp

lemma euclid_gradient_eq_sum {d} (f : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    gradient f x = ∑ i, fderiv ℝ f x (EuclideanSpace.single i 1) • EuclideanSpace.single i 1 := by
  apply ext_inner_right (𝕜 := ℝ) fun y => ?_
  simp [gradient]
  have hy : y = ∑ i, y i • EuclideanSpace.single i 1 := by
    conv_lhs => rw [← OrthonormalBasis.sum_repr (EuclideanSpace.basisFun (Fin d) ℝ) y]
    simp
  conv_lhs => rw [hy]
  simp [sum_inner, inner_smul_left, EuclideanSpace.inner_single_left]
  congr
  funext i
  have hsingle : ⟪EuclideanSpace.single i (1 : ℝ), y⟫_ℝ = y i := by
    rw [PiLp.inner_apply]
    rw [Fintype.sum_eq_single i]
    · change ⟪(EuclideanSpace.single i (1 : ℝ)) i, y i⟫_ℝ = y i
      simp only [EuclideanSpace.single_apply, ↓reduceIte]
      change y i * (1 : ℝ) = y i
      ring
    · intro j hj
      simp [hj]
  rw [hsingle]
  ring_nf

/-!

### A.10. Value of gradient in the direction of the position vector

-/

/-- The gradient in the direction of the space position. -/
lemma grad_inner_space_unit_vector {d} (x : Space d) (f : Space d → ℝ) (hd : Differentiable ℝ f) :
    ⟪∇ f x, ‖x‖⁻¹ • basis.repr x⟫_ℝ = _root_.deriv (fun r => f (r • ‖x‖⁻¹ • x)) ‖x‖ := by
  let line : ℝ → Space d := fun r => r • ‖x‖⁻¹ • x
  have hline_x : line ‖x‖ = x := by
    dsimp [line]
    by_cases hx : x = 0
    · subst hx
      simp
    · have hnx : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
      rw [smul_smul, mul_inv_cancel₀ hnx, one_smul]
  have hline_deriv : HasDerivAt line (‖x‖⁻¹ • x) ‖x‖ := by
    dsimp [line]
    simpa [smul_smul] using (hasDerivAt_id ‖x‖).smul_const (‖x‖⁻¹ • x)
  have hcomp : HasDerivAt (fun r => f (line r)) (fderiv ℝ f x (‖x‖⁻¹ • x)) ‖x‖ := by
    have hf' : HasFDerivAt f (fderiv ℝ f x) (line ‖x‖) := by
      rw [hline_x]
      exact (hd x).hasFDerivAt
    simpa using HasFDerivAt.comp_hasDerivAt (x := ‖x‖) hf' hline_deriv
  calc
    ⟪∇ f x, ‖x‖⁻¹ • basis.repr x⟫_ℝ = ⟪∇ f x, basis.repr (‖x‖⁻¹ • x)⟫_ℝ := by
      simp
    _ = fderiv ℝ f x (‖x‖⁻¹ • x) := by
      simpa using (grad_inner_repr_eq (f := f) (x := x) (y := ‖x‖⁻¹ • x))
    _ = _root_.deriv (fun r => f (r • ‖x‖⁻¹ • x)) ‖x‖ := by
      symm
      simpa [line] using hcomp.deriv

lemma grad_inner_space {d} (x : Space d) (f : Space d → ℝ) (hd : Differentiable ℝ f) :
    ⟪∇ f x, basis.repr x⟫_ℝ = ‖x‖ * _root_.deriv (fun r => f (r • ‖x‖⁻¹ • x)) ‖x‖ := by
  rw [← grad_inner_space_unit_vector _ _ hd, inner_smul_right]
  by_cases hx : x = 0
  · subst hx
    simp
  have hx : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  field_simp

/-!

### A.11. Gradient of the norm squared function

-/

lemma grad_norm_sq (x : Space d) :
    ∇ (fun x => ‖x‖ ^ 2) x = (2 : ℝ) • basis.repr x := by
  ext i
  change deriv i (fun x => ‖x‖ ^ 2) x = 2 * x.val i
  exact deriv_norm_sq x i

/-!

### A.12. Gradient of the inner product function

-/

/-- The gradient of the inner product is given by `2 • x`. -/
lemma grad_inner {d : ℕ} :
    ∇ (fun y : Space d => ⟪y, y⟫_ℝ) = fun z => (2 : ℝ) • basis.repr z := by
  ext z i
  change deriv i (fun y : Space d => ⟪y, y⟫_ℝ) z = 2 * z.val i
  exact deriv_eq_inner_self z i

lemma grad_inner_left {d : ℕ} (x : Space d) :
    ∇ (fun y : Space d => ⟪y, x⟫_ℝ) = fun _ => basis.repr x := by
  ext z i
  simp [Space.grad]

lemma grad_inner_right {d : ℕ} (x : Space d) :
    ∇ (fun y : Space d => ⟪x, y⟫_ℝ) = fun _ => basis.repr x := by
  rw [← grad_inner_left x]
  congr
  funext y
  exact real_inner_comm y x

/-!

### A.13. Integrability with bounded functions

The distribution-construction results using `IsDistBounded` live in
`SpaceAndTime.Space.DistOfFunction`.

-/

open InnerProductSpace Distribution SchwartzMap MeasureTheory

/-!

## B. Gradient of distributions

-/

/-!

### B.1. The definition

-/

/-- The gradient of a distribution `(Space d) →d[ℝ] ℝ` as a distribution
  `(Space d) →d[ℝ] (EuclideanSpace ℝ (Fin d))`. -/
noncomputable def distGrad {d} :
    ((Space d) →d[ℝ] ℝ) →ₗ[ℝ] (Space d) →d[ℝ] (EuclideanSpace ℝ (Fin d)) where
  toFun f := {
    toFun := fun ε => WithLp.toLp 2 fun i => distDeriv i f ε
    map_add' := by
      intro ε1 ε2
      ext i
      simpa [add_comm, add_left_comm, add_assoc] using
        (distDeriv (M := ℝ) (d := d) i f).map_add ε1 ε2
    map_smul' := by
      intro a ε
      ext i
      simpa using (distDeriv (M := ℝ) (d := d) i f).map_smul a ε
  }
  map_add' := by
    intro f1 f2
    ext ε i
    simpa [Pi.add_apply] using
      congrArg (fun g : (Space d) →d[ℝ] ℝ => g ε)
        ((distDeriv (M := ℝ) (d := d) i).map_add f1 f2)
  map_smul' := by
    intro a f
    ext ε i
    simpa [Pi.smul_apply] using
      congrArg (fun g : (Space d) →d[ℝ] ℝ => g ε)
        ((distDeriv (M := ℝ) (d := d) i).map_smul a f)

/-!

### B.2. The gradient of inner products

-/

lemma distGrad_inner_eq {d} (f : (Space d) →d[ℝ] ℝ) (η : 𝓢(Space d, ℝ))
    (y : EuclideanSpace ℝ (Fin d)) : ⟪distGrad f η, y⟫_ℝ = ∑ i, y i * distDeriv i f η := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl ?_
  intro i _
  change ⟪((distDeriv i) f) η, y i⟫_ℝ = y i * ((distDeriv i) f) η
  change y i * ((distDeriv i) f) η = y i * ((distDeriv i) f) η
  rfl

lemma distGrad_eq_of_inner {d} (f : (Space d) →d[ℝ] ℝ)
    (g : (Space d) →d[ℝ] EuclideanSpace ℝ (Fin d))
    (h : ∀ η i, distDeriv i f η = ⟪g η, EuclideanSpace.single i 1⟫_ℝ) :
    distGrad f = g := by
  ext η i
  change distDeriv i f η = g η i
  have hi := h η i
  change distDeriv i f η =
    ∑ j, ⟪(g η) j, (EuclideanSpace.single i (1 : ℝ)) j⟫_ℝ at hi
  rw [Fintype.sum_eq_single i] at hi
  · change ((distDeriv i) f) η =
      (EuclideanSpace.single i (1 : ℝ)) i * (g η) i at hi
    simpa using hi
  · intro j hj
    simp [hj]

/-!

### B.3. The gradient as a sum over basis vectors

-/

lemma distGrad_eq_sum_basis {d} (f : (Space d) →d[ℝ] ℝ) (η : 𝓢(Space d, ℝ))
    (h_distGrad_eq_sum_basis :
      distGrad f η =
        ∑ i, - f ((SchwartzMap.evalCLM ℝ (Space d) ℝ (basis i))
          (SchwartzMap.fderivCLM ℝ (Space d) ℝ η)) •
        EuclideanSpace.single i 1) :
    distGrad f η =
      ∑ i, - f ((SchwartzMap.evalCLM ℝ (Space d) ℝ (basis i))
        (SchwartzMap.fderivCLM ℝ (Space d) ℝ η)) •
      EuclideanSpace.single i 1 := by
  exact h_distGrad_eq_sum_basis

/-!

### B.4. The underlying function of the gradient distribution

-/

lemma distGrad_toFun_eq_distDeriv {d} (f : (Space d) →d[ℝ] ℝ) :
    (distGrad f).toFun = fun ε => WithLp.toLp 2 fun i => distDeriv i f ε := by
  rfl

/-!

### B.5. The gradient applied to a Schwartz function

-/

lemma distGrad_apply {d} (f : (Space d) →d[ℝ] ℝ) (ε : 𝓢(Space d, ℝ)) :
    (distGrad f) ε = fun i => distDeriv i f ε := by
  ext i
  rfl

end Space
