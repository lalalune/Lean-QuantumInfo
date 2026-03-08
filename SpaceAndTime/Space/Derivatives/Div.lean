/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong, Joseph Tooby-Smith, Lode Vermeulen
-/
import SpaceAndTime.Space.Derivatives.Grad
/-!

# Divergence on Space

## i. Overview

In this module we define the divergence operator on functions and
distributions from `Space d` to `EuclideanSpace ℝ (Fin d)`, and prove various basic
properties about it.

## ii. Key results

- `div` : The divergence operator on functions from `Space d` to `EuclideanSpace ℝ (Fin d)`.
- `distDiv` : The divergence operator on distributions from `Space d` to `EuclideanSpace ℝ (Fin d)`.
- `distDiv_ofFunction` : The divergence of a distribution from a bounded function.

## iii. Table of contents

- A. The divergence on functions
  - A.1. The divergence on the zero function
  - A.2. The divergence on a constant function
  - A.3. The divergence distributes over addition
  - A.4. The divergence distributes over scalar multiplication
  - A.5. The divergence of a linear map is a linear map
- B. Divergence of distributions
  - B.1. Basic equalities
  - B.2. Divergence on distributions from bounded functions

## iv. References

-/

namespace Space

variable {W} [NormedAddCommGroup W] [NormedSpace ℝ W]

/-!

## A. The divergence on functions

-/

/-- The vector calculus operator `div`. -/
noncomputable def div {d} (f : Space d → EuclideanSpace ℝ (Fin d)) :
    Space d → ℝ := fun x =>
  -- get i-th component of `f`
  let fi i x := (f x) i
  -- derivative of i-th component in i-th coordinate
  -- ∂fᵢ/∂xⱼ
  let df i x := ∂[i] (fi i) x
  ∑ i, df i x

@[inherit_doc div]
macro (name := divNotation) "∇" "⬝" f:term:100 : term => `(div $f)

/-!

### A.1. The divergence on the zero function

-/

@[simp]
lemma div_zero : ∇ ⬝ (0 : Space d → EuclideanSpace ℝ (Fin d)) = 0 := by
  unfold div Space.deriv Finset.sum
  simp only [Pi.ofNat_apply, fderiv_fun_const, ContinuousLinearMap.zero_apply, Multiset.map_const',
    Finset.card_val, Finset.card_univ, Fintype.card_fin, Multiset.sum_replicate, smul_zero]
  rfl

/-!

### A.2. The divergence on a constant function

-/

@[simp]
lemma div_const : ∇ ⬝ (fun _ : Space d => v) = 0 := by
  unfold div Space.deriv Finset.sum
  simp only [fderiv_fun_const, Pi.ofNat_apply, ContinuousLinearMap.zero_apply, Multiset.map_const',
    Finset.card_val, Finset.card_univ, Fintype.card_fin, Multiset.sum_replicate, smul_zero]
  rfl

/-!

### A.3. The divergence distributes over addition

-/

lemma div_add (f1 f2 : Space d → EuclideanSpace ℝ (Fin d))
    (hf1 : Differentiable ℝ f1) (hf2 : Differentiable ℝ f2) :
    ∇ ⬝ (f1 + f2) = ∇ ⬝ f1 + ∇ ⬝ f2 := by
  unfold div
  simp only [Pi.add_apply]
  funext x
  simp only [Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  congr
  funext i
  simp [Space.deriv]
  rw [fderiv_fun_add]
  simp only [ContinuousLinearMap.add_apply]
  · fun_prop
  · fun_prop

/-!

### A.4. The divergence distributes over scalar multiplication

-/

lemma div_smul (f : Space d → EuclideanSpace ℝ (Fin d)) (k : ℝ)
    (hf : Differentiable ℝ f) :
    ∇ ⬝ (k • f) = k • ∇ ⬝ f := by
  unfold div
  simp only [Pi.smul_apply]
  funext x
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  congr
  funext i
  simp [Space.deriv]
  rw [fderiv_const_mul]
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul]
  · fun_prop

/-!

### A.5. The divergence of a linear map is a linear map

-/

lemma div_linear_map (f : W → Space 3 → EuclideanSpace ℝ (Fin 3))
    (hf : ∀ w, Differentiable ℝ (f w))
    (hf' : IsLinearMap ℝ f) :
    IsLinearMap ℝ (fun w => ∇ ⬝ (f w)) := by
  constructor
  · intro w w'
    rw [hf'.map_add]
    rw [div_add]
    repeat fun_prop
  · intros k w
    rw [hf'.map_smul]
    rw [div_smul]
    fun_prop

/-!

## B. Divergence of distributions

-/

open MeasureTheory SchwartzMap InnerProductSpace Distribution

/-- The divergence of a distribution `(Space d) →d[ℝ] (EuclideanSpace ℝ (Fin d))` as a distribution
  `(Space d) →d[ℝ] ℝ`. -/
noncomputable def distDiv {d} :
    ((Space d) →d[ℝ] (EuclideanSpace ℝ (Fin d))) →ₗ[ℝ] (Space d) →d[ℝ] ℝ where
  toFun f := ∑ i,
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).comp (distDeriv i f)
  map_add' f1 f2 := by
    ext η
    simp [Finset.sum_add_distrib]
  map_smul' a f := by
    ext η
    simp [Finset.mul_sum]

/-!

### B.1. Basic equalities

-/

lemma distDiv_apply_eq_sum_distDeriv {d}
    (f : (Space d) →d[ℝ] EuclideanSpace ℝ (Fin d)) (η : 𝓢(Space d, ℝ)) :
    distDiv f η = ∑ i, distDeriv i f η i := by
  simp [distDiv]
  exact Finset.sum_congr rfl (by intro i hi; rfl)

/-!

### B.2. Divergence on distributions from bounded functions

-/

/-- The divergence of a distribution from a bounded function. -/
lemma distDiv_ofFunction {dm1 : ℕ} {f : Space dm1.succ → EuclideanSpace ℝ (Fin dm1.succ)}
    {hf : IsDistBounded f} (η : 𝓢(Space dm1.succ, ℝ)) :
    distDiv (distOfFunction f hf) η =
    - ∫ x : Space dm1.succ, ⟪f x, Space.grad η x⟫_ℝ := by
  rw [distDiv_apply_eq_sum_distDeriv]
  simp [distDeriv, distOfFunction_apply, SchwartzMap.pderivCLM_apply, Space.grad, Space.deriv]
  calc
    ∑ i, (∫ y : Space dm1.succ, (fderiv ℝ (⇑η) y) (basis i) • f y) i
        = ∑ i, ∫ y : Space dm1.succ, (fderiv ℝ (⇑η) y) (basis i) * f y i := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          let proji : EuclideanSpace ℝ (Fin dm1.succ) →L[ℝ] ℝ :=
            ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin dm1.succ => ℝ) i
          change proji (∫ y : Space dm1.succ, (fderiv ℝ (⇑η) y) (basis i) • f y)
            = ∫ y : Space dm1.succ, (fderiv ℝ (⇑η) y) (basis i) * f y i
          rw [← proji.integral_comp_comm
            (φ := fun y : Space dm1.succ => (fderiv ℝ (⇑η) y) (basis i) • f y)
            (hf.integrable_space_fderiv η (basis i))]
          refine integral_congr_ae ?_
          exact Filter.Eventually.of_forall (fun y => by
            change ((fderiv ℝ (⇑η) y) (basis i) • f y) i =
              (fderiv ℝ (⇑η) y) (basis i) * f y i
            simp [smul_eq_mul])
    _ = ∫ y : Space dm1.succ, ∑ i, (fderiv ℝ (⇑η) y) (basis i) * f y i := by
          rw [← integral_finset_sum (s := Finset.univ)
            (f := fun i : Fin dm1.succ => fun y : Space dm1.succ =>
              (fderiv ℝ (⇑η) y) (basis i) * f y i)]
          intro i hi
          exact (hf.pi_comp i).integrable_space_fderiv_mul η (basis i)
    _ = ∫ y : Space dm1.succ, ⟪f y, WithLp.toLp 2 fun i => (fderiv ℝ (⇑η) y) (basis i)⟫_ℝ := by
          refine integral_congr_ae ?_
          exact Filter.Eventually.of_forall (fun y => by simp [PiLp.inner_apply, mul_comm])

end Space
