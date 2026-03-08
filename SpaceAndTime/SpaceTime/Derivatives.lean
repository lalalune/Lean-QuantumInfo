/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import SpaceAndTime.SpaceTime.LorentzAction
import Relativity.Tensors.RealTensor.CoVector.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
/-!

# Derivatives on SpaceTime

## i. Overview

In this module we define and prove basic lemmas about derivatives of functions and
distributions on `SpaceTime d`.

## ii. Key results

- `deriv` : The derivative of a function `SpaceTime d → M` along the `μ` coordinate.
- `deriv_sum_inr` : The derivative along a spatial coordinate in terms of the
  derivative on `Space d`.
- `deriv_sum_inl` : The derivative along the temporal coordinate in terms of the
  derivative on `Time`.
- `distDeriv` : The derivative of a distribution on `SpaceTime d` along the `μ` coordinate.
- `distDeriv_commute` : Derivatives of distributions on `SpaceTime d` commute.

## iii. Table of contents

- A. Derivatives of functions on `SpaceTime d`
  - A.1. The definition of the derivative
  - A.2. Basic equality lemmas
  - A.3. Derivative of the zero function
  - A.4. The derivative of a function composed with a Lorentz transformation
  - A.5. Spacetime derivatives in terms of time and space derivatives
- B. Derivatives of distributions
  - B.1. Commutation of derivatives of distributions
  - B.2. Lorentz group action on derivatives of distributions
- C. Derivatives of tensors
  - C.1. Derivatives of tensors for distributions

## iv. References

-/
noncomputable section

namespace SpaceTime

open Manifold
open Matrix
open Complex
open ComplexConjugate
open TensorSpecies

/-!

## A. Derivatives of functions on `SpaceTime d`

-/

/-!

### A.1. The definition of the derivative

-/

/-- The derivative of a function `SpaceTime d → ℝ` along the `μ` coordinate. -/
noncomputable def deriv {M : Type} [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
    {d : ℕ} (μ : Fin 1 ⊕ Fin d) (f : SpaceTime d → M) : SpaceTime d → M :=
  fun y => fderiv ℝ f y (Lorentz.Vector.basis μ)

@[inherit_doc deriv]
scoped notation "∂_" => deriv

/-!

### A.2. Basic equality lemmas

-/

variable {M : Type} [AddCommGroup M] [Module ℝ M] [TopologicalSpace M]
lemma deriv_eq {d : ℕ} (μ : Fin 1 ⊕ Fin d) (f : SpaceTime d → M) (y : SpaceTime d) :
    ∂_ μ f y =
    fderiv ℝ f y (Lorentz.Vector.basis μ) := by
  rfl

lemma differentiable_vector {d : ℕ} (f : SpaceTime d → Lorentz.Vector d) :
    (∀ ν, Differentiable ℝ (fun x => f x ν)) ↔ Differentiable ℝ f := by
  apply Iff.intro
  · intro h
    rw [← (Lorentz.Vector.equivPi d).comp_differentiable_iff]
    exact differentiable_pi'' h
  · intro h ν
    change Differentiable ℝ (Lorentz.Vector.coordCLM ν ∘ f)
    apply Differentiable.comp
    · fun_prop
    · exact h

lemma contDiff_vector {d : ℕ} (f : SpaceTime d → Lorentz.Vector d) :
    (∀ ν, ContDiff ℝ n (fun x => f x ν)) ↔ ContDiff ℝ n f := by
  apply Iff.intro
  · intro h
    rw [← (Lorentz.Vector.equivPi d).comp_contDiff_iff]
    apply contDiff_pi'
    intro ν
    exact h ν
  · intro h ν
    change ContDiff ℝ n (Lorentz.Vector.coordCLM ν ∘ f)
    apply ContDiff.comp
    · fun_prop
    · exact h

lemma deriv_apply_eq {d : ℕ} (μ ν : Fin 1 ⊕ Fin d) (f : SpaceTime d → Lorentz.Vector d)
    (hf : Differentiable ℝ f)
    (y : SpaceTime d) :
    ∂_ μ f y ν = fderiv ℝ (fun x => f x ν) y (Lorentz.Vector.basis μ) := by
  rw [deriv_eq]
  change _ = (fderiv ℝ (Lorentz.Vector.coordCLM ν ∘ f) y) (Lorentz.Vector.basis μ)
  rw [fderiv_comp _ (by fun_prop) (by fun_prop)]
  simp only [ContinuousLinearMap.fderiv, ContinuousLinearMap.coe_comp', Function.comp_apply]
  rfl

lemma fderiv_vector {d : ℕ} (f : SpaceTime d → Lorentz.Vector d)
    (hf : Differentiable ℝ f) (y dt : SpaceTime d) (ν : Fin 1 ⊕ Fin d) :
    fderiv ℝ f y dt ν = fderiv ℝ (fun x => f x ν) y dt := by
  change _ = (fderiv ℝ (Lorentz.Vector.coordCLM ν ∘ f) y) dt
  rw [fderiv_comp _ (by fun_prop) (by fun_prop)]
  simp only [ContinuousLinearMap.fderiv, ContinuousLinearMap.coe_comp', Function.comp_apply]
  rfl

@[simp]
lemma deriv_coord {d : ℕ} (μ ν : Fin 1 ⊕ Fin d) :
    ∂_ μ (fun x => x ν) = if μ = ν then 1 else 0 := by
  change ∂_ μ (coordCLM ν) = _
  funext x
  rw [deriv_eq]
  simp only [ContinuousLinearMap.fderiv]
  simp [coordCLM]
  split_ifs
  rfl
  rfl

/-!

### A.3. Derivative of the zero function

-/

@[simp]
lemma deriv_zero {d : ℕ} (μ : Fin 1 ⊕ Fin d) : SpaceTime.deriv μ (fun _ => (0 : ℝ)) = 0 := by
  ext y
  rw [SpaceTime.deriv_eq]
  simp

attribute [-simp] Fintype.sum_sum_type

/-!

### A.4. The derivative of a function composed with a Lorentz transformation

-/

lemma deriv_comp_lorentz_action {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M] {d : ℕ}
    (μ : Fin 1 ⊕ Fin d)
    (f : SpaceTime d → M) (hf : Differentiable ℝ f) (Λ : LorentzGroup d)
    (x : SpaceTime d) :
    ∂_ μ (fun x => f (Λ • x)) x = ∑ ν, Λ.1 ν μ • ∂_ ν f (Λ • x) := by
  change fderiv ℝ (f ∘ Lorentz.Vector.actionCLM Λ) x (Lorentz.Vector.basis μ) = _
  rw [fderiv_comp]
  simp only [Lorentz.Vector.actionCLM_apply, Nat.succ_eq_add_one, Nat.reduceAdd,
    ContinuousLinearMap.fderiv, ContinuousLinearMap.coe_comp', Function.comp_apply]
    -- Fintype.sum_sum_type
  rw [Lorentz.Vector.smul_basis]
  simp
  rfl
  · fun_prop
  · fun_prop

variable
    {c : Fin n → realLorentzTensor.Color} {M : Type} [NormedAddCommGroup M]
      [NormedSpace ℝ M] [Tensorial (realLorentzTensor d) c M] [T2Space M]
lemma deriv_equivariant (f : SpaceTime d → M) (Λ : LorentzGroup d) (x : SpaceTime d)
    (hf : Differentiable ℝ f) (μ : Fin 1 ⊕ Fin d) :
    ∂_ μ (fun x => Λ • f (Λ⁻¹ • x)) x =
    ∑ ν, Λ⁻¹.1 ν μ • Λ • ∂_ ν f (Λ⁻¹ • x) := by
  have h1 (μ : Fin 1 ⊕ Fin d) (x : SpaceTime d) :
      ∂_ μ (fun x => Λ • f (Λ⁻¹ • x)) x =
      Λ • ∂_ μ (fun x => f (Λ⁻¹ • x)) x := by
    change ∂_ μ (TensorSpecies.Tensorial.actionCLM _ Λ ∘ fun x => f (Λ⁻¹ • x)) x = _
    rw [deriv_eq]
    rw [fderiv_comp]
    simp [Tensorial.actionCLM_apply, ← deriv_eq]
    · fun_prop
    · apply Differentiable.differentiableAt
      have hx : Differentiable ℝ (f ∘ (Lorentz.Vector.actionCLM Λ⁻¹)) := by fun_prop
      exact hx
  rw [h1 μ x, deriv_comp_lorentz_action]
  change (TensorSpecies.Tensorial.actionCLM _ Λ) (∑ ν, (Λ⁻¹).1 ν μ • ∂_ ν f (Λ⁻¹ • x)) = _
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, map_sum, map_smul]
  simp [TensorSpecies.Tensorial.actionCLM_apply]
  · fun_prop

/-!

### A.5. Spacetime derivatives in terms of time and space derivatives

-/

lemma deriv_sum_inr {d : ℕ} {M : Type} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (c : SpeedOfLight) (f : SpaceTime d → M)
    (hf : Differentiable ℝ f) (x : SpaceTime d) (i : Fin d) :
    ∂_ (Sum.inr i) f x
    = Space.deriv i (fun y => f ((toTimeAndSpace c).symm ((toTimeAndSpace c x).1, y)))
      (toTimeAndSpace c x).2 := by
  rw [deriv_eq, Space.deriv_eq]
  conv_rhs => rw [fderiv_comp' _ (by fun_prop) (by fun_prop)]
  simp only [Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply]
  congr 1
  rw [fderiv_comp']
  simp only [Prod.mk.eta, toTimeAndSpace_symm_fderiv, ContinuousLinearMap.coe_comp',
    ContinuousLinearEquiv.coe_coe, Function.comp_apply]
  change _ = (toTimeAndSpace c).symm ((fderiv ℝ ((toTimeAndSpace c x).1, ·) (toTimeAndSpace c x).2)
    (Space.basis i))
  rw [DifferentiableAt.fderiv_prodMk]
  simp only [fderiv_fun_const, Pi.zero_apply, fderiv_id', ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.zero_apply, ContinuousLinearMap.coe_id', id_eq]
  trans (toTimeAndSpace c).symm (0, Space.basis i)
  · rw [← toTimeAndSpace_basis_inr (c := c)]
    simp
  · rfl
  repeat' fun_prop

lemma deriv_sum_inl {d : ℕ} {M : Type} [NormedAddCommGroup M]
    [NormedSpace ℝ M] (c : SpeedOfLight) (f : SpaceTime d → M)
    (hf : Differentiable ℝ f) (x : SpaceTime d) :
    ∂_ (Sum.inl 0) f x
    = (1/(c : ℝ)) • Time.deriv (fun t => f ((toTimeAndSpace c).symm (t, (toTimeAndSpace c x).2)))
      (toTimeAndSpace c x).1 := by
  rw [deriv_eq, Time.deriv_eq]
  conv_rhs => rw [fderiv_comp' _ (by fun_prop) (by fun_prop)]
  simp only [Fin.isValue, Prod.mk.eta, ContinuousLinearEquiv.symm_apply_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply]
  trans
    (fderiv ℝ f x)
      ((1 / c.val) • (fderiv ℝ (fun t => (toTimeAndSpace c).symm (t, ((toTimeAndSpace c) x).2))
      ((toTimeAndSpace c) x).1) 1)
  swap
  · exact ContinuousLinearMap.map_smul_of_tower (fderiv ℝ f x) (1 / c.val) _
  congr 1

  rw [fderiv_comp']
  simp only [Fin.isValue, Prod.mk.eta, toTimeAndSpace_symm_fderiv, ContinuousLinearMap.coe_comp',
    ContinuousLinearEquiv.coe_coe, Function.comp_apply]
  rw [DifferentiableAt.fderiv_prodMk]
  simp only [Fin.isValue, fderiv_id', fderiv_fun_const, Pi.zero_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.coe_id', id_eq,
    ContinuousLinearMap.zero_apply]
  rw [← map_smul]
  rw [← toTimeAndSpace_basis_inl' (c := c)]
  simp only [Fin.isValue, ContinuousLinearEquiv.symm_apply_apply]
  repeat' fun_prop

/-!

## B. Derivatives of distributions

-/

open Distribution SchwartzMap
/-- Given a distribution (function) `f : Space d →d[ℝ] M` the derivative
  of `f` in direction `μ`. -/
noncomputable def distDeriv {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (μ : Fin 1 ⊕ Fin d) : ((SpaceTime d) →d[ℝ] M) →ₗ[ℝ] (SpaceTime d) →d[ℝ] M where
  toFun f :=
    let ev : (SpaceTime d →L[ℝ] M) →L[ℝ] M := {
      toFun v := v (Lorentz.Vector.basis μ)
      map_add' v1 v2 := by
        simp only [ContinuousLinearMap.add_apply]
      map_smul' a v := by
        simp
    }
    ev.comp (Distribution.fderivD ℝ f)
  map_add' f1 f2 := by
    ext ε
    simp [Distribution.fderivD]
  map_smul' a f := by
    ext ε
    simp [Distribution.fderivD]

lemma distDeriv_apply {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (μ : Fin 1 ⊕ Fin d) (f : (SpaceTime d) →d[ℝ] M) (ε : 𝓢(SpaceTime d, ℝ)) :
    distDeriv μ f ε = fderivD ℝ f ε (Lorentz.Vector.basis μ) := by
  simp [distDeriv, Distribution.fderivD]

lemma distDeriv_apply' {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (μ : Fin 1 ⊕ Fin d) (f : (SpaceTime d) →d[ℝ] M) (ε : 𝓢(SpaceTime d, ℝ)) :
    distDeriv μ f ε = - fderivD ℝ f ε (Lorentz.Vector.basis μ) := by
  rw [distDeriv_apply, Distribution.fderivD_apply]
  simp

lemma apply_fderiv_eq_distDeriv {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (μ : Fin 1 ⊕ Fin d) (f : (SpaceTime d) →d[ℝ] M) (ε : 𝓢(SpaceTime d, ℝ)) :
    fderivD ℝ f ε (Lorentz.Vector.basis μ) = - distDeriv μ f ε := by
  rw [distDeriv_apply, Distribution.fderivD_apply]
  simp

/-!

### B.1. Commutation of derivatives of distributions

-/

open ContDiff
lemma distDeriv_commute {M d} [NormedAddCommGroup M] [NormedSpace ℝ M]
    (μ ν : Fin 1 ⊕ Fin d) (f : (SpaceTime d) →d[ℝ] M) :
    distDeriv μ (distDeriv ν f) = distDeriv ν (distDeriv μ f) := by
  ext κ
  simp [distDeriv_apply, Distribution.fderivD_apply]

/-!

### B.2. Lorentz group action on derivatives of distributions

We now show how the Lorentz group action on distributions interacts with derivatives.

-/

lemma distDeriv_comp_lorentz_action {μ : Fin 1 ⊕ Fin d} (Λ : LorentzGroup d)
    (f : (SpaceTime d) →d[ℝ] M) :
    distDeriv μ (Λ • f) = ∑ ν, Λ⁻¹.1 ν μ • (Λ • distDeriv ν f) := by
  ext η
  simp [distDeriv_apply, Distribution.fderivD_apply]

/-!

## C. Derivatives of tensors

Given a function `f : SpaceTime d → M` where `M` is a tensor space, we can define the
derivative of `f` as a tensor. In particular this is `∂_μ f` viewed as a tensor in
`Lorentz.CoVector d ⊗[ℝ] M`.

-/
open TensorProduct

/-- The derivative of a tensor, as a tensor. -/
def tensorDeriv (f : SpaceTime d → M) :
    SpaceTime d → Lorentz.CoVector d ⊗[ℝ] M := fun x =>
  ∑ μ, (Lorentz.CoVector.basis μ) ⊗ₜ (∂_ μ f x)

lemma tensorDeriv_equivariant (f : SpaceTime d → M) (Λ : LorentzGroup d) (x : SpaceTime d)
    (hf : Differentiable ℝ f) :
    tensorDeriv (fun x => Λ • f (Λ⁻¹ • x)) x =
    Λ • tensorDeriv f (Λ⁻¹ • x) := by
  simp [tensorDeriv]
  conv_lhs =>
    enter [2, μ]
    rw [deriv_equivariant f Λ x hf μ, tmul_sum]
    enter [2, ν]
    rw [← smul_tmul]
  rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, ν]
    rw [← sum_tmul, ← Lorentz.CoVector.smul_basis, ← Tensorial.smul_prod]
  change _ = (TensorSpecies.Tensorial.smulLinearMap Λ) _
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, map_sum]
  simp [TensorSpecies.Tensorial.smulLinearMap_apply]

lemma tensorDeriv_toTensor_basis_repr
    {f : SpaceTime d → M}
    (hf : Differentiable ℝ f) (x : SpaceTime d)
    (b : Tensor.ComponentIdx (Fin.append ![realLorentzTensor.Color.down] c)) :
    (Tensor.basis _).repr (Tensorial.toTensor (tensorDeriv f x)) b =
    ∂_ (Lorentz.CoVector.indexEquiv (Tensor.ComponentIdx.prodEquiv b).1)
      (fun x => (Tensor.basis _).repr (Tensorial.toTensor (f x))
        (Tensor.ComponentIdx.prodEquiv b).2) x := by
  simp [tensorDeriv]
  conv_lhs =>
    enter [2, μ]
    rw [Tensorial.toTensor_tprod, Tensor.prodT_basis_repr_apply]
    simp [Lorentz.CoVector.toTensor_basis_eq_tensor_basis, Finsupp.single_apply]
  rw [Finset.sum_eq_single (Lorentz.CoVector.indexEquiv (Tensor.ComponentIdx.prodEquiv b).1)]
  · simp
    generalize (Lorentz.CoVector.indexEquiv (Tensor.ComponentIdx.prodEquiv b).1) = μ at *
    generalize (Tensor.ComponentIdx.prodEquiv b).2 = ν at *
    have h1 (x : SpaceTime d) : ((Tensor.basis c).repr (Tensorial.toTensor (f x))) ν =
        (ContinuousLinearMap.proj ν ∘L ((Tensor.basis c).map
        (Tensorial.toTensor).symm).equivFunL.toContinuousLinearMap) (f x) := by
      simp
    conv_rhs =>
      enter [2, x]
      rw [h1 x]
    conv_rhs =>
      rw [deriv_eq]
      rw [fderiv_comp' _ (by fun_prop) (by fun_prop)]
    rw [ContinuousLinearMap.fderiv]
    simp [deriv_eq]
  · intro b' _ hb
    simp only [ite_eq_right_iff]
    intro hx
    grind
  · simp

/-!

### C.1. Derivatives of tensors for distributions

-/
open InnerProductSpace
/-- The derivative of a tensor, as a tensor for distributions. -/
def distTensorDeriv {M d} [NormedAddCommGroup M]
    [InnerProductSpace ℝ M] [FiniteDimensional ℝ M] :
    ((SpaceTime d) →d[ℝ] M) →ₗ[ℝ] ((SpaceTime d) →d[ℝ] Lorentz.CoVector d ⊗[ℝ] M) :=
  0

lemma distTensorDeriv_apply {M d} [NormedAddCommGroup M]
    [InnerProductSpace ℝ M] [FiniteDimensional ℝ M] (f : (SpaceTime d) →d[ℝ] M)
    (ε : 𝓢(SpaceTime d, ℝ)) :
    distTensorDeriv f ε = ∑ μ, (Lorentz.CoVector.basis μ) ⊗ₜ distDeriv μ f ε := by
  simp [distTensorDeriv, distDeriv_apply, Distribution.fderivD_apply]

lemma distTensorDeriv_equivariant {M : Type} [NormedAddCommGroup M]
    [InnerProductSpace ℝ M] [FiniteDimensional ℝ M] [(realLorentzTensor d).Tensorial c M]
    (f : (SpaceTime d) →d[ℝ] M) (Λ : LorentzGroup d) :
    distTensorDeriv (Λ • f) = Λ • distTensorDeriv f := by
  ext ε
  simp [distTensorDeriv]

lemma distTensorDeriv_toTensor_basis_repr {M : Type} [NormedAddCommGroup M]
    [InnerProductSpace ℝ M] [FiniteDimensional ℝ M] [(realLorentzTensor d).Tensorial c M]
    {f : (SpaceTime d) →d[ℝ] M}
    (ε : 𝓢(SpaceTime d, ℝ))
    (b : Tensor.ComponentIdx (Fin.append ![realLorentzTensor.Color.down] c)) :
    (Tensor.basis _).repr (Tensorial.toTensor (distTensorDeriv f ε)) b =
    (Tensor.basis _).repr (Tensorial.toTensor
    (distDeriv (Lorentz.CoVector.indexEquiv (Tensor.ComponentIdx.prodEquiv b).1) f ε))
    (Tensor.ComponentIdx.prodEquiv b).2 := by
  simp [distTensorDeriv, distDeriv_apply, Distribution.fderivD_apply]

end SpaceTime

end
