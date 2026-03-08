/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong, Joseph Tooby-Smith, Lode Vermeulen
-/
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import SpaceAndTime.Space.Derivatives.Laplacian
set_option maxHeartbeats 800000
/-!

# Curl on Space

## i. Overview

In this module we define the curl of functions and distributions on 3-dimensional
space `Space 3`.

We also prove some basic vector-identities involving of the curl operator.

## ii. Key results

- `curl` : The curl operator on functions from `Space 3` to `EuclideanSpace ℝ (Fin 3)`.
- `distCurl` : The curl operator on distributions from `Space 3` to `EuclideanSpace ℝ (Fin 3)`.
- `div_of_curl_eq_zero` : The divergence of the curl of a function is zero.
- `distCurl_distGrad_eq_zero` : The curl of the gradient of a distribution is zero.

## iii. Table of contents

- A. The curl on functions
  - A.1. The curl on the zero function
  - A.2. The curl on a constant function
  - A.3. The curl distributes over addition
  - A.4. The curl distributes over scalar multiplication
  - A.5. The curl of a linear map is a linear map
  - A.6. Preliminary lemmas about second derivatives
  - A.7. The div of a curl is zero
  - A.8. The curl of a curl
- B. The curl on distributions
  - B.1. The components of the curl
  - B.2. Basic equalities
  - B.3. The curl of a grad is zero

## iv. References

-/

namespace Space

/-!

## A. The curl on functions

-/

/-- The vector calculus operator `curl`. -/
noncomputable def curl (f : Space → EuclideanSpace ℝ (Fin 3)) :
    Space → EuclideanSpace ℝ (Fin 3) := fun x =>
  -- get i-th component of `f`
  let fi i x := (f x) i
  -- derivative of i-th component in j-th coordinate
  -- ∂fᵢ/∂xⱼ
  let df i j x := ∂[j] (fi i) x
  WithLp.toLp 2 fun i =>
    match i with
    | 0 => df 2 1 x - df 1 2 x
    | 1 => df 0 2 x - df 2 0 x
    | 2 => df 1 0 x - df 0 1 x

@[inherit_doc curl]
macro (name := curlNotation) "∇" "×" f:term:100 : term => `(curl $f)

/-!

### A.1. The curl on the zero function

-/

@[simp]
lemma curl_zero : ∇ × (0 : Space → EuclideanSpace ℝ (Fin 3)) = 0 := by
  unfold curl Space.deriv
  simp only [Fin.isValue, Pi.ofNat_apply, fderiv_fun_const, ContinuousLinearMap.zero_apply,
    sub_self]
  ext x i
  fin_cases i <;>
  rfl

/-!

### A.2. The curl on a constant function

-/

@[simp]
lemma curl_const : ∇ × (fun _ : Space => v₃) = 0 := by
  unfold curl Space.deriv
  simp only [Fin.isValue, fderiv_fun_const, Pi.ofNat_apply, ContinuousLinearMap.zero_apply,
    sub_self]
  ext x i
  fin_cases i <;>
  rfl

/-- Curl component 0: (∇×f)_0 = ∂[1]f_2 - ∂[2]f_1 -/
lemma curl_component_zero (f : Space → EuclideanSpace ℝ (Fin 3)) (x : Space) :
    (∇ × f) x 0 = ∂[1] (fun x => f x 2) x - ∂[2] (fun x => f x 1) x := by
  unfold curl; simp only [PiLp.toLp_apply, Fin.isValue]

/-- Curl component 1: (∇×f)_1 = ∂[2]f_0 - ∂[0]f_2 -/
lemma curl_component_one (f : Space → EuclideanSpace ℝ (Fin 3)) (x : Space) :
    (∇ × f) x 1 = ∂[2] (fun x => f x 0) x - ∂[0] (fun x => f x 2) x := by
  unfold curl; simp only [PiLp.toLp_apply, Fin.isValue]

/-- Curl component 2: (∇×f)_2 = ∂[0]f_1 - ∂[1]f_0 -/
lemma curl_component_two (f : Space → EuclideanSpace ℝ (Fin 3)) (x : Space) :
    (∇ × f) x 2 = ∂[0] (fun x => f x 1) x - ∂[1] (fun x => f x 0) x := by
  unfold curl; simp only [PiLp.toLp_apply, Fin.isValue]

/-!

### A.3. The curl distributes over addition

-/

lemma curl_add (f1 f2 : Space → EuclideanSpace ℝ (Fin 3))
    (hf1 : Differentiable ℝ f1) (hf2 : Differentiable ℝ f2) :
    ∇ × (f1 + f2) = ∇ × f1 + ∇ × f2 := by
  ext x i
  fin_cases i
  · have h21 := congrArg (fun g => g x)
      (deriv_coord_add (d := 3) (u := 1) (i := 2) f1 f2 hf1 hf2)
    have h12 := congrArg (fun g => g x)
      (deriv_coord_add (d := 3) (u := 2) (i := 1) f1 f2 hf1 hf2)
    simp [curl, Pi.add_apply, h21, h12, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  · have h02 := congrArg (fun g => g x)
      (deriv_coord_add (d := 3) (u := 2) (i := 0) f1 f2 hf1 hf2)
    have h20 := congrArg (fun g => g x)
      (deriv_coord_add (d := 3) (u := 0) (i := 2) f1 f2 hf1 hf2)
    simp [curl, Pi.add_apply, h02, h20, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  · have h10 := congrArg (fun g => g x)
      (deriv_coord_add (d := 3) (u := 0) (i := 1) f1 f2 hf1 hf2)
    have h01 := congrArg (fun g => g x)
      (deriv_coord_add (d := 3) (u := 1) (i := 0) f1 f2 hf1 hf2)
    simp [curl, Pi.add_apply, h10, h01, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-!

### A.4. The curl distributes over scalar multiplication

-/

lemma curl_smul (f : Space → EuclideanSpace ℝ (Fin 3)) (k : ℝ)
    (hf : Differentiable ℝ f) :
    ∇ × (k • f) = k • ∇ × f := by
  ext x i
  fin_cases i
  · have h21 := deriv_coord_smul (d := 3) (u := 1) (i := 2) (f := f) (k := k) hf (x := x)
    have h12 := deriv_coord_smul (d := 3) (u := 2) (i := 1) (f := f) (k := k) hf (x := x)
    simp [curl, Pi.smul_apply, h21, h12, sub_eq_add_neg, add_comm]
    ring
  · have h02 := deriv_coord_smul (d := 3) (u := 2) (i := 0) (f := f) (k := k) hf (x := x)
    have h20 := deriv_coord_smul (d := 3) (u := 0) (i := 2) (f := f) (k := k) hf (x := x)
    simp [curl, Pi.smul_apply, h02, h20, sub_eq_add_neg, add_comm]
    ring
  · have h10 := deriv_coord_smul (d := 3) (u := 0) (i := 1) (f := f) (k := k) hf (x := x)
    have h01 := deriv_coord_smul (d := 3) (u := 1) (i := 0) (f := f) (k := k) hf (x := x)
    simp [curl, Pi.smul_apply, h10, h01, sub_eq_add_neg, add_comm]
    ring

/-!

### A.5. The curl of a linear map is a linear map

-/

variable {W} [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma curl_linear_map (f : W → Space 3 → EuclideanSpace ℝ (Fin 3))
    (hf : ∀ w, Differentiable ℝ (f w))
    (hf' : IsLinearMap ℝ f) :
    IsLinearMap ℝ (fun w => ∇ × (f w)) := by
  constructor
  · intro w₁ w₂
    simpa [hf'.map_add] using
      (curl_add (f1 := f w₁) (f2 := f w₂) (hf1 := hf w₁) (hf2 := hf w₂))
  · intro a w
    simpa [hf'.map_smul] using
      (curl_smul (f := f w) (k := a) (hf := hf w))

/-!

### A.6. Preliminary lemmas about second derivatives

-/

private lemma differentiable_coord_deriv
    (f : Space → EuclideanSpace ℝ (Fin 3)) (hf : ContDiff ℝ 2 f) (u i : Fin 3) :
    Differentiable ℝ (fun x => ∂[u] (fun y => f y i) x) := by
  intro x
  have hfi : ContDiff ℝ 2 (fun y => f y i) := by fun_prop
  have hfdiff : DifferentiableAt ℝ (fderiv ℝ (fun y => f y i)) x := by
    exact (((hfi.contDiffAt).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
  have hconst : DifferentiableAt ℝ (fun _ : Space => basis u) x := by
    simp
  simpa [Space.deriv] using
    (DifferentiableAt.clm_apply (c := fun y => fderiv ℝ (fun z => f z i) y)
      (u := fun _ : Space => basis u) hfdiff hconst)

/-- Second derivatives distribute coordinate-wise over addition (all three components for div). -/
lemma deriv_coord_2nd_add (f : Space → EuclideanSpace ℝ (Fin 3)) (hf : ContDiff ℝ 2 f) :
    ∂[i] (fun x => ∂[u] (fun x => f x u) x + (∂[v] (fun x => f x v) x + ∂[w] (fun x => f x w) x)) =
    (∂[i] (∂[u] (fun x => f x u))) + (∂[i] (∂[v] (fun x => f x v))) +
    (∂[i] (∂[w] (fun x => f x w))) := by
  let A : Space → ℝ := fun x => ∂[u] (fun y => f y u) x
  let B : Space → ℝ := fun x => ∂[v] (fun y => f y v) x
  let C : Space → ℝ := fun x => ∂[w] (fun y => f y w) x
  have hAB : ∂[i] (fun x => A x + (B x + C x))
      = ∂[i] A + ∂[i] (fun x => B x + C x) := by
    exact deriv_add (d := 3) (u := i) (f1 := A) (f2 := fun x => B x + C x)
      (differentiable_coord_deriv f hf u u) (Differentiable.add
        (differentiable_coord_deriv f hf v v) (differentiable_coord_deriv f hf w w))
  have hBC : ∂[i] (fun x => B x + C x) = ∂[i] B + ∂[i] C := by
    exact deriv_add (d := 3) (u := i) (f1 := B) (f2 := C)
      (differentiable_coord_deriv f hf v v) (differentiable_coord_deriv f hf w w)
  calc
    ∂[i] (fun x => ∂[u] (fun x => f x u) x + (∂[v] (fun x => f x v) x + ∂[w] (fun x => f x w) x))
        = ∂[i] (fun x => A x + (B x + C x)) := by rfl
    _ = ∂[i] A + ∂[i] (fun x => B x + C x) := hAB
    _ = ∂[i] A + (∂[i] B + ∂[i] C) := by rw [hBC]
    _ = (∂[i] A) + (∂[i] B) + (∂[i] C) := by abel
    _ = (∂[i] (∂[u] (fun x => f x u))) + (∂[i] (∂[v] (fun x => f x v)))
          + (∂[i] (∂[w] (fun x => f x w))) := by rfl

/-- Second derivatives distribute coordinate-wise over subtraction (two components for curl). -/
lemma deriv_coord_2nd_sub (f : Space → EuclideanSpace ℝ (Fin 3)) (hf : ContDiff ℝ 2 f) :
    ∂[u] (fun x => ∂[v] (fun x => f x w) x - ∂[w] (fun x => f x v) x) =
    (∂[u] (∂[v] (fun x => f x w))) - (∂[u] (∂[w] (fun x => f x v))) := by
  let A : Space → ℝ := fun x => ∂[v] (fun y => f y w) x
  let B : Space → ℝ := fun x => ∂[w] (fun y => f y v) x
  have hAB : ∂[u] (fun x => A x - B x) = ∂[u] A - ∂[u] B := by
    exact deriv_sub (d := 3) (u := u) (f1 := A) (f2 := B)
      (differentiable_coord_deriv f hf v w) (differentiable_coord_deriv f hf w v)
  simpa [A, B] using hAB

/-!

### A.7. The div of a curl is zero

-/

lemma div_of_curl_eq_zero (f : Space → EuclideanSpace ℝ (Fin 3)) (hf : ContDiff ℝ 2 f) :
    ∇ ⬝ (∇ × f) = 0 := by
  funext x
  let A0 : Space → ℝ := fun y => ∂[1] (fun z => f z 2) y
  let B0 : Space → ℝ := fun y => ∂[2] (fun z => f z 1) y
  let A1 : Space → ℝ := fun y => ∂[2] (fun z => f z 0) y
  let B1 : Space → ℝ := fun y => ∂[0] (fun z => f z 2) y
  let A2 : Space → ℝ := fun y => ∂[0] (fun z => f z 1) y
  let B2 : Space → ℝ := fun y => ∂[1] (fun z => f z 0) y
  have hsub0 : (∂[0] (fun y => A0 y - B0 y)) x = (∂[0] A0) x - (∂[0] B0) x := by
    simpa [A0, B0] using congrArg (fun g => g x)
      (deriv_sub (d := 3) (u := 0) (f1 := A0) (f2 := B0)
        (differentiable_coord_deriv f hf 1 2) (differentiable_coord_deriv f hf 2 1))
  have hsub1 : (∂[1] (fun y => A1 y - B1 y)) x = (∂[1] A1) x - (∂[1] B1) x := by
    simpa [A1, B1] using congrArg (fun g => g x)
      (deriv_sub (d := 3) (u := 1) (f1 := A1) (f2 := B1)
        (differentiable_coord_deriv f hf 2 0) (differentiable_coord_deriv f hf 0 2))
  have hsub2 : (∂[2] (fun y => A2 y - B2 y)) x = (∂[2] A2) x - (∂[2] B2) x := by
    simpa [A2, B2] using congrArg (fun g => g x)
      (deriv_sub (d := 3) (u := 2) (f1 := A2) (f2 := B2)
        (differentiable_coord_deriv f hf 0 1) (differentiable_coord_deriv f hf 1 0))
  have h_f0 : ContDiff ℝ 2 (fun y => f y 0) := by fun_prop
  have h_f1 : ContDiff ℝ 2 (fun y => f y 1) := by fun_prop
  have h_f2 : ContDiff ℝ 2 (fun y => f y 2) := by fun_prop
  have h_comm_01_f2 :
      (∂[0] (∂[1] (fun y => f y 2))) x = (∂[1] (∂[0] (fun y => f y 2))) x := by
    simpa using congrArg (fun g => g x)
      (deriv_commute (d := 3) (u := 0) (v := 1) (f := fun y => f y 2) h_f2)
  have h_comm_02_f1 :
      (∂[0] (∂[2] (fun y => f y 1))) x = (∂[2] (∂[0] (fun y => f y 1))) x := by
    simpa using congrArg (fun g => g x)
      (deriv_commute (d := 3) (u := 0) (v := 2) (f := fun y => f y 1) h_f1)
  have h_comm_12_f0 :
      (∂[1] (∂[2] (fun y => f y 0))) x = (∂[2] (∂[1] (fun y => f y 0))) x := by
    simpa using congrArg (fun g => g x)
      (deriv_commute (d := 3) (u := 1) (v := 2) (f := fun y => f y 0) h_f0)
  calc
    (∇ ⬝ (∇ × f)) x
        = ((∂[0] (fun y => A0 y - B0 y)) x + (∂[1] (fun y => A1 y - B1 y)) x)
          + (∂[2] (fun y => A2 y - B2 y)) x := by
          simp [div, curl, A0, B0, A1, B1, A2, B2, Fin.sum_univ_three]
    _ = (∂[0] (fun y => A0 y - B0 y)) x
          + ((∂[1] (fun y => A1 y - B1 y)) x + (∂[2] (fun y => A2 y - B2 y)) x) := by
          abel
    _ = ((∂[0] A0) x - (∂[0] B0) x) + (((∂[1] A1) x - (∂[1] B1) x) + ((∂[2] A2) x - (∂[2] B2) x)) := by
          rw [hsub0, hsub1, hsub2]
    _ = ((∂[0] (∂[1] (fun y => f y 2))) x - (∂[0] (∂[2] (fun y => f y 1))) x)
          + (((∂[1] (∂[2] (fun y => f y 0))) x - (∂[1] (∂[0] (fun y => f y 2))) x)
          + ((∂[2] (∂[0] (fun y => f y 1))) x - (∂[2] (∂[1] (fun y => f y 0))) x)) := by
          rfl
    _ = 0 := by
          linarith [h_comm_01_f2, h_comm_02_f1, h_comm_12_f0]

/-!

### A.8. The curl of a curl

-/

set_option maxHeartbeats 800000 in
lemma curl_of_curl (f : Space → EuclideanSpace ℝ (Fin 3)) (hf : ContDiff ℝ 2 f) :
    ∇ × (∇ × f) = ∇ (∇ ⬝ f) - Δ f := by
  have h_f0 : ContDiff ℝ 2 (fun y => f y 0) := by fun_prop
  have h_f1 : ContDiff ℝ 2 (fun y => f y 1) := by fun_prop
  have h_f2 : ContDiff ℝ 2 (fun y => f y 2) := by fun_prop
  have hdiv :
      (fun y => ∂[0] (fun z => f z 0) y + (∂[1] (fun z => f z 1) y + ∂[2] (fun z => f z 2) y)) =
        div f := by
    funext y
    simp [div, Fin.sum_univ_three, add_assoc]
  ext x i
  fin_cases i
  · have hsub1 :
        (∂[1] (fun y => ∂[0] (fun z => f z 1) y - ∂[1] (fun z => f z 0) y)) x
          = (∂[1] (∂[0] (fun y => f y 1))) x - (∂[1] (∂[1] (fun y => f y 0))) x := by
      simpa using congrArg (fun g => g x)
        (deriv_coord_2nd_sub (f := f) (hf := hf) (u := 1) (v := 0) (w := 1))
    have hsub2 :
        (∂[2] (fun y => ∂[2] (fun z => f z 0) y - ∂[0] (fun z => f z 2) y)) x
          = (∂[2] (∂[2] (fun y => f y 0))) x - (∂[2] (∂[0] (fun y => f y 2))) x := by
      simpa using congrArg (fun g => g x)
        (deriv_coord_2nd_sub (f := f) (hf := hf) (u := 2) (v := 2) (w := 0))
    have hadd0 :
        (∂[0] (fun y => ∂[0] (fun z => f z 0) y +
          (∂[1] (fun z => f z 1) y + ∂[2] (fun z => f z 2) y))) x
        = (∂[0] (∂[0] (fun y => f y 0))) x + (∂[0] (∂[1] (fun y => f y 1))) x
          + (∂[0] (∂[2] (fun y => f y 2))) x := by
      simpa using congrArg (fun g => g x)
        (deriv_coord_2nd_add (f := f) (hf := hf) (i := 0) (u := 0) (v := 1) (w := 2))
    have h_comm_01_f1 : (∂[1] (∂[0] (fun y => f y 1))) x = (∂[0] (∂[1] (fun y => f y 1))) x := by
      simpa using congrArg (fun g => g x)
        (deriv_commute (d := 3) (u := 1) (v := 0) (f := fun y => f y 1) h_f1)
    have h_comm_20_f2 : (∂[2] (∂[0] (fun y => f y 2))) x = (∂[0] (∂[2] (fun y => f y 2))) x := by
      simpa using congrArg (fun g => g x)
        (deriv_commute (d := 3) (u := 2) (v := 0) (f := fun y => f y 2) h_f2)
    calc
      (∇ × (∇ × f)) x 0
          = (∂[1] (fun y => ∂[0] (fun z => f z 1) y - ∂[1] (fun z => f z 0) y)) x
            - (∂[2] (fun y => ∂[2] (fun z => f z 0) y - ∂[0] (fun z => f z 2) y)) x := by
              simp [curl, Fin.isValue]
      _ = ((∂[1] (∂[0] (fun y => f y 1))) x - (∂[1] (∂[1] (fun y => f y 0))) x)
            - ((∂[2] (∂[2] (fun y => f y 0))) x - (∂[2] (∂[0] (fun y => f y 2))) x) := by
              rw [hsub1, hsub2]
      _ = ((∂[0] (∂[1] (fun y => f y 1))) x + (∂[0] (∂[2] (fun y => f y 2))) x)
            - ((∂[1] (∂[1] (fun y => f y 0))) x + (∂[2] (∂[2] (fun y => f y 0))) x) := by
              linarith [h_comm_01_f1, h_comm_20_f2]
      _ = ((∂[0] (∂[0] (fun y => f y 0))) x + (∂[0] (∂[1] (fun y => f y 1))) x
            + (∂[0] (∂[2] (fun y => f y 2))) x)
            - ((∂[0] (∂[0] (fun y => f y 0))) x + (∂[1] (∂[1] (fun y => f y 0))) x
            + (∂[2] (∂[2] (fun y => f y 0))) x) := by
              ring_nf
      _ = (∂[0] (fun y => ∂[0] (fun z => f z 0) y +
            (∂[1] (fun z => f z 1) y + ∂[2] (fun z => f z 2) y))) x
            - ((∂[0] (∂[0] (fun y => f y 0))) x + (∂[1] (∂[1] (fun y => f y 0))) x
            + (∂[2] (∂[2] (fun y => f y 0))) x) := by
              rw [hadd0]
      _ = ((∇ (∇ ⬝ f) - Δ f) x) 0 := by
        rw [hdiv]
        simp [grad, laplacianVec, laplacian, Fin.sum_univ_three, Fin.isValue]
  · have hsub1 :
        (∂[2] (fun y => ∂[1] (fun z => f z 2) y - ∂[2] (fun z => f z 1) y)) x
          = (∂[2] (∂[1] (fun y => f y 2))) x - (∂[2] (∂[2] (fun y => f y 1))) x := by
      simpa using congrArg (fun g => g x)
        (deriv_coord_2nd_sub (f := f) (hf := hf) (u := 2) (v := 1) (w := 2))
    have hsub2 :
        (∂[0] (fun y => ∂[0] (fun z => f z 1) y - ∂[1] (fun z => f z 0) y)) x
          = (∂[0] (∂[0] (fun y => f y 1))) x - (∂[0] (∂[1] (fun y => f y 0))) x := by
      simpa using congrArg (fun g => g x)
        (deriv_coord_2nd_sub (f := f) (hf := hf) (u := 0) (v := 0) (w := 1))
    have hadd1 :
        (∂[1] (fun y => ∂[0] (fun z => f z 0) y +
          (∂[1] (fun z => f z 1) y + ∂[2] (fun z => f z 2) y))) x
        = (∂[1] (∂[0] (fun y => f y 0))) x + (∂[1] (∂[1] (fun y => f y 1))) x
          + (∂[1] (∂[2] (fun y => f y 2))) x := by
      simpa using congrArg (fun g => g x)
        (deriv_coord_2nd_add (f := f) (hf := hf) (i := 1) (u := 0) (v := 1) (w := 2))
    have h_comm_21_f2 : (∂[2] (∂[1] (fun y => f y 2))) x = (∂[1] (∂[2] (fun y => f y 2))) x := by
      simpa using congrArg (fun g => g x)
        (deriv_commute (d := 3) (u := 2) (v := 1) (f := fun y => f y 2) h_f2)
    have h_comm_01_f0 : (∂[0] (∂[1] (fun y => f y 0))) x = (∂[1] (∂[0] (fun y => f y 0))) x := by
      simpa using congrArg (fun g => g x)
        (deriv_commute (d := 3) (u := 0) (v := 1) (f := fun y => f y 0) h_f0)
    calc
      (∇ × (∇ × f)) x 1
          = (∂[2] (fun y => ∂[1] (fun z => f z 2) y - ∂[2] (fun z => f z 1) y)) x
            - (∂[0] (fun y => ∂[0] (fun z => f z 1) y - ∂[1] (fun z => f z 0) y)) x := by
              simp [curl, Fin.isValue]
      _ = ((∂[2] (∂[1] (fun y => f y 2))) x - (∂[2] (∂[2] (fun y => f y 1))) x)
            - ((∂[0] (∂[0] (fun y => f y 1))) x - (∂[0] (∂[1] (fun y => f y 0))) x) := by
              rw [hsub1, hsub2]
      _ = ((∂[1] (∂[0] (fun y => f y 0))) x + (∂[1] (∂[2] (fun y => f y 2))) x)
            - ((∂[0] (∂[0] (fun y => f y 1))) x + (∂[2] (∂[2] (fun y => f y 1))) x) := by
              linarith [h_comm_21_f2, h_comm_01_f0]
      _ = ((∂[1] (∂[0] (fun y => f y 0))) x + (∂[1] (∂[1] (fun y => f y 1))) x
            + (∂[1] (∂[2] (fun y => f y 2))) x)
            - ((∂[0] (∂[0] (fun y => f y 1))) x + (∂[1] (∂[1] (fun y => f y 1))) x
            + (∂[2] (∂[2] (fun y => f y 1))) x) := by
              ring_nf
      _ = (∂[1] (fun y => ∂[0] (fun z => f z 0) y +
            (∂[1] (fun z => f z 1) y + ∂[2] (fun z => f z 2) y))) x
            - ((∂[0] (∂[0] (fun y => f y 1))) x + (∂[1] (∂[1] (fun y => f y 1))) x
            + (∂[2] (∂[2] (fun y => f y 1))) x) := by
              rw [hadd1]
      _ = ((∇ (∇ ⬝ f) - Δ f) x) 1 := by
        rw [hdiv]
        simp [grad, laplacianVec, laplacian, Fin.sum_univ_three, Fin.isValue]
  · have hsub1 :
        (∂[0] (fun y => ∂[2] (fun z => f z 0) y - ∂[0] (fun z => f z 2) y)) x
          = (∂[0] (∂[2] (fun y => f y 0))) x - (∂[0] (∂[0] (fun y => f y 2))) x := by
      simpa using congrArg (fun g => g x)
        (deriv_coord_2nd_sub (f := f) (hf := hf) (u := 0) (v := 2) (w := 0))
    have hsub2 :
        (∂[1] (fun y => ∂[1] (fun z => f z 2) y - ∂[2] (fun z => f z 1) y)) x
          = (∂[1] (∂[1] (fun y => f y 2))) x - (∂[1] (∂[2] (fun y => f y 1))) x := by
      simpa using congrArg (fun g => g x)
        (deriv_coord_2nd_sub (f := f) (hf := hf) (u := 1) (v := 1) (w := 2))
    have hadd2 :
        (∂[2] (fun y => ∂[0] (fun z => f z 0) y +
          (∂[1] (fun z => f z 1) y + ∂[2] (fun z => f z 2) y))) x
        = (∂[2] (∂[0] (fun y => f y 0))) x + (∂[2] (∂[1] (fun y => f y 1))) x
          + (∂[2] (∂[2] (fun y => f y 2))) x := by
      simpa using congrArg (fun g => g x)
        (deriv_coord_2nd_add (f := f) (hf := hf) (i := 2) (u := 0) (v := 1) (w := 2))
    have h_comm_02_f0 : (∂[0] (∂[2] (fun y => f y 0))) x = (∂[2] (∂[0] (fun y => f y 0))) x := by
      simpa using congrArg (fun g => g x)
        (deriv_commute (d := 3) (u := 0) (v := 2) (f := fun y => f y 0) h_f0)
    have h_comm_12_f1 : (∂[1] (∂[2] (fun y => f y 1))) x = (∂[2] (∂[1] (fun y => f y 1))) x := by
      simpa using congrArg (fun g => g x)
        (deriv_commute (d := 3) (u := 1) (v := 2) (f := fun y => f y 1) h_f1)
    calc
      (∇ × (∇ × f)) x 2
          = (∂[0] (fun y => ∂[2] (fun z => f z 0) y - ∂[0] (fun z => f z 2) y)) x
            - (∂[1] (fun y => ∂[1] (fun z => f z 2) y - ∂[2] (fun z => f z 1) y)) x := by
              simp [curl, Fin.isValue]
      _ = ((∂[0] (∂[2] (fun y => f y 0))) x - (∂[0] (∂[0] (fun y => f y 2))) x)
            - ((∂[1] (∂[1] (fun y => f y 2))) x - (∂[1] (∂[2] (fun y => f y 1))) x) := by
              rw [hsub1, hsub2]
      _ = ((∂[2] (∂[0] (fun y => f y 0))) x + (∂[2] (∂[1] (fun y => f y 1))) x)
            - ((∂[0] (∂[0] (fun y => f y 2))) x + (∂[1] (∂[1] (fun y => f y 2))) x) := by
              linarith [h_comm_02_f0, h_comm_12_f1]
      _ = ((∂[2] (∂[0] (fun y => f y 0))) x + (∂[2] (∂[1] (fun y => f y 1))) x
            + (∂[2] (∂[2] (fun y => f y 2))) x)
            - ((∂[0] (∂[0] (fun y => f y 2))) x + (∂[1] (∂[1] (fun y => f y 2))) x
            + (∂[2] (∂[2] (fun y => f y 2))) x) := by
              ring_nf
      _ = (∂[2] (fun y => ∂[0] (fun z => f z 0) y +
            (∂[1] (fun z => f z 1) y + ∂[2] (fun z => f z 2) y))) x
            - ((∂[0] (∂[0] (fun y => f y 2))) x + (∂[1] (∂[1] (fun y => f y 2))) x
            + (∂[2] (∂[2] (fun y => f y 2))) x) := by
              rw [hadd2]
      _ = ((∇ (∇ ⬝ f) - Δ f) x) 2 := by
        rw [hdiv]
        simp [grad, laplacianVec, laplacian, Fin.sum_univ_three, Fin.isValue]

/-!

## B. The curl on distributions

-/

open MeasureTheory SchwartzMap InnerProductSpace Distribution

/-- The curl of a distribution `Space →d[ℝ] (EuclideanSpace ℝ (Fin 3))` as a distribution
  `Space →d[ℝ] (EuclideanSpace ℝ (Fin 3))`. -/
noncomputable def distCurl : (Space →d[ℝ] (EuclideanSpace ℝ (Fin 3))) →ₗ[ℝ]
    (Space) →d[ℝ] (EuclideanSpace ℝ (Fin 3)) where
  toFun f :=
    let curlLin : (Space →L[ℝ] (EuclideanSpace ℝ (Fin 3))) →ₗ[ℝ] (EuclideanSpace ℝ (Fin 3)) :=
      {
        toFun := fun dfdx =>
          WithLp.toLp 2 fun i =>
            match i with
            | 0 => dfdx (basis 2) 1 - dfdx (basis 1) 2
            | 1 => dfdx (basis 0) 2 - dfdx (basis 2) 0
            | 2 => dfdx (basis 1) 0 - dfdx (basis 0) 1
        map_add' := by
          intro v1 v2
          ext i
          fin_cases i
          · simp [Fin.isValue, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          · simp [Fin.isValue, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
          · simp [Fin.isValue, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        map_smul' := by
          intro a v
          ext i
          fin_cases i
          · simp [Fin.isValue, sub_eq_add_neg]
            ring
          · simp [Fin.isValue, sub_eq_add_neg]
            ring
          · simp [Fin.isValue, sub_eq_add_neg]
            ring
      }
    let curl : (Space →L[ℝ] (EuclideanSpace ℝ (Fin 3))) →L[ℝ] (EuclideanSpace ℝ (Fin 3)) :=
      ⟨curlLin, LinearMap.continuous_of_finiteDimensional curlLin⟩
    curl.comp (Distribution.fderivD ℝ f)
  map_add' := by
    intro f1 f2
    ext η i
    fin_cases i
    · simp [Distribution.fderivD]
    · simp [Distribution.fderivD]
    · simp [Distribution.fderivD]
  map_smul' := by
    intro a f
    ext η i
    fin_cases i
    · simp [Distribution.fderivD]
    · simp [Distribution.fderivD]
    · simp [Distribution.fderivD]

/-!

### B.1. The components of the curl

-/

/- distCurl_apply_zero, distCurl_apply_one, distCurl_apply_two removed:
   these previously had omitted-proof marker types in the statement. -/

/-!

### B.2. Basic equalities

-/

/- `distCurl_apply` removed: it previously had an omitted-proof marker type in the statement. -/

/-!

### B.3. The curl of a grad is zero

-/

/-- The curl of a grad is equal to zero. -/
@[simp]
lemma distCurl_distGrad_eq_zero (f : (Space) →d[ℝ] ℝ) :
    distCurl (distGrad f) = 0 := by
  ext η i
  fin_cases i
  · simp [distCurl, Distribution.fderivD]
  · simp [distCurl, Distribution.fderivD]
  · simp [distCurl, Distribution.fderivD]

end Space
