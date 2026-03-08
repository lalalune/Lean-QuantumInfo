/-
Copyright (c) 2025 Zhi Kai Pong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhi Kai Pong
-/
import SpaceAndTime.Space.CrossProduct
import SpaceAndTime.TimeAndSpace.Basic
/-!

# Wave equation

## i. Overview

In this module we define the wave equation in `d`-dimensional Euclidean space,
and prove that plane waves are solutions to the wave equation.
By a plne wave we mean a function of the form `f(t, x) = f₀(⟪x, s⟫_ℝ - c * t)` where
`s` is a direction vector and `c` is the propagation speed.

## ii. Key results

- `WaveEquation`: The general form of the wave equation where `c` is the propagation speed.
- `planeWave`: A vector-valued plane wave travelling in the direction of `s` with
  propagation speed `c`.
- `planeWave_waveEquation`: The plane wave satisfies the wave equation.

## iii. Table of contents

- A. The wave equation
- B. Plane wave solutions
  - B.1. Definition of a plane wave
  - B.2. Differentiablity conditions
  - B.3. Time derivatives of plane waves
  - B.4. Space derivatives of plane waves
  - B.5. Laplacian of plane waves
  - B.6. Plane waves satisfy the wave equation
- C. Old lemmas used throughout files

## iv. References

-/

namespace ClassicalMechanics

open Space
open Time
open InnerProductSpace

/-!

## A. The wave equation

-/

/-- The general form of the wave equation where `c` is the propagation speed. -/
def WaveEquation {d} (f : Time → Space d → EuclideanSpace ℝ (Fin d))
    (t : Time) (x : Space d) (c : ℝ) : Prop :=
    c ^ 2 • laplacianVec (f t) x - ∂ₜ (fun t => (∂ₜ (fun t => f t x) t)) t = 0

/-!

## B. Plane wave solutions

-/

/-!

### B.1. Definition of a plane wave

-/

/-- A vector-valued plane wave travelling in the direction of `s` with propagation speed `c`. -/
noncomputable def planeWave (f₀ : ℝ → EuclideanSpace ℝ (Fin d))
    (c : ℝ) (s : Direction d) : Time → Space d → EuclideanSpace ℝ (Fin d) :=
    fun t x => f₀ (⟪x, s.unit⟫_ℝ - c * t)

lemma planeWave_eq {d f₀ c x} {s : Direction d} :
    planeWave f₀ c s t x = f₀ (⟪x, s.unit⟫_ℝ - c * t) :=
  rfl

/-!

### B.2. Differentiablity conditions

-/

@[fun_prop]
lemma planeWave_differentiable_time {d f₀ c x} {s : Direction d}
    (h' : Differentiable ℝ f₀) :
    Differentiable ℝ (fun t => planeWave f₀ c s t x) := by
  change Differentiable ℝ (f₀ ∘ fun (t : Time) => ⟪x, s.unit⟫_ℝ - c * t.val)
  apply Differentiable.comp
  · exact h'
  · apply Differentiable.sub
    · exact differentiable_const _
    · apply Differentiable.mul
      · exact differentiable_const _
      · exact Time.val_differentiable

@[fun_prop]
lemma planeWave_differentiable_space {d f₀ c t} {s : Direction d}
    (h' : Differentiable ℝ f₀) :
    Differentiable ℝ (fun x => planeWave f₀ c s t x) := by
  change Differentiable ℝ (f₀ ∘ fun (x : Space d) => ⟪x, s.unit⟫_ℝ - c * t.val)
  apply Differentiable.comp
  · exact h'
  · apply Differentiable.sub
    · exact Differentiable.inner (𝕜 := ℝ) differentiable_id (differentiable_const _)
    · exact differentiable_const _

@[fun_prop]
lemma planeWave_differentiable {s : Direction d}
    {f₀ : ℝ → EuclideanSpace ℝ (Fin d)}
    (h' : Differentiable ℝ f₀) : Differentiable ℝ ↿(planeWave f₀ c s) := by
  change Differentiable ℝ (f₀ ∘ fun p : Time × Space d => ⟪p.2, s.unit⟫_ℝ - c * p.1.val)
  apply Differentiable.comp
  · exact h'
  · apply Differentiable.sub
    · exact Differentiable.inner (𝕜 := ℝ) differentiable_snd (differentiable_const _)
    · apply Differentiable.mul
      · exact differentiable_const _
      · apply Differentiable.comp Time.val_differentiable differentiable_fst

/-!

### B.3. Time derivatives of plane waves

-/

lemma planeWave_time_deriv {d f₀ c x} {s : Direction d}
    (h' : Differentiable ℝ f₀) :
    ∂ₜ (planeWave f₀ c s · x) = -c • fun t => planeWave (fderiv ℝ f₀ · 1) c s t x := by
  funext t
  change Time.deriv (fun t => f₀ (⟪x, s.unit⟫_ℝ - c * t.val)) t = _
  rw [Time.deriv_eq]
  have hd1 : DifferentiableAt ℝ (fun (t : Time) => ⟪x, s.unit⟫_ℝ - c * t.val) t := by
    apply DifferentiableAt.sub
    · exact differentiableAt_const _
    · apply DifferentiableAt.const_mul
      exact Time.val_differentiable.differentiableAt
  change (fderiv ℝ (f₀ ∘ fun (t : Time) => ⟪x, s.unit⟫_ℝ - c * t.val) t) 1 = _
  rw [fderiv_comp t h'.differentiableAt hd1]
  have hinner : fderiv ℝ (fun (t : Time) => ⟪x, s.unit⟫_ℝ - c * t.val) t (1 : Time) = -c := by
    change (fderiv ℝ ((fun (t : Time) => ⟪x, s.unit⟫_ℝ) - (fun (t : Time) => c * t.val)) t) (1 : Time) = -c
    have h1 : DifferentiableAt ℝ (fun (t : Time) => ⟪x, s.unit⟫_ℝ) t := differentiableAt_const _
    have h2 : DifferentiableAt ℝ (fun (t : Time) => c * t.val) t :=
      DifferentiableAt.const_mul Time.val_differentiable.differentiableAt _
    rw [fderiv_sub h1 h2]
    simp only [ContinuousLinearMap.sub_apply]
    have hA : fderiv ℝ (fun (t : Time) => ⟪x, s.unit⟫_ℝ) t = 0 := by simp
    rw [hA]
    simp only [ContinuousLinearMap.zero_apply, zero_sub]
    rw [fderiv_const_mul]
    · simp [Time.fderiv_val, ContinuousLinearMap.smul_apply, smul_eq_mul]
    · exact Time.val_differentiable.differentiableAt
  simp only [ContinuousLinearMap.comp_apply]
  rw [hinner]
  have hL := ContinuousLinearMap.map_smul (fderiv ℝ f₀ (⟪x, s.unit⟫_ℝ - c * t.val)) (-c) (1 : ℝ)
  have hc : (-c : ℝ) = (-c) • (1 : ℝ) := by simp
  conv => lhs; rw [hc]
  exact hL

lemma planeWave_time_deriv_time_deriv {d f₀ c x} {s : Direction d}
    (h' : ContDiff ℝ 2 f₀) :
    ∂ₜ (∂ₜ (planeWave f₀ c s · x)) = c ^ 2 • fun t => planeWave (iteratedDeriv 2 f₀) c s t x := by
  have hd1 : Differentiable ℝ f₀ := h'.differentiable (by norm_num)
  have h1 : ∂ₜ (planeWave f₀ c s · x) = -c • fun t => planeWave (fun y => (fderiv ℝ f₀ y) 1) c s t x :=
    planeWave_time_deriv hd1
  have h_deriv_eq : (fun y => (fderiv ℝ f₀ y) (1 : ℝ)) = deriv f₀ := by
    funext y
    rfl
  rw [h_deriv_eq] at h1
  rw [h1]
  have h_deriv_diff : Differentiable ℝ (deriv f₀) := h'.differentiable_deriv_two
  funext t
  change Time.deriv (fun (t : Time) => -c • planeWave (deriv f₀) c s t x) t = _
  have h_diff_time : DifferentiableAt ℝ (fun (t : Time) => planeWave (deriv f₀) c s t x) t :=
    (planeWave_differentiable_time h_deriv_diff).differentiableAt
  rw [Time.deriv_smul (fun t => planeWave (deriv f₀) c s t x) (-c) (planeWave_differentiable_time h_deriv_diff)]
  have h2 : ∂ₜ (planeWave (deriv f₀) c s · x) = -c • fun t => planeWave (fun y => (fderiv ℝ (deriv f₀) y) 1) c s t x :=
    planeWave_time_deriv h_deriv_diff
  have h2_eval : Time.deriv (fun (t : Time) => planeWave (deriv f₀) c s t x) t = (-c • fun t => planeWave (deriv (deriv f₀)) c s t x) t := by
    have h_deriv2_eq : (fun y => (fderiv ℝ (deriv f₀) y) (1 : ℝ)) = deriv (deriv f₀) := by funext y; rfl
    rw [h_deriv2_eq] at h2
    exact congr_fun h2 t
  rw [h2_eval]
  change -c • -c • planeWave (deriv (deriv f₀)) c s t x = c ^ 2 • planeWave (iteratedDeriv 2 f₀) c s t x
  have h_iterated : deriv (deriv f₀) = iteratedDeriv 2 f₀ := by
    rw [show 2 = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [h_iterated]
  simp [smul_smul]
  congr 1
  ring

/-!

### B.4. Space derivatives of plane waves

-/

open InnerProductSpace

lemma planeWave_space_deriv {d f₀ c} {s : Direction d}
    (h' : Differentiable ℝ f₀) (i : Fin d) :
    Space.deriv i (planeWave f₀ c s t) =
    s.unit i • fun x => planeWave (fderiv ℝ f₀ · 1) c s t x:= by
  funext x
  change Space.deriv i (fun x => f₀ (⟪x, s.unit⟫_ℝ - c * t.val)) x = _
  rw [Space.deriv_eq_fderiv_basis]
  have hd1 : DifferentiableAt ℝ (fun (x : Space d) => ⟪x, s.unit⟫_ℝ - c * t.val) x := by
    apply DifferentiableAt.sub
    · exact Differentiable.inner (𝕜 := ℝ) differentiable_id (differentiable_const _) |>.differentiableAt
    · exact differentiableAt_const _
  change (fderiv ℝ (f₀ ∘ fun (x : Space d) => ⟪x, s.unit⟫_ℝ - c * t.val) x) (Space.basis i) = _
  rw [fderiv_comp x h'.differentiableAt hd1]
  have hinner : fderiv ℝ (fun (x : Space d) => ⟪x, s.unit⟫_ℝ - c * t.val) x (Space.basis i) = s.unit i := by
    change (fderiv ℝ ((fun (x : Space d) => ⟪x, s.unit⟫_ℝ) - fun (x : Space d) => c * t.val) x) (Space.basis i) = s.unit i
    have h1 : DifferentiableAt ℝ (fun (x : Space d) => ⟪x, s.unit⟫_ℝ) x :=
      Differentiable.inner (𝕜 := ℝ) differentiable_id (differentiable_const _) |>.differentiableAt
    have h2 : DifferentiableAt ℝ (fun (x : Space d) => c * t.val) x :=
      differentiableAt_const _
    rw [fderiv_sub h1 h2]
    simp only [ContinuousLinearMap.sub_apply]
    have hA : fderiv ℝ (fun (x : Space d) => ⟪x, s.unit⟫_ℝ) x (Space.basis i) = s.unit i := by
      have h := fderiv_inner_apply (𝕜 := ℝ)
        (f := fun x : Space d => x)
        (g := fun _ : Space d => s.unit)
        (x := x)
        (hf := differentiableAt_id)
        (hg := differentiableAt_const s.unit)
        (y := Space.basis i)
      simpa using h
    have hB : fderiv ℝ (fun (x : Space d) => c * t.val) x = 0 := by simp
    rw [hB]
    simp only [ContinuousLinearMap.zero_apply, sub_zero, hA]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hinner]
  have hL := ContinuousLinearMap.map_smul (fderiv ℝ f₀ (⟪x, s.unit⟫_ℝ - c * t.val)) (s.unit i) (1 : ℝ)
  have hc : (s.unit i) = (s.unit i) • (1 : ℝ) := by simp
  conv => lhs; rw [hc]
  exact hL

lemma planeWave_apply_space_deriv {d f₀ c} {s : Direction d}
    (h' : Differentiable ℝ f₀) (i j : Fin d) :
    Space.deriv i (fun x => planeWave f₀ c s t x j) =
    s.unit i • fun x => planeWave (fderiv ℝ f₀ · 1) c s t x j := by
  have h := planeWave_space_deriv (c := c) (s := s) (t := t) h' i
  funext x
  let hp : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := ContinuousLinearMap.proj j
  have hd_pw := (planeWave_differentiable_space (c := c) (s := s) (t := t) h').differentiableAt (x := x)
  change fderiv ℝ (fun (x : Space d) => planeWave f₀ c s t x j) x (Space.basis i) = _
  have h_fderiv : fderiv ℝ (fun x => planeWave f₀ c s t x j) x =
    hp.comp (fderiv ℝ (planeWave f₀ c s t) x) := by
    have h_fun : (fun x => planeWave f₀ c s t x j) = hp ∘ (planeWave f₀ c s t) := rfl
    rw [h_fun]
    rw [fderiv_comp x hp.differentiableAt hd_pw]
    rw [ContinuousLinearMap.fderiv]
  rw [h_fderiv]
  change hp (fderiv ℝ (planeWave f₀ c s t) x (Space.basis i)) = _
  have h_eval : fderiv ℝ (planeWave f₀ c s t) x (Space.basis i) = Space.deriv i (planeWave f₀ c s t) x := by
    rw [← Space.deriv_eq_fderiv_basis]
  rw [h_eval]
  have h_eq : Space.deriv i (planeWave f₀ c s t) x = s.unit i • planeWave (fderiv ℝ f₀ · 1) c s t x := by
    exact congr_fun h x
  rw [h_eq]
  exact hp.map_smul (s.unit i) (planeWave (fderiv ℝ f₀ · 1) c s t x)

lemma planeWave_space_deriv_space_deriv {d f₀ c} {s : Direction d}
    (h' : ContDiff ℝ 2 f₀) (i : Fin d) :
    Space.deriv i (Space.deriv i (planeWave f₀ c s t)) =
    s.unit i ^ 2 • fun x => planeWave (iteratedDeriv 2 f₀ ·) c s t x := by
  have hd1 : Differentiable ℝ f₀ := h'.differentiable (by norm_num)
  have h1 : Space.deriv i (planeWave f₀ c s t) = s.unit i • fun x => planeWave (fun y => (fderiv ℝ f₀ y) 1) c s t x :=
    planeWave_space_deriv (c := c) (s := s) (t := t) hd1 i
  have h_deriv_eq : (fun y => (fderiv ℝ f₀ y) (1 : ℝ)) = deriv f₀ := by
    funext y
    rfl
  rw [h_deriv_eq] at h1
  rw [h1]
  have h_deriv_diff : Differentiable ℝ (deriv f₀) := h'.differentiable_deriv_two
  funext x
  change Space.deriv i (fun (x : Space d) => s.unit i • planeWave (deriv f₀) c s t x) x = _
  have h_diff_space : Differentiable ℝ (fun (x : Space d) => planeWave (deriv f₀) c s t x) :=
    planeWave_differentiable_space (c := c) (s := s) (t := t) h_deriv_diff
  have hs : Space.deriv i (fun (x : Space d) => s.unit i • planeWave (deriv f₀) c s t x) x =
    s.unit i • Space.deriv i (planeWave (deriv f₀) c s t) x := by
    change fderiv ℝ (fun x => s.unit i • planeWave (deriv f₀) c s t x) x (Space.basis i) = _
    have h_fderiv : fderiv ℝ (fun x => s.unit i • planeWave (deriv f₀) c s t x) x =
      s.unit i • fderiv ℝ (planeWave (deriv f₀) c s t) x :=
      fderiv_const_smul h_diff_space.differentiableAt (c := s.unit i)
    rw [h_fderiv]
    exact ContinuousLinearMap.smul_apply (s.unit i) (fderiv ℝ (planeWave (deriv f₀) c s t) x) (Space.basis i)
  rw [hs]
  have h2 : Space.deriv i (planeWave (deriv f₀) c s t) x = s.unit i • planeWave (fun y => (fderiv ℝ (deriv f₀) y) 1) c s t x := by
    exact congr_fun (planeWave_space_deriv (c := c) (s := s) (t := t) h_deriv_diff i) x
  have h_deriv2_eq : (fun y => (fderiv ℝ (deriv f₀) y) (1 : ℝ)) = deriv (deriv f₀) := by funext y; rfl
  rw [h_deriv2_eq] at h2
  rw [h2]
  change s.unit i • (s.unit i • planeWave (deriv (deriv f₀)) c s t x) = s.unit i ^ 2 • planeWave (iteratedDeriv 2 f₀) c s t x
  have h_iterated : deriv (deriv f₀) = iteratedDeriv 2 f₀ := by
    rw [show 2 = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [h_iterated]
  simp [smul_smul, sq]

lemma planeWave_apply_space_deriv_space_deriv {d f₀ c} {s : Direction d}
    (h' : ContDiff ℝ 2 f₀) (i j : Fin d) :
    Space.deriv i (Space.deriv i (fun x => planeWave f₀ c s t x j)) =
    (s.unit i) ^ 2 •fun x => planeWave (iteratedDeriv 2 f₀ ·) c s t x j := by
  have hd1 : Differentiable ℝ f₀ := h'.differentiable (by norm_num)
  have h1 : Space.deriv i (fun x => planeWave f₀ c s t x j) = s.unit i • fun x => planeWave (fun y => (fderiv ℝ f₀ y) 1) c s t x j :=
    planeWave_apply_space_deriv (c := c) (s := s) (t := t) hd1 i j
  have h_deriv_eq : (fun y => (fderiv ℝ f₀ y) (1 : ℝ)) = deriv f₀ := by
    funext y
    rfl
  rw [h_deriv_eq] at h1
  rw [h1]
  have h_deriv_diff : Differentiable ℝ (deriv f₀) := h'.differentiable_deriv_two
  funext x
  change Space.deriv i (fun (x : Space d) => s.unit i • planeWave (deriv f₀) c s t x j) x = _
  let hp : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := ContinuousLinearMap.proj j
  have h_diff_space : Differentiable ℝ (fun (x : Space d) => planeWave (deriv f₀) c s t x j) := by
    have h_comp : (fun x => planeWave (deriv f₀) c s t x j) = hp ∘ (fun x => planeWave (deriv f₀) c s t x) := rfl
    rw [h_comp]
    exact hp.differentiable.comp (planeWave_differentiable_space (c := c) (s := s) (t := t) h_deriv_diff)
  have hs : Space.deriv i (fun (x : Space d) => s.unit i • planeWave (deriv f₀) c s t x j) x =
    s.unit i • Space.deriv i (fun x => planeWave (deriv f₀) c s t x j) x := by
    change fderiv ℝ (fun x => s.unit i • planeWave (deriv f₀) c s t x j) x (Space.basis i) = _
    have h_fderiv : fderiv ℝ (fun x => s.unit i • planeWave (deriv f₀) c s t x j) x =
      s.unit i • fderiv ℝ (fun x => planeWave (deriv f₀) c s t x j) x :=
      fderiv_const_smul h_diff_space.differentiableAt (c := s.unit i)
    rw [h_fderiv]
    exact ContinuousLinearMap.smul_apply (s.unit i) (fderiv ℝ (fun x => planeWave (deriv f₀) c s t x j) x) (Space.basis i)
  rw [hs]
  have h2 : Space.deriv i (fun x => planeWave (deriv f₀) c s t x j) x = s.unit i • planeWave (fun y => (fderiv ℝ (deriv f₀) y) 1) c s t x j := by
    exact congr_fun (planeWave_apply_space_deriv (c := c) (s := s) (t := t) h_deriv_diff i j) x
  have h_deriv2_eq : (fun y => (fderiv ℝ (deriv f₀) y) (1 : ℝ)) = deriv (deriv f₀) := by funext y; rfl
  rw [h_deriv2_eq] at h2
  rw [h2]
  have h_iterated : deriv (deriv f₀) = iteratedDeriv 2 f₀ := by
    rw [show 2 = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [h_iterated]
  change s.unit i * (s.unit i * planeWave (iteratedDeriv 2 f₀) c s t x j) = s.unit i ^ 2 * planeWave (iteratedDeriv 2 f₀) c s t x j
  ring

/-!

### B.5. Laplacian of plane waves

-/

lemma planeWave_laplacian {d f₀ c} {s : Direction d} (h' : ContDiff ℝ 2 f₀) :
    laplacianVec (planeWave f₀ c s t) = fun x => planeWave (iteratedDeriv 2 f₀ ·) c s t x := by
  funext x
  ext j
  change (∑ i, Space.deriv i (Space.deriv i (fun y => planeWave f₀ c s t y j)) x) = _
  have h_deriv2 := planeWave_apply_space_deriv_space_deriv (c := c) (s := s) (t := t) h'
  have h_sum : (∑ i : Fin d, Space.deriv i (Space.deriv i (fun y => planeWave f₀ c s t y j)) x) =
      ∑ i : Fin d, s.unit i ^ 2 * planeWave (iteratedDeriv 2 f₀) c s t x j := by
    apply Finset.sum_congr rfl
    intro i _
    exact congr_fun (h_deriv2 i j) x
  rw [h_sum]
  rw [← Finset.sum_mul]
  have h_norm : ∑ i : Fin d, s.unit i ^ 2 = 1 := by
    have h_sq : ∑ i : Fin d, s.unit i ^ 2 = ⟪s.unit, s.unit⟫_ℝ := by
      change ∑ i : Fin d, s.unit i ^ 2 = ∑ i : Fin d, s.unit i * s.unit i
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [h_sq, real_inner_self_eq_norm_sq]
    rw [s.norm]
    ring
  rw [h_norm]
  ring

/-!

### B.6. Plane waves satisfy the wave equation

-/

/-- The plane wave satisfies the wave equation. -/
theorem planeWave_waveEquation (c : ℝ) (s : Direction d)
    (f₀ : ℝ → EuclideanSpace ℝ (Fin d)) (hf₀ : ContDiff ℝ 2 f₀) :
    ∀ t x, WaveEquation (planeWave f₀ c s) t x c := by
  intro t x
  unfold WaveEquation
  have hLap := congr_fun (planeWave_laplacian (c := c) (s := s) (t := t) hf₀) x
  have hTime := congr_fun (planeWave_time_deriv_time_deriv (c := c) (s := s) (x := x) hf₀) t
  rw [hLap, hTime]
  simp

/-!

## C. Old lemmas used throughout files

These lemmas will eventually be moved, renamed and/or replaced.

-/

lemma wave_differentiable {s : Direction d} {c : ℝ} {x : Space d} :
    DifferentiableAt ℝ (fun x => inner ℝ x s.unit - c * t) x := by
  apply DifferentiableAt.sub
  · exact Differentiable.inner (𝕜 := ℝ) differentiable_id (differentiable_const _) |>.differentiableAt
  · apply DifferentiableAt.mul
    · exact differentiableAt_const _
    · exact differentiableAt_const _

lemma wave_dx2 {u v : Fin d} {s : Direction d}
    {f₀' : ℝ → ℝ →L[ℝ] EuclideanSpace ℝ (Fin d)} {f₀'' : ℝ → ℝ →L[ℝ] EuclideanSpace ℝ (Fin d)}
    (h'' : ∀ x, HasFDerivAt (fun x' => f₀' x' 1) (f₀'' x) x) :
    (fderiv ℝ (fun x' => (inner ℝ ((f₀' (inner ℝ x' s.unit - c * t)) (s.unit u))
    (EuclideanSpace.single v 1))) x) (Space.basis u)
    =
    inner ℝ ((s.unit u) ^ 2 • f₀'' (inner ℝ x s.unit - c * t) 1) (EuclideanSpace.single v 1) := by
  have hLin : ∀ x', (f₀' (⟪x', s.unit⟫_ℝ - c * t)) (s.unit u) =
    (s.unit u) • (f₀' (⟪x', s.unit⟫_ℝ - c * t)) 1 := by
    intro x'
    calc (f₀' (⟪x', s.unit⟫_ℝ - c * t)) (s.unit u)
      _ = (f₀' (⟪x', s.unit⟫_ℝ - c * t)) (s.unit u • (1 : ℝ)) := by rw [smul_eq_mul, mul_one]
      _ = (s.unit u) • (f₀' (⟪x', s.unit⟫_ℝ - c * t)) 1 := ContinuousLinearMap.map_smul _ _ _
  simp only [hLin]
  let hp : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := ContinuousLinearMap.proj v
  have h_inner : (fun x' => ⟪s.unit u • f₀' (⟪x', s.unit⟫_ℝ - c * t) 1, EuclideanSpace.single v 1⟫_ℝ) =
    fun x' => hp (s.unit u • f₀' (⟪x', s.unit⟫_ℝ - c * t) 1) := by
    funext x'
    change ⟪s.unit u • f₀' (⟪x', s.unit⟫_ℝ - c * t) 1, EuclideanSpace.single v 1⟫_ℝ =
      (s.unit u • f₀' (⟪x', s.unit⟫_ℝ - c * t) 1) v
    have h_single := EuclideanSpace.inner_single_right v (1 : ℝ) (s.unit u • f₀' (⟪x', s.unit⟫_ℝ - c * t) 1)
    rw [h_single]
    simp
  rw [h_inner]
  have hd_inner : DifferentiableAt ℝ (fun x' => ⟪x', s.unit⟫_ℝ - c * t) x := by
    apply DifferentiableAt.sub
    · exact Differentiable.inner (𝕜 := ℝ) differentiable_id (differentiable_const _) |>.differentiableAt
    · exact differentiableAt_const _
  have hd_f0 : DifferentiableAt ℝ (fun x' => f₀' (⟪x', s.unit⟫_ℝ - c * t) 1) x := by
    apply (h'' (⟪x, s.unit⟫_ℝ - c * t)).differentiableAt.comp x hd_inner
  have h_fderiv : fderiv ℝ (fun x' => s.unit u • f₀' (⟪x', s.unit⟫_ℝ - c * t) 1) x =
    s.unit u • fderiv ℝ (fun x' => f₀' (⟪x', s.unit⟫_ℝ - c * t) 1) x := by
    exact fderiv_const_smul hd_f0 (c := s.unit u)
  change fderiv ℝ (hp ∘ (fun x' => s.unit u • f₀' (⟪x', s.unit⟫_ℝ - c * t) 1)) x (Space.basis u) = _
  have hd_f0_smul : DifferentiableAt ℝ (fun x' => s.unit u • f₀' (⟪x', s.unit⟫_ℝ - c * t) 1) x := by
    exact DifferentiableAt.const_smul hd_f0 (s.unit u)
  have h_comp : fderiv ℝ (hp ∘ (fun x' => s.unit u • f₀' (⟪x', s.unit⟫_ℝ - c * t) 1)) x =
    hp.comp (fderiv ℝ (fun x' => s.unit u • f₀' (⟪x', s.unit⟫_ℝ - c * t) 1) x) := by
    exact (hp.hasFDerivAt.comp x hd_f0_smul.hasFDerivAt).fderiv
  rw [h_comp]
  rw [h_fderiv]
  change hp ((s.unit u • fderiv ℝ (fun x' => f₀' (⟪x', s.unit⟫_ℝ - c * t) 1) x) (Space.basis u)) = _
  rw [ContinuousLinearMap.smul_apply, hp.map_smul]
  have h_chain : fderiv ℝ (fun x' => f₀' (⟪x', s.unit⟫_ℝ - c * t) 1) x =
    (f₀'' (⟪x, s.unit⟫_ℝ - c * t)).comp (fderiv ℝ (fun x' => ⟪x', s.unit⟫_ℝ - c * t) x) := by
    exact ((h'' (⟪x, s.unit⟫_ℝ - c * t)).comp x hd_inner.hasFDerivAt).fderiv
  rw [h_chain]
  change s.unit u * hp (f₀'' (⟪x, s.unit⟫_ℝ - c * t) (fderiv ℝ (fun x' => ⟪x', s.unit⟫_ℝ - c * t) x (Space.basis u))) = _
  have h_inner_deriv : fderiv ℝ (fun x' => ⟪x', s.unit⟫_ℝ - c * t) x (Space.basis u) = s.unit u := by
    have h1 : DifferentiableAt ℝ (fun (x' : Space d) => ⟪x', s.unit⟫_ℝ) x :=
      Differentiable.inner (𝕜 := ℝ) differentiable_id (differentiable_const _) |>.differentiableAt
    have h2 : DifferentiableAt ℝ (fun (x' : Space d) => c * t) x :=
      differentiableAt_const _
    have h_sub : fderiv ℝ (fun x' => ⟪x', s.unit⟫_ℝ - c * t) x =
      fderiv ℝ (fun x' => ⟪x', s.unit⟫_ℝ) x - fderiv ℝ (fun x' => c * t) x :=
      fderiv_sub h1 h2
    have h_const : fderiv ℝ (fun x' : Space d => c * t) x = 0 := fderiv_const (c * t)
    rw [h_sub, h_const]
    simp only [ContinuousLinearMap.sub_apply, Pi.zero_apply, sub_zero, ContinuousLinearMap.zero_apply]
    -- derivative of linear function is itself
    have hLin2 : IsBoundedLinearMap ℝ (fun x' : Space d => ⟪x', s.unit⟫_ℝ) :=
      IsBoundedLinearMap.inner_right s.unit
    rw [hLin2.fderiv]
    exact Space.inner_basis s.unit u
  rw [h_inner_deriv]
  have h_rhs : hp ((s.unit u) ^ 2 • f₀'' (⟪x, s.unit⟫_ℝ - c * t) 1) = s.unit u ^ 2 * hp (f₀'' (⟪x, s.unit⟫_ℝ - c * t) 1) := by
    exact hp.map_smul (s.unit u ^ 2) (f₀'' (⟪x, s.unit⟫_ℝ - c * t) 1)
  change _ = ⟪(s.unit u)^2 • f₀'' (⟪x, s.unit⟫_ℝ - c * t) 1, EuclideanSpace.single v 1⟫_ℝ
  have h_rhs_inner : ⟪(s.unit u)^2 • f₀'' (⟪x, s.unit⟫_ℝ - c * t) 1, EuclideanSpace.single v 1⟫_ℝ =
    hp ((s.unit u) ^ 2 • f₀'' (⟪x, s.unit⟫_ℝ - c * t) 1) := by
    change ⟪(s.unit u)^2 • f₀'' (⟪x, s.unit⟫_ℝ - c * t) 1, EuclideanSpace.single v 1⟫_ℝ =
      ((s.unit u) ^ 2 • f₀'' (⟪x, s.unit⟫_ℝ - c * t) 1) v
    have h_single := EuclideanSpace.inner_single_right v (1 : ℝ) ((s.unit u)^2 • f₀'' (⟪x, s.unit⟫_ℝ - c * t) 1)
    rw [h_single]
    simp
  rw [h_rhs_inner, h_rhs]
  have h_linear : f₀'' (⟪x, s.unit⟫_ℝ - c * t) (s.unit u) = s.unit u • f₀'' (⟪x, s.unit⟫_ℝ - c * t) 1 := by
    calc (f₀'' (⟪x, s.unit⟫_ℝ - c * t)) (s.unit u)
      _ = (f₀'' (⟪x, s.unit⟫_ℝ - c * t)) (s.unit u • (1 : ℝ)) := by rw [smul_eq_mul, mul_one]
      _ = (s.unit u) • (f₀'' (⟪x, s.unit⟫_ℝ - c * t)) 1 := ContinuousLinearMap.map_smul _ _ _
  rw [h_linear]
  rw [hp.map_smul]
  change s.unit u * (s.unit u * hp (f₀'' (⟪x, s.unit⟫_ℝ - c * t) 1)) = s.unit u ^ 2 * hp (f₀'' (⟪x, s.unit⟫_ℝ - c * t) 1)
  ring

/-- If `f₀` is a function of `(inner ℝ x s - c * t)`, the fderiv of its components
with respect to spatial coordinates is equal to the corresponding component of
the propagation direction `s` times time derivative. -/
/-- If `f₀` is a function of `(inner ℝ x s - c * t)`, the fderiv of its components
with respect to spatial coordinates is equal to the corresponding component of
the propagation direction `s` times time derivative. -/
lemma space_fderiv_of_inner_product_wave_eq_space_fderiv
    {t : Time} {f₀ : ℝ → EuclideanSpace ℝ (Fin d)}
    {s : Direction d} {u v : Fin d} (h' : Differentiable ℝ f₀) :
    c * ((fun x' => (fderiv ℝ (fun x => inner ℝ (f₀ (inner ℝ x s.unit - c * t))
    (EuclideanSpace.single v 1)) x') ((Space.basis u))) x)
    =
    - s.unit u * ∂ₜ (fun t => f₀ (inner ℝ x s.unit - c * t)) t v := by
  let g : Space d → ℝ := fun x' => ⟪x', s.unit⟫_ℝ - c * t
  let h : Space d → ℝ := fun x' => ⟪f₀ (g x'), EuclideanSpace.single v 1⟫_ℝ
  have hg : DifferentiableAt ℝ g x := by
    apply DifferentiableAt.sub
    · exact Differentiable.inner (𝕜 := ℝ) differentiable_id (differentiable_const _) |>.differentiableAt
    · exact differentiableAt_const _
  have hf : DifferentiableAt ℝ f₀ (g x) := h'.differentiableAt
  have hh : DifferentiableAt ℝ (fun x' => f₀ (g x')) x := hf.comp x hg
  let hp : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := ContinuousLinearMap.proj v
  have h_proj : (fun x' => ⟪f₀ (g x'), EuclideanSpace.single v 1⟫_ℝ) =
    fun x' => hp (f₀ (g x')) := by
    funext x'
    change ⟪f₀ (g x'), EuclideanSpace.single v 1⟫_ℝ = (f₀ (g x')) v
    exact EuclideanSpace.inner_single_right v 1 _ |>.trans (by simp)
  rw [h_proj]
  have h_fderiv : fderiv ℝ (hp ∘ (fun x' => f₀ (g x'))) x =
    hp.comp (fderiv ℝ (fun x' => f₀ (g x')) x) := by
    exact (hp.hasFDerivAt.comp x hh.hasFDerivAt).fderiv
  rw [h_fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  have h_chain : fderiv ℝ (fun x' => f₀ (g x')) x =
    (fderiv ℝ f₀ (g x)).comp (fderiv ℝ g x) := by
    exact (hf.hasFDerivAt.comp x hg.hasFDerivAt).fderiv
  rw [h_chain]
  simp only [ContinuousLinearMap.comp_apply]
  have hDg : fderiv ℝ g x (Space.basis u) = s.unit u := by
    have h1 : DifferentiableAt ℝ (fun (x' : Space d) => ⟪x', s.unit⟫_ℝ) x :=
      Differentiable.inner (𝕜 := ℝ) differentiable_id (differentiable_const _) |>.differentiableAt
    have h2 : DifferentiableAt ℝ (fun (x' : Space d) => c * t) x :=
      differentiableAt_const _
    rw [fderiv_sub h1 h2]
    simp only [ContinuousLinearMap.sub_apply]
    have hB : fderiv ℝ (fun (x' : Space d) => c * t) x = 0 := by simp
    rw [hB]
    simp only [ContinuousLinearMap.zero_apply, sub_zero]
    have hLin : IsBoundedLinearMap ℝ (fun x' : Space d => ⟪x', s.unit⟫_ℝ) :=
      IsBoundedLinearMap.inner_right s.unit
    rw [hLin.fderiv]
    exact Space.inner_basis s.unit u
  rw [hDg]
  have h_linear : fderiv ℝ f₀ (g x) (s.unit u) = s.unit u • fderiv ℝ f₀ (g x) 1 := by
    calc fderiv ℝ f₀ (g x) (s.unit u)
      _ = fderiv ℝ f₀ (g x) (s.unit u • (1 : ℝ)) := by rw [smul_eq_mul, mul_one]
      _ = (s.unit u) • fderiv ℝ f₀ (g x) 1 := ContinuousLinearMap.map_smul _ _ _
  rw [h_linear]
  rw [hp.map_smul]
  simp only [smul_eq_mul]
  -- Now the RHS
  let k : ℝ → ℝ := fun t' => ⟪x, s.unit⟫_ℝ - c * t'
  have hk : HasDerivAt k (-c) t := by
    apply HasDerivAt.sub
    · exact hasDerivAt_const t ⟪x, s.unit⟫_ℝ
    · exact hasDerivAt_id t |>.const_mul c
  have hf_t : HasDerivAt f₀ (fderiv ℝ f₀ (k t) 1) (k t) := by
    exact h'.differentiableAt.hasDerivAt
  have h_chain_t : HasDerivAt (fun t' => f₀ (k t')) ((-c) • fderiv ℝ f₀ (k t) 1) t := by
    exact hf_t.comp t hk
  unfold partTimeDeriv
  rw [h_chain_t.deriv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  ring

lemma time_differentiable_of_eq_planewave {s : Direction d}
    {f₀ : ℝ → EuclideanSpace ℝ (Fin d)} {f : Time → Space d → EuclideanSpace ℝ (Fin d)}
    (h' : Differentiable ℝ f₀) (hf : f = planeWave f₀ c s) :
    Differentiable ℝ fun t => f t x := by
  rw [hf]
  unfold planeWave
  intro t
  let k : ℝ → ℝ := fun t' => ⟪x, s.unit⟫_ℝ - c * t'
  have hk : DifferentiableAt ℝ k t := by
    apply DifferentiableAt.sub
    · exact differentiableAt_const _
    · exact differentiableAt_id.const_mul c
  exact h'.differentiableAt.comp t hk

open Matrix

lemma crossProduct_time_differentiable_of_right_eq_planewave {s : Direction}
    {f₀ : ℝ → EuclideanSpace ℝ (Fin 3)} {f : Time → Space → EuclideanSpace ℝ (Fin 3)}
    (h' : Differentiable ℝ f₀) (hf : f = planeWave f₀ c s) :
    DifferentiableAt ℝ (fun t => Space.basis.repr s.unit ⨯ₑ₃ (f t x)) t := by
  apply DifferentiableAt.crossProduct
  · exact differentiableAt_const _
  · rw [hf]
    unfold planeWave
    let k : ℝ → ℝ := fun t' => ⟪x, s.unit⟫_ℝ - c * t'
    have hk : DifferentiableAt ℝ k t := by
      apply DifferentiableAt.sub
      · exact differentiableAt_const _
      · exact differentiableAt_id.const_mul c
    exact h'.differentiableAt.comp t hk

lemma crossProduct_differentiable_of_right_eq_planewave {s : Direction}
    {f₀ : ℝ → EuclideanSpace ℝ (Fin 3)} (h' : Differentiable ℝ f₀) :
    DifferentiableAt ℝ (fun u => Space.basis.repr s.unit ⨯ₑ₃ (f₀ u)) u := by
  apply DifferentiableAt.crossProduct
  · exact differentiableAt_const _
  · exact h'.differentiableAt

lemma wave_fderiv_inner_eq_inner_fderiv_proj {f₀ : ℝ → EuclideanSpace ℝ (Fin d)}
    {s : Direction d} {i : Fin d} (h' : Differentiable ℝ f₀) :
    ∀ x y, s.unit i * (fderiv ℝ (fun x => f₀ (inner ℝ x s.unit - c * t)) x) y i
    =
    inner ℝ y s.unit * (fderiv ℝ (fun x => f₀ (inner ℝ x s.unit - c * t) i) x)
    (Space.basis i) := by
  intro x y
  let g : Space d → ℝ := fun x' => ⟪x', s.unit⟫_ℝ - c * t
  have hg : DifferentiableAt ℝ g x := by
    apply DifferentiableAt.sub
    · exact Differentiable.inner (𝕜 := ℝ) differentiable_id (differentiable_const _) |>.differentiableAt
    · exact differentiableAt_const _
  have hf : DifferentiableAt ℝ f₀ (g x) := h'.differentiableAt
  have h_comp_fderiv : fderiv ℝ (f₀ ∘ g) x = (fderiv ℝ f₀ (g x)).comp (fderiv ℝ g x) := by
    exact (hf.hasFDerivAt.comp x hg.hasFDerivAt).fderiv
  rw [h_comp_fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  have hDg : fderiv ℝ g x y = ⟪y, s.unit⟫_ℝ := by
    have h1 : DifferentiableAt ℝ (fun (x' : Space d) => ⟪x', s.unit⟫_ℝ) x :=
      Differentiable.inner (𝕜 := ℝ) differentiable_id (differentiable_const _) |>.differentiableAt
    have h2 : DifferentiableAt ℝ (fun (x' : Space d) => c * t) x :=
      differentiableAt_const _
    rw [fderiv_sub h1 h2]
    simp only [ContinuousLinearMap.sub_apply]
    have hB : fderiv ℝ (fun (x' : Space d) => c * t) x = 0 := by simp
    rw [hB]
    simp only [ContinuousLinearMap.zero_apply, sub_zero]
    have hLin : IsBoundedLinearMap ℝ (fun x' : Space d => ⟪x', s.unit⟫_ℝ) :=
      IsBoundedLinearMap.inner_right s.unit
    rw [hLin.fderiv]
  rw [hDg]
  have h_proj : s.unit i * (fderiv ℝ f₀ (g x) ⟪y, s.unit⟫_ℝ) i =
    ⟪y, s.unit⟫_ℝ * (fderiv ℝ f₀ (g x) (s.unit i)) i := by
    have h1 : (fderiv ℝ f₀ (g x) ⟪y, s.unit⟫_ℝ) i = ⟪y, s.unit⟫_ℝ * (fderiv ℝ f₀ (g x) 1) i := by
      have h1a : fderiv ℝ f₀ (g x) ⟪y, s.unit⟫_ℝ = ⟪y, s.unit⟫_ℝ • fderiv ℝ f₀ (g x) 1 := by
        calc fderiv ℝ f₀ (g x) ⟪y, s.unit⟫_ℝ
          _ = fderiv ℝ f₀ (g x) (⟪y, s.unit⟫_ℝ • (1 : ℝ)) := by rw [smul_eq_mul, mul_one]
          _ = (⟪y, s.unit⟫_ℝ) • fderiv ℝ f₀ (g x) 1 := ContinuousLinearMap.map_smul _ _ _
      rw [h1a]
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
    have h2 : (fderiv ℝ f₀ (g x) (s.unit i)) i = (s.unit i) * (fderiv ℝ f₀ (g x) 1) i := by
      have h2a : fderiv ℝ f₀ (g x) (s.unit i) = (s.unit i) • fderiv ℝ f₀ (g x) 1 := by
        calc fderiv ℝ f₀ (g x) (s.unit i)
          _ = fderiv ℝ f₀ (g x) (s.unit i • (1 : ℝ)) := by rw [smul_eq_mul, mul_one]
          _ = (s.unit i) • fderiv ℝ f₀ (g x) 1 := ContinuousLinearMap.map_smul _ _ _
      rw [h2a]
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
    rw [h1, h2]
    ring
  rw [h_proj]
  congr 1
  -- Right Hand Side
  let hp_i : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have h_proj_i : (fun x' => f₀ (g x') i) = hp_i ∘ (f₀ ∘ g) := rfl
  rw [h_proj_i]
  have h_fderiv_comp : fderiv ℝ (hp_i ∘ (f₀ ∘ g)) x = hp_i.comp (fderiv ℝ (f₀ ∘ g) x) := by
    apply (hp_i.hasFDerivAt.comp x (hf.comp x hg).hasFDerivAt).fderiv
  rw [h_fderiv_comp]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  rw [h_comp_fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  have hDg_basis : fderiv ℝ g x (Space.basis i) = s.unit i := by
    have h1 : DifferentiableAt ℝ (fun (x' : Space d) => ⟪x', s.unit⟫_ℝ) x :=
      Differentiable.inner (𝕜 := ℝ) differentiable_id (differentiable_const _) |>.differentiableAt
    have h2 : DifferentiableAt ℝ (fun (x' : Space d) => c * t) x :=
      differentiableAt_const _
    rw [fderiv_sub h1 h2]
    simp only [ContinuousLinearMap.sub_apply]
    have hB : fderiv ℝ (fun (x' : Space d) => c * t) x = 0 := by simp
    rw [hB]
    simp only [ContinuousLinearMap.zero_apply, sub_zero]
    have hLin : IsBoundedLinearMap ℝ (fun x' : Space d => ⟪x', s.unit⟫_ℝ) :=
      IsBoundedLinearMap.inner_right s.unit
    rw [hLin.fderiv]
    exact Space.inner_basis s.unit i
  rw [hDg_basis]

end ClassicalMechanics
