/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Joseph Tooby-Smith
-/
import Relativity.Tensors.RealTensor.Vector.Causality.Basic

/-!

## Properties of time like vectors

-/

noncomputable section
namespace Lorentz
open realLorentzTensor
open InnerProductSpace
namespace Vector

/-- For timelike vectors with negative time components,
    their time components multiply to give a positive number -/
@[simp]
lemma timelike_neg_time_component_product {d : ℕ} (v w : Vector d)
    (hv_neg : v (Sum.inl 0) < 0) (hw_neg : w (Sum.inl 0) < 0) :
    v (Sum.inl 0) * w (Sum.inl 0) > 0 := by
  exact mul_pos_of_neg_of_neg hv_neg hw_neg

/-- For timelike vectors, the Minkowski inner product is positive -/
lemma timeLike_iff_norm_sq_pos {d : ℕ} (p : Vector d) :
    causalCharacter p = CausalCharacter.timeLike ↔ 0 < ⟪p, p⟫ₘ := by
  unfold causalCharacter
  by_cases h0 : ⟪p, p⟫ₘ = 0
  · simp [h0]
  · by_cases hpos : 0 < ⟪p, p⟫ₘ
    · simp [h0, hpos]
    · simp [h0, hpos]

/-- For timeLike vectors in Minkowski space, the inner product of the spatial part
    is less than the square of the time component -/
lemma timelike_time_dominates_space {d : ℕ} {v : Vector d}
    (hv : causalCharacter v = .timeLike) :
    ⟪spatialPart v, spatialPart v⟫_ℝ < (timeComponent v) * (timeComponent v) := by
  rw [timeLike_iff_norm_sq_pos] at hv
  rw [minkowskiProduct_toCoord] at hv
  have hcoord : ∑ i, v (Sum.inr i) * v (Sum.inr i) < v (Sum.inl 0) * v (Sum.inl 0) :=
    sub_pos.mp hv
  simpa [spatialPart, timeComponent, PiLp.inner_apply, RCLike.inner_apply, conj_trivial] using hcoord

/-- For nonzero timelike vectors, the time component is nonzero -/
@[simp]
lemma time_component_ne_zero_of_timelike {d : ℕ} {v : Vector d}
    (hv : causalCharacter v = .timeLike) :
    v (Sum.inl 0) ≠ 0 := by
  have hnorm_pos : 0 < ⟪v, v⟫ₘ := (timeLike_iff_norm_sq_pos v).mp hv
  have hnorm_le : ⟪v, v⟫ₘ ≤ (timeComponent v)^2 := minkowskiProduct_self_le_timeComponent_sq v
  have hsq_pos : 0 < (timeComponent v)^2 := lt_of_lt_of_le hnorm_pos hnorm_le
  intro h
  have hsq_zero : (timeComponent v)^2 = 0 := by simp [h]
  exact (ne_of_gt hsq_pos) hsq_zero

/-- For timelike vectors, the time component is nonzero -/
lemma timelike_time_component_ne_zero {d : ℕ} {v : Vector d}
    (hv : causalCharacter v = .timeLike) :
    timeComponent v ≠ 0 := time_component_ne_zero_of_timelike hv

/-- A vector is timelike if and only if its time component squared is less than
    the sum of its spatial components squared -/
lemma timeLike_iff_time_lt_space {d : ℕ} {v : Vector d} :
    causalCharacter v = .timeLike ↔
    ⟪spatialPart v, spatialPart v⟫_ℝ < v (Sum.inl 0) * v (Sum.inl 0) := by
  constructor
  · intro h_timelike
    exact timelike_time_dominates_space h_timelike
  · intro h_time_lt_space
    rw [timeLike_iff_norm_sq_pos, minkowskiProduct_toCoord]
    refine sub_pos.mpr ?_
    simpa [spatialPart, PiLp.inner_apply, RCLike.inner_apply, conj_trivial] using h_time_lt_space

/-- Time component squared is positive for timelike vectors -/
@[simp]
lemma timeComponent_squared_pos_of_timelike {d : ℕ} {v : Vector d}
    (hv : causalCharacter v = .timeLike) :
    0 < (timeComponent v)^2 := by
  exact sq_pos_of_ne_zero (time_component_ne_zero_of_timelike hv)

/-- For timelike vectors, the spatial norm squared is strictly less
    than the time component squared -/
lemma timelike_spatial_lt_time_squared {d : ℕ} {v : Vector d}
    (hv : causalCharacter v = .timeLike) :
    ⟪spatialPart v, spatialPart v⟫_ℝ < (timeComponent v)^2 := by
  have h := (timeLike_iff_time_lt_space (v := v)).mp hv
  simpa [pow_two, timeComponent] using h

end Vector
end Lorentz
