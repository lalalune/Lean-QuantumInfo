/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Joseph Tooby-Smith
-/
import Relativity.Tensors.RealTensor.Vector.Causality.Basic

/-!

## Properties of light like vectors

-/

noncomputable section
namespace Lorentz
open realLorentzTensor
open InnerProductSpace
namespace Vector

lemma lightLike_iff_norm_sq_zero {d : ℕ} (p : Vector d) :
    causalCharacter p = CausalCharacter.lightLike ↔ ⟪p, p⟫ₘ = 0 := by
  unfold causalCharacter
  by_cases h0 : ⟪p, p⟫ₘ = 0
  · simp [h0]
  · by_cases hpos : 0 < ⟪p, p⟫ₘ
    · simp [h0, hpos]
    · simp [h0, hpos]

  -- Zero vector has zero Minkowski norm squared
@[simp]
lemma causalCharacter_zero {d : ℕ} : causalCharacter (0 : Vector d) =
    CausalCharacter.lightLike := by
  simp [causalCharacter]

/-- Causally preceding is reflexive -/
@[simp]
lemma causallyPrecedes_refl {d : ℕ} (p : Vector d) : causallyPrecedes p p := by
  right
  simp [pastLightConeBoundary]

/-- For two lightlike vectors with equal time components, their spatial parts
    have equal Euclidean norms -/
lemma lightlike_eq_spatial_norm_of_eq_time {d : ℕ} {v w : Vector d}
    (hv : causalCharacter v = .lightLike) (hw : causalCharacter w = .lightLike)
    (h_time : timeComponent v = timeComponent w) :
    ⟪spatialPart v, spatialPart v⟫_ℝ = ⟪spatialPart w, spatialPart w⟫_ℝ := by
  have hv0 : ⟪v, v⟫ₘ = 0 := (lightLike_iff_norm_sq_zero v).mp hv
  have hw0 : ⟪w, w⟫ₘ = 0 := (lightLike_iff_norm_sq_zero w).mp hw
  have hv_spatial : ⟪spatialPart v, spatialPart v⟫_ℝ = timeComponent v * timeComponent v := by
    have hv_coord : 0 = timeComponent v * timeComponent v - ⟪spatialPart v, spatialPart v⟫_ℝ := by
      simpa [hv0] using (minkowskiProduct_eq_timeComponent_spatialPart (p := v) (q := v))
    linarith
  have hw_spatial : ⟪spatialPart w, spatialPart w⟫_ℝ = timeComponent w * timeComponent w := by
    have hw_coord : 0 = timeComponent w * timeComponent w - ⟪spatialPart w, spatialPart w⟫_ℝ := by
      simpa [hw0] using (minkowskiProduct_eq_timeComponent_spatialPart (p := w) (q := w))
    linarith
  calc
    ⟪spatialPart v, spatialPart v⟫_ℝ = timeComponent v * timeComponent v := hv_spatial
    _ = timeComponent w * timeComponent w := by simpa [h_time]
    _ = ⟪spatialPart w, spatialPart w⟫_ℝ := hw_spatial.symm

/-- If two lightlike vectors have parallel spatial components, their temporal components
must also be proportional, which implies the entire vectors are proportional -/
lemma lightlike_spatial_parallel_implies_proportional {d : ℕ} {v w : Vector d}
    (_hv : causalCharacter v = .lightLike) (_hw : causalCharacter w = .lightLike)
    (h_spatial_parallel : ∃ (r : ℝ), v = r • w) :
    ∃ (r : ℝ), |v (Sum.inl 0)| = |r| * |w (Sum.inl 0)| := by
  rcases h_spatial_parallel with ⟨r, hr⟩
  use r
  simpa [hr, abs_mul]

end Vector

end Lorentz
