/-
Copyright (c) 2026 TheLeaningOfEverything contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: TheLeaningOfEverything contributors
-/
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Complex.Basic

/-!
# Linear maps up to nonzero scalar

This file collects a small projective-linear-map API used by diagrammatic
quantum calculi, where denotations are often invariant under nonzero global
phase or scalar.
-/

namespace LinearMap

variable {V W X : Type*}
variable [AddCommMonoid V] [AddCommMonoid W] [AddCommMonoid X]
variable [Module ℂ V] [Module ℂ W] [Module ℂ X]

/-- Two complex-linear maps are equal up to a nonzero scalar. -/
def EqualUpToScalar (A B : V →ₗ[ℂ] W) : Prop :=
  ∃ c : ℂ, c ≠ 0 ∧ A = c • B

scoped infix:50 " ≈ₛ " => EqualUpToScalar

namespace EqualUpToScalar

@[refl]
theorem refl (A : V →ₗ[ℂ] W) : A ≈ₛ A := by
  exact ⟨1, one_ne_zero, by simp⟩

@[symm]
theorem symm {A B : V →ₗ[ℂ] W} (h : A ≈ₛ B) : B ≈ₛ A := by
  rcases h with ⟨c, hc, rfl⟩
  refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
  ext v
  simp [smul_smul, inv_mul_cancel₀ hc]

@[trans]
theorem trans {A B C : V →ₗ[ℂ] W} (hAB : A ≈ₛ B) (hBC : B ≈ₛ C) : A ≈ₛ C := by
  rcases hAB with ⟨c, hc, rfl⟩
  rcases hBC with ⟨d, hd, rfl⟩
  refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
  ext v
  simp [smul_smul]

/-- Left-composition preserves equality up to scalar. -/
theorem comp_left {A B : V →ₗ[ℂ] W} (h : A ≈ₛ B) (C : W →ₗ[ℂ] X) :
    C.comp A ≈ₛ C.comp B := by
  rcases h with ⟨c, hc, rfl⟩
  refine ⟨c, hc, ?_⟩
  ext v
  simp [LinearMap.comp_apply]

/-- Right-composition preserves equality up to scalar. -/
theorem comp_right {A B : W →ₗ[ℂ] X} (h : A ≈ₛ B) (C : V →ₗ[ℂ] W) :
    A.comp C ≈ₛ B.comp C := by
  rcases h with ⟨c, hc, rfl⟩
  refine ⟨c, hc, ?_⟩
  ext v
  simp [LinearMap.comp_apply]

end EqualUpToScalar

end LinearMap
