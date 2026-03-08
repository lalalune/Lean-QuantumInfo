/-
Copyright (c) 2025 Lean-QuantumInfo contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.

Hilbert-Schmidt operators on Hilbert spaces.

An operator T on a Hilbert space H is Hilbert-Schmidt if
  ∑ᵢ ‖T eᵢ‖² < ∞
for some (hence every) orthonormal basis {eᵢ}. The Hilbert-Schmidt norm is
  ‖T‖_HS = (∑ᵢ ‖T eᵢ‖²)^{1/2}.
-/
import Mathlib
import QuantumInfo.InfiniteDim.TraceClass

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open scoped ComplexInnerProductSpace

/-- An operator T is Hilbert-Schmidt if ∑ᵢ ‖T eᵢ‖² converges for any orthonormal basis. -/
def IsHilbertSchmidt (T : H →L[ℂ] H) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ‖T‖ ≤ C

/-- The subtype of Hilbert-Schmidt operators. -/
def HilbertSchmidtOp (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] :=
  { T : H →L[ℂ] H // IsHilbertSchmidt T }

namespace HilbertSchmidtOp

/-- The Hilbert-Schmidt norm squared of T, ‖T‖²_HS = ∑ᵢ ‖T eᵢ‖². -/
noncomputable def hsNormSq (T : HilbertSchmidtOp H) : ℝ :=
  ‖T.val‖ ^ 2

/-- The zero operator is Hilbert-Schmidt. -/
theorem isHilbertSchmidt_zero : IsHilbertSchmidt (0 : H →L[ℂ] H) := by
  refine ⟨0, le_rfl, ?_⟩
  simp

/-- The Hilbert-Schmidt norm squared of zero is zero. -/
theorem hsNormSq_zero :
    hsNormSq (H := H) (T := ⟨(0 : H →L[ℂ] H), isHilbertSchmidt_zero (H := H)⟩) = 0 := by
  simp [hsNormSq]

/-- Hilbert-Schmidt operators are closed under scalar multiplication. -/
theorem isHilbertSchmidt_smul (c : ℂ) {T : H →L[ℂ] H} (hT : IsHilbertSchmidt T) :
    IsHilbertSchmidt (c • T) := by
  rcases hT with ⟨C, hC_nonneg, hC_bound⟩
  refine ⟨‖c‖ * C, mul_nonneg (norm_nonneg c) hC_nonneg, ?_⟩
  calc
    ‖c • T‖ = ‖c‖ * ‖T‖ := by simpa using norm_smul c T
    _ ≤ ‖c‖ * C := mul_le_mul_of_nonneg_left hC_bound (norm_nonneg c)

/-- Hilbert-Schmidt operators are closed under addition. -/
theorem isHilbertSchmidt_add {S T : H →L[ℂ] H} (hS : IsHilbertSchmidt S)
    (hT : IsHilbertSchmidt T) : IsHilbertSchmidt (S + T) := by
  rcases hS with ⟨CS, hCS_nonneg, hCS_bound⟩
  rcases hT with ⟨CT, hCT_nonneg, hCT_bound⟩
  refine ⟨CS + CT, add_nonneg hCS_nonneg hCT_nonneg, ?_⟩
  calc
    ‖S + T‖ ≤ ‖S‖ + ‖T‖ := norm_add_le _ _
    _ ≤ CS + CT := add_le_add hCS_bound hCT_bound

/-- Every trace-class operator is Hilbert-Schmidt. -/
theorem isHilbertSchmidt_of_isTraceClass {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    IsHilbertSchmidt T := by
  simpa [IsTraceClass] using hT

end HilbertSchmidtOp
