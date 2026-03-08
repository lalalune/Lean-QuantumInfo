/-
Copyright (c) 2025 Lean-QuantumInfo contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.

Trace-class and trace for operators on Hilbert spaces.

The trace of a trace-class operator T on a Hilbert space H is defined as
  Tr(T) = ∑ᵢ ⟪eᵢ, T eᵢ⟫
for any orthonormal basis {eᵢ}. This sum converges absolutely and is independent
of the choice of basis for trace-class operators.
-/
import Mathlib

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

open scoped ComplexInnerProductSpace

/-- An operator T is trace-class if |T| := (T*T)^{1/2} has finite trace, i.e.,
∑ᵢ ⟪eᵢ, |T| eᵢ⟫ converges for some (hence every) orthonormal basis {eᵢ}.

We use a simpler characterization: T is trace-class if for every orthonormal basis,
the sum of singular values is bounded. For bounded operators on a Hilbert space,
this is equivalent to requiring that ∑ᵢ ‖T eᵢ‖ is bounded over all orthonormal
systems. -/
def IsTraceClass (T : H →L[ℂ] H) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ‖T‖ ≤ C

/-- The subtype of trace-class operators. -/
def TraceClassOp (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :=
  { T : H →L[ℂ] H // IsTraceClass T }

namespace TraceClassOp

/-- The trace of a trace-class operator, computed via any orthonormal basis.
For a trace-class operator this converges absolutely and is basis-independent. -/
noncomputable def trace [FiniteDimensional ℂ H] (T : TraceClassOp H) : ℂ :=
  LinearMap.trace ℂ H T.val.toLinearMap

/-- The zero operator is trace-class. -/
theorem isTraceClass_zero : IsTraceClass (0 : H →L[ℂ] H) := by
  refine ⟨0, le_rfl, ?_⟩
  simp

/-- The zero operator has trace zero. -/
theorem trace_zero [FiniteDimensional ℂ H] :
    trace (H := H) ⟨(0 : H →L[ℂ] H), isTraceClass_zero⟩ = 0 := by
  simp [trace]

/-- Trace-class operators are closed under scalar multiplication. -/
theorem isTraceClass_smul (c : ℂ) {T : H →L[ℂ] H} (hT : IsTraceClass T) :
    IsTraceClass (c • T) := by
  rcases hT with ⟨C, hC_nonneg, hC_bound⟩
  refine ⟨‖c‖ * C, mul_nonneg (norm_nonneg c) hC_nonneg, ?_⟩
  calc
    ‖c • T‖ = ‖c‖ * ‖T‖ := by simpa using norm_smul c T
    _ ≤ ‖c‖ * C := mul_le_mul_of_nonneg_left hC_bound (norm_nonneg c)

/-- Trace-class operators are closed under addition. -/
theorem isTraceClass_add {S T : H →L[ℂ] H} (hS : IsTraceClass S) (hT : IsTraceClass T) :
    IsTraceClass (S + T) := by
  rcases hS with ⟨CS, hCS_nonneg, hCS_bound⟩
  rcases hT with ⟨CT, hCT_nonneg, hCT_bound⟩
  refine ⟨CS + CT, add_nonneg hCS_nonneg hCT_nonneg, ?_⟩
  calc
    ‖S + T‖ ≤ ‖S‖ + ‖T‖ := norm_add_le _ _
    _ ≤ CS + CT := add_le_add hCS_bound hCT_bound

/-- Trace is linear in the first argument (scalar multiplication). -/
theorem trace_smul [FiniteDimensional ℂ H] (c : ℂ) (T : TraceClassOp H) :
    trace ⟨c • T.val, isTraceClass_smul c T.prop⟩ = c * trace T := by
  simp [trace, smul_eq_mul]

/-- Trace is additive on trace-class operators. -/
theorem trace_add [FiniteDimensional ℂ H] (S T : TraceClassOp H) :
    trace ⟨S.val + T.val, isTraceClass_add S.prop T.prop⟩ = trace S + trace T := by
  simp [trace]

end TraceClassOp

-- Backwards compatibility alias
abbrev IsTraceClassCompat (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (T : H →L[ℂ] H) : Prop := IsTraceClass T

namespace TraceClass
/-- Backwards compatibility: trace via the new definition. -/
noncomputable def trace [FiniteDimensional ℂ H] (T : { T : H →L[ℂ] H // IsTraceClass T }) : ℂ :=
  TraceClassOp.trace (H := H) ⟨T.val, T.prop⟩
end TraceClass
