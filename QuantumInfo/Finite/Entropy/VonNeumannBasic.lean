/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.Finite.MState
import ClassicalInfo.Entropy

/-! # Minimal Von Neumann Entropy Interface

This file provides the subset of `VonNeumann.lean` needed by modules that only require
the entropy definitions and the trace-log identity, without importing the full CPTP stack.
-/

noncomputable section

variable {d dA dB : Type*}
variable [Fintype d] [DecidableEq d]
variable [Fintype dA] [DecidableEq dA]
variable [Fintype dB] [DecidableEq dB]

open scoped InnerProductSpace RealInnerProductSpace

namespace VonNeumannBasic

/-- Von Neumann entropy of a mixed state. -/
def Sᵥₙ (ρ : MState d) : ℝ :=
  Hₛ ρ.spectrum

/-- Quantum mutual information `I(A:B) = S(A) + S(B) - S(AB)`. -/
def qMutualInfo (ρ : MState (dA × dB)) : ℝ :=
  Sᵥₙ ρ.traceLeft + Sᵥₙ ρ.traceRight - Sᵥₙ ρ

/-- Von Neumann entropy as `-Tr(ρ log ρ)` in the Hermitian inner-product form. -/
theorem Sᵥₙ_eq_neg_trace_log (ρ : MState d) : Sᵥₙ ρ = -⟪ρ.M.log, ρ.M⟫ := by
  open HermitianMat in
  rw [log, inner_eq_re_trace]
  nth_rw 2 [← cfc_id ρ.M]
  rw [← mat_cfc_mul]
  simp only [Sᵥₙ, Hₛ, H₁, Real.negMulLog, neg_mul, Finset.sum_neg_distrib, neg_inj]
  rw [← trace_eq_re_trace, ← sum_eigenvalues_eq_trace]
  obtain ⟨e, he⟩ := ρ.M.cfc_eigenvalues (Real.log * id)
  apply Finset.sum_equiv e.symm (by simp)
  simp [MState.spectrum, Distribution.mk', he, mul_comm]

end VonNeumannBasic
