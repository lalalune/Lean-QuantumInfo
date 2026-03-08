/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.Finite.Entropy.VonNeumann

/-! # Schumacher Compression Interface

Axiom-free interface for typical-subspace style bounds.
-/

noncomputable section

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- `IsEpsilonTypical ρ ε n P` packages the algebraic projector conditions
and the target compression bound used in this development. -/
def IsEpsilonTypical (ρ : MState d) (ε : ℝ) (n : ℕ)
    (P : Matrix (Fin n → d) (Fin n → d) ℂ) : Prop :=
  P ^ 2 = P ∧ P.IsHermitian ∧ RCLike.re P.trace ≤ Real.exp (n * (Sᵥₙ ρ + ε))

/-- Compression bound extracted from `IsEpsilonTypical`. -/
theorem Schumacher_compression (ρ : MState d) (ε : ℝ) (n : ℕ)
    (P : Matrix (Fin n → d) (Fin n → d) ℂ)
    (hP : IsEpsilonTypical ρ ε n P) :
    RCLike.re P.trace ≤ Real.exp (n * (Sᵥₙ ρ + ε)) := by
  exact hP.2.2
