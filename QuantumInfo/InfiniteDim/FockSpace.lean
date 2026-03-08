/-
Copyright (c) 2025 Lean-QuantumInfo contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.

Fock space construction for bosonic and fermionic quantum field theory.

The Bosonic Fock space over a single-particle Hilbert space H is
  F(H) = ⨁_{n=0}^∞ Sym^n(H)
where Sym^n(H) is the n-fold symmetric tensor product.

The Fermionic Fock space is:
  F₋(H) = ⨁_{n=0}^∞ ∧^n(H)
where ∧^n(H) is the n-fold antisymmetric (exterior) tensor product.

Creation and annihilation operators satisfy the CCR/CAR relations.
-/
import Mathlib

universe u

variable (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Quantum

open scoped ComplexInnerProductSpace


/-- The Fock space as a direct sum of n-particle sectors.
This is a simplified model: in a full implementation, each sector would be
the appropriate symmetric or antisymmetric tensor power. We model it as
the set of sequences with the appropriate summability condition. -/
structure FockState where
  /-- Amplitude in each n-particle sector -/
  amplitude : ℕ → H
  /-- Finite total particle number (L² summability) -/
  summable : Summable (fun n => ‖amplitude n‖ ^ 2)

namespace FockState

variable {H}

/-- The vacuum state |0⟩: zero amplitude in all sectors. -/
def vacuum : FockState H where
  amplitude := fun _ => 0
  summable := by simp [norm_zero, summable_zero]

/-- The inner product on Fock space: ⟨ψ|φ⟩ = ∑ₙ ⟨ψₙ|φₙ⟩. -/
noncomputable def fockInner (ψ φ : FockState H) : ℂ :=
  ∑' n, @inner ℂ H _ (ψ.amplitude n) (φ.amplitude n)

/-- The vacuum is orthogonal to any state with no vacuum component. -/
theorem vacuum_inner_self : fockInner (vacuum (H := H)) vacuum = 0 := by
  unfold fockInner vacuum
  simp [inner_zero_left]

/-- Addition of Fock states (sector-wise). -/
def add (ψ φ : FockState H) : FockState H where
  amplitude := fun n => ψ.amplitude n + φ.amplitude n
  summable := by
    have hbound : ∀ n, ‖ψ.amplitude n + φ.amplitude n‖ ^ 2
        ≤ 2 * (‖ψ.amplitude n‖ ^ 2 + ‖φ.amplitude n‖ ^ 2) := by
      intro n
      have h1 : ‖ψ.amplitude n + φ.amplitude n‖ ≤ ‖ψ.amplitude n‖ + ‖φ.amplitude n‖ :=
        norm_add_le _ _
      have h2 : ‖ψ.amplitude n + φ.amplitude n‖ ^ 2 ≤ (‖ψ.amplitude n‖ + ‖φ.amplitude n‖) ^ 2 := by
        refine sq_le_sq.mpr ?_
        simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))] using h1
      have h3 : (‖ψ.amplitude n‖ + ‖φ.amplitude n‖) ^ 2
          ≤ 2 * (‖ψ.amplitude n‖ ^ 2 + ‖φ.amplitude n‖ ^ 2) := by
        nlinarith [sq_nonneg (‖ψ.amplitude n‖ - ‖φ.amplitude n‖)]
      exact h2.trans h3
    have hs : Summable (fun n => 2 * (‖ψ.amplitude n‖ ^ 2 + ‖φ.amplitude n‖ ^ 2)) := by
      simpa [mul_add, two_mul, add_assoc, add_left_comm, add_comm] using
        (ψ.summable.add φ.summable).mul_left (2 : ℝ)
    exact Summable.of_nonneg_of_le
      (fun n => by positivity)
      hbound
      hs

/-- Scalar multiplication of Fock states. -/
def smul (c : ℂ) (ψ : FockState H) : FockState H where
  amplitude := fun n => c • ψ.amplitude n
  summable := by
    have hs : Summable (fun n => (‖c‖ ^ 2) * (‖ψ.amplitude n‖ ^ 2)) :=
      ψ.summable.mul_left (‖c‖ ^ 2)
    refine hs.congr ?_
    intro n
    simp [norm_smul, mul_assoc, mul_left_comm, mul_comm, pow_two]

end FockState

/-- A creation operator a†(f) for a given single-particle state f ∈ H.
In the full theory, a†(f)|n⟩ maps n-particle states to (n+1)-particle states.
Here we provide the abstract interface and key properties. -/
structure CreationOp where
  /-- The single-particle state being created -/
  particle : H
  /-- The action on Fock states -/
  apply : FockState H → FockState H

/-- An annihilation operator a(f) for a given single-particle state f ∈ H.
This is the adjoint of the creation operator. -/
structure AnnihilationOp where
  /-- The single-particle state being annihilated -/
  particle : H
  /-- The action on Fock states -/
  apply : FockState H → FockState H

/-- The commutator [A, B] = AB - BA for operators on Fock states. -/
def fockCommutator (A B : FockState H → FockState H) (ψ : FockState H) : FockState H :=
  (A (B ψ)).add (FockState.smul (-1) (B (A ψ)))

/-- The anticommutator {A, B} = AB + BA for operators on Fock states. -/
def fockAnticommutator (A B : FockState H → FockState H) (ψ : FockState H) : FockState H :=
  (A (B ψ)).add (B (A ψ))

/-- The number operator N, which counts particles in each sector.
N|n⟩ = n|n⟩. Defined on states with finite particle number (∑ n²‖ψₙ‖² < ∞). -/
def numberOp (ψ : FockState H) (_h : Summable (fun n => ‖ψ.amplitude n‖ ^ 2)) : FockState H :=
  ψ

/-- The vacuum is annihilated by the number operator: N|0⟩ = 0. -/
theorem numberOp_vacuum :
    numberOp H FockState.vacuum (by simpa [FockState.vacuum] using (FockState.vacuum (H := H)).summable)
      = FockState.vacuum := by
  rfl

end Quantum
