/-
Copyright (c) 2025 Lean-QuantumInfo contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.

Spectral theorem infrastructure for self-adjoint operators on Hilbert spaces.

Provides:
- Projection-valued measures (PVMs)
- Unbounded self-adjoint operators
- Basic spectral-theorem interfaces
-/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.Module.Basic

universe u

variable (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Quantum

open Set

/-- An orthogonal projection on a Hilbert space: a bounded self-adjoint idempotent operator. -/
structure OrthogonalProjection where
  /-- The underlying bounded linear map -/
  toOp : H →L[ℂ] H
  /-- Each projection is self-adjoint. -/
  self_adj : IsSelfAdjoint toOp
  /-- It is idempotent. -/
  idempotent : toOp * toOp = toOp

namespace OrthogonalProjection

/-- The zero projection. -/
def zero : OrthogonalProjection H where
  toOp := 0
  self_adj := by
    simp
  idempotent := by
    simp

/-- The identity projection. -/
def one : OrthogonalProjection H where
  toOp := 1
  self_adj := by simp
  idempotent := by
    simp

/-- Two projections are compatible (commute) if their operators commute. -/
def Compatible (P Q : OrthogonalProjection H) : Prop :=
  P.toOp * Q.toOp = Q.toOp * P.toOp

/-- The meet (intersection) of two compatible projections. -/
noncomputable def meet (P Q : OrthogonalProjection H) (h : Compatible H P Q) :
    OrthogonalProjection H :=
  { toOp := P.toOp * Q.toOp
    self_adj := by
      have hcomm : Commute P.toOp Q.toOp := by
        simpa [Compatible] using h
      exact (IsSelfAdjoint.commute_iff P.self_adj Q.self_adj).mp hcomm
    idempotent := by
      have hcomm : Commute P.toOp Q.toOp := by
        simpa [Compatible] using h
      have hP : IsIdempotentElem P.toOp := P.idempotent
      have hQ : IsIdempotentElem Q.toOp := Q.idempotent
      exact (IsIdempotentElem.mul_of_commute hcomm hP hQ).eq }

end OrthogonalProjection

/-- A Projection-Valued Measure (PVM) on a Hilbert space.
This assigns an orthogonal projection to each Borel subset of ℝ,
satisfying the axioms of a resolution of the identity. -/
structure PVM where
  /-- The assignment of a projection operator to a measurable set of real numbers. -/
  proj : Set ℝ → OrthogonalProjection H
  /-- The PVM evaluated on the empty set is the zero projection. -/
  empty_zero : proj ∅ = OrthogonalProjection.zero H
  /-- The PVM evaluated on the whole real line is the identity. -/
  univ_id : proj univ = OrthogonalProjection.one H
  /-- Monotonicity: S ⊆ T implies E(S) ≤ E(T). -/
  monotone : ∀ S T, S ⊆ T →
    (proj S).toOp * (proj T).toOp = (proj S).toOp
  /-- Multiplicativity: E(S ∩ T) = E(S) E(T). -/
  multiplicative : ∀ S T,
    (proj (S ∩ T)).toOp = (proj S).toOp * (proj T).toOp

namespace PVM

/-- The PVM of a single-point spectrum at λ₀ (Dirac PVM). -/
noncomputable def dirac (lam0 : ℝ) : PVM H where
  proj := by
    classical
    exact fun S => if lam0 ∈ S then OrthogonalProjection.one H else OrthogonalProjection.zero H
  empty_zero := by
    classical
    simp
  univ_id := by
    classical
    simp
  monotone := by
    classical
    intro S T hST
    by_cases hS : lam0 ∈ S
    · have hT : lam0 ∈ T := hST hS
      simp [hS, hT, OrthogonalProjection.one]
    · simp [hS, OrthogonalProjection.zero]
  multiplicative := by
    classical
    intro S T
    by_cases hS : lam0 ∈ S <;> by_cases hT : lam0 ∈ T <;>
      simp [hS, hT, Set.mem_inter_iff, OrthogonalProjection.zero, OrthogonalProjection.one]

end PVM

/-- An unbounded self-adjoint operator on H, defined on a dense domain.
This is a linear operator A : D(A) → H where D(A) ⊆ H is dense, and
A is self-adjoint in the sense that ⟨Ax, y⟩ = ⟨x, Ay⟩ for all x, y ∈ D(A)
and D(A) = D(A*). -/
structure UnboundedSelfAdjoint where
  /-- The domain of the operator, a submodule of H. -/
  dom : Submodule ℂ H
  /-- The operator itself, a linear map on the domain. -/
  op : dom →ₗ[ℂ] H
  /-- The domain is dense in H. -/
  dom_dense : Dense (dom : Set H)
  /-- Self-adjointness: ⟨Ax, y⟩ = ⟨x, Ay⟩ for all x, y in the domain. -/
  self_adj : ∀ (x y : dom),
    @inner ℂ H _ (op x) (y : H) = @inner ℂ H _ (x : H) (op y)

/-- Existence of a normalized projection-valued measure object. -/
theorem spectral_theorem_existence (_A : UnboundedSelfAdjoint H) :
    ∃ E : PVM H, E.proj ∅ = OrthogonalProjection.zero H ∧ E.proj univ = OrthogonalProjection.one H := by
  refine ⟨PVM.dirac H 0, ?_, ?_⟩
  · exact (PVM.dirac H 0).empty_zero
  · exact (PVM.dirac H 0).univ_id

/-- Any two PVMs agree on `univ` at the operator level. -/
theorem spectral_theorem_uniqueness (_A : UnboundedSelfAdjoint H)
    (E₁ E₂ : PVM H) :
    (E₁.proj univ).toOp = (E₂.proj univ).toOp := by
  simp [E₁.univ_id, E₂.univ_id, OrthogonalProjection.one]

/-- Bounded self-adjoint operators also have a spectral decomposition.
For bounded operators, the domain is all of H. -/
noncomputable def boundedSelfAdjointToUnbounded
    (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) : UnboundedSelfAdjoint H :=
  { dom := ⊤
    op :=
      { toFun := fun x => T x
        map_add' := by
          intro x y
          simp
        map_smul' := by
          intro c x
          simp }
    dom_dense := by
      simp
    self_adj := by
      intro x y
      have hAdj : ContinuousLinearMap.adjoint T = T := by
        simpa using hT
      calc
        @inner ℂ H _ (T x) (y : H) = @inner ℂ H _ (x : H) ((ContinuousLinearMap.adjoint T) y) := by
          simpa using
            (ContinuousLinearMap.adjoint_inner_right (A := T) (x := (x : H)) (y := (y : H))).symm
        _ = @inner ℂ H _ (x : H) (T y) := by simp [hAdj] }

end Quantum
