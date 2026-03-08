import Mathlib
import QuantumMechanics.UnitaryEvo.Stone
import QuantumMechanics.UnitaryEvo.Resolvent
import QuantumMechanics.UnitaryEvo.Yosida
import QuantumMechanics.BellsTheorem.CHSH_bounds

/-!
# Logos Bridge

Compatibility lemmas that connect Lean-QuantumInfo's finite-dimensional
`EuclideanSpace` setup with the abstract Hilbert-space assumptions used in
the integrated Logos development.

## Contents

* `FiniteHilbert d` — abbreviation for `EuclideanSpace ℂ d`, the canonical
  n-dimensional Hilbert space over ℂ in Lean-QuantumInfo.
* Basic `CompleteSpace` / `FiniteDimensional` instances for `FiniteHilbert`.
* `finiteDim_dense_univ` — density of the whole space.
* `finiteDim_operator_bounded` — every `ContinuousLinearMap` has an op-norm bound.
* `stone_finite_dim` — finite-dimensional corollary of Stone's theorem:
  every strongly-continuous one-parameter unitary group on `FiniteHilbert d` has
  a unique self-adjoint generator.
* CHSH / Tsirelson bridge: re-exports finite-dimensional CHSH theorems under `LogosBridge`
  namespace so the finite-dimensional integration surface is fully self-contained.
-/

open QuantumMechanics.StonesTheorem

noncomputable section

namespace QuantumInfo
namespace LogosBridge

abbrev FiniteHilbert (d : Type*) := EuclideanSpace ℂ d

variable {d : Type*} [Fintype d] [DecidableEq d]

instance instCompleteSpaceFiniteHilbert : CompleteSpace (FiniteHilbert d) := inferInstance

instance instFiniteDimensionalFiniteHilbert : FiniteDimensional ℂ (FiniteHilbert d) :=
  inferInstance

/-- In finite dimensions, the whole space is dense. -/
lemma finiteDim_dense_univ : Dense (Set.univ : Set (FiniteHilbert d)) :=
  dense_univ

/-- Any continuous linear operator has an operator-norm bound. -/
lemma finiteDim_operator_bounded (T : FiniteHilbert d →L[ℂ] FiniteHilbert d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ψ, ‖T ψ‖ ≤ C * ‖ψ‖ := by
  refine ⟨‖T‖, norm_nonneg _, ?_⟩
  intro ψ
  simpa using T.le_opNorm ψ

/-! ## Finite-Dimensional Stone Corollary

In finite dimensions every strongly-continuous one-parameter unitary group has
a *unique* self-adjoint generator.  This is an immediate specialisation of the
abstract `stone_bijection` from `QuantumMechanics.UnitaryEvo.Stone`
to `FiniteHilbert d`. No additional proof work is required because
`FiniteHilbert d` is already a complete complex inner-product space, which is
precisely the hypothesis of the abstract theorem.
-/

/-- **Finite-dimensional Stone theorem.**

For any `d : Type*` with `[Fintype d]`, every strongly-continuous one-parameter
unitary group on `FiniteHilbert d` has a unique self-adjoint generator.

This is the matrix-level corollary of the abstract `stone_bijection` from the
Logos library. -/
theorem stone_finite_dim :
    ∀ (U_grp : QuantumMechanics.Generators.OneParameterUnitaryGroup (H := FiniteHilbert d)),
    ∃! (gen : QuantumMechanics.Generators.Generator U_grp), gen.IsSelfAdjoint ∧
      (∀ (hsa : gen.IsSelfAdjoint) (h_dense : Dense (gen.domain : Set (FiniteHilbert d))),
        ∀ t ψ, (U_grp.U t) ψ = (QuantumMechanics.Yosida.exponential gen hsa h_dense t) ψ) :=
  stone_bijection

/-! ## CHSH / Tsirelson Bridge

The Tsirelson bound is proved in Logos over finite-dimensional `Matrix (Fin n) (Fin n) ℂ`.
We re-export the main theorem here so that the full integration surface for
Lean-QuantumInfo can be obtained by importing `QuantumInfo.InfiniteDim.LogosBridge`
alone.
-/

/-- **Tsirelson's bound** (re-export).

For any CHSH tuple `(A₀, A₁, B₀, B₁)` of Hermitian involutions on `Matrix (Fin n) (Fin n) ℂ`
with A-operators commuting with B-operators, and any density matrix `ρ`:

`|⟨A₀B₀ + A₀B₁ + A₁B₀ - A₁B₁⟩_ρ| ≤ 2√2`

This is the Tsirelson / quantum bound on the CHSH correlator — the Logos proof
transferred to the finite-dimensional matrix setting. -/
alias tsirelson_bound_transfer := QuantumInfo.tsirelson_bound

/-- **Commuting-observable CHSH bound** (re-export).

If either Alice's observables commute or Bob's observables commute, then CHSH
cannot exceed the classical bound `2` in magnitude. -/
alias chsh_commuting_bound_transfer := QuantumInfo.CHSH_commuting_bound

end LogosBridge
end QuantumInfo
