import QuantumInfo.Finite.ResourceTheory.FreeState

/-!
# Finite-dimensional binary quantum hypothesis tests

This module contains the finite-dimensional testing interface used by
quantum Stein-type statements.  A binary test is represented by an effect
`A` with `0 ≤ A ≤ 1`; operationally, `A` is the POVM element for accepting
the first hypothesis.
-/

noncomputable section

namespace QuantumInfo
namespace Finite
namespace HypothesisTesting

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- A two-outcome quantum hypothesis test, represented by the effect for accepting
the first hypothesis. -/
structure BinaryTest (d : Type*) [Fintype d] [DecidableEq d] where
  effect : HermitianMat d ℂ
  zero_le : 0 ≤ effect
  le_one : effect ≤ 1

namespace BinaryTest

instance : Coe (BinaryTest d) (HermitianMat d ℂ) := ⟨BinaryTest.effect⟩

@[simp]
theorem coe_mk (A : HermitianMat d ℂ) (h0 h1) :
    ((BinaryTest.mk A h0 h1 : BinaryTest d) : HermitianMat d ℂ) = A :=
  rfl

/-- The complementary effect, accepting the second hypothesis. -/
def rejectFirst (T : BinaryTest d) : HermitianMat d ℂ :=
  1 - T.effect

theorem rejectFirst_zero_le (T : BinaryTest d) : 0 ≤ T.rejectFirst :=
  HermitianMat.zero_le_iff.mpr T.le_one

theorem rejectFirst_le_one (T : BinaryTest d) : T.rejectFirst ≤ 1 := by
  rw [← sub_nonneg]
  simpa [rejectFirst, sub_sub_cancel] using T.zero_le

/-- Type-I error: accepting the second hypothesis when the state is `ρ`. -/
def typeIError (T : BinaryTest d) (ρ : MState d) : ℝ :=
  ρ.exp_val T.rejectFirst

/-- Type-II error: accepting the first hypothesis when the state is `σ`. -/
def typeIIError (T : BinaryTest d) (σ : MState d) : ℝ :=
  σ.exp_val T.effect

theorem typeIError_nonneg (T : BinaryTest d) (ρ : MState d) :
    0 ≤ T.typeIError ρ :=
  ρ.exp_val_nonneg T.rejectFirst_zero_le

theorem typeIError_le_one (T : BinaryTest d) (ρ : MState d) :
    T.typeIError ρ ≤ 1 :=
  ρ.exp_val_le_one T.rejectFirst_le_one

theorem typeIError_prob (T : BinaryTest d) (ρ : MState d) :
    0 ≤ T.typeIError ρ ∧ T.typeIError ρ ≤ 1 :=
  ⟨T.typeIError_nonneg ρ, T.typeIError_le_one ρ⟩

theorem typeIIError_nonneg (T : BinaryTest d) (σ : MState d) :
    0 ≤ T.typeIIError σ :=
  σ.exp_val_nonneg T.zero_le

theorem typeIIError_le_one (T : BinaryTest d) (σ : MState d) :
    T.typeIIError σ ≤ 1 :=
  σ.exp_val_le_one T.le_one

theorem typeIIError_prob (T : BinaryTest d) (σ : MState d) :
    0 ≤ T.typeIIError σ ∧ T.typeIIError σ ≤ 1 :=
  ⟨T.typeIIError_nonneg σ, T.typeIIError_le_one σ⟩

/-- Feasibility for asymmetric hypothesis testing with type-I error at most `ε`. -/
def IsFeasible (T : BinaryTest d) (ρ : MState d) (ε : ℝ) : Prop :=
  T.typeIError ρ ≤ ε

/-- The set of type-II errors achievable under a type-I constraint. -/
def typeIIErrorSet (ρ σ : MState d) (ε : ℝ) : Set ℝ :=
  {β | ∃ T : BinaryTest d, T.IsFeasible ρ ε ∧ T.typeIIError σ = β}

/-- A real-valued finite-dimensional analogue of the `β_{ε}` optimization target
appearing in quantum Stein's lemma. -/
noncomputable def betaOptimal (ρ σ : MState d) (ε : ℝ) : ℝ :=
  sInf (typeIIErrorSet ρ σ ε)

theorem typeII_mem_typeIIErrorSet (T : BinaryTest d) {ρ σ : MState d} {ε : ℝ}
    (hT : T.IsFeasible ρ ε) :
    T.typeIIError σ ∈ typeIIErrorSet ρ σ ε :=
  ⟨T, hT, rfl⟩

end BinaryTest

end HypothesisTesting
end Finite
end QuantumInfo
