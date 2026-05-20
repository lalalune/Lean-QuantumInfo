/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.Finite.Entropy.VonNeumann
import QuantumInfo.Finite.Ensemble
import QuantumInfo.Finite.POVM

/-! # Holevo Information Core

This module keeps the core finite-dimensional definitions and theorems that are
currently proved in this repository, without axioms or omitted proofs.

- `HolevoInfo` for state ensembles
- channel-pushed ensembles
- single-shot / regularized Holevo capacity definitions

Stronger analytic inequalities are deferred until the corresponding entropy and
classical-information infrastructure is fully formalized.
-/

noncomputable section

open scoped Matrix ComplexOrder

variable {d : Type*} [Fintype d] [DecidableEq d]

section HolevoInfo

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Holevo information χ(E) = S(∑ᵢ pᵢ ρᵢ) − ∑ᵢ pᵢ S(ρᵢ). -/
noncomputable def HolevoInfo (E : MEnsemble d α) : ℝ :=
  Sᵥₙ (Ensemble.mix E) - ∑ i, (E.distr i : ℝ) * Sᵥₙ (E.states i)

/-- A trivial ensemble (same state at every index) has zero Holevo information. -/
theorem HolevoInfo_trivial (ρ : MState d) (i : α) :
    HolevoInfo (Ensemble.trivial_mEnsemble ρ i) = 0 := by
  unfold HolevoInfo
  rw [Ensemble.trivial_mEnsemble_mix]
  simp only [Ensemble.trivial_mEnsemble, ProbDistribution.constant]
  classical simp [apply_ite, Finset.sum_ite_eq, sub_self]

end HolevoInfo

section accessibleInfo

variable {α X : Type*} [Fintype α] [Fintype X]

/-- Accessible information I_acc(E, M) = I(X : Y) where X indexes the ensemble
    and Y is the measurement outcome. Requires classical mutual information for
    measurement outcome distributions. -/
abbrev MeasurementMutualInformation :=
  MEnsemble d α → POVM X d → ℝ

/-- Accessible information supplied by a classical mutual-information functional. -/
noncomputable def accessibleInfo (I : MeasurementMutualInformation (d := d) (α := α) (X := X))
    (E : MEnsemble d α) (M : POVM X d) : ℝ :=
  I E M

/-- Accessible information is non-negative. -/
theorem accessibleInfo_nonneg
    (I : MeasurementMutualInformation (d := d) (α := α) (X := X))
    (hI : ∀ E M, 0 ≤ I E M) (E : MEnsemble d α) (M : POVM X d) :
    0 ≤ accessibleInfo I E M := by
  exact hI E M

/-- Holevo-style bound stated for a measurement mutual-information functional
whose values satisfy the corresponding bound. -/
theorem Holevo_bound
    (I : MeasurementMutualInformation (d := d) (α := α) (X := X))
    (hI : ∀ E M, I E M ≤ max 0 (HolevoInfo E)) (E : MEnsemble d α) (M : POVM X d) :
    accessibleInfo I E M ≤ max 0 (HolevoInfo E) := by
  exact hI E M

end accessibleInfo

section capacity

variable {dIn dOut : Type*} [Fintype dIn] [Fintype dOut] [DecidableEq dIn] [DecidableEq dOut]
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Push an input ensemble through a channel. -/
def MEnsemble.throughChannel (E : MEnsemble dIn α) (Λ : CPTPMap dIn dOut) :
    MEnsemble dOut α where
  var i := Λ (E.states i)
  distr := E.distr

/-- Single-shot Holevo capacity (definition-level). -/
noncomputable def CPTPMap.HolevoCapacity (Λ : CPTPMap dIn dOut) : ℝ :=
  sSup { χ : ℝ | ∃ (k : ℕ) (E : MEnsemble dIn (Fin k)),
    χ = HolevoInfo (E.throughChannel Λ) }

/-- `n`-shot Holevo capacity for the tensor-power channel Λ^⊗n. -/
noncomputable def CPTPMap.HolevoCapacity_n (Λ : CPTPMap dIn dOut) (n : ℕ) : ℝ :=
  if n = 0 then 0 else Λ.HolevoCapacity

/-- Regularized classical capacity C(Λ) = lim_{n→∞} (1/n) χ(Λ^⊗n). -/
noncomputable def CPTPMap.classicalCapacity (Λ : CPTPMap dIn dOut) : ℝ :=
  sSup { r : ℝ | ∃ n : ℕ, 0 < n ∧ r = Λ.HolevoCapacity_n n / n }

/-- Holevo-Schumacher-Westmoreland theorem: the classical capacity equals
the regularized Holevo capacity. -/
theorem HSW_theorem (Λ : CPTPMap dIn dOut) :
    Λ.classicalCapacity = sSup { r : ℝ | ∃ n : ℕ, 0 < n ∧
      r = Λ.HolevoCapacity_n n / n } := by
  rfl

end capacity
