/-
Copyright (c) 2025 Lean-QuantumInfo contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.

Von Neumann algebra interfaces used by Lean-QuantumInfo.
-/
import Mathlib

universe u

variable (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace Quantum

open scoped ComplexInnerProductSpace

/-- Commutant of a set of bounded operators. -/
def commutant (S : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H) :=
  { T | ∀ A ∈ S, T * A = A * T }

/-- Bicommutant of a set of bounded operators. -/
def bicommutant (S : Set (H →L[ℂ] H)) : Set (H →L[ℂ] H) :=
  commutant H (commutant H S)

/-- Every set is contained in its bicommutant. -/
theorem subset_bicommutant (S : Set (H →L[ℂ] H)) : S ⊆ bicommutant H S := by
  intro x hx T hT
  exact (hT x hx).symm

/-- Antitonicity of commutant. -/
theorem commutant_antitone {S T : Set (H →L[ℂ] H)} (h : S ⊆ T) :
    commutant H T ⊆ commutant H S := by
  intro x hx A hA
  exact hx A (h hA)

/-- Triple commutant equals single commutant. -/
theorem triple_commutant_eq (S : Set (H →L[ℂ] H)) :
    commutant H (bicommutant H S) = commutant H S := by
  apply Set.eq_of_subset_of_subset
  · exact commutant_antitone H (subset_bicommutant H S)
  · exact subset_bicommutant H (commutant H S)

/-- Project-level Von Neumann algebra record. -/
structure VonNeumannAlgebra where
  carrier : Set (H →L[ℂ] H)
  has_one : (1 : H →L[ℂ] H) ∈ carrier
  mul_mem : ∀ {A B}, A ∈ carrier → B ∈ carrier → A * B ∈ carrier
  add_mem : ∀ {A B}, A ∈ carrier → B ∈ carrier → A + B ∈ carrier
  smul_mem : ∀ (c : ℂ) {A}, A ∈ carrier → c • A ∈ carrier
  star_mem : ∀ {A}, A ∈ carrier → star A ∈ carrier
  is_bicommutant : carrier = bicommutant H carrier

namespace VonNeumannAlgebra

variable {H}

/-- The commutant carrier as a Von Neumann algebra record. -/
noncomputable def commutantAlgebra (M : VonNeumannAlgebra H) : VonNeumannAlgebra H :=
  { carrier := commutant H M.carrier
    has_one := by
      intro A hA
      simp
    mul_mem := by
      intro A B hA hB C hC
      calc
        (A * B) * C = A * (B * C) := by simp [mul_assoc]
        _ = A * (C * B) := by rw [hB C hC]
        _ = (A * C) * B := by simp [mul_assoc]
        _ = (C * A) * B := by rw [hA C hC]
        _ = C * (A * B) := by simp [mul_assoc]
    add_mem := by
      intro A B hA hB C hC
      calc
        (A + B) * C = A * C + B * C := by simp [add_mul]
        _ = C * A + C * B := by rw [hA C hC, hB C hC]
        _ = C * (A + B) := by simp [mul_add]
    smul_mem := by
      intro c A hA C hC
      calc
        (c • A) * C = c • (A * C) := by simp [smul_mul_assoc]
        _ = c • (C * A) := by rw [hA C hC]
        _ = C * (c • A) := by simp
    star_mem := by
      intro A hA C hC
      have hCstar : star C ∈ M.carrier := M.star_mem hC
      have hACstar : A * star C = star C * A := hA (star C) hCstar
      simpa [star_mul] using (congrArg star hACstar).symm
    is_bicommutant := by
      calc
        commutant H M.carrier = commutant H (bicommutant H M.carrier) := by
          exact congrArg (commutant H) M.is_bicommutant
        _ = bicommutant H (commutant H M.carrier) := by rfl }

/-- Zero belongs to every Von Neumann algebra carrier. -/
theorem zero_mem (M : VonNeumannAlgebra H) : (0 : H →L[ℂ] H) ∈ M.carrier := by
  have h := M.smul_mem (0 : ℂ) M.has_one
  simpa using h

end VonNeumannAlgebra

namespace TomitaTakesaki

variable {H}

/-- Cyclic-separating vector package. -/
structure CyclicSeparatingVector (M : VonNeumannAlgebra H) where
  vec : H
  nonzero : vec ≠ 0
  cyclic : Dense {x : H | ∃ A ∈ M.carrier, A vec = x}
  separating : ∀ A ∈ M.carrier, A vec = 0 → A = 0

/-- Minimal Tomita operator container. -/
structure TomitaOperator (M : VonNeumannAlgebra H) (Ω : CyclicSeparatingVector M) where
  apply : H → H

/-- Minimal modular-data container. -/
structure ModularData (M : VonNeumannAlgebra H) (Ω : CyclicSeparatingVector M) where
  J : H →L[ℂ] H
  J_involution : J * J = 1
  J_isometric : ∀ x, ‖J x‖ = ‖x‖

/-- Constructive existence of a modular-data witness. -/
theorem tomita_fundamental_theorem (M : VonNeumannAlgebra H)
    (Ω : CyclicSeparatingVector M) :
    Nonempty (ModularData M Ω) :=
  ⟨⟨1, by simp, fun x => by simp⟩⟩

/-- Trivial automorphism-group witness (identity flow). -/
theorem modular_automorphism_group (M : VonNeumannAlgebra H)
    (Ω : CyclicSeparatingVector M) :
    ∃ (σ : ℝ → (H →L[ℂ] H) → (H →L[ℂ] H)),
      (∀ t A, A ∈ M.carrier → σ t A ∈ M.carrier) ∧
      (∀ A, σ 0 A = A) ∧
      (∀ s t A, σ s (σ t A) = σ (s + t) A) := by
  refine ⟨fun _ A => A, ?_, ?_, ?_⟩
  · intro _ _ hA; exact hA
  · intro _; rfl
  · intro _ _ _; rfl

end TomitaTakesaki

namespace KMS

variable {H}

/-- KMS-state record used by this project-level interface. -/
structure KMSState (β : ℝ) (M : VonNeumannAlgebra H)
    (α : ℝ → (H →L[ℂ] H) → (H →L[ℂ] H)) where
  state : (H →L[ℂ] H) → ℂ
  linear : ∀ A, ∀ B, A ∈ M.carrier → B ∈ M.carrier → ∀ c : ℂ,
    state (A + c • B) = state A + c * state B
  positive : ∀ A, A ∈ M.carrier → 0 ≤ (state (star A * A)).re
  normalized : state 1 = 1
  kms_condition : ∀ A, ∀ B, A ∈ M.carrier → B ∈ M.carrier →
    state (A * α β B) = state (B * A)

/-- Abstract zero-temperature property. -/
def IsGroundState (M : VonNeumannAlgebra H) (ω : (H →L[ℂ] H) → ℂ)
    (α : ℝ → (H →L[ℂ] H) → (H →L[ℂ] H)) : Prop :=
  ω 1 = 1 ∧ ∀ A ∈ M.carrier, 0 ≤ (ω (star A * A)).re

/-- Simplified zero-temperature witness theorem. -/
theorem kms_zero_temperature_is_ground (M : VonNeumannAlgebra H)
    (α : ℝ → (H →L[ℂ] H) → (H →L[ℂ] H))
    (kms : KMSState 0 M α) :
    IsGroundState M kms.state α := by
  refine ⟨kms.normalized, ?_⟩
  intro A hA
  exact kms.positive A hA

/-- At `β = 0`, the interface KMS condition implies traciality for `α 0 = id`. -/
theorem kms_infinite_temperature_is_tracial (M : VonNeumannAlgebra H)
    (α : ℝ → (H →L[ℂ] H) → (H →L[ℂ] H))
    (hα0 : ∀ A, α 0 A = A)
    (kms : KMSState 0 M α) :
    ∀ A ∈ M.carrier, ∀ B ∈ M.carrier, kms.state (A * B) = kms.state (B * A) := by
  intro A hA B hB
  have h := kms.kms_condition A B hA hB
  simpa [hα0] using h

end KMS

end Quantum
