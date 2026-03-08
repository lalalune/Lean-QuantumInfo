import Mathlib
import QEC.Foundations.Foundations
import QuantumInfo.Finite.Braket
import QuantumInfo.Finite.MState

/-!
# QEC Bridge

Bridge definitions between the integrated `QEC` library and the existing
`QuantumInfo` finite-dimensional state model.
-/

noncomputable section

namespace QuantumInfo
namespace QECBridge

open Quantum

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Convert a QEC normalized state into a `QuantumInfo` ket. -/
def toKet (ψ : QuantumState α) : Ket α := by
  refine ⟨ψ.1, ?_⟩
  have hsq : (Quantum.norm ψ.1) ^ 2 = ∑ i, ‖ψ.1 i‖ ^ 2 := Quantum.norm_sq_def (v := ψ.1)
  calc
    ∑ i, ‖ψ.1 i‖ ^ 2 = (Quantum.norm ψ.1) ^ 2 := by simpa using hsq.symm
    _ = (1 : ℝ) ^ 2 := by rw [ψ.2]
    _ = 1 := by norm_num

/-- Convert a `QuantumInfo` ket into a QEC normalized state. -/
def fromKet (ψ : Ket α) : QuantumState α := by
  refine ⟨ψ.vec, ?_⟩
  unfold Quantum.norm
  have : Real.sqrt (∑ x, ‖ψ.vec x‖ ^ 2) = Real.sqrt 1 := by
    simpa [ψ.normalized']
  simpa using this.trans Real.sqrt_one

/-- The conversions are inverse on `Ket`. -/
theorem toKet_fromKet (ψ : Ket α) : toKet (fromKet ψ) = ψ := by
  ext i
  rfl

/-- The conversions are inverse on `QuantumState`. -/
theorem fromKet_toKet (ψ : QuantumState α) : fromKet (toKet ψ) = ψ := by
  cases ψ
  rfl

/-- Pure-state bridge into `MState`. -/
def toPureMState (ψ : QuantumState α) : MState α :=
  MState.pure (toKet ψ)

/-- Finite basis equivalence for QEC n-qubit basis states. -/
noncomputable def basisEquiv (n : ℕ) : NQubitBasis n ≃ Fin (2 ^ n) := by
  let e : NQubitBasis n ≃ Fin (Fintype.card (NQubitBasis n)) := Fintype.equivFin (NQubitBasis n)
  have hcard : Fintype.card (NQubitBasis n) = 2 ^ n := by
    simpa [NQubitBasis, QubitBasis] using
      (Fintype.card_fun (α := Fin n) (β := Fin 2))
  exact hcard ▸ e

end QECBridge
end QuantumInfo
