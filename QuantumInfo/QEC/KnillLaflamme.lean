import QEC.Foundations.KnillLaflamme
import QuantumInfo.QEC.Channels

/-!
# QEC Knill-Laflamme Bridge

Bridge layer from stabilizer-code integration points to the existing Knill-Laflamme
matrix conditions in the integrated QEC library.
-/

noncomputable section

namespace QuantumInfo
namespace QECBridge

open Quantum
open Quantum.StabilizerGroup

variable {n k : ℕ}
variable (C : StabilizerCode n k)

/-- Bundled Knill-Laflamme data over the physical `n`-qubit matrix interface
associated to a stabilizer code. -/
structure KnillLaflammeWitness (C : StabilizerCode n k) where
  projector : Matrix (NQubitBasis n) (NQubitBasis n) ℂ
  errors : Finset (Matrix (NQubitBasis n) (NQubitBasis n) ℂ)
  correctable : Quantum.IsCorrectableCode projector errors

namespace KnillLaflammeWitness

variable {C}
variable (W : KnillLaflammeWitness C)

/-- Diagonal Knill-Laflamme coefficients are nonnegative reals
(re-export of the proved QEC theorem on the bridged interface). -/
theorem diag_nonneg (hP_nonzero : W.projector ≠ 0) (Ei : W.errors) :
    ∃ r : ℝ, 0 ≤ r ∧
      W.projector * (Ei.1.conjTranspose * Ei.1) * W.projector = (r : ℂ) • W.projector := by
  exact Quantum.IsCorrectableCode_diag_nonneg W.correctable hP_nonzero Ei

end KnillLaflammeWitness

end QECBridge
end QuantumInfo
