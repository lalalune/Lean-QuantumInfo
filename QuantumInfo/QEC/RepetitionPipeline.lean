import QEC.RepetitionCode.Recovery
import QEC.Stabilizer.Codes.RepetitionCode3
import QuantumInfo.QEC.Bridge
import QuantumInfo.QEC.Channels

/-!
# Repetition-Code Pipeline Bridge

Concrete end-to-end recovery results for the 3-qubit repetition code, expressed
through the `QuantumInfo` bridge layer.
-/

noncomputable section

namespace QuantumInfo
namespace QECBridge

open Quantum
open Quantum.StabilizerGroup

/-- Restatement of the integrated QEC theorem in the bridge namespace:
the 3-qubit repetition code corrects a single `X` error on qubit 1 after
encode → noise → recover → decode. -/
theorem repetition_corrects_single_X_q1
    (ψ : Quantum.Qubit) :
    Quantum.decode_state
      (Quantum.recover_state (Quantum.X_q1_3 • Quantum.encode_state ψ)
        (Quantum.norm_recoverVec_X_q1_3_encode_state ψ)) = ψ.val := by
  simpa using Quantum.repetition_corrects_single_X_q1 ψ

/-- The decoded output of the repetition recovery pipeline, packaged as a
normalized QEC state. -/
noncomputable def repetitionRecoveredQubit (ψ : Quantum.Qubit) : Quantum.Qubit :=
  ⟨Quantum.decode_state
      (Quantum.recover_state (Quantum.X_q1_3 • Quantum.encode_state ψ)
        (Quantum.norm_recoverVec_X_q1_3_encode_state ψ)),
    by
      have hdecode :
          Quantum.decode_state
              (Quantum.recover_state (Quantum.X_q1_3 • Quantum.encode_state ψ)
                (Quantum.norm_recoverVec_X_q1_3_encode_state ψ)) = ψ.val :=
        repetition_corrects_single_X_q1 (ψ := ψ)
      have hdecodeVec :
          Quantum.decodeVec
              (↑(Quantum.recover_state (Quantum.X_q1_3 • Quantum.encode_state ψ)
                (Quantum.norm_recoverVec_X_q1_3_encode_state ψ))) = ψ.val := by
        simpa [Quantum.decode_state] using hdecode
      simpa [hdecodeVec] using ψ.property⟩

/-- The recovered qubit equals the input qubit. -/
theorem repetitionRecoveredQubit_eq (ψ : Quantum.Qubit) :
    repetitionRecoveredQubit ψ = ψ := by
  ext q
  exact congrArg (fun v : Quantum.QubitVec => v q) (repetition_corrects_single_X_q1 (ψ := ψ))

/-- Bridge to `QuantumInfo` ket representation: recovery preserves the state. -/
theorem repetitionRecovered_toKet_eq (ψ : Quantum.Qubit) :
    toKet (repetitionRecoveredQubit ψ) = toKet ψ := by
  simpa [repetitionRecoveredQubit_eq (ψ := ψ)]

/-- Bridge to `QuantumInfo` pure mixed-state representation:
recovery preserves the induced pure `MState`. -/
theorem repetitionRecovered_toPureMState_eq (ψ : Quantum.Qubit) :
    toPureMState (repetitionRecoveredQubit ψ) = toPureMState ψ := by
  simpa [repetitionRecoveredQubit_eq (ψ := ψ)]

/-- Baseline CPTP adapter instance for the integrated repetition-code stabilizer
object, using the physical-space identity channels. -/
noncomputable def repetition3IdentityAdapters :
    StabilizerChannelAdapters RepetitionCode3.stabilizerCode (NQubitBasis 3) :=
  identityAdapters RepetitionCode3.stabilizerCode

/-- The baseline repetition-code adapter exactly corrects identity noise. -/
theorem repetition3IdentityAdapters_exactlyCorrects_id :
    ExactlyCorrects repetition3IdentityAdapters (CPTPMap.id (dIn := NQubitBasis 3)) := by
  simpa [repetition3IdentityAdapters] using
    identityAdapters_exactlyCorrects_id RepetitionCode3.stabilizerCode

end QECBridge
end QuantumInfo
