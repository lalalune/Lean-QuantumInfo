/-
Copyright (c) 2026 Lean-QuantumInfo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Relativity.TimeTravel.CausalCycles

noncomputable section

namespace Relativity
namespace TimeTravel

/-- Chronology-respecting model class (SR-style, no CTC primitive). -/
structure ChronologyRespectingModel (d : ℕ) where
  channel : ChronologyPreservingChannel d

/-- Deutsch-style CTC model class with explicit CTC device primitive. -/
structure DeutschCTCModel (d : ℕ) where
  device : CTCBitDevice d

/-- Post-selected CTC (P-CTC) model class, formalized with the same signaling primitive. -/
structure PCTCModel (d : ℕ) where
  device : CTCBitDevice d

theorem chronologyRespectingModel_no_backward_protocol {d : ℕ}
    (M : ChronologyRespectingModel d) :
    ¬ WeakBackwardBitProtocol M.channel.accepts :=
  no_weak_backward_protocol_on_chronology_preserving_channel M.channel

theorem deutschCTCModel_has_backward_protocol {d : ℕ}
    (M : DeutschCTCModel d) :
    WeakBackwardBitProtocol M.device.accepts :=
  ctc_accepts_weak_backward_protocol M.device

theorem pCTCModel_has_backward_protocol {d : ℕ}
    (M : PCTCModel d) :
    WeakBackwardBitProtocol M.device.accepts :=
  ctc_accepts_weak_backward_protocol M.device

theorem paper_model_classification_one_nanosecond {d : ℕ} :
    (∀ M : ChronologyRespectingModel d, ¬ WeakBackwardBitProtocol M.channel.accepts) ∧
    (∀ M : DeutschCTCModel d, WeakBackwardBitProtocol M.device.accepts) ∧
    (∀ M : PCTCModel d, WeakBackwardBitProtocol M.device.accepts) := by
  constructor
  · intro M
    exact chronologyRespectingModel_no_backward_protocol M
  constructor
  · intro M
    exact deutschCTCModel_has_backward_protocol M
  · intro M
    exact pCTCModel_has_backward_protocol M

end TimeTravel
end Relativity
