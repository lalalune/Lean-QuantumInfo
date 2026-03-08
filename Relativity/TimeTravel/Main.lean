/-
Copyright (c) 2026 Lean-QuantumInfo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Relativity.TimeTravel.ChronologyPreserving
import Relativity.TimeTravel.CTCModel
import Relativity.TimeTravel.CommunicationSemantics
import Relativity.TimeTravel.CausalCycles
import Relativity.TimeTravel.PaperModels

noncomputable section

namespace Relativity
namespace TimeTravel

/-- Unified answer layer:
- chronology-preserving channels forbid sending one bit one nanosecond to the past;
- a CTC-style device can produce such a message. -/
theorem one_nanosecond_time_travel_answer_by_model {d : ℕ} :
    (∀ (C : ChronologyPreservingChannel d) {m : BitMessage d},
      C.accepts m → ¬ sentBackOneNanosecond m) ∧
    (∀ (D : CTCBitDevice d) (bit : Bit) (sender : Event d),
      ∃ m : BitMessage d,
        m = D.emit bit sender ∧
        m.sender = sender ∧ m.bit = bit ∧ sentBackOneNanosecond m ∧ backwardCausal m) := by
  constructor
  · intro C m hAccept
    exact no_bit_to_past_one_nanosecond C hAccept
  · intro D bit sender
    exact ctc_device_produces_one_nanosecond_backward_message D bit sender

/-- Equivalent cycle framing:
chronology-preserving channels forbid accepted backward-cycle witnesses,
while CTC devices construct them. -/
theorem one_nanosecond_cycle_answer_by_model {d : ℕ} :
    (∀ C : ChronologyPreservingChannel d, ¬ AdmitsCausalCycle C.accepts) ∧
    (∀ D : CTCBitDevice d, AdmitsCausalCycle D.accepts) := by
  constructor
  · intro C
    exact chronology_preserving_forbids_causal_cycle_protocol C
  · intro D
    exact ctc_accepts_admits_causal_cycle D

end TimeTravel
end Relativity
