/-
Copyright (c) 2026 Lean-QuantumInfo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Relativity.TimeTravel.CommunicationSemantics
import Relativity.TimeTravel.ChronologyPreserving

noncomputable section

namespace Relativity
namespace TimeTravel

/-- In chronology-preserving models, no weak one-bit backward protocol can exist. -/
theorem no_weak_backward_protocol_on_chronology_preserving_channel {d : ℕ}
    (C : ChronologyPreservingChannel d) :
    ¬ WeakBackwardBitProtocol C.accepts := by
  intro hWeak
  let sender : Event d := fun _ => 0
  rcases (hWeak sender).1 with ⟨m, hmAcc, _, _, hmBack⟩
  exact (no_bit_to_past_one_nanosecond C hmAcc) hmBack

/-- In chronology-preserving models, no strong one-bit backward protocol can exist. -/
theorem no_strong_backward_protocol_on_chronology_preserving_channel {d : ℕ}
    (C : ChronologyPreservingChannel d) :
    ¬ StrongBackwardBitProtocol C.accepts := by
  intro hStrong
  exact no_weak_backward_protocol_on_chronology_preserving_channel C
    (strongBackwardBitProtocol_implies_weak hStrong)

end TimeTravel
end Relativity
