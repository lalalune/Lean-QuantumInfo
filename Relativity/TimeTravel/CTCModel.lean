/-
Copyright (c) 2026 Lean-QuantumInfo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Relativity.TimeTravel.BitProtocol

noncomputable section

namespace Relativity
namespace TimeTravel

/-- A CTC-style signaling primitive that returns a receive event in the sender's causal past. -/
structure CTCBitDevice (d : ℕ) where
  receiveEvent : Bit → Event d → Event d
  in_past : ∀ bit sender, timeCoord (receiveEvent bit sender) ≤ timeCoord sender
  exact_shift : ∀ bit sender,
    timeCoord sender - timeCoord (receiveEvent bit sender) = oneNanosecondInSeconds

/-- Package one CTC transmission into a `BitMessage`. -/
def CTCBitDevice.emit {d : ℕ} (D : CTCBitDevice d) (bit : Bit) (sender : Event d) :
    BitMessage d where
  sender := sender
  receiver := D.receiveEvent bit sender
  bit := bit

theorem ctc_device_produces_one_nanosecond_backward_message {d : ℕ}
    (D : CTCBitDevice d) (bit : Bit) (sender : Event d) :
    ∃ m : BitMessage d,
      m = D.emit bit sender ∧
      m.sender = sender ∧ m.bit = bit ∧ sentBackOneNanosecond m ∧ backwardCausal m := by
  refine ⟨D.emit bit sender, rfl, rfl, rfl, ?_, ?_⟩
  · simpa [sentBackOneNanosecond, sentBackBy, CTCBitDevice.emit] using D.exact_shift bit sender
  · simpa [backwardCausal, CTCBitDevice.emit] using D.in_past bit sender

theorem ctc_device_can_send_yes_or_no {d : ℕ}
    (D : CTCBitDevice d) (sender : Event d) :
    (∃ m : BitMessage d, m.sender = sender ∧ m.bit = true ∧ sentBackOneNanosecond m) ∧
    (∃ m : BitMessage d, m.sender = sender ∧ m.bit = false ∧ sentBackOneNanosecond m) := by
  constructor
  · rcases ctc_device_produces_one_nanosecond_backward_message D true sender with
      ⟨m, _, hm_sender, hm_bit, hm_shift, _⟩
    exact ⟨m, hm_sender, hm_bit, hm_shift⟩
  · rcases ctc_device_produces_one_nanosecond_backward_message D false sender with
      ⟨m, _, hm_sender, hm_bit, hm_shift, _⟩
    exact ⟨m, hm_sender, hm_bit, hm_shift⟩

end TimeTravel
end Relativity
