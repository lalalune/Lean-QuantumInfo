/-
Copyright (c) 2026 Lean-QuantumInfo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Relativity.TimeTravel.CTCModel

noncomputable section

namespace Relativity
namespace TimeTravel

/-- Acceptance predicate for candidate message transmissions. -/
abbrev MessagePolicy (d : ℕ) : Type := BitMessage d → Prop

/-- A weak one-bit protocol: both bit values can be sent one nanosecond to the past. -/
def WeakBackwardBitProtocol {d : ℕ} (accepts : MessagePolicy d) : Prop :=
  ∀ sender : Event d,
    (∃ m : BitMessage d,
      accepts m ∧ m.sender = sender ∧ m.bit = true ∧ sentBackOneNanosecond m) ∧
    (∃ m : BitMessage d,
      accepts m ∧ m.sender = sender ∧ m.bit = false ∧ sentBackOneNanosecond m)

/-- A strong one-bit protocol: the two bit-values are realized by distinct receive events. -/
def StrongBackwardBitProtocol {d : ℕ} (accepts : MessagePolicy d) : Prop :=
  ∀ sender : Event d, ∃ mTrue mFalse : BitMessage d,
    accepts mTrue ∧ accepts mFalse ∧
    mTrue.sender = sender ∧ mFalse.sender = sender ∧
    mTrue.bit = true ∧ mFalse.bit = false ∧
    sentBackOneNanosecond mTrue ∧ sentBackOneNanosecond mFalse ∧
    mTrue.receiver ≠ mFalse.receiver

lemma strongBackwardBitProtocol_implies_weak {d : ℕ} {accepts : MessagePolicy d}
    (h : StrongBackwardBitProtocol accepts) :
    WeakBackwardBitProtocol accepts := by
  intro sender
  rcases h sender with ⟨mTrue, mFalse, hmTrue_acc, hmFalse_acc, hmTrue_sender, hmFalse_sender,
    hmTrue_bit, hmFalse_bit, hmTrue_shift, hmFalse_shift, _⟩
  constructor
  · exact ⟨mTrue, hmTrue_acc, hmTrue_sender, hmTrue_bit, hmTrue_shift⟩
  · exact ⟨mFalse, hmFalse_acc, hmFalse_sender, hmFalse_bit, hmFalse_shift⟩

/-- Canonical policy accepting exactly the emitted messages of a CTC device. -/
def CTCBitDevice.accepts {d : ℕ} (D : CTCBitDevice d) : MessagePolicy d :=
  fun m => ∃ bit sender, m = D.emit bit sender

theorem ctc_accepts_weak_backward_protocol {d : ℕ} (D : CTCBitDevice d) :
    WeakBackwardBitProtocol D.accepts := by
  intro sender
  constructor
  · refine ⟨D.emit true sender, ?_, rfl, rfl, D.exact_shift true sender⟩
    exact ⟨true, sender, rfl⟩
  · refine ⟨D.emit false sender, ?_, rfl, rfl, D.exact_shift false sender⟩
    exact ⟨false, sender, rfl⟩

theorem ctc_accepts_strong_backward_protocol {d : ℕ} (D : CTCBitDevice d)
    (hDistinct : ∀ sender, D.receiveEvent true sender ≠ D.receiveEvent false sender) :
    StrongBackwardBitProtocol D.accepts := by
  intro sender
  refine ⟨D.emit true sender, D.emit false sender, ?_, ?_, rfl, rfl, rfl, rfl,
    D.exact_shift true sender, D.exact_shift false sender, ?_⟩
  · exact ⟨true, sender, rfl⟩
  · exact ⟨false, sender, rfl⟩
  · simpa [CTCBitDevice.emit] using hDistinct sender

end TimeTravel
end Relativity
