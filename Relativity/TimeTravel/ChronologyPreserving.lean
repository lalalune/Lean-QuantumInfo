/-
Copyright (c) 2026 Lean-QuantumInfo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Relativity.TimeTravel.BitProtocol

noncomputable section

namespace Relativity
namespace TimeTravel

/-- A channel model that only permits forward-causal transmissions. -/
structure ChronologyPreservingChannel (d : ℕ) where
  accepts : BitMessage d → Prop
  forward_only : ∀ {m : BitMessage d}, accepts m → forwardCausal m

lemma timeComponent_nonneg_of_forwardCausal {d : ℕ} {sender receiver : Event d}
    (h : timeCoord sender ≤ timeCoord receiver) :
    0 ≤ timeCoord receiver - timeCoord sender := by
  exact sub_nonneg.mpr h

lemma no_backward_shift_of_forwardCausal {d : ℕ}
    {sender receiver : Event d} {Δt : ℝ}
    (hForward : timeCoord sender ≤ timeCoord receiver)
    (hShift : timeCoord sender - timeCoord receiver = Δt)
    (hΔt : 0 < Δt) : False := by
  have hNonneg : 0 ≤ timeCoord receiver - timeCoord sender :=
    timeComponent_nonneg_of_forwardCausal hForward
  have hToReceiver : timeCoord receiver - timeCoord sender = -Δt := by
    linarith
  have hLt : timeCoord receiver - timeCoord sender < 0 := by
    rw [hToReceiver]
    linarith
  exact (not_lt_of_ge hNonneg) hLt

theorem no_one_nanosecond_back_on_chronology_preserving_channel {d : ℕ}
    (C : ChronologyPreservingChannel d) {m : BitMessage d}
    (hAccept : C.accepts m)
    (hBack : sentBackOneNanosecond m) : False := by
  exact no_backward_shift_of_forwardCausal
    (hForward := C.forward_only hAccept)
    (hShift := hBack)
    (hΔt := oneNanosecondInSeconds_pos)

theorem no_bit_to_past_one_nanosecond {d : ℕ}
    (C : ChronologyPreservingChannel d) :
    ∀ {m : BitMessage d}, C.accepts m → ¬ sentBackOneNanosecond m := by
  intro m hAccept hBack
  exact no_one_nanosecond_back_on_chronology_preserving_channel C hAccept hBack

end TimeTravel
end Relativity
