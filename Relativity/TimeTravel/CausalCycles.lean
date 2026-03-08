/-
Copyright (c) 2026 Lean-QuantumInfo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Relativity.TimeTravel.NoPastSignaling

noncomputable section

namespace Relativity
namespace TimeTravel

/-- A policy admits one-nanosecond backward signaling if some accepted message is sent back. -/
def AdmitsBackwardSignal {d : ℕ} (accepts : MessagePolicy d) : Prop :=
  ∃ m : BitMessage d, accepts m ∧ sentBackOneNanosecond m

/-- A policy admits a causal cycle witness if some accepted message is backward-causal. -/
def AdmitsCausalCycle {d : ℕ} (accepts : MessagePolicy d) : Prop :=
  ∃ m : BitMessage d, accepts m ∧ backwardCausal m ∧ sentBackOneNanosecond m

theorem admitsBackwardSignal_iff_admitsCausalCycle {d : ℕ} (accepts : MessagePolicy d) :
    AdmitsBackwardSignal accepts ↔ AdmitsCausalCycle accepts := by
  constructor
  · rintro ⟨m, hmAcc, hmBack⟩
    exact ⟨m, hmAcc, sentBackOneNanosecond_implies_backwardCausal hmBack, hmBack⟩
  · rintro ⟨m, hmAcc, _, hmBack⟩
    exact ⟨m, hmAcc, hmBack⟩

theorem weakBackwardBitProtocol_implies_admitsCausalCycle {d : ℕ} {accepts : MessagePolicy d}
    (hWeak : WeakBackwardBitProtocol accepts) :
    AdmitsCausalCycle accepts := by
  let sender : Event d := fun _ => 0
  rcases (hWeak sender).1 with ⟨m, hmAcc, _, _, hmBack⟩
  exact ⟨m, hmAcc, sentBackOneNanosecond_implies_backwardCausal hmBack, hmBack⟩

theorem chronology_preserving_forbids_causal_cycle_protocol {d : ℕ}
    (C : ChronologyPreservingChannel d) :
    ¬ AdmitsCausalCycle C.accepts := by
  intro hCycle
  rcases hCycle with ⟨m, hmAcc, _, hmBack⟩
  exact (no_bit_to_past_one_nanosecond C hmAcc) hmBack

theorem ctc_accepts_admits_causal_cycle {d : ℕ} (D : CTCBitDevice d) :
    AdmitsCausalCycle D.accepts := by
  let sender : Event d := fun _ => 0
  refine ⟨D.emit true sender, ?_, ?_, ?_⟩
  · exact ⟨true, sender, rfl⟩
  · exact sentBackOneNanosecond_implies_backwardCausal (D.exact_shift true sender)
  · exact D.exact_shift true sender

end TimeTravel
end Relativity
