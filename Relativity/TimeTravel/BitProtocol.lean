/-
Copyright (c) 2026 Lean-QuantumInfo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

noncomputable section

namespace Relativity
namespace TimeTravel

/-- A one-bit payload. -/
abbrev Bit : Type := Bool

/-- Minimal event model: an event is a coordinate assignment with one distinguished time slot. -/
abbrev Event (d : ℕ) : Type := Fin (d + 1) → ℝ

/-- Time-coordinate index. -/
def timeIndex (d : ℕ) : Fin (d + 1) := ⟨0, Nat.succ_pos d⟩

/-- Time-coordinate projection. -/
def timeCoord {d : ℕ} (e : Event d) : ℝ := e (timeIndex d)

/-- A single bit-transmission event pair in Minkowski spacetime. -/
structure BitMessage (d : ℕ) where
  sender : Event d
  receiver : Event d
  bit : Bit

/-- One nanosecond in seconds. -/
noncomputable def oneNanosecondInSeconds : ℝ :=
  (1 : ℝ) / 1000000000

lemma oneNanosecondInSeconds_pos : 0 < oneNanosecondInSeconds := by
  norm_num [oneNanosecondInSeconds]

/-- Message `m` is received `Δt` seconds before it is sent. -/
def sentBackBy {d : ℕ} (Δt : ℝ) (m : BitMessage d) : Prop :=
  timeCoord m.sender - timeCoord m.receiver = Δt

/-- Message `m` is received exactly one nanosecond before sending. -/
def sentBackOneNanosecond {d : ℕ} (m : BitMessage d) : Prop :=
  sentBackBy oneNanosecondInSeconds m

/-- Forward-causal admissibility for a message. -/
def forwardCausal {d : ℕ} (m : BitMessage d) : Prop :=
  timeCoord m.sender ≤ timeCoord m.receiver

/-- Backward-causal placement for a message (receiver in the sender's causal past). -/
def backwardCausal {d : ℕ} (m : BitMessage d) : Prop :=
  timeCoord m.receiver ≤ timeCoord m.sender

lemma sentBackBy_pos_implies_backwardCausal {d : ℕ} {m : BitMessage d} {Δt : ℝ}
    (hShift : sentBackBy Δt m) (hΔt : 0 < Δt) : backwardCausal m := by
  unfold sentBackBy backwardCausal at *
  linarith

lemma sentBackOneNanosecond_implies_backwardCausal {d : ℕ} {m : BitMessage d}
    (h : sentBackOneNanosecond m) : backwardCausal m := by
  exact sentBackBy_pos_implies_backwardCausal h oneNanosecondInSeconds_pos

end TimeTravel
end Relativity
