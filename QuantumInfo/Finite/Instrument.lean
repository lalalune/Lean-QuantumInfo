/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.Finite.CPTPMap

/-! # Quantum Instruments

A quantum instrument is a finite collection of completely positive (CP) maps whose
sum is trace-preserving (TP). This generalizes both CPTP maps (a single-outcome instrument)
and POVMs (instruments where we discard the post-measurement state).

Quantum instruments were introduced by Davies and Lewis (1970) as a way to describe
measurements that also record the post-measurement state.

## Main definitions

 * `Instrument`: A collection of CP maps whose sum is TP.
 * `Instrument.channel`: The overall CPTP channel (sum of all maps).
 * `Instrument.probability`: Probability of outcome `x` on state `ρ`.
 * `Instrument.postMeasurementMap`: The subnormalized output map for outcome `x`.

## References

 * Davies, E.B. and Lewis, J.T. "An operational approach to quantum probability."
   Communications in Mathematical Physics, 1970.
-/

noncomputable section

open scoped Matrix ComplexOrder

variable {X : Type*} {dIn dOut : Type*} [Fintype X] [Fintype dIn] [Fintype dOut]
  [DecidableEq dIn] [DecidableEq dOut] [DecidableEq X]

/-- A quantum instrument is a finite collection of completely positive (CP) linear maps
indexed by outcomes `X`, whose sum is trace-preserving. Each individual map `Φ_x`
represents the state transformation conditioned on outcome `x`.

The sum `∑ x, maps x` gives a CPTP map (available as `Instrument.channel`). -/
structure Instrument (X : Type*) (dIn dOut : Type*)
    [Fintype X] [Fintype dIn] [Fintype dOut] [DecidableEq dIn] [DecidableEq dOut] where
  /-- The CP maps indexed by outcomes. Each map is completely positive but generally
  not trace-preserving individually. -/
  cpMaps : X → MatrixMap dIn dOut ℂ
  /-- Each component map is completely positive. -/
  cp : ∀ x, (cpMaps x).IsCompletelyPositive
  /-- The sum of all component maps is trace-preserving. -/
  sum_TP : (∑ x, cpMaps x).IsTracePreserving

namespace Instrument

variable (I : Instrument X dIn dOut)

/-- The overall CPTP channel of an instrument, obtained by summing all component maps.
This represents the channel obtained when we perform the instrument but forget the outcome. -/
def channel : CPTPMap dIn dOut where
  toLinearMap := ∑ x, I.cpMaps x
  cp := by
    apply Finset.sum_induction
    · exact fun _ _ ha ↦ ha.add
    · exact MatrixMap.IsCompletelyPositive.zero _ _
    · exact fun x _ ↦ I.cp x
  TP := I.sum_TP

/-- The probability of outcome `x` given input state `ρ`.
This is the trace of the (subnormalized) output Φ_x(ρ). -/
def probability (x : X) (ρ : MState dIn) : ℝ :=
  ((I.cpMaps x) ρ.m).trace.re

/-- The probabilities of all outcomes sum to 1 for any input state. -/
theorem sum_probability (ρ : MState dIn) :
    ∑ x, I.probability x ρ = 1 := by
  simp only [probability]
  rw [← Complex.re_sum, ← Matrix.trace_sum, ← LinearMap.sum_apply]
  rw [show (∑ x : X, I.cpMaps x) = I.channel.map from rfl]
  rw [I.channel.TP ρ.m]
  exact Complex.one_re ▸ congrArg Complex.re ρ.tr'

/-- Each outcome probability is non-negative. -/
theorem probability_nonneg (x : X) (ρ : MState dIn) :
    0 ≤ I.probability x ρ := by
  unfold probability
  have hpos : ((I.cpMaps x) ρ.m).PosSemidef := (I.cp x).IsPositive ρ.nonneg
  exact (RCLike.nonneg_iff.mp hpos.trace_nonneg).1

/-- The (subnormalized) post-measurement linear map for outcome `x`. -/
def postMeasurementMap (x : X) : MatrixMap dIn dOut ℂ :=
  I.cpMaps x

/-- Applying the full instrument channel is the same as summing over all outcomes. -/
theorem channel_eq_sum (ρ : MState dIn) :
    I.channel.map ρ.m = ∑ x, I.postMeasurementMap x ρ.m := by
  change ((∑ x, I.cpMaps x) ρ.m) = ∑ x, I.cpMaps x ρ.m
  simpa using LinearMap.sum_apply (σ₁₂ := RingHom.id ℂ) Finset.univ I.cpMaps ρ.m

/-- A single-outcome instrument (where `X` is a `Unique` type) is equivalent to
a CPTP map. -/
def ofCPTPMap [Unique X] (Λ : CPTPMap dIn dOut) : Instrument X dIn dOut where
  cpMaps _ := Λ.map
  cp _ := Λ.cp
  sum_TP := by
    simp only [Finset.univ_unique, Finset.sum_singleton]
    exact Λ.TP

/-- The instrument whose channel is the given CPTP map and which has a single outcome. -/
theorem ofCPTPMap_channel [Unique X] (Λ : CPTPMap dIn dOut) :
    (ofCPTPMap (X := X) Λ).channel = Λ := by
  ext ρ i j
  simp [ofCPTPMap, channel]

end Instrument
