/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import Mathlib.Analysis.SpecialFunctions.Log.Base

import QuantumInfo.Finite.Entropy
import QuantumInfo.Finite.CPTPMap
import QuantumInfo.Finite.Distance


/-! # Quantum Capacity

This focuses on defining and proving theorems about quantum capacities, especially the asymptotic quantum capacity: the maximum rate at which quantum information can be coherently transmitted. The precise asymptotic definition is not consistent in the literature, see [Capacity_doc](./QuantumInfo/Finite/Capacity_doc.html) for a note on what has been used and how that was used to arrive at the following definition:

 1. A channel A `Emulates` another channel B if there are D and E such that D∘A∘E = B.
 2. A channel A `εApproximates` channel B (of the same dimensions) if the for every state ρ, the fidelity F(A(ρ), B(ρ)) is at least 1-ε.
 3. A channel A `AchievesRate` R:ℝ if for every ε>0, n copies of A emulates some channel B such that log2(dimout(B))/n ≥ R, and that B is εApproximately the identity.
 4. The `quantumCapacity` of the channel A is the supremum of the achievable rates, i.e. `sSup { R : ℝ | AchievesRate A R }`.

The most basic facts:
 * `emulates_self`: Every channel emulates itself.
 * `emulates_trans`: If A emulates B and B emulates C, then A emulates C. (That is, emulation is an ordering.)
 * `piProd_id`: The finite tensor product of identity channels is the identity channel.
 * `εApproximates A B ε` is equivalent to the existence of some δ (depending ε and dims(A)) so that |A-B| has diamond norm at most δ, and δ→0 as ε→0.
 * `achievesRate_0`: Every channel achievesRate 0. So, the set of achievable rates is Nonempty.
 * If a channel achievesRate R₁, it also every achievesRate R₂ every R₂ ≤ R₁, i.e. it is an interval extending left towards -∞. Achievable rates are `¬BddBelow`.
 * `bddAbove_achievesRate`: A channel C : dimX → dimY cannot achievesRate R with `R > log2(min(dimX, dimY))`. Thus, the interval is `BddAbove`.

The nice lemmas we would want:
 * Capacity of a replacement channel is zero.
 * Capacity of an identity channel is `log2(D)`.
 * Capacity is superadditive under tensor products. (That is, at least additive. Showing that it isn't _exactly_ additive, unlike classical capacity which is additive, is a much harder task.)
 * Capacity of a kth tensor power is exactly k times the capacity of the original channel.
 * Capacity does not decrease under tensor sums.
 * Capacity does not increase under composition.

Then, we should show that our definition is equivalent to some above. Most, except (3), should be not too hard to prove.

Then the LSD theorem establishes that the single-copy coherent information is a lower bound. This is stated in `coherentInfo_le_quantumCapacity`. The corollary, that the n-copy coherent information converges to the capacity, is `quantumCapacity_eq_piProd_coherentInfo`.

# Implemented capacity API

 * `CPTPMap.quantumCapacity`: asymptotic quantum capacity from achievable emulation rates.
 * `CPTPMap.oneShotQuantumCapacity`: single-use coherent-information capacity, defined as the supremum of `coherentInfo ρ Λ` over input states.
-/

namespace CPTPMap

variable {d₁ d₂ d₃ d₄ d₅ d₆ : Type*}
variable [Fintype d₁] [Fintype d₂] [Fintype d₃] [Fintype d₄] [Fintype d₅] [Fintype d₆] [DecidableEq d₁] [DecidableEq d₂]

variable [DecidableEq d₃] [DecidableEq d₄] in
/--
A channel Λ₁ `Emulates` another channel Λ₂ if there are D and E such that D∘Λ₁∘E = Λ₂.
-/
def Emulates (Λ₁ : CPTPMap d₁ d₂) (Λ₂ : CPTPMap d₃ d₄) : Prop :=
  ∃ (E : CPTPMap d₃ d₁) (D : CPTPMap d₂ d₄), D.compose (Λ₁.compose E) = Λ₂

/--
A channel A `εApproximates` channel B of the same dimensions if the for every state ρ, the fidelity F(A(ρ), B(ρ)) is at least 1-ε.
-/
def εApproximates (A B : CPTPMap d₁ d₂) (ε : ℝ) : Prop :=
  ∀ (ρ : MState d₁), (A ρ).fidelity (B ρ) ≥ 1-ε

/--
A channel A `AchievesRate` R:ℝ if for every ε>0, some n copies of A emulates a channel B such that log2(dimout(B))/n ≥ R, and that B εApproximates the identity channel.
-/
def AchievesRate (A : CPTPMap d₁ d₂) (R : ℝ) : Prop :=
  ∀ ε : ℝ, ε > 0 →
    ∃ n > 0, ∃ (dimB : ℕ) (B : CPTPMap (Fin dimB) (Fin dimB)),
      (CPTPMap.piProd (fun (_ : Fin n) ↦ A)).Emulates B ∧
      Real.logb 2 dimB ≥ R*n ∧
      B.εApproximates CPTPMap.id ε

noncomputable def quantumCapacity (A : CPTPMap d₁ d₂) : ℝ :=
  sSup { R : ℝ | AchievesRate A R }

/-- One-shot quantum capacity, as the supremum of coherent information over input states. -/
noncomputable def oneShotQuantumCapacity (A : CPTPMap d₁ d₂) : ℝ :=
  sSup { R : ℝ | ∃ ρ : MState d₁, R = coherentInfo ρ A }

section emulates
variable [DecidableEq d₃] [DecidableEq d₄] [DecidableEq d₅]

/-- Every quantum channel emulates itself. -/
@[refl]
theorem emulates_self (Λ : CPTPMap d₁ d₂) : Λ.Emulates Λ :=
  ⟨CPTPMap.id, CPTPMap.id, by simp⟩

/-- If a quantum channel A emulates B, and B emulates C, then A emulates C. -/
@[trans]
theorem emulates_trans (Λ₁ : CPTPMap d₁ d₂) (Λ₂ : CPTPMap d₃ d₄) (Λ₃ : CPTPMap d₅ d₆)
  (h₁₂ : Λ₁.Emulates Λ₂) (h₂₃ : Λ₂.Emulates Λ₃) : Λ₁.Emulates Λ₃ := by
  obtain ⟨E₁, D₁, hED₁⟩ := h₁₂
  obtain ⟨E₂, D₂, hED₂⟩ := h₂₃
  exact ⟨E₁.compose E₂, D₂.compose D₁, by classical simp [← hED₁, ← hED₂, compose_assoc]⟩

end emulates

section piProd

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {d : ι → Type*} [∀ i, Fintype (d i)] [∀ i, DecidableEq (d i)]

/-- The finite tensor product of identity channels is the identity channel. -/
@[simp]
theorem piProd_id : piProd (fun i ↦ id (dIn := d i)) = id (dIn := (i : ι) → d i) := by
  apply CPTPMap.ext
  simp [CPTPMap.piProd, MatrixMap.piProd]

end piProd

section id

variable [DecidableEq d₃]

/-- Identity channels on equivalent spaces emulate one another by relabeling. -/
theorem id_emulates_id_of_equiv (e : d₁ ≃ d₃) :
    (id (dIn := d₁)).Emulates (id (dIn := d₃)) := by
  refine ⟨CPTPMap.ofEquiv e.symm, CPTPMap.ofEquiv e, ?_⟩
  simp

end id

section εApproximates

/-- Every quantum channel perfectly approximates itself, that is, `εApproximates` with `ε = 0`. -/
theorem εApproximates_self (Λ : CPTPMap d₁ d₂) : Λ.εApproximates Λ 0 :=
  fun ρ ↦ ((Λ ρ).fidelity_self_eq_one.trans (sub_zero 1).symm).ge

/-- If a quantum channel A approximates B with ε₀, it also approximates B with all larger ε₁. -/
theorem εApproximates_monotone {A B : CPTPMap d₁ d₂} {ε₀ : ℝ} (h : A.εApproximates B ε₀)
    {ε₁ : ℝ} (h₂ : ε₀ ≤ ε₁) : A.εApproximates B ε₁ :=
  fun ρ ↦ (tsub_le_tsub_left h₂ 1).trans (h ρ)

end εApproximates

section AchievesRate

/-- Every quantum channel achieves a rate of zero. -/
theorem achievesRate_0 (Λ : CPTPMap d₁ d₂) [Nonempty d₁] : Λ.AchievesRate 0 := by
  intro ε hε
  have h_nonempty_d₂ : Nonempty d₂ := PTPMap.nonemptyOut Λ.toPTPMap
  use 1, zero_lt_one, 1, CPTPMap.id (dIn := Fin 1)
  constructor
  · let E : CPTPMap (Fin 1) (Fin 1 → d₁) := CPTPMap.replacement default
    let D : CPTPMap (Fin 1 → d₂) (Fin 1) := CPTPMap.destroy
    refine ⟨E, D, ?_⟩
    exact CPTPMap.eq_if_output_unique _ _
  constructor
  · norm_num
  · exact εApproximates_monotone (εApproximates_self (CPTPMap.id (dIn := Fin 1))) hε.le

/-- The identity channel on D dimensional space achieves a rate of log2(D). -/
theorem id_achievesRate_log_dim : (id (dIn := d₁)).AchievesRate (Real.logb 2 (Fintype.card d₁)) := by
  intro ε hε
  use 1, zero_lt_one, Fintype.card d₁, id
  constructor
  · let e : (Fin 1 → d₁) ≃ Fin (Fintype.card d₁) :=
      Fintype.equivFinOfCardEq (by simp +decide)
    simpa [e] using id_emulates_id_of_equiv e
  constructor
  · norm_num
  · exact εApproximates_monotone (εApproximates_self id) hε.le

end AchievesRate
