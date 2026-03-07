/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import ClassicalInfo.Distribution
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

open BigOperators

/- Channels, as in information theory.

A `Channel` is as a function from `List`s over an input alphabet A to a distribution
of lists over an output alphabet B. The most important case of interest here
is the memoryless channel, which preserves lengths and acts on each symbol
identically and independently.
-/

variable (I O : Type*) [Fintype O]

/- Actually defining Channels this way gets messy fast because of the measure theory.

/-- Although we could simply `def Channel := List A → List B`, defining it as
a structure lets us extend this structure by adding additional properties while
staying a `Channel`. -/
structure Channel [MeasurableSpace O] where
  map : List I → MeasureTheory.Measure (List O)
  map_prob : ∀is, IsProbabilityMeasure (map is)

namespace Channel

variable (A B C D : Type*)
variable (Cab : Channel A B) (Cbc : Channel B C) (Ccd : Channel C D)

/-- Identity channel -/
def id : Channel A A :=
  ⟨_root_.id⟩

/-- Composition of two channels -/
def comp : Channel A C :=
  ⟨Cbc.map ∘ Cab.map⟩

/-- Product of two channels, acting on two product types in parallel. -/
def product : Channel (A × C) (B × D) :=
  ⟨Cab.map × Ccd.map⟩
-/

/-- Discrete Memoryless Channel. Each input symbol `I` has a corresponding
 output distribution `Distribution O`, and this process is applied
 independently on each symbol in the list. -/
structure DMChannel where
  symb_dist : I → Distribution O

namespace DMChannel

-- Helper lemma: coercion distributes over finite products of probabilities
private lemma coe_finset_prod_prob {α : Type*} (s : Finset α) (p : α → Prob) :
    ((s.prod p : Prob) : ℝ) = s.prod (fun i => (p i : ℝ)) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i t hi ih =>
    simp only [Finset.prod_cons hi, Prob.coe_mul]
    rw [ih]

/-- Apply a discrete memoryless channel to an n-character string. -/
def on_fin (C : DMChannel I O) {n : ℕ} (is : Fin n → I) : Distribution (Fin n → O) :=
  ⟨fun os ↦ ∏ k, C.symb_dist (is k) (os k), by
    simp_rw [coe_finset_prod_prob]
    let g : Fin n → O → ℝ := fun k o => ↑((C.symb_dist (is k)) o)
    show ∑ x ∈ Fintype.piFinset (fun _ => Finset.univ), ∏ k, g k (x k) = 1
    rw [Finset.sum_prod_piFinset]
    simp only [g, Distribution.normalized, Finset.prod_const_one]⟩

/-- Apply a discrete memoryless channel to a list. -/
def on_list (C : DMChannel I O) (is : List I) : Distribution (Fin (is.length) → O) :=
  on_fin I O C is.get

end DMChannel
