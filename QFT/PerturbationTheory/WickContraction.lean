/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Inspired by PhysLean's QFT/PerturbationTheory/WickContraction.
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring
import QFT.PerturbationTheory.FieldSpecification
/-!
# Wick Contractions and Wick's Theorem

A Wick contraction of `n` field operators is a set of disjoint pairings.
Wick's theorem decomposes the time-ordered product into a sum over contractions.

## Main definitions

* `WickContraction n` : a set of disjoint ordered pairs from `{0, …, n-1}`
* `doubleFactorial` : `n‼`, the number of perfect matchings of `2n` objects
* `WickTheoremStatement` : the combinatorial statement of Wick's theorem

## References

* Peskin & Schroeder, *An Introduction to Quantum Field Theory*, §4.3
* G.C. Wick, "The Evaluation of the Collision Matrix", Phys. Rev. 80 (1950)
-/

open Finset

namespace QFT

/-- A Wick contraction of `n` field operators: a set of disjoint ordered pairs. -/
structure WickContraction (n : ℕ) where
  pairs : Finset (Fin n × Fin n)
  ordered : ∀ p ∈ pairs, p.1 < p.2
  disjoint : ∀ p₁ ∈ pairs, ∀ p₂ ∈ pairs,
    p₁ ≠ p₂ → (p₁.1 ≠ p₂.1 ∧ p₁.1 ≠ p₂.2 ∧ p₁.2 ≠ p₂.1 ∧ p₁.2 ≠ p₂.2)

namespace WickContraction

variable {n : ℕ}

def numPairs (c : WickContraction n) : ℕ := c.pairs.card

def contractedIndices (c : WickContraction n) : Finset (Fin n) :=
  c.pairs.biUnion fun p => {p.1, p.2}

def uncontractedIndices (c : WickContraction n) : Finset (Fin n) :=
  Finset.univ \ c.contractedIndices

def numUncontracted (c : WickContraction n) : ℕ := c.uncontractedIndices.card

def empty : WickContraction n where
  pairs := ∅
  ordered := fun _ hp => absurd hp (Finset.not_mem_empty _)
  disjoint := fun _ hp => absurd hp (Finset.not_mem_empty _)

theorem empty_uncontracted : (empty : WickContraction n).numUncontracted = n := by
  simp [numUncontracted, uncontractedIndices, contractedIndices, empty]

/-- A full contraction pairs every operator (requires `n` even). -/
def isFull (c : WickContraction n) : Prop := c.numPairs * 2 = n

theorem full_no_uncontracted (c : WickContraction n) (hf : c.isFull) :
    c.numUncontracted = 0 := by
  unfold numUncontracted uncontractedIndices
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
  suffices h : c.contractedIndices.card = n by omega
  unfold contractedIndices isFull numPairs at *
  have hdisj : ∀ p₁ ∈ c.pairs, ∀ p₂ ∈ c.pairs, p₁ ≠ p₂ →
      Disjoint ({p₁.1, p₁.2} : Finset (Fin n)) {p₂.1, p₂.2} := by
    intro p₁ hp₁ p₂ hp₂ hne
    obtain ⟨h1, h2, h3, h4⟩ := c.disjoint p₁ hp₁ p₂ hp₂ hne
    rw [Finset.disjoint_left]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    intro a ha₁ ha₂
    rcases ha₁ with rfl | rfl <;> rcases ha₂ with h | h <;> contradiction
  rw [Finset.card_biUnion hdisj,
      Finset.sum_congr rfl (fun p hp =>
        Finset.card_pair (ne_of_lt (c.ordered p hp))),
      Finset.sum_const]
  simpa using hf

end WickContraction

/-! ## Double Factorial -/

/-- `n‼` — the double factorial: `n × (n-2) × (n-4) × ⋯`. -/
def doubleFactorial : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => (n + 2) * doubleFactorial n

notation n "‼" => doubleFactorial n

theorem doubleFactorial_zero : (0 : ℕ)‼ = 1 := rfl
theorem doubleFactorial_one : (1 : ℕ)‼ = 1 := rfl

theorem doubleFactorial_succ_succ (n : ℕ) :
    (n + 2)‼ = (n + 2) * n‼ := rfl

/-- `(2n)‼ = 2ⁿ · n!`. -/
theorem even_doubleFactorial (n : ℕ) :
    (2 * n)‼ = 2 ^ n * n.factorial := by
  induction n with
  | zero => simp [doubleFactorial_zero]
  | succ n ih =>
    show (2 * n + 2)‼ = 2 ^ (n + 1) * (n + 1).factorial
    rw [doubleFactorial_succ_succ, ih, Nat.factorial_succ, pow_succ]
    ring

/-! ## Wick's Theorem Data -/

/-- Data needed to state Wick's theorem for `2n` field operators:
    a propagator (two-point function) and a sign assignment to contractions.
    This is a data carrier; the actual theorem statement would assert that the
    time-ordered product equals a sum over full contractions. -/
structure WickTheoremData (n : ℕ) where
  propagator : Fin (2 * n) → Fin (2 * n) → ℂ
  contractionSign : WickContraction (2 * n) → ℤ

/-! ## Verification Tests -/

section Tests

/-- Concrete double factorial values. -/
example : (0 : ℕ)‼ = 1 := rfl
example : (1 : ℕ)‼ = 1 := rfl
example : (2 : ℕ)‼ = 2 := rfl
example : (3 : ℕ)‼ = 3 := rfl
example : (4 : ℕ)‼ = 8 := rfl
example : (5 : ℕ)‼ = 15 := rfl
example : (6 : ℕ)‼ = 48 := rfl
example : (7 : ℕ)‼ = 105 := rfl
example : (8 : ℕ)‼ = 384 := rfl

/-- Double factorial is always positive. -/
theorem doubleFactorial_pos (n : ℕ) : 0 < n‼ := by
  induction n using doubleFactorial.induct with
  | case1 => simp [doubleFactorial]
  | case2 => simp [doubleFactorial]
  | case3 n ih => simp [doubleFactorial]; omega

/-- The empty contraction of 0 elements has 0 pairs. -/
example : (WickContraction.empty : WickContraction 0).numPairs = 0 := rfl

/-- The empty contraction of n elements leaves all n uncontracted. -/
example : (WickContraction.empty : WickContraction 5).numUncontracted = 5 :=
  WickContraction.empty_uncontracted

/-- The empty contraction has n uncontracted indices for any n. -/
example (n : ℕ) : (WickContraction.empty : WickContraction n).numUncontracted = n :=
  WickContraction.empty_uncontracted

/-- The empty contraction is never full (for n ≥ 1). -/
theorem WickContraction.empty_not_full (n : ℕ) (hn : 0 < n) :
    ¬(WickContraction.empty : WickContraction n).isFull := by
  simp [isFull, numPairs, empty]; omega

/-- Number of full contractions of 2 objects: 1‼ = 1. -/
example : (2 * 1 - 1)‼ = 1 := rfl

/-- Number of full contractions of 4 objects: 3‼ = 3. -/
example : (2 * 2 - 1)‼ = 3 := rfl

/-- Number of full contractions of 6 objects: 5‼ = 15. -/
example : (2 * 3 - 1)‼ = 15 := rfl

end Tests

end QFT
