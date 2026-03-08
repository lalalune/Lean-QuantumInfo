import Mathlib

/-!
# Qudit Basics

Generalized Pauli `X/Z` operators on a finite `d`-level system.
-/

noncomputable section

namespace Qudit

/-- Computational-basis index type for a `d`-level system. -/
abbrev Idx (d : ℕ) : Type := Fin d

/-- Canonical phase used for the generalized clock operator. -/
noncomputable def omega (d : ℕ) [NeZero d] : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / (d : ℂ))

/-- Generalized shift operator `X_d`: sends `|j⟩` to `|j+1 mod d⟩`. -/
def X (d : ℕ) : Matrix (Idx d) (Idx d) ℂ :=
  fun i j => if i.1 = (j.1 + 1) % d then 1 else 0

/-- Generalized clock operator `Z_d`: diagonal with powers of `omega d`. -/
noncomputable def Z (d : ℕ) [NeZero d] : Matrix (Idx d) (Idx d) ℂ :=
  Matrix.diagonal (fun i => (omega d) ^ (i : ℕ))

@[simp] theorem X_apply (d : ℕ) (i j : Idx d) :
    X d i j = (if i.1 = (j.1 + 1) % d then 1 else 0) := rfl

@[simp] theorem Z_apply (d : ℕ) [NeZero d] (i j : Idx d) :
    Z d i j = if i = j then (omega d) ^ (i : ℕ) else 0 := by
  by_cases h : i = j
  · simp [Z, h]
  · simp [Z, h]

@[simp] theorem Z_apply_diag (d : ℕ) [NeZero d] (i : Idx d) :
    Z d i i = (omega d) ^ (i : ℕ) := by
  simp [Z]

@[simp] theorem Z_apply_ne (d : ℕ) [NeZero d] {i j : Idx d} (h : i ≠ j) :
    Z d i j = 0 := by
  simp [Z, h]

theorem X_apply_eq_one_of_eq (d : ℕ) {i j : Idx d} (h : i.1 = (j.1 + 1) % d) :
    X d i j = 1 := by
  simp [X, h]

theorem X_apply_eq_zero_of_ne (d : ℕ) {i j : Idx d} (h : i.1 ≠ (j.1 + 1) % d) :
    X d i j = 0 := by
  simp [X, h]

end Qudit
