/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.ForMathlib.HermitianMat

/-!
# Lieb concavity

This file records the Lean-facing surface for Lieb's joint concavity theorem.
The standard theorem is a statement on the positive semidefinite cone, not on
all Hermitian matrices.  The remaining analytic ingredient is isolated as
`LiebConcavityCore`: the Jensen inequality for the Lieb functional on positive
semidefinite inputs.  Once that noncommutative matrix-inequality result is
available, `LiebConcavity` packages it as a `ConcaveOn` theorem.
-/

variable {m n : Type*} {q r : ℝ}

noncomputable section
open ComplexOrder
open Classical
open RealInnerProductSpace

/-- The positive semidefinite domain for Lieb's two-variable functional. -/
def LiebPsdDomain : Set (HermitianMat m ℂ × HermitianMat n ℂ) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2}

/-- The positive semidefinite domain is convex. -/
theorem LiebPsdDomain_convex :
    Convex ℝ (LiebPsdDomain (m := m) (n := n)) := by
  intro x hx y hy a b ha hb hab
  rcases x with ⟨A, C⟩
  rcases y with ⟨B, D⟩
  exact ⟨HermitianMat.convex_cone hx.1 hy.1 ha hb,
    HermitianMat.convex_cone hx.2 hy.2 ha hb⟩

variable [Fintype m] [Fintype n]

/-- The finite-dimensional Lieb functional
`(A, B) ↦ Tr[K * A^q * Kᴴ * B^r]`, expressed through the Hermitian inner product. -/
def LiebFunctional (K : Matrix n m ℂ) (q r : ℝ) :
    HermitianMat m ℂ × HermitianMat n ℂ → ℝ :=
  fun p ↦ ⟪(p.1 ^ q).conj K, p.2 ^ r⟫

/--
The exact matrix-inequality prerequisite still missing from the imported API:
the Jensen inequality for the Lieb functional on positive semidefinite inputs.

The hypotheses `hq`, `hr`, and `hqr` are part of the mathematical range of
Lieb's theorem: `0 ≤ q`, `0 ≤ r`, and `q + r ≤ 1`.
-/
def LiebConcavityCore (K : Matrix n m ℂ) {q r : ℝ}
    (_hq : 0 ≤ q) (_hr : 0 ≤ r) (_hqr : q + r ≤ 1) : Prop :=
  ∀ (A B : HermitianMat m ℂ) (C D : HermitianMat n ℂ) (a b : ℝ),
    0 ≤ A → 0 ≤ B → 0 ≤ C → 0 ≤ D →
    0 ≤ a → 0 ≤ b → a + b = 1 →
      a * LiebFunctional K q r (A, C) + b * LiebFunctional K q r (B, D) ≤
        LiebFunctional K q r (a • A + b • B, a • C + b • D)

/--
Lieb concavity, reduced to the one missing noncommutative Jensen inequality
`LiebConcavityCore`.
-/
theorem LiebConcavity (K : Matrix n m ℂ)
    (hq : 0 ≤ q) (hr : 0 ≤ r) (hqr : q + r ≤ 1)
    (hcore : LiebConcavityCore K hq hr hqr) :
    ConcaveOn ℝ (LiebPsdDomain (m := m) (n := n)) (LiebFunctional K q r) := by
  refine ⟨LiebPsdDomain_convex, ?_⟩
  rintro ⟨A, C⟩ hAC ⟨B, D⟩ hBD a b ha hb hab
  simpa [LiebFunctional] using hcore A B C D a b hAC.1 hBD.1 hAC.2 hBD.2 ha hb hab

end
