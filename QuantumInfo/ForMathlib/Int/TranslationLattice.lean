import Mathlib

/-!
# Integer translation lattices

Elementary facts about the standard lattice `ℤ^d`, represented as `Fin d → ℤ`.
-/

namespace Int

/-- The standard integer translation lattice in dimension `d`. -/
abbrev TranslationLattice (d : ℕ) :=
  Fin d → ℤ

namespace TranslationLattice

/-- The rank of `ℤ^d` as a `ℤ`-module is `d`. -/
theorem finrank (d : ℕ) : Module.finrank ℤ (TranslationLattice d) = d := by
  unfold TranslationLattice
  rw [Module.finrank_pi]
  simp

/-- The `i`th standard basis vector in `ℤ^d`. -/
def stdBasisVec (d : ℕ) (i : Fin d) : TranslationLattice d :=
  fun j => if i = j then 1 else 0

/-- The negative of the `i`th standard basis vector in `ℤ^d`. -/
def negStdBasisVec (d : ℕ) (i : Fin d) : TranslationLattice d :=
  fun j => if i = j then -1 else 0

/-- The cardinality of the formal standard signed generator list is `2d`. -/
theorem signed_coordination_number (d : ℕ) :
    2 * d = Fintype.card (Fin d) + Fintype.card (Fin d) := by
  simp [Fintype.card_fin]
  ring

/-- Standard basis vectors are nonzero. -/
theorem stdBasisVec_ne_zero (d : ℕ) (i : Fin d) :
    stdBasisVec d i ≠ 0 := by
  intro h
  have := congr_fun h i
  simp [stdBasisVec] at this

/-- Equality of standard basis vectors reflects equality of their indices. -/
theorem stdBasisVec_injective (d : ℕ) (i j : Fin d)
    (h : stdBasisVec d i = stdBasisVec d j) : i = j := by
  by_contra hij
  have := congr_fun h i
  simp [stdBasisVec] at this
  exact hij this.symm

/-- The positive and negative standard basis vectors are distinct. -/
theorem stdBasisVec_ne_negStdBasisVec (d : ℕ) (i : Fin d) :
    stdBasisVec d i ≠ negStdBasisVec d i := by
  intro h
  have := congr_fun h i
  simp [stdBasisVec, negStdBasisVec] at this

/-- The rank of a standard integer translation lattice is invariant under
`ℤ`-linear equivalence. -/
theorem rank_invariant (d₁ d₂ : ℕ)
    (e : TranslationLattice d₁ ≃ₗ[ℤ] TranslationLattice d₂) :
    d₁ = d₂ := by
  have h₁ := finrank d₁
  have h₂ := finrank d₂
  have heq := e.finrank_eq
  omega

@[simp]
theorem finrank_zero : Module.finrank ℤ (TranslationLattice 0) = 0 :=
  finrank 0

@[simp]
theorem finrank_one : Module.finrank ℤ (TranslationLattice 1) = 1 :=
  finrank 1

@[simp]
theorem finrank_three : Module.finrank ℤ (TranslationLattice 3) = 3 :=
  finrank 3

end TranslationLattice
end Int
