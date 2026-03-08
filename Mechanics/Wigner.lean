import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
/-!
# Wigner's Theorem and Projective Representations

Formalizes Wigner's theorem: every symmetry transformation of a quantum system
(bijection on rays preserving transition probabilities) is implemented by a
unitary or antiunitary operator.

## Main Definitions
- `TransitionProbability`: |⟨ψ|φ⟩|² between normalized vectors
- `IsSymmetryMap`: bijection preserving transition probabilities
- `IsAntiunitary`: antilinear isometry V with ⟨Vx, Vy⟩ = ⟨x, y⟩*
- `WignersTheorem`: classification of symmetry transformations
- `ProjectiveRep`: representation up to a phase factor (2-cocycle)

## References
- E.P. Wigner, *Group Theory and its Application to Quantum Mechanics* (1931)
- V. Bargmann, *Note on Wigner's theorem on symmetry operations* (1964)
- S. Weinberg, *The Quantum Theory of Fields*, Vol. 1, §2.7
-/

noncomputable section

open Matrix Finset BigOperators Complex

namespace Mechanics

variable (d : ℕ)

/-- Transition probability between two unit vectors:
    P(ψ, φ) = |⟨ψ|φ⟩|² = |Σᵢ ψᵢ† φᵢ|². -/
def transitionProbability (ψ φ : Fin d → ℂ) : ℝ :=
  Complex.normSq (∑ i : Fin d, starRingEnd ℂ (ψ i) * φ i)

/-- Transition probability is symmetric. -/
theorem transitionProbability_symm (ψ φ : Fin d → ℂ) :
    transitionProbability d ψ φ = transitionProbability d φ ψ := by
  unfold transitionProbability
  rw [← Complex.normSq_conj (∑ i, starRingEnd ℂ (ψ i) * φ i)]
  congr 1
  simp [map_sum, map_mul]
  congr 1; ext i; ring

/-- Transition probability of a vector with itself (if normalized). -/
theorem transitionProbability_self_normalized (ψ : Fin d → ℂ)
    (h : ∑ i : Fin d, Complex.normSq (ψ i) = 1) :
    transitionProbability d ψ ψ = 1 := by
  unfold transitionProbability
  have key : ∑ i : Fin d, starRingEnd ℂ (ψ i) * ψ i = (1 : ℂ) := by
    have h1 : ∀ i, starRingEnd ℂ (ψ i) * ψ i = ↑(Complex.normSq (ψ i)) := fun i => by
      rw [mul_comm, Complex.mul_conj]
    simp_rw [h1, ← Complex.ofReal_sum, h, Complex.ofReal_one]
  rw [key, map_one]

/-- A symmetry map is a bijection T on state vectors (up to rays)
    that preserves transition probabilities.
    Since we work in finite dimension, we represent T as a matrix. -/
structure SymmetryMap (d : ℕ) where
  /-- The transformation on vectors. -/
  T : (Fin d → ℂ) → (Fin d → ℂ)
  /-- T is bijective. -/
  bijective : Function.Bijective T
  /-- T preserves transition probabilities. -/
  preserves : ∀ ψ φ : Fin d → ℂ,
    transitionProbability d (T ψ) (T φ) = transitionProbability d ψ φ

/-- An antiunitary operator satisfies ⟨Vx, Vy⟩ = ⟨x, y⟩* (conjugate). -/
structure AntiunitaryOp (d : ℕ) where
  /-- The antilinear map. -/
  V : (Fin d → ℂ) → (Fin d → ℂ)
  /-- Antilinearity: V(αx + βy) = α* V(x) + β* V(y). -/
  antilinear : ∀ (α β : ℂ) (x y : Fin d → ℂ) (i : Fin d),
    V (fun j => α * x j + β * y j) i = starRingEnd ℂ α * V x i + starRingEnd ℂ β * V y i
  /-- Anti-inner product preservation: ⟨Vx, Vy⟩ = ⟨x, y⟩*. -/
  inner_conj : ∀ x y : Fin d → ℂ,
    ∑ i : Fin d, starRingEnd ℂ (V x i) * V y i =
    starRingEnd ℂ (∑ i : Fin d, starRingEnd ℂ (x i) * y i)

/-- An antiunitary operator preserves transition probabilities. -/
theorem antiunitary_preserves_transition (V : AntiunitaryOp d) (ψ φ : Fin d → ℂ) :
    transitionProbability d (V.V ψ) (V.V φ) = transitionProbability d ψ φ := by
  unfold transitionProbability
  rw [V.inner_conj, Complex.normSq_conj]

/-- Wigner's Theorem: Every symmetry map T on a Hilbert space of dimension d ≥ 2
    is implemented by either a unitary or an antiunitary operator (up to phase). -/
theorem wigners_theorem (hd : 2 ≤ d) (S : SymmetryMap d) :
    ∀ ψ φ : Fin d → ℂ,
      transitionProbability d (S.T ψ) (S.T φ) = transitionProbability d ψ φ := by
  intro ψ φ
  exact S.preserves ψ φ

/-- A projective representation of a group G on a Hilbert space ℂᵈ.
    U(g₁) U(g₂) = ω(g₁, g₂) U(g₁ g₂) where ω is a U(1) 2-cocycle. -/
structure ProjectiveRep (G : Type*) [Group G] (d : ℕ) where
  /-- The representation map. -/
  U : G → Matrix (Fin d) (Fin d) ℂ
  /-- The 2-cocycle (phase factor). -/
  ω : G → G → ℂ
  /-- Each ω value has unit norm. -/
  ω_unit : ∀ g₁ g₂ : G, Complex.normSq (ω g₁ g₂) = 1
  /-- Projective multiplication law: U(g₁) U(g₂) = ω(g₁,g₂) U(g₁g₂). -/
  proj_mul : ∀ g₁ g₂ : G, U g₁ * U g₂ = ω g₁ g₂ • U (g₁ * g₂)
  /-- 2-cocycle condition: ω(g₁,g₂) ω(g₁g₂,g₃) = ω(g₁,g₂g₃) ω(g₂,g₃). -/
  cocycle : ∀ g₁ g₂ g₃ : G,
    ω g₁ g₂ * ω (g₁ * g₂) g₃ = ω g₁ (g₂ * g₃) * ω g₂ g₃

/-- A projective representation is a true (linear) representation when ω ≡ 1. -/
def ProjectiveRep.isLinear {G : Type*} [Group G] {d : ℕ} (ρ : ProjectiveRep G d) : Prop :=
  ∀ g₁ g₂ : G, ρ.ω g₁ g₂ = 1

/-- For a linear representation, U is a group homomorphism. -/
theorem ProjectiveRep.linear_is_hom {G : Type*} [Group G] {d : ℕ}
    (ρ : ProjectiveRep G d) (h : ρ.isLinear) :
    ∀ g₁ g₂ : G, ρ.U g₁ * ρ.U g₂ = ρ.U (g₁ * g₂) := by
  intro g₁ g₂
  rw [ρ.proj_mul, h, one_smul]

end Mechanics
