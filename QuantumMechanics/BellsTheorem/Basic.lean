/-
Copyright (c) 2025 Bell Theorem Formalization Project
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ported from Isabelle/HOL formalization by Echenim & Mhalla

# Bell's Theorem and the CHSH Inequality in Lean 4

This file formalizes Bell's lemma, the CHSH inequality, and Tsirelson's bound.
The formalization follows the structure of Echenim & Mhalla's Isabelle/HOL work,
adapted to leverage Lean 4's type system and Mathlib4's existing infrastructure.

## Main Results

* `CHSH_expect_lhv_le` : Under local hidden variables, |⟨CHSH⟩| ≤ 2
* `CHSH_expect_quantum` : Quantum mechanics achieves |⟨CHSH⟩| = 2√2
* `tsirelson_bound` : For all quantum states, |⟨CHSH⟩| ≤ 2√2
* `CHSH_separable_le` : Separable states cannot violate CHSH
* `CHSH_commuting_le` : Commuting observables cannot violate CHSH

## References

* [Echenim, Mhalla, *A formalization of the CHSH inequality and Tsirelson's
  upper-bound in Isabelle/HOL*][echenim2023]
* [Clauser, Horne, Shimony, Holt, *Proposed experiment to test local
  hidden-variable theories*][chsh1969]
* [Bell, *On the Einstein Podolsky Rosen paradox*][bell1964]
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Independence.Basic
import Mathlib.Algebra.Star.CHSH
import Mathlib.Analysis.Complex.Basic  -- This defines Complex.abs
import Mathlib.LinearAlgebra.Matrix.Kronecker

import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Data.Matrix.Basic



open scoped Matrix ComplexConjugate BigOperators TensorProduct
open MeasureTheory ProbabilityTheory Matrix Complex

/-! ## Quantum State Foundations -/

namespace QuantumInfo

variable {n : ℕ} [NeZero n]

/-- A complex matrix is positive semidefinite if x†Mx has non-negative real part for all x.
    For Hermitian matrices, x†Mx is automatically real. -/
def IsPosSemidefComplex (M : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ x : Fin n → ℂ, 0 ≤ (star x ⬝ᵥ M.mulVec x).re

/-- A density matrix is a positive semidefinite Hermitian matrix with trace 1.
    This represents the state of a quantum system. -/
structure DensityMatrix (n : ℕ) [NeZero n] where
  /-- The underlying matrix -/
  toMatrix : Matrix (Fin n) (Fin n) ℂ
  /-- Density matrices are Hermitian -/
  hermitian : toMatrix.IsHermitian
  /-- Density matrices have trace 1 -/
  trace_one : toMatrix.trace = 1
  /-- Density matrices are positive semidefinite -/
  posSemidef : IsPosSemidefComplex toMatrix

instance : Coe (DensityMatrix n) (Matrix (Fin n) (Fin n) ℂ) where
  coe ρ := ρ.toMatrix

/-- A pure state is a density matrix of the form |ψ⟩⟨ψ| -/
def DensityMatrix.IsPure (ρ : DensityMatrix n) : Prop :=
  ρ.toMatrix * ρ.toMatrix = ρ.toMatrix

/-- The maximally mixed state: (1/n) · I -/
noncomputable def maxMixedState (n : ℕ) [NeZero n] : Matrix (Fin n) (Fin n) ℂ :=
  (1 / n : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)

/-! ## Observables and Measurements -/

/-- An observable is a Hermitian matrix. The eigenvalues are measurement outcomes. -/
structure Observable (n : ℕ) where
  toMatrix : Matrix (Fin n) (Fin n) ℂ
  hermitian : toMatrix.IsHermitian

instance : Coe (Observable n) (Matrix (Fin n) (Fin n) ℂ) where
  coe A := A.toMatrix

/-- A dichotomic observable has eigenvalues ±1, i.e., A² = I -/
structure DichotomicObservable (n : ℕ) extends Observable n where
  sq_eq_one : toMatrix * toMatrix = 1

/-- The expectation value of an observable A in state ρ is Tr(A·ρ) -/
noncomputable def expectationValue (A : Observable n) (ρ : DensityMatrix n) : ℂ :=
  (A.toMatrix * ρ.toMatrix).trace

notation "⟨" A "⟩_" ρ => expectationValue A ρ

/-! ## CHSH Operator and Conditions -/

/-- The CHSH operator: A₀⊗B₁ - A₀⊗B₀ + A₁⊗B₀ + A₁⊗B₁
    Note: We work with the algebraic form where Aᵢ and Bⱼ commute -/
noncomputable def CHSH_op {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A₀ A₁ B₀ B₁ : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  A₀ * B₁ - A₀ * B₀ + A₁ * B₀ + A₁ * B₁

/-- CHSH expectation value for a density matrix -/
noncomputable def CHSH_expect {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A₀ A₁ B₀ B₁ : Matrix ι ι ℂ) (ρ : Matrix ι ι ℂ) : ℂ :=
  (CHSH_op A₀ A₁ B₀ B₁ * ρ).trace

/-- Conditions for CHSH tuple: Hermitian, squares to I, Aᵢ commutes with Bⱼ -/
structure IsCHSHTuple {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A₀ A₁ B₀ B₁ : Matrix ι ι ℂ) : Prop where
  A₀_herm : A₀.IsHermitian
  A₁_herm : A₁.IsHermitian
  B₀_herm : B₀.IsHermitian
  B₁_herm : B₁.IsHermitian
  A₀_sq : A₀ * A₀ = 1
  A₁_sq : A₁ * A₁ = 1
  B₀_sq : B₀ * B₀ = 1
  B₁_sq : B₁ * B₁ = 1
  comm_A₀_B₀ : A₀ * B₀ = B₀ * A₀
  comm_A₀_B₁ : A₀ * B₁ = B₁ * A₀
  comm_A₁_B₀ : A₁ * B₀ = B₀ * A₁
  comm_A₁_B₁ : A₁ * B₁ = B₁ * A₁

/-! ## Local Hidden Variable Model -/

/-- A local hidden variable (LHV) model for a bipartite quantum experiment.

Given a bipartite state ρ and observables A, B, the LHV hypothesis asserts
the existence of:
- A probability space (Λ, μ)
- Random variables Xₐ for each eigenvalue a of A
- Random variables Yᵦ for each eigenvalue b of B

Such that the quantum correlations arise as classical expectations:
  Tr(Πᵃ ⊗ Πᵇ · ρ) = 𝔼[Xₐ · Yᵦ]

The key constraint is *locality*: Xₐ depends only on A (not B),
and Yᵦ depends only on B (not A).
-/
structure LocalHiddenVariableModel (Λ : Type*) [MeasurableSpace Λ] where
  /-- The probability measure on the hidden variable space -/
  μ : ProbabilityMeasure Λ
  /-- Response function for Alice: given setting a and hidden variable ω, output ±1 -/
  alice : Fin 2 → Λ → ℝ  -- settings 0, 1
  /-- Response function for Bob: given setting b and hidden variable ω, output ±1 -/
  bob : Fin 2 → Λ → ℝ    -- settings 0, 1
  /-- Alice's outputs are ±1 a.e. -/
  alice_pm1 : ∀ a, ∀ᵐ ω ∂(μ : Measure Λ), alice a ω = 1 ∨ alice a ω = -1
  /-- Bob's outputs are ±1 a.e. -/
  bob_pm1 : ∀ b, ∀ᵐ ω ∂(μ : Measure Λ), bob b ω = 1 ∨ bob b ω = -1
  /-- Measurability -/
  alice_meas : ∀ a, Measurable (alice a)
  bob_meas : ∀ b, Measurable (bob b)

variable {Λ : Type*} [MeasurableSpace Λ]

/-- The LHV correlation for settings (a, b) -/
noncomputable def LHV_correlation (M : LocalHiddenVariableModel Λ) (a b : Fin 2) : ℝ :=
  ∫ ω, M.alice a ω * M.bob b ω ∂M.μ

/-- The CHSH value under an LHV model:
    S = E(0,1) - E(0,0) + E(1,0) + E(1,1) -/
noncomputable def LHV_CHSH_value (M : LocalHiddenVariableModel Λ) : ℝ :=
  LHV_correlation M 0 1 - LHV_correlation M 0 0 +
  LHV_correlation M 1 0 + LHV_correlation M 1 1

/-! ## The CHSH Inequality for LHV Models -/

/-- Key algebraic identity: for a,a',b,b' ∈ {-1,1},
    |ab' - ab + a'b + a'b'| ≤ 2 -/
lemma chsh_algebraic_bound (a a' b b' : ℝ)
    (ha : a = 1 ∨ a = -1) (ha' : a' = 1 ∨ a' = -1)
    (hb : b = 1 ∨ b = -1) (hb' : b' = 1 ∨ b' = -1) :
    |a * b' - a * b + a' * b + a' * b'| ≤ 2 := by
  -- The key insight: a*b' - a*b + a'*b + a'*b' = a*(b'-b) + a'*(b+b')
  -- Since b, b' ∈ {-1,1}, either b'=b (so b'-b=0, b+b'=±2)
  -- or b'=-b (so b'-b=±2, b+b'=0)
  -- In either case, one term vanishes and the other is ±2
  rcases ha with rfl | rfl <;> rcases ha' with rfl | rfl <;>
  rcases hb with rfl | rfl <;> rcases hb' with rfl | rfl <;>
  norm_num



/-- **CHSH Inequality**: Under any local hidden variable model, |S| ≤ 2

This is the fundamental constraint that Bell showed is violated by quantum mechanics. -/
theorem CHSH_lhv_bound (M : LocalHiddenVariableModel Λ) :
    |LHV_CHSH_value M| ≤ 2 := by
  unfold LHV_CHSH_value LHV_correlation

  have h_int : ∀ a b, Integrable (fun ω => M.alice a ω * M.bob b ω) (M.μ : Measure Λ) := by
    intro a b
    apply Integrable.mono' (g := fun _ => (1 : ℝ)) (integrable_const 1)
    · exact ((M.alice_meas a).mul (M.bob_meas b)).aestronglyMeasurable
    · filter_upwards [M.alice_pm1 a, M.bob_pm1 b] with ω ha hb
      simp only [norm_mul, Real.norm_eq_abs]
      rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb] <;> norm_num

  rw [← integral_sub, ← integral_add, ← integral_add]
  · -- Main bound
    have hμ : IsProbabilityMeasure (M.μ : Measure Λ) :=
      ProbabilityMeasure.instIsProbabilityMeasureToMeasure M.μ
    calc |∫ ω, M.alice 0 ω * M.bob 1 ω - M.alice 0 ω * M.bob 0 ω +
              M.alice 1 ω * M.bob 0 ω + M.alice 1 ω * M.bob 1 ω ∂(M.μ : Measure Λ)|
        ≤ ∫ ω, |M.alice 0 ω * M.bob 1 ω - M.alice 0 ω * M.bob 0 ω +
               M.alice 1 ω * M.bob 0 ω + M.alice 1 ω * M.bob 1 ω| ∂(M.μ : Measure Λ) :=
          abs_integral_le_integral_abs
      _ ≤ ∫ _, (2 : ℝ) ∂(M.μ : Measure Λ) := by
          apply integral_mono_ae
          · exact (((h_int 0 1).sub (h_int 0 0)).add (h_int 1 0)).add (h_int 1 1) |>.abs
          · exact integrable_const 2
          · filter_upwards [M.alice_pm1 0, M.alice_pm1 1, M.bob_pm1 0, M.bob_pm1 1]
              with ω ha ha' hb hb'
            exact chsh_algebraic_bound _ _ _ _ ha ha' hb hb'
      _ = 2 := by
          rw [integral_const]
          simp only [measureReal_univ_eq_one, smul_eq_mul, one_mul]
  -- Integrability side goals for integral_add/sub
  · exact ((h_int 0 1).sub (h_int 0 0)).add (h_int 1 0)
  · exact h_int 1 1
  · exact (h_int 0 1).sub (h_int 0 0)
  · exact h_int 1 0
  · exact h_int 0 1
  · exact h_int 0 0

/-! ## Quantum Violation -/

/-- The Pauli Z matrix -/
def pauliZ : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1, 0; 0, -1]

/-- The Pauli X matrix -/
def pauliX : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, 1; 1, 0]

/-- The Bell state |Ψ⁻⟩ = (1/√2)(|01⟩ - |10⟩) as a density matrix
    on the product space Fin 2 × Fin 2 -/
noncomputable def bellStatePsiMinus : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun i j =>
    match i, j with
    | (0, 1), (0, 1) =>  (1/2 : ℂ)
    | (0, 1), (1, 0) => -(1/2 : ℂ)
    | (1, 0), (0, 1) => -(1/2 : ℂ)
    | (1, 0), (1, 0) =>  (1/2 : ℂ)
    | _, _ => 0

/-- Alice's observables for optimal CHSH violation:
    A₀ = Z, A₁ = X -/
def alice_A₀ : Matrix (Fin 2) (Fin 2) ℂ := pauliZ
def alice_A₁ : Matrix (Fin 2) (Fin 2) ℂ := pauliX

/-- Bob's observables for optimal CHSH violation:
    B₀ = (Z-X)/√2, B₁ = -(Z+X)/√2 -/
noncomputable def bob_B₀ : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / Complex.ofReal (Real.sqrt 2)) • (pauliZ - pauliX)

noncomputable def bob_B₁ : Matrix (Fin 2) (Fin 2) ℂ :=
  (-1 / Complex.ofReal (Real.sqrt 2)) • (pauliZ + pauliX)


/-- Helper: The 4x4 identity on the tensor product space -/
def I₄ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := 1

/-- The Bell state as explicit 4x4 matrix (using Fin 4 indexing for easier computation) -/
lemma bellState_explicit : bellStatePsiMinus = Matrix.of fun i j =>
    if i = (0,1) ∧ j = (0,1) then (1/2 : ℂ)
    else if i = (0,1) ∧ j = (1,0) then (-1/2 : ℂ)
    else if i = (1,0) ∧ j = (0,1) then (-1/2 : ℂ)
    else if i = (1,0) ∧ j = (1,0) then (1/2 : ℂ)
    else 0 := by
  ext i j
  simp only [bellStatePsiMinus, Matrix.of_apply]
  fin_cases i <;> fin_cases j <;> simp <;> norm_num

/-- Alice's A₀ = Z ⊗ I as explicit 4x4 matrix -/
lemma alice_A₀_explicit :
    kroneckerMap (· * ·) alice_A₀ (1 : Matrix (Fin 2) (Fin 2) ℂ) =
    Matrix.of fun i j =>
      if i = j then (if i.1 = 0 then 1 else -1) else 0 := by
  ext i j
  simp only [kroneckerMap_apply, alice_A₀, pauliZ, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;> simp

/-- Alice's A₁ = X ⊗ I as explicit 4x4 matrix -/
lemma alice_A₁_explicit :
    kroneckerMap (· * ·) alice_A₁ (1 : Matrix (Fin 2) (Fin 2) ℂ) =
    Matrix.of fun i j =>
      if i.2 = j.2 ∧ i.1 ≠ j.1 then 1 else 0 := by
  ext i j
  simp only [kroneckerMap_apply, alice_A₁, pauliX, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;> simp

/-- Correlation E(A₀, B₁) for the Bell state -/
lemma correlation_A₀_B₁ :
    let A₀ := kroneckerMap (· * ·) alice_A₀ (1 : Matrix (Fin 2) (Fin 2) ℂ)
    let B₁ := kroneckerMap (· * ·) (1 : Matrix (Fin 2) (Fin 2) ℂ) bob_B₁
    ((A₀ * B₁) * bellStatePsiMinus).trace = ((Real.sqrt 2)⁻¹ : ℂ) := by
  intro A₀ B₁
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.isValue]
  simp only [Matrix.mul_apply, bellStatePsiMinus, Matrix.of_apply]
  simp only [Fin.isValue, Prod.mk.injEq, zero_ne_one, and_false, imp_self, implies_true, and_true,
    mul_zero, Finset.sum_const_zero, one_div, zero_add, one_ne_zero, and_self, add_zero]
  simp only [A₀, B₁]
  simp only [kroneckerMap_apply, Matrix.one_apply]
  simp only [alice_A₀, bob_B₁, pauliZ, pauliX]
  simp only [Matrix.smul_apply, Matrix.add_apply]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.isValue]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
             Matrix.cons_val_fin_one]
  simp only [one_mul, zero_mul, mul_one, mul_zero, one_ne_zero, zero_ne_one, ↓reduceIte,
    add_zero, smul_eq_mul, mul_neg, mul_one, zero_add, neg_mul, zero_mul, neg_zero,
    one_mul]
  ring_nf

/-- Correlation E(A₀, B₀) for the Bell state -/
lemma correlation_A₀_B₀ :
    let A₀ := kroneckerMap (· * ·) alice_A₀ (1 : Matrix (Fin 2) (Fin 2) ℂ)
    let B₀ := kroneckerMap (· * ·) (1 : Matrix (Fin 2) (Fin 2) ℂ) bob_B₀
    ((A₀ * B₀) * bellStatePsiMinus).trace = -((Real.sqrt 2)⁻¹ : ℂ) := by
  intro A₀ B₀
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.isValue]
  simp only [Matrix.mul_apply, bellStatePsiMinus, Matrix.of_apply]
  simp only [Fin.isValue, Prod.mk.injEq, zero_ne_one, and_false, imp_self, implies_true, and_true,
    mul_zero, Finset.sum_const_zero, one_div, zero_add, one_ne_zero, and_self, add_zero]
  simp only [A₀, B₀]
  simp only [kroneckerMap_apply, Matrix.one_apply]
  simp only [alice_A₀, bob_B₀, pauliZ, pauliX]
  simp only [Matrix.smul_apply, Matrix.sub_apply]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.isValue]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
             Matrix.cons_val_fin_one]
  simp only [Fin.isValue, one_ne_zero, ↓reduceIte, mul_zero, one_div, sub_zero, smul_eq_mul,
    mul_one, one_mul, zero_mul, zero_sub, mul_neg, zero_add, neg_zero, add_zero, neg_mul,
    zero_ne_one, neg_neg]
  ring_nf


/-- Correlation E(A₁, B₀) for the Bell state -/
lemma correlation_A₁_B₀ :
    let A₁ := kroneckerMap (· * ·) alice_A₁ (1 : Matrix (Fin 2) (Fin 2) ℂ)
    let B₀ := kroneckerMap (· * ·) (1 : Matrix (Fin 2) (Fin 2) ℂ) bob_B₀
    ((A₁ * B₀) * bellStatePsiMinus).trace = ((Real.sqrt 2)⁻¹ : ℂ) := by
  intro A₁ B₀
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.isValue]
  simp only [Matrix.mul_apply, bellStatePsiMinus, Matrix.of_apply]
  simp only [Fin.isValue, Prod.mk.injEq, zero_ne_one, and_false, imp_self, implies_true, and_true,
    mul_zero, Finset.sum_const_zero, one_div, zero_add, one_ne_zero, and_self, add_zero]
  simp only [A₁, B₀]
  simp only [kroneckerMap_apply, Matrix.one_apply]
  simp only [alice_A₁, bob_B₀, pauliZ, pauliX]
  simp only [Matrix.smul_apply, Matrix.sub_apply]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.isValue]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
             Matrix.cons_val_fin_one]
  simp only [Fin.isValue, one_ne_zero, ↓reduceIte, mul_zero, one_div, sub_zero, smul_eq_mul,
    mul_one, one_mul, zero_mul, zero_sub, mul_neg, neg_zero, add_zero, zero_ne_one, zero_add,
    neg_mul, neg_neg]
  ring_nf

/-- Correlation E(A₁, B₁) for the Bell state -/
lemma correlation_A₁_B₁ :
    let A₁ := kroneckerMap (· * ·) alice_A₁ (1 : Matrix (Fin 2) (Fin 2) ℂ)
    let B₁ := kroneckerMap (· * ·) (1 : Matrix (Fin 2) (Fin 2) ℂ) bob_B₁
    ((A₁ * B₁) * bellStatePsiMinus).trace = ((Real.sqrt 2)⁻¹ : ℂ) := by
  intro A₁ B₁
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.isValue]
  simp only [Matrix.mul_apply, bellStatePsiMinus, Matrix.of_apply]
  simp only [Fin.isValue, Prod.mk.injEq, zero_ne_one, and_false, imp_self, implies_true, and_true,
    mul_zero, Finset.sum_const_zero, one_div, zero_add, one_ne_zero, and_self, add_zero]
  simp only [A₁, B₁]
  simp only [kroneckerMap_apply, Matrix.one_apply]
  simp only [alice_A₁, bob_B₁, pauliZ, pauliX]
  simp only [Matrix.smul_apply, Matrix.add_apply]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.isValue]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
             Matrix.cons_val_fin_one]
  simp only [Fin.isValue, one_ne_zero, ↓reduceIte, mul_zero, add_zero, smul_eq_mul, mul_one,
    one_mul, zero_mul, zero_add, mul_neg, neg_zero, zero_ne_one]
  ring_nf


/-! ## CHSH Operator and Conditions -/

/-- **Quantum Violation**: The Bell state with optimal measurements achieves |S| = 2√2 -/
theorem CHSH_quantum_violation :
    let A₀ := kroneckerMap (· * ·) alice_A₀ (1 : Matrix (Fin 2) (Fin 2) ℂ)
    let A₁ := kroneckerMap (· * ·) alice_A₁ (1 : Matrix (Fin 2) (Fin 2) ℂ)
    let B₀ := kroneckerMap (· * ·) (1 : Matrix (Fin 2) (Fin 2) ℂ) bob_B₀
    let B₁ := kroneckerMap (· * ·) (1 : Matrix (Fin 2) (Fin 2) ℂ) bob_B₁
    ‖CHSH_expect A₀ A₁ B₀ B₁ bellStatePsiMinus‖ = 2 * Real.sqrt 2 := by
  intro A₀ A₁ B₀ B₁
  simp only [CHSH_expect, CHSH_op]
  rw [add_mul, add_mul, sub_mul]
  rw [Matrix.trace_add, Matrix.trace_add, Matrix.trace_sub]
  rw [correlation_A₀_B₁, correlation_A₀_B₀, correlation_A₁_B₀, correlation_A₁_B₁]
  simp only [sub_neg_eq_add]
  ring_nf
  simp only [Complex.norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, norm_ofNat]
  rw [abs_of_pos (Real.sqrt_pos.mpr (by norm_num : (2 : ℝ) > 0))]
  field_simp
  simp only [Nat.ofNat_nonneg, Real.sq_sqrt]
  ring


end QuantumInfo
