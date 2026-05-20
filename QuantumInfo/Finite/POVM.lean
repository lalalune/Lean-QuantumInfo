/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.Finite.CPTPMap

/-! # Positive Operator-Valued Measures

A Positive Operator-Valued Measures, or POVM, is the most general notion of a quantum "measurement":
a collection of positive semidefinite (PSD) operators that sum to the identity. These induce a distribution,
`POVM.measure`, of measurement outcomes; and they induce a CPTP map, `POVM.measurement_map`, which changes the state
but adds learned information.

Developing this theory is important if one wants to discuss classical information across quantum channels, as POVMs
are the route to get back to classical information (a `ProbDistribution` of outcomes). Further refinements include
Heisenberg-picture evolution under CPTP maps, commutativity properties, and projective measurements.
-/
noncomputable section
open BigOperators
open ComplexOrder
open Matrix
open scoped RealInnerProductSpace

namespace Matrix

theorem traceLeft_sum {ι d d₁ d₂ R : Type*} [Fintype ι] [Fintype d] [AddCommMonoid R]
    (A : ι → Matrix (d × d₁) (d × d₂) R) :
    Matrix.traceLeft (∑ x, A x) = ∑ x, Matrix.traceLeft (A x) := by
  ext i j
  calc
    (Matrix.traceLeft (∑ x, A x)) i j = ∑ i₂, ∑ x, A x (i₂, i) (i₂, j) := by
      simp only [Matrix.traceLeft, Matrix.of_apply, Matrix.sum_apply]
    _ = ∑ x, ∑ i₂, A x (i₂, i) (i₂, j) := Finset.sum_comm
    _ = (∑ x, Matrix.traceLeft (A x)) i j := by
      simp only [Matrix.traceLeft, Matrix.of_apply, Matrix.sum_apply]

end Matrix

namespace HermitianMat

variable {n 𝕜 : Type*} [RCLike 𝕜] [DecidableEq n]

/-- A diagonal Hermitian matrix with one real entry. -/
def single (i : n) (r : ℝ) : HermitianMat n 𝕜 :=
  diagonal 𝕜 fun j ↦ if i = j then r else 0

@[simp]
theorem single_mat (i : n) (r : ℝ) :
    (single (𝕜 := 𝕜) i r).mat = Matrix.single i i (r : 𝕜) := by
  change (HermitianMat.diagonal 𝕜 (fun j ↦ if i = j then r else 0)).mat =
    Matrix.single i i (r : 𝕜)
  rw [HermitianMat.diagonal_mat]
  ext j k
  simp only [diagonal_apply, Matrix.single, of_apply]
  split_ifs <;> grind

end HermitianMat

/-- A POVM is a (finite) collection of PSD matrices on the same Hilbert space
 that sum to the identity. Here `X` indexes the matrices, and `d` is the space
 dimension.

 Applied to an `MState` on that on that space with
 `POVM.measure`, this produces a distribution of outcomes indexed by the same
 type as the collection.

 This measurement action can be composed with `MState.of_classical`, in which
 case it is equal to a CPTP map `measurement_map`. -/
structure POVM (X : Type*) (d : Type*) [Fintype X] [Fintype d] [DecidableEq d] where
  mats : X → HermitianMat d ℂ
  zero_le : ∀ x, 0 ≤ (mats x)
  normalized : ∑ x, mats x = 1

namespace POVM

variable {X : Type*} {d : Type*} [Fintype X] [Fintype d] [DecidableEq d] [DecidableEq X]

/-- The projective measurement in the distinguished computational basis. -/
def computationalBasis (d : Type*) [Fintype d] [DecidableEq d] : POVM d d where
  mats i := HermitianMat.single (𝕜 := ℂ) i 1
  zero_le i := by
    rw [HermitianMat.zero_le_iff]
    rw [HermitianMat.single_mat]
    exact (Matrix.PosSemidef.stdBasisMatrix_iff_eq i i (zero_lt_one' ℂ)).2 rfl
  normalized := by
    ext1
    rw [HermitianMat.mat_finset_sum]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [HermitianMat.single_mat, Matrix.single, Matrix.sum_apply]
    · simp [HermitianMat.single_mat, Matrix.single, Matrix.sum_apply, hij]

@[simp]
theorem computationalBasis_mats (i : d) :
    (computationalBasis d).mats i = HermitianMat.single (𝕜 := ℂ) i 1 :=
  rfl

/-- The act of measuring is a quantum channel, that maps a `d`-dimensional quantum
state to an `d × X`-dimensional quantum-classical state. -/
def measurementMap (Λ : POVM X d) : CPTPMap d (d × X) where
  toLinearMap :=
    ∑ (x : X), open Kronecker in {
      toFun := fun ρ ↦ ((((Λ.mats x) ^ (1/2:ℝ)).mat * ρ * ((Λ.mats x)^(1/2:ℝ)).mat) ⊗ₖ Matrix.single x x 1)
      map_add' := by simp [mul_add, add_mul, Matrix.kroneckerMap_add_left]
      map_smul' := by simp [Matrix.smul_kronecker]
    }
  cp := by
    apply Finset.sum_induction
    · exact fun _ _ ha ↦ ha.add
    · exact MatrixMap.IsCompletelyPositive.zero _ _
    · intro x _
      --Note: this map M₁ would do as well as an object on its own, it's "measure and forget the result".
      let M₁ : MatrixMap d d ℂ := ⟨⟨
        fun ρ ↦ ((Λ.mats x) ^ (1/2:ℝ)).mat * ρ * ((Λ.mats x)^(1/2:ℝ)).mat,
        by simp [mul_add, add_mul]⟩,
        by simp⟩
      let M₂ : MatrixMap d (d × X) ℂ := ⟨⟨
        fun ρ ↦ (ρ.kronecker (Matrix.single x x 1)),
        by simp [add_mul, Matrix.kroneckerMap_add_left]⟩,
        by simp [Matrix.smul_kronecker]⟩
      set M₃ := LinearMap.comp M₂ M₁ with hM₃
      simp only [M₁, M₂, LinearMap.comp, kronecker, LinearMap.coe_mk, AddHom.coe_mk] at hM₃
      unfold Function.comp at hM₃
      rw [← hM₃]
      apply MatrixMap.IsCompletelyPositive.comp
      · dsimp [M₁]
        conv =>
          enter [1, 1, 1, ρ, 2]
          rw [← HermitianMat.conjTranspose_mat]
        exact MatrixMap.conj_isCompletelyPositive (Λ.mats x ^ (1 / 2)).mat
      · apply MatrixMap.kron_kronecker_const
        exact (Matrix.PosSemidef.stdBasisMatrix_iff_eq x x (zero_lt_one' ℂ)).2 rfl
  TP := by
    intro x
    rw [LinearMap.sum_apply, trace_sum]
    dsimp
    simp only [Matrix.trace_kronecker, Matrix.trace_mul_cycle (B := x),
      Matrix.trace_single_eq_same, mul_one]
    rw [← trace_sum, ← Finset.sum_mul]
    congr
    convert one_mul x
    rw [show (1 : Matrix d d ℂ) = (1 : HermitianMat d ℂ).mat by rfl, ← Λ.normalized]
    rw [HermitianMat.mat_finset_sum]
    congr! with i _
    exact HermitianMat.pow_half_mul (Λ.zero_le i)

open Kronecker in
theorem measurementMap_apply_matrix (Λ : POVM X d) (m : Matrix d d ℂ) :
  Λ.measurementMap.map m =  ∑ x : X,
    ((((Λ.mats x) ^ (1/2:ℝ)).mat * m * ((Λ.mats x)^(1/2:ℝ)).mat) ⊗ₖ Matrix.single x x 1) := by
  dsimp [measurementMap, HPMap.map]
  rw [LinearMap.sum_apply]
  rfl

open HermitianMat in
theorem measurementMap_apply_hermitianMat (Λ : POVM X d) (m : HermitianMat d ℂ) :
  Λ.measurementMap.toHPMap m = ∑ x : X,
    ((m.conj ((Λ.mats x)^(1/2:ℝ)).mat : HermitianMat d ℂ) ⊗ₖ
      HermitianMat.single (𝕜 := ℂ) x 1) := by
  ext1
  convert Λ.measurementMap_apply_matrix m.mat
  simp [conj_apply, conjTranspose_mat, HermitianMat.mat_finset_sum,
    kronecker_mat, mat_mk, HermitianMat.single_mat]

/-- A POVM leads to a distribution of outcomes on any given mixed state ρ. -/
def measure (Λ : POVM X d) (ρ : MState d) : ProbDistribution X := .mk'
    (f := fun x ↦ ⟪Λ.mats x, ρ.M⟫)
    (h₁ := fun x ↦ HermitianMat.inner_ge_zero (Λ.zero_le x) ρ.zero_le)
    (hN := by
      simp [HermitianMat.inner_eq_re_trace, ← Complex.re_sum, ← trace_sum, ← Finset.sum_mul,
        ← HermitianMat.mat_finset_sum, Λ.normalized])

/-- Measuring a pure state in the computational basis gives the squared amplitude. -/
theorem computationalBasis_measure_pure (ψ : Ket d) (i : d) :
    (((computationalBasis d).measure (MState.pure ψ) i : Prob) : ℝ) =
      Complex.normSq (ψ i) := by
  change ⟪HermitianMat.single (𝕜 := ℂ) i 1, (MState.pure ψ).M⟫ =
    Complex.normSq (ψ i)
  simp [HermitianMat.inner_def, HermitianMat.single_mat, Matrix.trace,
    Matrix.mul_apply, Matrix.single, MState.pure_apply]
  rw [show (∑ x, ∑ y,
      (if i = x ∧ i = y then ψ y * (starRingEnd ℂ) (ψ x) else 0).re) =
        (ψ i * (starRingEnd ℂ) (ψ i)).re by
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single i]
      · simp
      · intro y _ hy
        simp [Ne.symm hy]
      · intro hi
        exact (hi (Finset.mem_univ i)).elim
    · intro x _ hx
      simp [Ne.symm hx]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim]
  simp [Complex.mul_conj]

/-- Measuring a computational-basis ket gives the matching point mass distribution. -/
theorem computationalBasis_measure_basis (i : d) :
    (computationalBasis d).measure (MState.pure (Ket.basis i)) =
      ProbDistribution.constant i := by
  ext j
  rw [computationalBasis_measure_pure]
  by_cases hij : i = j
  · subst j
    simp [Ket.basis, Ket.apply]
  · simp [ProbDistribution.constant_eq, Ket.basis, Ket.apply, hij]

/-- The quantum-classical `POVM.measurement_map`, gives a marginal on the right equal to `POVM.measure`.-/
theorem traceLeft_measurementMap_eq_measure (Λ : POVM X d) (ρ : MState d) :
    (Λ.measurementMap ρ).traceLeft = MState.ofClassical (Λ.measure ρ) := by
  open Kronecker in
  ext i j
  rcases ρ with ⟨⟨ρ, ρH⟩, hρ0, hρ1⟩
  change (Matrix.traceLeft (Λ.measurementMap.map ρ)) i j = _
  rw [measurementMap_apply_matrix]
  rw [Matrix.traceLeft_sum]
  simp only [Matrix.traceLeft, Matrix.of_apply, Matrix.sum_apply]
  simp only [kroneckerMap_apply, MState.coe_ofClassical]
  simp only [single, of_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_irrel,
    Finset.sum_const_zero]
  simp only [HermitianMat.diagonal, HermitianMat.mat_mk, diagonal_apply]
  symm; split
  · subst j
    simp only [measure, ProbDistribution.mk', ProbDistribution.funlike_apply, and_self, Finset.sum_ite_eq',
      Finset.mem_univ, ↓reduceIte]
    change _ = Matrix.trace _
    rw [Matrix.trace_mul_cycle, HermitianMat.pow_half_mul (Λ.zero_le i)]
    exact HermitianMat.inner_eq_trace_rc _ _
  · conv => enter [2, 2, x]; rw [if_neg (by grind)]
    simp

/-- The action of measuring a state with the POVM `Λ`, discarding the resulting state, and keeping
the mixed state recording the outcome. This resulting state is purely diagonal, as given in
`POVM.measureDiscard_apply`. -/
noncomputable def measureDiscard (Λ : POVM X d) : CPTPMap d X :=
  CPTPMap.traceLeft ∘ₘ Λ.measurementMap

theorem measureDiscard_apply (Λ : POVM X d) (ρ : MState d) :
    Λ.measureDiscard ρ = MState.ofClassical (Λ.measure ρ) := by
  simp [measureDiscard, traceLeft_measurementMap_eq_measure]

/-- The action of measuring a state with the POVM `Λ`, forgetting the measurement outcome, and
keeping the disturbed state. -/
noncomputable def measureForget (Λ : POVM X d) : CPTPMap d d :=
  CPTPMap.traceRight ∘ₘ Λ.measurementMap

open scoped Kronecker in
omit [Fintype d] [DecidableEq d] in
private theorem traceRight_sum_kronecker_single {R : Type*} [Semiring R]
    (A : X → Matrix d d R) :
    Matrix.traceRight (∑ x, A x ⊗ₖ Matrix.single x x (1 : R)) = ∑ x, A x := by
  ext i j
  simp_rw [Matrix.traceRight, Matrix.of_apply, Matrix.sum_apply, Matrix.kroneckerMap, Matrix.single]
  rw [Finset.sum_comm]
  simp

theorem measureForget_eq_kraus (Λ : POVM X d) :
    Λ.measureForget = CPTPMap.of_kraus_CPTPMap (fun i ↦ ((Λ.mats i) ^ (1/2 : ℝ)).mat) (by
      let K : X → Matrix d d ℂ := fun i => ((Λ.mats i) ^ (1 / 2 : ℝ)).mat
      calc
        ∑ k, (K k).conjTranspose * K k = ∑ k, K k * K k := by
          congr with k
          simp [K]
        _ = ∑ k, (Λ.mats k).mat := by
          ext i j
          simp_rw [Matrix.sum_apply]
          refine Finset.sum_congr rfl ?_
          intro k _
          simpa [K] using congrFun₂ (HermitianMat.pow_half_mul (Λ.zero_le k)) i j
        _ = (1 : Matrix d d ℂ) := by
          simpa [HermitianMat.mat_finset_sum] using congrArg HermitianMat.mat Λ.normalized
    ) := by
  let K : X → Matrix d d ℂ := fun i => ((Λ.mats i) ^ (1 / 2 : ℝ)).mat
  have hTP : (∑ k, (K k).conjTranspose * K k) = 1 := by
    calc
      ∑ k, (K k).conjTranspose * K k = ∑ k, K k * K k := by
        congr with k
        simp [K]
      _ = ∑ k, (Λ.mats k).mat := by
        ext i j
        simp_rw [Matrix.sum_apply]
        refine Finset.sum_congr rfl ?_
        intro k _
        simpa [K] using congrFun₂ (HermitianMat.pow_half_mul (Λ.zero_le k)) i j
      _ = (1 : Matrix d d ℂ) := by
        simpa [HermitianMat.mat_finset_sum] using congrArg HermitianMat.mat Λ.normalized
  change Λ.measureForget = CPTPMap.of_kraus_CPTPMap K hTP
  apply CPTPMap.funext
  intro ρ
  apply MState.ext_m
  change Matrix.traceRight (Λ.measurementMap.map ρ.m) = MatrixMap.of_kraus K K ρ.m
  rw [measurementMap_apply_matrix, traceRight_sum_kronecker_single, MatrixMap.of_kraus,
    LinearMap.sum_apply]
  ext i j : 2
  simp_rw [Matrix.sum_apply]
  refine Finset.sum_congr rfl ?_
  intro x _
  change (K x * ρ.m * K x) i j = (K x * ρ.m * (K x).conjTranspose) i j
  rw [show (K x).conjTranspose = K x by simp [K]]

end POVM
