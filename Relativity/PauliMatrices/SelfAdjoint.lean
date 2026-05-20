/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Relativity.PauliMatrices.Basic
import Relativity.MinkowskiMatrix
/-!

## Interaction of Pauli matrices with self-adjoint matrices

-/
namespace PauliMatrix
open Matrix Module

/-- The trace of a pauli-matrix multiplied by a self-adjoint `2×2` matrix is real. -/
lemma trace_pauliMatrix_mul_selfAdjoint_re (μ : Fin 1 ⊕ Fin 3)
    (A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    (Matrix.trace (pauliMatrix μ * A.1)).re = Matrix.trace (pauliMatrix μ * A.1) := by
  rw [← Complex.conj_eq_iff_re, starRingEnd_apply, ← trace_conjTranspose, conjTranspose_mul,
    pauliMatrix_selfAdjoint μ, ← star_eq_conjTranspose, A.2, trace_mul_comm]

open Complex

/-- Two `2×2` self-adjoint matrices are equal if the (complex) traces of each matrix multiplied by
  each of the Pauli-matrices are equal. -/
lemma selfAdjoint_ext_complex {A B : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)}
    (h0 : Matrix.trace (σ0 * A.1) = Matrix.trace (σ0 * B.1))
    (h1 : Matrix.trace (σ1 * A.1) = Matrix.trace (σ1 * B.1))
    (h2 : Matrix.trace (σ2 * A.1) = Matrix.trace (σ2 * B.1))
    (h3 : Matrix.trace (σ3 * A.1) = Matrix.trace (σ3 * B.1)) : A = B := by
  ext i j
  rw [eta_fin_two A.1, eta_fin_two B.1] at h0 h1 h2 h3
  simp only [Fin.isValue, pauliMatrix_inl_zero_eq_one, one_mul, trace_fin_two_of] at h0
  simp only [pauliMatrix, Fin.isValue, cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons,
    head_cons, zero_smul, tail_cons, one_smul, empty_vecMul, add_zero, zero_add, empty_mul,
    Equiv.symm_apply_apply, trace_fin_two_of] at h1
  simp only [pauliMatrix, Fin.isValue, cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons,
    head_cons, zero_smul, tail_cons, neg_smul, smul_cons, smul_eq_mul, smul_empty, neg_cons,
    neg_empty, empty_vecMul, add_zero, zero_add, empty_mul, Equiv.symm_apply_apply,
    trace_fin_two_of] at h2
  simp only [pauliMatrix, Fin.isValue, cons_mul, Nat.succ_eq_add_one, Nat.reduceAdd, vecMul_cons,
    head_cons, one_smul, tail_cons, zero_smul, empty_vecMul, add_zero, neg_smul, neg_cons,
    neg_empty, zero_add, empty_mul, Equiv.symm_apply_apply, trace_fin_two_of] at h3
  match i, j with
  | 0, 0 =>
    linear_combination (norm := ring_nf) (h0 + h3) / 2
  | 0, 1 =>
    linear_combination (norm := ring_nf) (h1 - I * h2) / 2
    simp
  | 1, 0 =>
    linear_combination (norm := ring_nf) (h1 + I * h2) / 2
    simp
  | 1, 1 =>
    linear_combination (norm := ring_nf) (h0 - h3) / 2

/-- Two `2×2` self-adjoint matrices are equal if the real traces of each matrix multiplied by
  each of the Pauli-matrices are equal. -/
lemma selfAdjoint_ext {A B : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)}
    (h0 : ((Matrix.trace (σ0 * A.1))).re = ((Matrix.trace (σ0 * B.1))).re)
    (h1 : ((Matrix.trace (σ1 * A.1))).re = ((Matrix.trace (σ1 * B.1))).re)
    (h2 : ((Matrix.trace (σ2 * A.1))).re = ((Matrix.trace (σ2 * B.1))).re)
    (h3 : ((Matrix.trace (σ3 * A.1))).re = ((Matrix.trace (σ3 * B.1))).re) :
    A = B := by
  have h0' := congrArg ofRealHom h0
  have h1' := congrArg ofRealHom h1
  have h2' := congrArg ofRealHom h2
  have h3' := congrArg ofRealHom h3
  rw [ofRealHom_eq_coe, ofRealHom_eq_coe] at h0' h1' h2' h3'
  rw [trace_pauliMatrix_mul_selfAdjoint_re _ A,
    trace_pauliMatrix_mul_selfAdjoint_re _ B] at h0' h1' h2' h3'
  exact selfAdjoint_ext_complex h0' h1' h2' h3'

noncomputable section

private lemma half_smul_two_re (x : ℝ) : (((2 : ℝ)⁻¹ * x) • (2 : ℂ)).re = x := by
  norm_num [Complex.smul_re]
  ring_nf

private lemma inv_two_smul_one_re_add_self (x : ℝ) :
    (((2 : ℝ)⁻¹ * x) • (1 : ℂ)).re + (((2 : ℝ)⁻¹ * x) • (1 : ℂ)).re = x := by
  norm_num [Complex.smul_re]
  ring_nf

private lemma mul_half_smul_two_re (x : ℝ) : (((x * (1 / 2 : ℝ)) • (2 : ℂ)).re) = x := by
  norm_num [Complex.smul_re]
  ring_nf

private lemma mul_half_smul_one_re_mul_two (x : ℝ) :
    (((x * (1 / 2 : ℝ)) • (1 : ℂ)).re * 2) = x := by
  norm_num [Complex.smul_re]
  ring_nf

private lemma neg_half_smul_two_re (x : ℝ) : -(((-1 / 2 : ℝ) * x) • (2 : ℂ)).re = x := by
  norm_num [Complex.smul_re]
  ring_nf

private lemma neg_half_smul_one_re_add_neg_half_smul_one_re (x : ℝ) :
    -(((-1 / 2 : ℝ) * x) • (1 : ℂ)).re +
      -(((-1 / 2 : ℝ) * x) • (1 : ℂ)).re = x := by
  norm_num [Complex.smul_re]
  ring_nf

private lemma neg_mul_neg_half_smul_one_re_mul_two (x : ℝ) :
    -((((x * (-1 / 2 : ℝ)) • (1 : ℂ)).re * 2)) = x := by
  norm_num [Complex.smul_re]
  ring_nf

private lemma trace_real_smul_re (r : ℝ) (A : Matrix (Fin 2) (Fin 2) ℂ) :
    (Matrix.trace (r • A)).re = r * (Matrix.trace A).re := by
  simp [Matrix.trace, Fin.sum_univ_two, mul_add]

/-- An auxiliary function which on `i : Fin 1 ⊕ Fin 3` returns the corresponding
  Pauli-matrix as a self-adjoint matrix. -/
def pauliSelfAdjoint (i : Fin 1 ⊕ Fin 3) : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ) :=
  ⟨pauliMatrix i, pauliMatrix_selfAdjoint i⟩

/-- The Pauli matrices are linearly independent. -/
lemma pauliSelfAdjoint_linearly_independent : LinearIndependent ℝ pauliSelfAdjoint := by
  apply Fintype.linearIndependent_iff.mpr
  intro g hg
  simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton] at hg
  rw [Fin.sum_univ_three] at hg
  simp only [Fin.isValue, pauliSelfAdjoint] at hg
  intro i
  have h1 := congrArg (fun A => (Matrix.trace (pauliMatrix i * A.1))) hg
  simp only [Fin.isValue, AddSubgroup.coe_add, selfAdjoint.val_smul, mul_add, mul_smul_comm,
    trace_add, trace_real_smul_re, ZeroMemClass.coe_zero, mul_zero, trace_zero] at h1
  fin_cases i <;> simpa [pauliMatrix] using h1

/-- The Pauli matrices span all self-adjoint matrices. -/
lemma pauliSelfAdjoint_span : ⊤ ≤ Submodule.span ℝ (Set.range pauliSelfAdjoint) := by
  refine (Submodule.top_le_span_range_iff_forall_exists_fun ℝ).mpr ?_
  intro A
  let c : Fin 1 ⊕ Fin 3 → ℝ := fun i =>
    match i with
    | Sum.inl 0 => 1/2 * (Matrix.trace (σ0 * A.1)).re
    | Sum.inr 0 => 1/2 * (Matrix.trace (σ1 * A.1)).re
    | Sum.inr 1 => 1/2 * (Matrix.trace (σ2 * A.1)).re
    | Sum.inr 2 => 1/2 * (Matrix.trace (σ3 * A.1)).re
  use c
  simp only [one_div, Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton, Fin.sum_univ_three, c]
  apply selfAdjoint_ext
  · simp only [pauliSelfAdjoint, AddSubgroup.coe_add, selfAdjoint.val_smul, mul_add,
    mul_smul_comm, trace_add, trace_real_smul_re, σ0_σ0_trace, Complex.smul_re, real_smul, ofReal_mul, ofReal_inv,
    ofReal_ofNat, σ0_σ1_trace, smul_zero, σ0_σ2_trace, add_zero, σ0_σ3_trace, mul_re, inv_re,
    re_ofNat, normSq_ofNat, div_self_mul_self', ofReal_re, inv_im, im_ofNat, neg_zero, zero_div,
    ofReal_im, mul_zero, sub_zero, mul_im, zero_mul]
    simp [pauliMatrix]
    exact half_smul_two_re (Matrix.trace A.1).re
  · simp only [pauliSelfAdjoint, AddSubgroup.coe_add, selfAdjoint.val_smul, mul_add,
    mul_smul_comm, trace_add, trace_real_smul_re, σ1_σ0_trace, smul_zero, σ1_σ1_trace, Complex.smul_re, real_smul,
    ofReal_mul, ofReal_inv, ofReal_ofNat, σ1_σ2_trace, add_zero, σ1_σ3_trace, zero_add, mul_re,
    inv_re, re_ofNat, normSq_ofNat, div_self_mul_self', ofReal_re, inv_im, im_ofNat, neg_zero,
    zero_div, ofReal_im, mul_zero, sub_zero, mul_im, zero_mul]
    simp [pauliMatrix]
    exact inv_two_smul_one_re_add_self _
  · simp only [pauliSelfAdjoint, AddSubgroup.coe_add, selfAdjoint.val_smul, mul_add,
    mul_smul_comm, trace_add, trace_real_smul_re, σ2_σ0_trace, smul_zero, σ2_σ1_trace, σ2_σ2_trace,
    Complex.smul_re, real_smul, ofReal_mul, ofReal_inv, ofReal_ofNat, zero_add, σ2_σ3_trace, add_zero, mul_re,
    inv_re, re_ofNat, normSq_ofNat, div_self_mul_self', ofReal_re, inv_im, im_ofNat, neg_zero,
    zero_div, ofReal_im, mul_zero, sub_zero, mul_im, zero_mul]
    simp [pauliMatrix]
    exact inv_two_smul_one_re_add_self _
  · simp only [pauliSelfAdjoint, AddSubgroup.coe_add, selfAdjoint.val_smul, mul_add,
    mul_smul_comm, trace_add, trace_real_smul_re, σ3_σ0_trace, smul_zero, σ3_σ1_trace, σ3_σ2_trace,
    add_zero, σ3_σ3_trace, Complex.smul_re, real_smul, ofReal_mul, ofReal_inv, ofReal_ofNat, zero_add, mul_re,
    inv_re, re_ofNat, normSq_ofNat, div_self_mul_self', ofReal_re, inv_im, im_ofNat, neg_zero,
    zero_div, ofReal_im, mul_zero, sub_zero, mul_im, zero_mul]
    simp [pauliMatrix]
    exact inv_two_smul_one_re_add_self _

/-- The basis of `selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)` formed by Pauli matrices. -/
def pauliBasis : Basis (Fin 1 ⊕ Fin 3) ℝ (selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :=
  Basis.mk pauliSelfAdjoint_linearly_independent pauliSelfAdjoint_span

/-- An auxiliary function which on `i : Fin 1 ⊕ Fin 3` returns the corresponding
  Pauli-matrix as a self-adjoint matrix with a minus sign for `Sum.inr _`. -/
def pauliSelfAdjoint' (i : Fin 1 ⊕ Fin 3) : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ) :=
  match i with
  | Sum.inl 0 => ⟨σ0, pauliMatrix_selfAdjoint _⟩
  | Sum.inr 0 => ⟨-σ1, by simpa using neg_mem (pauliMatrix_selfAdjoint _)⟩
  | Sum.inr 1 => ⟨-σ2, by simpa using neg_mem (pauliMatrix_selfAdjoint _)⟩
  | Sum.inr 2 => ⟨-σ3, by simpa using neg_mem (pauliMatrix_selfAdjoint _)⟩

/-- The Pauli matrices where `σi` are negated are linearly independent. -/
lemma pauliSelfAdjoint'_linearly_independent : LinearIndependent ℝ pauliSelfAdjoint' := by
  apply Fintype.linearIndependent_iff.mpr
  intro g hg
  simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton] at hg
  rw [Fin.sum_univ_three] at hg
  simp only [Fin.isValue, pauliSelfAdjoint'] at hg
  intro i
  have h1 := congrArg (fun A => (Matrix.trace (pauliMatrix i * A.1))) hg
  simp [-real_smul, mul_add] at h1
  fin_cases i <;> simpa [pauliMatrix] using h1

/-- The Pauli matrices where `σi` are negated span all Self-adjoint matrices. -/
lemma pauliSelfAdjoint'_span : ⊤ ≤ Submodule.span ℝ (Set.range pauliSelfAdjoint') := by
  refine (Submodule.top_le_span_range_iff_forall_exists_fun ℝ).mpr ?_
  intro A
  let c : Fin 1 ⊕ Fin 3 → ℝ := fun i =>
    match i with
    | Sum.inl 0 => 1/2 * (Matrix.trace (σ0 * A.1)).re
    | Sum.inr 0 => - 1/2 * (Matrix.trace (σ1 * A.1)).re
    | Sum.inr 1 => - 1/2 * (Matrix.trace (σ2 * A.1)).re
    | Sum.inr 2 => - 1/2 * (Matrix.trace (σ3 * A.1)).re
  use c
  simp only [one_div, Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton, Fin.sum_univ_three, c]
  apply selfAdjoint_ext
  · simp only [pauliSelfAdjoint', AddSubgroup.coe_add, selfAdjoint.val_smul, smul_neg, mul_add,
    mul_smul_comm, mul_neg, trace_add, trace_real_smul_re, σ0_σ0_trace, real_smul, ofReal_mul,
    ofReal_inv, ofReal_ofNat, trace_neg, σ0_σ1_trace, smul_zero, neg_zero, σ0_σ2_trace, add_zero,
    σ0_σ3_trace, mul_re, inv_re, re_ofNat, normSq_ofNat, div_self_mul_self', ofReal_re, inv_im,
    im_ofNat, zero_div, ofReal_im, mul_zero, sub_zero, mul_im, zero_mul]
    simp [pauliMatrix]
    exact half_smul_two_re (Matrix.trace A.1).re
  · simp only [pauliSelfAdjoint', AddSubgroup.coe_add, selfAdjoint.val_smul, smul_neg, mul_add,
    mul_smul_comm, mul_neg, trace_add, trace_real_smul_re, σ1_σ0_trace, smul_zero, trace_neg,
    σ1_σ1_trace, real_smul, ofReal_mul, ofReal_div, ofReal_neg, ofReal_one, ofReal_ofNat,
    σ1_σ2_trace, neg_zero, add_zero, σ1_σ3_trace, zero_add, neg_re, mul_re, div_ofNat_re, one_re,
    ofReal_re, div_ofNat_im, neg_im, one_im, zero_div, ofReal_im, mul_zero, sub_zero, re_ofNat,
    mul_im, zero_mul, im_ofNat]
    simp [pauliMatrix]
    exact neg_half_smul_one_re_add_neg_half_smul_one_re _
  · simp only [pauliSelfAdjoint', AddSubgroup.coe_add, selfAdjoint.val_smul, smul_neg, mul_add,
    mul_smul_comm, mul_neg, trace_add, trace_real_smul_re, σ2_σ0_trace, smul_zero, trace_neg,
    σ2_σ1_trace, neg_zero, σ2_σ2_trace, real_smul, ofReal_mul, ofReal_div, ofReal_neg, ofReal_one,
    ofReal_ofNat, zero_add, σ2_σ3_trace, add_zero, neg_re, mul_re, div_ofNat_re, one_re, ofReal_re,
    div_ofNat_im, neg_im, one_im, zero_div, ofReal_im, mul_zero, sub_zero, re_ofNat, mul_im,
    zero_mul, im_ofNat]
    simp [pauliMatrix]
    exact neg_half_smul_one_re_add_neg_half_smul_one_re _
  · simp only [pauliSelfAdjoint', AddSubgroup.coe_add, selfAdjoint.val_smul, smul_neg, mul_add,
    mul_smul_comm, mul_neg, trace_add, trace_real_smul_re, σ3_σ0_trace, smul_zero, trace_neg,
    σ3_σ1_trace, neg_zero, σ3_σ2_trace, add_zero, σ3_σ3_trace, real_smul, ofReal_mul, ofReal_div,
    ofReal_neg, ofReal_one, ofReal_ofNat, zero_add, neg_re, mul_re, div_ofNat_re, one_re, ofReal_re,
    div_ofNat_im, neg_im, one_im, zero_div, ofReal_im, mul_zero, sub_zero, re_ofNat, mul_im,
    zero_mul, im_ofNat]
    simp [pauliMatrix]
    exact neg_half_smul_one_re_add_neg_half_smul_one_re _

/-- The basis of `selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)` formed by Pauli matrices
  where the `1, 2, 3` pauli matrices are negated. These can be thought of as the
  covariant Pauli-matrices. -/
def pauliBasis' : Basis (Fin 1 ⊕ Fin 3) ℝ (selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :=
  Basis.mk pauliSelfAdjoint'_linearly_independent pauliSelfAdjoint'_span

set_option maxHeartbeats 800000
/-- The decomposition of a self-adjoint matrix into the Pauli matrices (where `σi` are negated). -/
lemma pauliBasis'_decomp (M : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    M = (1/2 * (Matrix.trace (σ0 * M.1)).re) • pauliBasis' (Sum.inl 0)
    + (-1/2 * (Matrix.trace (σ1 * M.1)).re) • pauliBasis' (Sum.inr 0)
    + (-1/2 * (Matrix.trace (σ2 * M.1)).re) • pauliBasis' (Sum.inr 1)
    + (-1/2 * (Matrix.trace (σ3 * M.1)).re) • pauliBasis' (Sum.inr 2) := by
  apply selfAdjoint_ext
  · simp only [Fin.isValue, one_div, pauliBasis', Basis.coe_mk, pauliSelfAdjoint',
    AddSubgroup.coe_add, selfAdjoint.val_smul, smul_neg, mul_add, mul_smul_comm, mul_neg,
    trace_add, trace_real_smul_re, σ0_σ0_trace, real_smul, ofReal_mul, ofReal_inv, ofReal_ofNat, trace_neg,
    σ0_σ1_trace, smul_zero, neg_zero, add_zero, σ0_σ2_trace, σ0_σ3_trace, mul_re, inv_re, re_ofNat,
    normSq_ofNat, div_self_mul_self', ofReal_re, inv_im, im_ofNat, zero_div, ofReal_im, mul_zero,
    sub_zero, mul_im, zero_mul]
    simp [pauliMatrix, smul_eq_mul, Matrix.trace, Fin.sum_univ_two]
  · simp only [Fin.isValue, one_div, pauliBasis', Basis.coe_mk, pauliSelfAdjoint',
    AddSubgroup.coe_add, selfAdjoint.val_smul, smul_neg, mul_add, mul_smul_comm, mul_neg,
    trace_add, trace_real_smul_re, σ1_σ0_trace, smul_zero, trace_neg, σ1_σ1_trace, real_smul, ofReal_mul,
    ofReal_div, ofReal_neg, ofReal_one, ofReal_ofNat, zero_add, σ1_σ2_trace, neg_zero, add_zero,
    σ1_σ3_trace, neg_re, mul_re, div_ofNat_re, one_re, ofReal_re, div_ofNat_im, neg_im, one_im,
    zero_div, ofReal_im, mul_zero, sub_zero, re_ofNat, mul_im, zero_mul, im_ofNat]
    simp [pauliMatrix, smul_eq_mul, Matrix.trace, Fin.sum_univ_two]
    ring_nf
  · simp only [Fin.isValue, one_div, pauliBasis', Basis.coe_mk, pauliSelfAdjoint',
    AddSubgroup.coe_add, selfAdjoint.val_smul, smul_neg, mul_add, mul_smul_comm, mul_neg,
    trace_add, trace_real_smul_re, σ2_σ0_trace, smul_zero, trace_neg, σ2_σ1_trace, neg_zero, add_zero,
    σ2_σ2_trace, real_smul, ofReal_mul, ofReal_div, ofReal_neg, ofReal_one, ofReal_ofNat, zero_add,
    σ2_σ3_trace, neg_re, mul_re, div_ofNat_re, one_re, ofReal_re, div_ofNat_im, neg_im, one_im,
    zero_div, ofReal_im, mul_zero, sub_zero, re_ofNat, mul_im, zero_mul, im_ofNat]
    simp [pauliMatrix, smul_eq_mul, Matrix.trace, Fin.sum_univ_two]
    ring_nf
  · simp only [Fin.isValue, one_div, pauliBasis', Basis.coe_mk, pauliSelfAdjoint',
    AddSubgroup.coe_add, selfAdjoint.val_smul, smul_neg, mul_add, mul_smul_comm, mul_neg,
    trace_add, trace_real_smul_re, σ3_σ0_trace, smul_zero, trace_neg, σ3_σ1_trace, neg_zero, add_zero,
    σ3_σ2_trace, σ3_σ3_trace, real_smul, ofReal_mul, ofReal_div, ofReal_neg, ofReal_one,
    ofReal_ofNat, zero_add, neg_re, mul_re, div_ofNat_re, one_re, ofReal_re, div_ofNat_im, neg_im,
    one_im, zero_div, ofReal_im, mul_zero, sub_zero, re_ofNat, mul_im, zero_mul, im_ofNat]
    simp [pauliMatrix, smul_eq_mul, Matrix.trace, Fin.sum_univ_two]
    ring_nf

/-- The component of a self-adjoint matrix in the direction `σ0` under
  the basis formed by the covariant Pauli matrices. -/
@[simp]
lemma pauliBasis'_repr_inl_0 (M : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    pauliBasis'.repr M (Sum.inl 0) = 1 / 2 * Matrix.trace (σ0 * M.1) := by
  have hM : M = ∑ i, pauliBasis'.repr M i • pauliBasis' i :=
    (Basis.sum_repr pauliBasis' M).symm
  simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton, Fin.sum_univ_three] at hM
  have h0 := congrArg (fun A => Matrix.trace (σ0 * A.1)/ 2) hM
  simp only [Fin.isValue, pauliBasis', Basis.mk_repr, Basis.coe_mk, pauliSelfAdjoint',
    AddSubgroup.coe_add, selfAdjoint.val_smul, smul_neg, mul_add, mul_smul_comm, mul_neg,
    trace_add, trace_real_smul_re, σ0_σ0_trace, real_smul, trace_neg, σ0_σ1_trace, smul_zero, neg_zero,
    σ0_σ2_trace, add_zero, σ0_σ3_trace, isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, IsUnit.mul_div_cancel_right] at h0
  simp [pauliMatrix, smul_eq_mul, Matrix.trace, Fin.sum_univ_two] at h0
  linear_combination (norm := ring_nf) -h0
  simp [pauliBasis', pauliMatrix, smul_eq_mul, Matrix.trace, Fin.sum_univ_two]
  ring_nf

/-- The component of a self-adjoint matrix in the direction `-σ1` under
  the basis formed by the covariant Pauli matrices. -/
@[simp]
lemma pauliBasis'_repr_inr_0 (M : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    pauliBasis'.repr M (Sum.inr 0) = - 1 / 2 * Matrix.trace (σ1 * M.1) := by
  have hM : M = ∑ i, pauliBasis'.repr M i • pauliBasis' i :=
    (Basis.sum_repr pauliBasis' M).symm
  simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton, Fin.sum_univ_three] at hM
  have h0 := congrArg (fun A => - Matrix.trace (σ1 * A.1)/ 2) hM
  simp only [Fin.isValue, pauliBasis', Basis.mk_repr, Basis.coe_mk, pauliSelfAdjoint',
    AddSubgroup.coe_add, selfAdjoint.val_smul, smul_neg, mul_add, mul_smul_comm, mul_neg,
    trace_add, trace_real_smul_re, σ1_σ0_trace, smul_zero, trace_neg, σ1_σ1_trace, real_smul, σ1_σ2_trace,
    neg_zero, add_zero, σ1_σ3_trace, zero_add, neg_neg, isUnit_iff_ne_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, IsUnit.mul_div_cancel_right] at h0
  simp [pauliMatrix, smul_eq_mul, Matrix.trace, Fin.sum_univ_two] at h0
  linear_combination (norm := ring_nf) -h0
  simp [pauliBasis', pauliMatrix, smul_eq_mul, Matrix.trace, Fin.sum_univ_two]
  ring_nf

/-- The component of a self-adjoint matrix in the direction `-σ2` under
  the basis formed by the covariant Pauli matrices. -/
@[simp]
lemma pauliBasis'_repr_inr_1 (M : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    pauliBasis'.repr M (Sum.inr 1) = - 1 / 2 * Matrix.trace (σ2 * M.1) := by
  have hM : M = ∑ i, pauliBasis'.repr M i • pauliBasis' i :=
    (Basis.sum_repr pauliBasis' M).symm
  simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton, Fin.sum_univ_three] at hM
  have h0 := congrArg (fun A => - Matrix.trace (σ2 * A.1)/ 2) hM
  simp only [Fin.isValue, pauliBasis', Basis.mk_repr, Basis.coe_mk, pauliSelfAdjoint',
    AddSubgroup.coe_add, selfAdjoint.val_smul, smul_neg, mul_add, mul_smul_comm, mul_neg,
    trace_add, trace_real_smul_re, σ2_σ0_trace, smul_zero, trace_neg, σ2_σ1_trace, neg_zero, σ2_σ2_trace,
    real_smul, zero_add, σ2_σ3_trace, add_zero, neg_neg, isUnit_iff_ne_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, IsUnit.mul_div_cancel_right] at h0
  simp [pauliMatrix, smul_eq_mul, Matrix.trace, Fin.sum_univ_two] at h0
  linear_combination (norm := ring_nf) -h0
  simp [pauliBasis', pauliMatrix, smul_eq_mul, Matrix.trace, Fin.sum_univ_two]
  ring_nf

/-- The component of a self-adjoint matrix in the direction `-σ3` under
  the basis formed by the covariant Pauli matrices. -/
@[simp]
lemma pauliBasis'_repr_inr_2 (M : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    pauliBasis'.repr M (Sum.inr 2) = - 1 / 2 * Matrix.trace (σ3 * M.1) := by
  have hM : M = ∑ i, pauliBasis'.repr M i • pauliBasis' i :=
    (Basis.sum_repr pauliBasis' M).symm
  simp only [Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero, Fin.isValue,
    Finset.sum_singleton, Fin.sum_univ_three] at hM
  have h0 := congrArg (fun A => - Matrix.trace (σ3 * A.1)/ 2) hM
  simp only [Fin.isValue, pauliBasis', Basis.mk_repr, Basis.coe_mk, pauliSelfAdjoint',
    AddSubgroup.coe_add, selfAdjoint.val_smul, smul_neg, mul_add, mul_smul_comm, mul_neg,
    trace_add, trace_real_smul_re, σ3_σ0_trace, smul_zero, trace_neg, σ3_σ1_trace, neg_zero, σ3_σ2_trace,
    add_zero, σ3_σ3_trace, real_smul, zero_add, neg_neg, isUnit_iff_ne_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, IsUnit.mul_div_cancel_right] at h0
  simp [pauliMatrix, smul_eq_mul, Matrix.trace, Fin.sum_univ_two] at h0
  linear_combination (norm := ring_nf) -h0
  simp [pauliBasis', pauliMatrix, smul_eq_mul, Matrix.trace, Fin.sum_univ_two]
  ring_nf

/-- The relationship between the basis `pauliBasis` of contravariant Pauli-matrices and the basis
  `pauliBasis'` of covariant Pauli matrices is by multiplication by the Minkowski matrix. -/
lemma pauliBasis_minkowskiMetric_pauliBasis' (i : Fin 1 ⊕ Fin 3) :
    pauliBasis i = minkowskiMatrix i i • pauliBasis' i := by
  fin_cases i <;>
    ext a b <;>
    simp [pauliBasis, pauliBasis', pauliSelfAdjoint, pauliSelfAdjoint',
      minkowskiMatrix.inr_i_inr_i]

end
end PauliMatrix
