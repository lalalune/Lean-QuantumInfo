/-
Copyright (c) 2026. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Antigravity
-/
import Mathlib
import QuantumInfo.ForMathlib.CompoundMatrix
import QuantumInfo.ForMathlib.HermitianMat.Order

/-!
# Weyl's Majorization Theorem

This file establishes Weyl's multiplicative majorization theorem for positive semidefinite matrices.

## Main Results

* `Majorization.weyl_multiplicative`: For PSD matrices A, B of dimension d, and k ≤ d:
  ∏_{i=1}^k λ↓_i(ABA) ≤ ∏_{i=1}^k λ↓_i(A²) × ∏_{i=1}^k λ↓_i(B)

## References

* Horn & Johnson, "Matrix Analysis", Chapter 3
* Bhatia, "Matrix Analysis", Chapter IV
-/

open Matrix BigOperators Finset ComplexOrder

namespace Majorization

section GeneralDefs

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- The largest eigenvalue of a Hermitian matrix. -/
noncomputable def maxEigenvalueGen (A : Matrix n n ℂ) (hA : A.IsHermitian) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty hA.eigenvalues

/-- The smallest eigenvalue of a Hermitian matrix. -/
noncomputable def minEigenvalueGen (A : Matrix n n ℂ) (hA : A.IsHermitian) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty hA.eigenvalues

/-- The spectral radius of a Hermitian matrix. -/
noncomputable def spectralRadiusGen (A : Matrix n n ℂ) (hA : A.IsHermitian) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => |hA.eigenvalues i|)

/-- For PSD matrices, spectral radius equals max eigenvalue. -/
lemma spectralRadiusGen_eq_maxEigenvalue_of_posSemidef (A : Matrix n n ℂ) (hA : A.PosSemidef) :
    spectralRadiusGen A hA.1 = maxEigenvalueGen A hA.1 := by
  simp only [spectralRadiusGen, maxEigenvalueGen]
  congr 1
  ext i
  exact abs_of_nonneg (hA.eigenvalues_nonneg i)

end GeneralDefs

section FinDefs

variable {d : ℕ} [NeZero d]

-- Need Nonempty (Fin d) when d > 0
instance instNonemptyFinOfNeZero : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_neZero d⟩⟩

/-- The largest eigenvalue specialized to Fin d. -/
noncomputable def maxEigenvalue (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) : ℝ :=
  maxEigenvalueGen A hA

/-- The smallest eigenvalue specialized to Fin d. -/
noncomputable def minEigenvalue (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) : ℝ :=
  minEigenvalueGen A hA

/-- The spectral radius specialized to Fin d. -/
noncomputable def spectralRadius (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.IsHermitian) : ℝ :=
  spectralRadiusGen A hA

/-- For PSD matrices, the max eigenvalue is non-negative. -/
lemma maxEigenvalue_nonneg (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.PosSemidef) :
    0 ≤ maxEigenvalue A hA.1 := by
  simp only [maxEigenvalue, maxEigenvalueGen]
  exact Finset.le_sup'_of_le _ (Finset.mem_univ 0) (hA.eigenvalues_nonneg 0)

/-- For PSD matrices, spectral radius equals max eigenvalue. -/
lemma spectralRadius_eq_maxEigenvalue_of_posSemidef (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.PosSemidef) :
    spectralRadius A hA.1 = maxEigenvalue A hA.1 :=
  spectralRadiusGen_eq_maxEigenvalue_of_posSemidef A hA

/-- The set of k-element subsets of Fin d is nonempty when k ≤ d. -/
lemma subsets_nonempty (hk : k ≤ d) : Nonempty (subsets d k) := by
  let S : Finset (Fin d) := Finset.univ.filter (fun i => i.val < k)
  have hcard : S.card = k := by
    simp only [S]
    trans (Finset.range k).card
    · apply Finset.card_bij (fun i _ => i.val) (fun i hi => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
        exact Finset.mem_range.mpr hi)
        (fun a₁ _ a₂ _ h => Fin.val_injective h)
        (fun b hb => ⟨⟨b, Nat.lt_of_lt_of_le (Finset.mem_range.mp hb) hk⟩,
          by simp [Finset.mem_range.mp hb]⟩)
    · exact Finset.card_range k
  have h : S ∈ subsets d k := by
    simp only [subsets, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hcard
  exact ⟨⟨S, h⟩⟩

section MaxEigLemmas

variable {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]

/-- A PSD HermitianMat is bounded above by its max eigenvalue times the identity. -/
lemma maxEig_bound (B : HermitianMat m ℂ) (hB : 0 ≤ B) :
    B ≤ maxEigenvalueGen B.mat B.H • 1 := by
  have ha' : B.mat.PosSemidef := HermitianMat.zero_le_iff.mp hB
  refine (Matrix.PosSemidef.le_smul_one_of_eigenvalues_iff ha'.1 (maxEigenvalueGen B.mat B.H)).mp ?_
  intro i
  exact Finset.le_sup'_of_le _ (Finset.mem_univ i) le_rfl

/-- Max eigenvalue is monotone with respect to the PSD order. -/
lemma maxEig_mono (A B : HermitianMat m ℂ) (hB : 0 ≤ B) (hAB : A ≤ B) :
    maxEigenvalueGen A.mat A.H ≤ maxEigenvalueGen B.mat B.H := by
  have hb_le_max : B ≤ maxEigenvalueGen B.mat B.H • 1 := maxEig_bound B hB
  have ha_le_max : A ≤ maxEigenvalueGen B.mat B.H • 1 := le_trans hAB hb_le_max
  open MatrixOrder in
  have ha_le_max' : A.mat ≤ maxEigenvalueGen B.mat B.H • 1 := HermitianMat.le_iff.mp ha_le_max
  have h_eig := (Matrix.PosSemidef.le_smul_one_of_eigenvalues_iff A.H (maxEigenvalueGen B.mat B.H)).mpr ha_le_max'
  apply Finset.sup'_le
  intro i _
  exact h_eig i

/-- If X ≤ c • Y in PSD order with c ≥ 0, then maxEig(X) ≤ c * maxEig(Y). -/
lemma maxEig_le_smul_maxEig (X Y : HermitianMat m ℂ)
    (hY : 0 ≤ Y) (c : ℝ) (hc : 0 ≤ c)
    (h : X ≤ c • Y) :
    maxEigenvalueGen X.mat X.H ≤ c * maxEigenvalueGen Y.mat Y.H := by
  have h1 : Y ≤ maxEigenvalueGen Y.mat Y.H • 1 := maxEig_bound Y hY
  have h2 : c • Y ≤ (c * maxEigenvalueGen Y.mat Y.H) • (1 : HermitianMat m ℂ) := by
    calc c • Y ≤ c • (maxEigenvalueGen Y.mat Y.H • 1) :=
          smul_le_smul_of_nonneg_left h1 hc
        _ = (c * maxEigenvalueGen Y.mat Y.H) • 1 := by rw [smul_smul]
  have h3 : X ≤ (c * maxEigenvalueGen Y.mat Y.H) • (1 : HermitianMat m ℂ) := le_trans h h2
  open MatrixOrder in
  have h4 : X.mat ≤ (c * maxEigenvalueGen Y.mat Y.H) • (1 : Matrix m m ℂ) := HermitianMat.le_iff.mp h3
  have h5 := (Matrix.PosSemidef.le_smul_one_of_eigenvalues_iff X.H (c * maxEigenvalueGen Y.mat Y.H)).mpr h4
  exact Finset.sup'_le _ _ (fun i _ => h5 i)

/-- maxEigenvalueGen is proof-irrelevant: if A = B then maxEig(A, hA) = maxEig(B, hB). -/
lemma maxEigenvalueGen_congr {A B : Matrix m m ℂ} (h : A = B) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    maxEigenvalueGen A hA = maxEigenvalueGen B hB := by
  cases h; rfl

end MaxEigLemmas

-- We establish PSDness for compound matrices.
lemma compound_posSemidef {d k : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.PosSemidef) :
    (compound k A).PosSemidef := by
  -- A PSD implies A = LᴴL for some L
  obtain ⟨L, hL⟩ := Matrix.posSemidef_iff_eq_conjTranspose_mul_self.mp hA
  -- compound k A = compound k (Lᴴ * L) = compound k Lᴴ * compound k L
  have h1 : compound k A = compound k (Lᴴ) * compound k L := by
    rw [hL, compound_mul]
  -- compound k Lᴴ = (compound k L)ᴴ by compound_conjTranspose
  have h2 : compound k (Lᴴ) = (compound k L)ᴴ :=
    compound_conjTranspose L
  rw [h1, h2]
  exact Matrix.posSemidef_conjTranspose_mul_self (compound k L)

private lemma Matrix.subset_order_fun_injective {n m : ℕ} (s : Finset (Fin n)) (hs : s.card = m) :
    Function.Injective (subset_order_fun s hs) := by
  intro i j hij
  apply (s.orderIsoOfFin hs).injective
  exact Subtype.ext hij

private lemma Matrix.subset_order_fun_range {n m : ℕ} (s : Finset (Fin n)) (hs : s.card = m) :
    Set.range (subset_order_fun s hs) = ↑s := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    simp [subset_order_fun]
  · intro hx
    obtain ⟨i, hi⟩ := (s.orderIsoOfFin hs).surjective ⟨x, hx⟩
    exact ⟨i, congrArg Subtype.val hi⟩

private lemma Matrix.compound_one {d k : ℕ} :
    compound k (1 : Matrix (Fin d) (Fin d) ℂ) = 1 := by
  ext I J
  classical
  let f := subset_order_fun I.val (Finset.mem_filter.mp I.property).2
  let g := subset_order_fun J.val (Finset.mem_filter.mp J.property).2
  by_cases hIJ : I = J
  · subst hIJ
    have hf : Function.Injective f := Matrix.subset_order_fun_injective _ _
    have hsub : (1 : Matrix (Fin d) (Fin d) ℂ).submatrix f f = 1 := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [f]
      · simp [hij, hf.ne hij]
    simp [compound, f, hsub]
  · have hsets : ¬ ∀ x, x ∈ I.val ↔ x ∈ J.val := by
      intro hmem
      apply hIJ
      apply Subtype.ext
      exact Finset.ext fun x => hmem x
    push_neg at hsets
    rcases hsets with ⟨x, hx⟩
    have hdiff : (x ∈ I.val ∧ x ∉ J.val) ∨ (x ∈ J.val ∧ x ∉ I.val) := by
      tauto
    rcases hdiff with hx | hx
    · have hxI : x ∈ Set.range f := by
        rw [Matrix.subset_order_fun_range I.val (Finset.mem_filter.mp I.property).2]
        simpa using hx.1
      rcases hxI with ⟨i, rfl⟩
      have hrow : ∀ j, ((1 : Matrix (Fin d) (Fin d) ℂ).submatrix f g) i j = 0 := by
        intro j
        simp [Matrix.one_apply]
        intro hEq
        have hg_mem : g j ∈ J.val := by
          simpa [g, subset_order_fun] using
            (J.val.orderIsoOfFin (Finset.mem_filter.mp J.property).2 j).property
        exact hx.2 (by simpa [hEq] using hg_mem)
      simp [compound, f, g, Matrix.det_eq_zero_of_row_eq_zero i hrow, hIJ]
    · have hxJ : x ∈ Set.range g := by
        rw [Matrix.subset_order_fun_range J.val (Finset.mem_filter.mp J.property).2]
        simpa using hx.1
      rcases hxJ with ⟨j, rfl⟩
      have hcol : ∀ i, ((1 : Matrix (Fin d) (Fin d) ℂ).submatrix f g) i j = 0 := by
        intro i
        simp [Matrix.one_apply]
        intro hEq
        have hf_mem : f i ∈ I.val := by
          simpa [f, subset_order_fun] using
            (I.val.orderIsoOfFin (Finset.mem_filter.mp I.property).2 i).property
        exact hx.2 (by simpa [hEq] using hf_mem)
      simp [compound, f, g, Matrix.det_eq_zero_of_column_eq_zero j hcol, hIJ]

private lemma Matrix.compound_isUnit {d k : ℕ} [NeZero d] [Nonempty (subsets d k)]
    (B : Matrix (Fin d) (Fin d) ℂ) [Invertible B] :
    IsUnit (compound k B) := by
  refine ⟨⟨compound k B, compound k (⅟ B), ?_, ?_⟩, rfl⟩
  · rw [← compound_mul, mul_invOf_self, Matrix.compound_one]
  · rw [← compound_mul, invOf_mul_self, Matrix.compound_one]

private lemma maxEigenvalueGen_pos_of_posSemidef_isUnit
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (A : Matrix n n ℂ) (hA : A.PosSemidef) (h_unit : IsUnit A) :
    0 < maxEigenvalueGen A hA.1 := by
  have h_eig_ne_zero : ∀ i : n, hA.1.eigenvalues i ≠ 0 := by
    intro i hi
    have hdet_ne : A.det ≠ 0 := by
      exact (h_unit.map Matrix.detMonoidHom).ne_zero
    apply hdet_ne
    rw [hA.1.det_eq_prod_eigenvalues]
    exact (Finset.prod_eq_zero_iff.2 ⟨i, Finset.mem_univ i, by simpa [hi]⟩)
  let i : n := Classical.arbitrary _
  have hpos_i : 0 < hA.1.eigenvalues i := by
    exact lt_of_le_of_ne (hA.eigenvalues_nonneg i) (Ne.symm (h_eig_ne_zero i))
  exact lt_of_lt_of_le hpos_i (Finset.le_sup' _ (Finset.mem_univ i))

-- Hermitianness of A*B*A when A, B are Hermitian
lemma isHermitian_mul_mul_self (A B : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A * B * A).IsHermitian := by
  rw [Matrix.IsHermitian]
  simp [conjTranspose_mul, hA.eq, hB.eq, mul_assoc]

-- Hermitianness of A*A when A is Hermitian
lemma isHermitian_mul_self (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) :
    (A * A).IsHermitian := by
  rw [Matrix.IsHermitian]
  simp [conjTranspose_mul, hA.eq]

-- PSD of A*B*A when A, B are PSD
lemma posSemidef_mul_mul_self (A B : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (A * B * A).PosSemidef := by
  have h : A * B * A = A * B * Aᴴ := by rw [hA.1.eq]
  rw [h]
  exact Matrix.PosSemidef.mul_mul_conjTranspose_same hB A

/-- **Weyl's Multiplicative Majorization Theorem**.
For PSD matrices A, B of dimension d, and k ≤ d:
  ∏_{i=1}^k λ↓_i(ABA) ≤ ∏_{i=1}^k λ↓_i(A²) × ∏_{i=1}^k λ↓_i(B)

This follows from compound matrix multiplicativity and eigenvalue monotonicity. -/
theorem weyl_multiplicative (A B : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) (k : ℕ) (hk : k ≤ d) :
    let _i : Nonempty (subsets d k) := subsets_nonempty hk
    maxEigenvalueGen (compound k (A * B * A)) (compound_isHermitian _ (isHermitian_mul_mul_self A B hA.1 hB.1)) ≤
    maxEigenvalueGen (compound k (A * A)) (compound_isHermitian _ (isHermitian_mul_self A hA.1)) *
    maxEigenvalueGen (compound k B) (compound_isHermitian B hB.1) := by
  intro _i
  haveI := subsets_nonempty hk
  have hCA_H := compound_isHermitian (k := k) A hA.1
  have hCB_H := compound_isHermitian (k := k) B hB.1
  have hCB_P := compound_posSemidef (k := k) B hB
  let CB_hm : HermitianMat _ ℂ := ⟨compound k B, hCB_H⟩
  let CA_hm : HermitianMat _ ℂ := ⟨compound k A, hCA_H⟩
  have hCB_pos : 0 ≤ CB_hm := HermitianMat.zero_le_iff.mpr hCB_P
  let maxB := maxEigenvalueGen (compound k B) hCB_H
  have h_B_bound : CB_hm ≤ maxB • 1 := maxEig_bound CB_hm hCB_pos
  have h_conj : CB_hm.conj CA_hm.mat ≤ (maxB • (1 : HermitianMat _ ℂ)).conj CA_hm.mat :=
    HermitianMat.conj_mono h_B_bound
  -- Use linearity: (c • X).conj M = c • (X.conj M)
  have h_smul_conj : (maxB • (1 : HermitianMat _ ℂ)).conj CA_hm.mat =
      maxB • ((1 : HermitianMat _ ℂ).conj CA_hm.mat) :=
    map_smul (HermitianMat.conjLinear (R := ℝ) CA_hm.mat) maxB 1
  rw [h_smul_conj] at h_conj
  have h_one_conj_pos : 0 ≤ (1 : HermitianMat _ ℂ).conj CA_hm.mat :=
    HermitianMat.conj_nonneg _ (zero_le_one)
  have hMaxB_nn : (0 : ℝ) ≤ maxB :=
    Finset.le_sup'_of_le _ (Finset.mem_univ (Classical.arbitrary _)) (hCB_P.eigenvalues_nonneg _)
  have h_bound := maxEig_le_smul_maxEig
    (CB_hm.conj CA_hm.mat) ((1 : HermitianMat _ ℂ).conj CA_hm.mat) h_one_conj_pos maxB hMaxB_nn h_conj
  -- Connect to goal via matrix equalities
  have h_lhs : compound k (A * B * A) = (CB_hm.conj CA_hm.mat).mat := by
    show compound k (A * B * A) = compound k A * compound k B * (compound k A)ᴴ
    rw [hCA_H.eq, ← compound_mul, ← compound_mul]
  have h_rhs : compound k (A * A) = ((1 : HermitianMat _ ℂ).conj CA_hm.mat).mat := by
    show compound k (A * A) = compound k A * (1 : Matrix _ _ ℂ) * (compound k A)ᴴ
    rw [hCA_H.eq, mul_one, ← compound_mul]
  rw [mul_comm]
  calc maxEigenvalueGen (compound k (A * B * A)) _
      = maxEigenvalueGen (CB_hm.conj CA_hm.mat).mat _ := maxEigenvalueGen_congr h_lhs _ _
    _ ≤ maxB * maxEigenvalueGen ((1 : HermitianMat _ ℂ).conj CA_hm.mat).mat _ := h_bound
    _ = maxB * maxEigenvalueGen (compound k (A * A)) _ := by
        congr 1; exact (maxEigenvalueGen_congr h_rhs _ _).symm

set_option maxHeartbeats 3000000 in
/-- Log-majorization: the log version of Weyl's theorem. -/
theorem weyl_log_majorization (A B : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hA_pos : ∀ i, 0 < hA.1.eigenvalues i) (hB_pos : ∀ i, 0 < hB.1.eigenvalues i)
    (k : ℕ) (hk : k ≤ d) :
    let _i : Nonempty (subsets d k) := subsets_nonempty hk
    Real.log (maxEigenvalueGen (compound k (A * B * A)) (compound_isHermitian _ (isHermitian_mul_mul_self A B hA.1 hB.1))) ≤
    Real.log (maxEigenvalueGen (compound k (A * A)) (compound_isHermitian _ (isHermitian_mul_self A hA.1))) +
    Real.log (maxEigenvalueGen (compound k B) (compound_isHermitian B hB.1)) := by
  intro _i
  haveI := subsets_nonempty hk
  have h_mult := weyl_multiplicative A B hA hB k hk
  let hA_def : A.PosDef := (Matrix.IsHermitian.posDef_iff_eigenvalues_pos hA.1).2 hA_pos
  let hB_def : B.PosDef := (Matrix.IsHermitian.posDef_iff_eigenvalues_pos hB.1).2 hB_pos
  -- Positivity of compound matrix max eigenvalues (from strict positivity of eigenvalues)
  have h_pos_aba : 0 < maxEigenvalueGen (compound k (A * B * A))
      (compound_isHermitian _ (isHermitian_mul_mul_self A B hA.1 hB.1)) := by
    have hABA_psd : (A * B * A).PosSemidef := posSemidef_mul_mul_self A B hA hB
    letI : Invertible (A * B * A) :=
      by simpa [mul_assoc] using
        (hA_def.isUnit.mul (hB_def.isUnit.mul hA_def.isUnit)).invertible
    exact maxEigenvalueGen_pos_of_posSemidef_isUnit _ (compound_posSemidef (k := k) _ hABA_psd)
      (Matrix.compound_isUnit (k := k) _)
  have h_pos_aa : 0 < maxEigenvalueGen (compound k (A * A))
      (compound_isHermitian _ (isHermitian_mul_self A hA.1)) := by
    have hAA_posDef : (A * A).PosDef := by
      simpa [hA.1.eq] using
        (Matrix.PosDef.mul_conjTranspose_self A
          ((Matrix.vecMul_injective_iff_isUnit (A := A)).2 hA_def.isUnit))
    have hAA_psd : (A * A).PosSemidef := hAA_posDef.posSemidef
    letI : Invertible (A * A) := (hA_def.isUnit.mul hA_def.isUnit).invertible
    exact maxEigenvalueGen_pos_of_posSemidef_isUnit _ (compound_posSemidef (k := k) _ hAA_psd)
      (Matrix.compound_isUnit (k := k) _)
  have h_pos_b : 0 < maxEigenvalueGen (compound k B)
      (compound_isHermitian B hB.1) := by
    letI : Invertible B := hB_def.isUnit.invertible
    exact maxEigenvalueGen_pos_of_posSemidef_isUnit _ (compound_posSemidef (k := k) _ hB)
      (Matrix.compound_isUnit (k := k) _)
  -- log(maxEig(ABA)) ≤ log(maxEig(AA) * maxEig(B)) = log(maxEig(AA)) + log(maxEig(B))
  calc Real.log (maxEigenvalueGen (compound k (A * B * A)) _)
      ≤ Real.log (maxEigenvalueGen (compound k (A * A)) _ *
          maxEigenvalueGen (compound k B) _) :=
        Real.log_le_log h_pos_aba h_mult
    _ = Real.log (maxEigenvalueGen (compound k (A * A)) _) +
        Real.log (maxEigenvalueGen (compound k B) _) :=
        Real.log_mul (ne_of_gt h_pos_aa) (ne_of_gt h_pos_b)

-- The convex trace consequences of log-majorization are deferred to a future file that packages
-- the required scalar majorization machinery. This module currently stops at Weyl-style
-- multiplicative and logarithmic majorization statements.

end FinDefs

end Majorization
