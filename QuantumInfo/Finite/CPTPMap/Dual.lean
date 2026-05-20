/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.Finite.CPTPMap.Bundled
import QuantumInfo.ForMathlib.Matrix
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

/-! # Duals of matrix map

Definitions and theorems about the dual of a matrix map. -/

noncomputable section
open ComplexOrder
open scoped InnerProductSpace RealInnerProductSpace

variable {dIn dOut : Type*} [Fintype dIn] [Fintype dOut]
variable {R : Type*} [CommRing R]
variable {𝕜 : Type*} [RCLike 𝕜]

namespace MatrixMap

variable [DecidableEq dIn] [DecidableEq dOut] {M : MatrixMap dIn dOut 𝕜}

namespace Unital

omit [Fintype dIn] [Fintype dOut] in
/-- Construct `MatrixMap.Unital` from the defining identity-preservation equality. -/
theorem of_map_one {M : MatrixMap dIn dOut R} (h : M 1 = 1) : M.Unital :=
  h

end Unital

--This should be definable with LinearMap.adjoint, but that requires InnerProductSpace stuff
--that is currently causing issues and pains (tried `open scoped Frobenius`).

/-- The dual of a map between matrices, defined by `Tr[A M(B)] = Tr[(dual M)(A) B]`. Sometimes
 called the adjoint of the map instead. -/
@[irreducible]
def dual (M : MatrixMap dIn dOut R) : MatrixMap dOut dIn R :=
  let iso1 := (Module.Basis.toDualEquiv <| Matrix.stdBasis R dIn dIn).symm
  let iso2 := (Module.Basis.toDualEquiv <| Matrix.stdBasis R dOut dOut)
  let raw : MatrixMap dOut dIn R := iso1.toLinearMap ∘ₗ LinearMap.dualMap M ∘ₗ iso2.toLinearMap
  (Matrix.transposeLinearEquiv dIn dIn R R).toLinearMap ∘ₗ raw ∘ₗ
    (Matrix.transposeLinearEquiv dOut dOut R R).toLinearMap

lemma dual_single_apply (M : MatrixMap dIn dOut R) (i₁ : dIn) (j₁ : dOut) (i₂ : dIn) (j₂ : dOut) :
    (M.dual (Matrix.single j₁ j₂ 1)) i₁ i₂ = (M (Matrix.single i₂ i₁ 1)) j₂ j₁ := by
  unfold dual
  dsimp
  change (Matrix.stdBasis R dIn dIn).coord (i₂, i₁)
      ((Matrix.stdBasis R dIn dIn).toDualEquiv.symm
        ((LinearMap.dualMap M) ((Matrix.stdBasis R dOut dOut).toDual (Matrix.single j₁ j₂ 1).transpose))) = _
  rw [(Matrix.stdBasis R dIn dIn).coord_toDualEquiv_symm_apply (i := (i₂, i₁))]
  rw [Module.Basis.coord_apply, Module.Basis.dualBasis_repr]
  rw [LinearMap.dualMap_apply', LinearMap.comp_apply]
  rw [show (Matrix.single j₁ j₂ (1 : R)).transpose = (Matrix.stdBasis R dOut dOut) (j₂, j₁) by
    simp [Matrix.stdBasis_eq_single]]
  rw [(Matrix.stdBasis R dOut dOut).toDual_apply_right (i := (j₂, j₁))]
  have hrepr : ((Matrix.stdBasis R dOut dOut).repr (M ((Matrix.stdBasis R dIn dIn) (i₂, i₁)))) (j₂, j₁) =
      M ((Matrix.stdBasis R dIn dIn) (i₂, i₁)) j₂ j₁ := by
    simp [Matrix.stdBasis]
  rw [hrepr]
  simp [Matrix.stdBasis_eq_single]

lemma dual_apply_eq_trace_mul (M : MatrixMap dIn dOut R) (B : Matrix dOut dOut R) (i j : dIn) :
    M.dual B j i = (M (Matrix.single i j 1) * B).trace := by
  let f : Matrix dOut dOut R →ₗ[R] R :=
    { toFun := fun X => M.dual X j i
      map_add' := by simp
      map_smul' := by simp }
  let g : Matrix dOut dOut R →ₗ[R] R :=
    { toFun := fun X => (M (Matrix.single i j 1) * X).trace
      map_add' := by intro X Y; simp [Matrix.mul_add, Matrix.trace_add]
      map_smul' := by intro c X; simp [Matrix.trace_smul] }
  have hfg : f = g := by
    apply (Matrix.stdBasis R dOut dOut).ext
    intro ij
    rcases ij with ⟨j₁, j₂⟩
    simp [f, g, dual_single_apply, Matrix.trace_mul_single, Matrix.stdBasis_eq_single]
  have h := congrArg (fun h : Matrix dOut dOut R →ₗ[R] R => h B) hfg
  simpa [f, g] using h

/-- The defining property of a dual map: inner products are preserved on the opposite argument. -/
theorem Dual.trace_eq (M : MatrixMap dIn dOut R) (A : Matrix dIn dIn R) (B : Matrix dOut dOut R) :
    (M A * B).trace = (A * M.dual B).trace := by
  let f : Matrix dIn dIn R →ₗ[R] R :=
    { toFun := fun X => (M X * B).trace
      map_add' := by intro X Y; simp [map_add, Matrix.add_mul, Matrix.trace_add]
      map_smul' := by intro c X; simp [map_smul, Matrix.trace_smul] }
  let g : Matrix dIn dIn R →ₗ[R] R :=
    { toFun := fun X => (X * M.dual B).trace
      map_add' := by intro X Y; simp [Matrix.add_mul, Matrix.trace_add]
      map_smul' := by intro c X; simp [Matrix.trace_smul] }
  have hfg : f = g := by
    apply (Matrix.stdBasis R dIn dIn).ext
    intro ij
    rcases ij with ⟨i, j⟩
    simp [f, g, Matrix.stdBasis_eq_single, Matrix.trace_single_mul, dual_apply_eq_trace_mul]
  have h := congrArg (fun h : Matrix dIn dIn R →ₗ[R] R => h A) hfg
  simpa [f, g] using h

--all properties below should provable just from `inner_eq`, since the definition of `dual` itself
-- is pretty hairy (and maybe could be improved...)

/-- The dual of a `IsHermitianPreserving` map also `IsHermitianPreserving`. -/
theorem IsHermitianPreserving.dual {M : MatrixMap dIn dOut ℂ}
    (h : M.IsHermitianPreserving) : M.dual.IsHermitianPreserving := by
  intro x hx
  rw [Matrix.IsHermitian]
  ext i j
  rw [Matrix.conjTranspose_apply, dual_apply_eq_trace_mul, dual_apply_eq_trace_mul]
  let a : ℂ := (M (Matrix.single i j 1) * x).trace
  let b : ℂ := (M (Matrix.single j i 1) * x).trace
  change star a = b
  let H1 : Matrix dIn dIn ℂ := Matrix.single i j 1 + Matrix.single j i 1
  let H2 : Matrix dIn dIn ℂ := Complex.I • (Matrix.single i j 1 - Matrix.single j i 1)
  have hH1 : H1.IsHermitian := by
    dsimp [H1]
    rw [Matrix.IsHermitian]
    simp [add_comm]
  have hH2 : H2.IsHermitian := by
    dsimp [H2]
    have hH2' : (Matrix.single i j Complex.I + Matrix.single j i (-Complex.I)).IsHermitian := by
      rw [Matrix.IsHermitian]
      simp [add_comm]
    convert hH2' using 1
    ext a' b'
    simp [sub_eq_add_neg, Matrix.single]
    split_ifs <;> simp
  have htrace1 : star ((M H1 * x).trace) = (M H1 * x).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, h hH1 |>.eq, hx.eq,
      Matrix.trace_mul_comm]
  have htrace2 : star ((M H2 * x).trace) = (M H2 * x).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, h hH2 |>.eq, hx.eq,
      Matrix.trace_mul_comm]
  have hsum : star (a + b) = a + b := by
    simpa [a, b, H1, map_add, Matrix.add_mul, Matrix.trace_add] using htrace1
  have haI : (M (Matrix.single i j Complex.I) * x).trace = Complex.I * a := by
    have hsingle : Matrix.single i j Complex.I = Complex.I • Matrix.single i j 1 := by
      simp
    rw [hsingle, map_smul, Matrix.smul_mul, Matrix.trace_smul]
    simp [a, smul_eq_mul]
  have hbI : (M (Matrix.single j i Complex.I) * x).trace = Complex.I * b := by
    have hsingle : Matrix.single j i Complex.I = Complex.I • Matrix.single j i 1 := by
      simp
    rw [hsingle, map_smul, Matrix.smul_mul, Matrix.trace_smul]
    simp [b, smul_eq_mul]
  have hdiffI : star (Complex.I * (a - b)) = Complex.I * (a - b) := by
    have htmp : star (Complex.I * a - Complex.I * b) = Complex.I * a - Complex.I * b := by
      simpa [H2, map_smul, map_sub, Matrix.smul_mul, Matrix.sub_mul, Matrix.trace_smul,
        Matrix.trace_sub, haI, hbI, sub_eq_add_neg, mul_add, add_mul, mul_assoc] using htrace2
    simpa [sub_eq_add_neg, mul_add, add_mul, mul_assoc] using htmp
  have hdiff : star a - star b = b - a := by
    have htmp := congrArg (fun z => z * Complex.I) hdiffI
    simp [star_mul, sub_eq_add_neg, mul_add, add_mul, mul_assoc] at htmp
    ring_nf at htmp
    simpa [sub_eq_add_neg, add_comm] using htmp
  have hsum' : star a + star b = a + b := by
    simpa [sub_eq_add_neg, star_add] using hsum
  have hdouble : (2 : ℂ) * star a = (2 : ℂ) * b := by
    calc
      (2 : ℂ) * star a = (star a + star b) + (star a - star b) := by ring
      _ = (a + b) + (b - a) := by rw [hsum', hdiff]
      _ = (2 : ℂ) * b := by ring
  exact mul_left_cancel₀ (two_ne_zero : (2 : ℂ) ≠ 0) hdouble

/-- The trace pairing of nonnegative Hermitian matrices is nonnegative. -/
theorem _root_.HermitianMat.trace_mul_nonneg {n : Type*} [Fintype n]
    {A B : HermitianMat n 𝕜} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    0 ≤ (A.mat * B.mat).trace := by
  have hinner : 0 ≤ ⟪A, B⟫ := HermitianMat.inner_ge_zero hA hB
  have hinner' : (0 : 𝕜) ≤ (⟪A, B⟫ : 𝕜) := by exact_mod_cast hinner
  simpa [HermitianMat.inner_eq_trace_rc] using hinner'

/-- The trace pairing of positive semidefinite matrices is nonnegative. -/
theorem _root_.Matrix.PosSemidef.trace_mul_nonneg {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n 𝕜} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace := by
  let AH : HermitianMat n 𝕜 := ⟨A, hA.1⟩
  let BH : HermitianMat n 𝕜 := ⟨B, hB.1⟩
  have hAH : 0 ≤ AH := HermitianMat.zero_le_iff.mpr hA
  have hBH : 0 ≤ BH := HermitianMat.zero_le_iff.mpr hB
  simpa [AH, BH] using HermitianMat.trace_mul_nonneg hAH hBH

/-- The dual of a `IsPositive` map also `IsPositive`. -/
theorem IsPositive.dual {M : MatrixMap dIn dOut ℂ} (h : M.IsPositive) : M.dual.IsPositive := by
  intro x hx
  have hx_psd : x.PosSemidef := hx
  rw [Matrix.posSemidef_iff_dotProduct_mulVec] at hx ⊢
  use IsHermitianPreserving.dual h.IsHermitianPreserving hx.1
  intro v
  have h_dual_pos : 0 ≤ (M (Matrix.vecMulVec v (star v)) * x).trace := by
    have hvv : (Matrix.vecMulVec v (star v)).PosSemidef :=
      Matrix.posSemidef_vecMulVec_self_star v
    let Mvv : HermitianMat dOut ℂ := ⟨M (Matrix.vecMulVec v (star v)), (h hvv).1⟩
    let xH : HermitianMat dOut ℂ := ⟨x, hx_psd.1⟩
    have hMvv : 0 ≤ Mvv := HermitianMat.zero_le_iff.mpr (h hvv)
    have hxH : 0 ≤ xH := HermitianMat.zero_le_iff.mpr hx_psd
    simpa [Mvv, xH] using HermitianMat.trace_mul_nonneg hMvv hxH
  convert h_dual_pos using 1;
  rw [ MatrixMap.Dual.trace_eq ];
  simp [ Matrix.vecMulVec, Matrix.mul_apply, Matrix.trace ];
  simp [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm ];
  exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring )

/-- The dual of a trace-preserving map sends the identity to the identity. -/
theorem dual_map_one_of_tracePreserving (h : M.IsTracePreserving) : M.dual 1 = 1 := by
  -- By definition of dual, we know that for any matrix A, Tr(M(A) * I) = Tr(A * M*(I)).
  have h_dual_trace : ∀ A : Matrix dIn dIn 𝕜, (M A * 1).trace = (A * M.dual 1).trace := by
    exact fun A => Dual.trace_eq M A 1;
  ext i j
  specialize h_dual_trace ( Matrix.of ( fun k l => if k = j then if l = i then 1 else 0 else 0 ) )
  simp_all [ Matrix.trace, Matrix.mul_apply ] ;
  specialize h ( Matrix.of ( fun k l => if k = j then if l = i then 1 else 0 else 0 ) )
  simp_all [ Matrix.trace ]
  simp [ Matrix.one_apply, eq_comm ]

/-- The dual of TracePreserving map is *not* trace-preserving, it's *unital*, that is, M*(I) = I. -/
theorem dual_Unital (h : M.IsTracePreserving) : M.dual.Unital :=
  Unital.of_map_one (dual_map_one_of_tracePreserving h)

alias IsTracePreserving.dual := dual_Unital

/--
If two matrix maps satisfy the trace duality property, they are equal.
-/
lemma dual_unique
    (M : MatrixMap dIn dOut 𝕜) (M' : MatrixMap dOut dIn 𝕜)
    (h : ∀ A B, (M A * B).trace = (A * M' B).trace) : M.dual = M' := by
  -- By definition of dual, we know that for any A and B, the trace of (M A) * B equals the trace of A * (M.dual B).
  have h_dual : ∀ A : Matrix dIn dIn 𝕜, ∀ B : Matrix dOut dOut 𝕜, (M A * B).trace = (A * M.dual B).trace := by
    exact fun A B => Dual.trace_eq M A B;
  -- Since these two linear maps agree on all bases, they must be equal.
  have h_eq : ∀ A : Matrix dIn dIn 𝕜, ∀ B : Matrix dOut dOut 𝕜, (A * M.dual B).trace = (A * M' B).trace := by
    exact fun A B => h_dual A B ▸ h A B;
  refine' LinearMap.ext fun B => _;
  exact Matrix.ext_iff_trace_mul_left.mpr fun x => h_eq x B

/--
The Choi matrix of the dual map is the transpose of the reindexed Choi matrix of the original map.
-/
lemma dual_choi_matrix (M : MatrixMap dIn dOut 𝕜) :
    M.dual.choi_matrix = (M.choi_matrix.transpose).reindex (Equiv.prodComm dOut dIn) (Equiv.prodComm dOut dIn) := by
  -- By definition of dual, we know that $(M.dual (single j₁ j₂ 1)) i₁ i₂ = (M (single i₂ i₁ 1)) j₂ j₁$.
  have h_dual_def : ∀ (i₁ : dIn) (j₁ : dOut) (i₂ : dIn) (j₂ : dOut), (M.dual (Matrix.single j₁ j₂ 1)) i₁ i₂ = (M (Matrix.single i₂ i₁ 1)) j₂ j₁ := by
    intro i₁ j₁ i₂ j₂
    have h_dual_def : (M.dual (Matrix.single j₁ j₂ 1)) i₁ i₂ = Matrix.trace (Matrix.single i₂ i₁ 1 * M.dual (Matrix.single j₁ j₂ 1)) := by
      simp [ Matrix.trace, Matrix.mul_apply ];
      simp [ Matrix.single];
      rw [ Finset.sum_eq_single i₂ ]
      · aesop
      · intro b a a_1
        simp [a_1.symm]
      · aesop
    rw [ h_dual_def, ← Dual.trace_eq ];
    rw [ Matrix.trace ];
    rw [ Finset.sum_eq_single j₂ ] <;> aesop;
  aesop

/--
If the Choi matrix of a map is positive semidefinite, then the Choi matrix of its dual is also positive semidefinite.
-/
lemma dual_choi_matrix_posSemidef_of_posSemidef (M : MatrixMap dIn dOut 𝕜) (h : M.choi_matrix.PosSemidef) :
    M.dual.choi_matrix.PosSemidef := by
  rw [ dual_choi_matrix ];
  simp +zetaDelta at *;
  apply_rules [ Matrix.PosSemidef.submatrix ];
  convert h.transpose using 1

/--
The dual of the identity map is the identity map.
-/
lemma dual_id : (MatrixMap.id dIn 𝕜).dual = MatrixMap.id dIn 𝕜 := by
  exact dual_unique (id dIn 𝕜) (id dIn 𝕜) fun A_1 => congrFun rfl

set_option maxHeartbeats 600000 in
/--
The dual of a Kronecker product of maps is the Kronecker product of their duals.
-/
lemma dual_kron {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    [DecidableEq A] [DecidableEq B] [DecidableEq C] [DecidableEq D]
    (M : MatrixMap A B 𝕜) (N : MatrixMap C D 𝕜) :
    (M ⊗ₖₘ N).dual = M.dual ⊗ₖₘ N.dual := by
  have h_trace : ∀ (X : Matrix (A × C) (A × C) 𝕜) (Y : Matrix (B × D) (B × D) 𝕜), ( (M ⊗ₖₘ N) X * Y ).trace = ( X * (M.dual ⊗ₖₘ N.dual) Y ).trace := by
    -- By definition of dual, we know that $(M x1 * y1).trace = (x1 * M.dual y1).trace$ and $(N x2 * y2).trace = (x2 * N.dual y2).trace$.
    have h_dual : ∀ (x1 : Matrix A A 𝕜) (y1 : Matrix B B 𝕜), (M x1 * y1).trace = (x1 * M.dual y1).trace := by
      intro x1 y1
      convert MatrixMap.Dual.trace_eq M x1 y1 using 1
    have h_dual_N : ∀ (x2 : Matrix C C 𝕜) (y2 : Matrix D D 𝕜), (N x2 * y2).trace = (x2 * N.dual y2).trace := by
      exact fun x2 y2 => MatrixMap.Dual.trace_eq N x2 y2;
    intro X Y;
    -- By definition of Kronecker product, we can write X and Y as sums of Kronecker products.
    obtain ⟨X_sum, hX_sum⟩ : ∃ X_sum : Finset (Matrix A A 𝕜 × Matrix C C 𝕜), X = ∑ p ∈ X_sum, (Matrix.kroneckerMap (fun a b => a * b) p.1 p.2) := by
      refine' ⟨ Finset.univ.image fun p : A × A × C × C => ( Matrix.of fun i j => if i = p.1 ∧ j = p.2.1 then X ( p.1, p.2.2.1 ) ( p.2.1, p.2.2.2 ) else 0, Matrix.of fun i j => if i = p.2.2.1 ∧ j = p.2.2.2 then 1 else 0 ), _ ⟩;
      ext ⟨a, c⟩ ⟨a', c'⟩;
      rw [ Matrix.sum_apply ];
      rw [ Finset.sum_eq_single ( ( Matrix.of fun i j => if i = a ∧ j = a' then X ( a, c ) ( a', c' ) else 0, Matrix.of fun i j => if i = c ∧ j = c' then 1 else 0 ) ) ] <;> simp;
      · intro a_1 b x x_1 x_2 x_3 a_2 a_3 a_4
        subst a_3 a_2
        contrapose! a_4; aesop;
      · exact fun h => False.elim ( h a a' c c' ( by ext i j; aesop ) ( by ext i j; aesop ) )
    obtain ⟨Y_sum, hY_sum⟩ : ∃ Y_sum : Finset (Matrix B B 𝕜 × Matrix D D 𝕜), Y = ∑ p ∈ Y_sum, (Matrix.kroneckerMap (fun a b => a * b) p.1 p.2) := by
      use Finset.image (fun p => (Matrix.of (fun i j => Y (i, p.1) (j, p.2)), Matrix.of (fun i j => if i = p.1 ∧ j = p.2 then 1 else 0))) (Finset.univ : Finset (D × D));
      ext ⟨i, j⟩ ⟨k, l⟩; simp [ Matrix.kroneckerMap ] ;
      rw [ Finset.sum_image ] <;> simp [ Matrix.sum_apply ];
      · rw [ Finset.sum_eq_single ( j, l ) ] <;> aesop;
      · intro p q h
        subst hX_sum
        simp_all only [Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq]
        obtain ⟨fst, snd⟩ := p
        obtain ⟨fst_1, snd_1⟩ := q
        obtain ⟨left, right⟩ := h
        simp_all only [Prod.mk.injEq]
        apply And.intro
        · have := congr_fun ( congr_fun right fst ) snd; aesop;
        · replace right := congr_fun ( congr_fun right fst ) snd; aesop;
    -- By linearity of the trace and the properties of the Kronecker product, we can expand both sides of the equation.
    have h_expand : ∀ (x1 y1 : Matrix A A 𝕜) (x2 y2 : Matrix C C 𝕜) (x3 y3 : Matrix B B 𝕜) (x4 y4 : Matrix D D 𝕜), ( (M ⊗ₖₘ N) (Matrix.kroneckerMap (fun a b => a * b) x1 x2) * Matrix.kroneckerMap (fun a b => a * b) x3 x4 ).trace = ( Matrix.kroneckerMap (fun a b => a * b) x1 x2 * (M.dual ⊗ₖₘ N.dual) (Matrix.kroneckerMap (fun a b => a * b) x3 x4) ).trace := by
      intro x1 y1 x2 y2 x3 y3 x4 y4
      simp [MatrixMap.kron_map_of_kron_state]
      convert congr_arg₂ ( · * · ) ( h_dual x1 x3 ) ( h_dual_N x2 x4 ) using 1 <;> simp [ Matrix.trace, Matrix.mul_apply, Matrix.kroneckerMap_apply ]
      · simp only [Finset.sum_sigma', Finset.sum_mul _ _ _, Finset.mul_sum];
        refine' Finset.sum_bij ( fun x _ => ⟨ ⟨ x.fst.1, x.snd.1 ⟩, ⟨ x.fst.2, x.snd.2 ⟩ ⟩ ) _ _ _ _ <;> simp [ mul_assoc, mul_comm, mul_left_comm ];
        · bound;
        · exact fun b => ⟨ _, _, _, _, rfl ⟩;
      · simp only [mul_assoc, Finset.mul_sum _ _ _, Finset.sum_mul];
        simp only [← Finset.sum_product', mul_left_comm];
        refine' Finset.sum_bij ( fun x _ => ( x.1.2, x.2.2, x.1.1, x.2.1 ) ) _ _ _ _ <;> simp;
    simp_all [ Matrix.trace_sum, Finset.sum_mul _ _ _ ];
    simp [Matrix.mul_sum, h_expand]
  apply dual_unique; assumption;

--The dual of a CompletelyPositive map is always CP, more generally it's k-positive
-- see Lemma 3.1 of https://www.math.uwaterloo.ca/~krdavids/Preprints/CDPRpositivereal.pdf
theorem IsCompletelyPositive.dual {M : MatrixMap dIn dOut ℂ}
    (h : M.IsCompletelyPositive) : M.dual.IsCompletelyPositive := by
  intro n
  have h_dual_pos : (MatrixMap.dual (M ⊗ₖₘ MatrixMap.id (Fin n) ℂ)).IsPositive := by
    exact IsPositive.dual (h n);
  -- By definition of complete positivity, we know that $(M ⊗ₖₘ id) dually map = M.dual ⊗ₖₘ id.dual$.
  have h_dual_kron : (MatrixMap.dual (M ⊗ₖₘ MatrixMap.id (Fin n) ℂ)) =
      (MatrixMap.dual M) ⊗ₖₘ (MatrixMap.dual (MatrixMap.id (Fin n) ℂ)) := by
    convert dual_kron M (MatrixMap.id (Fin n) ℂ) using 1
  convert h_dual_pos using 1;
  rw [ h_dual_kron, dual_id ]

/--
The composition of the dual of the inverse of the dual basis isomorphism with the dual basis isomorphism is the evaluation map.
-/
lemma Module.Basis.dualMap_toDualEquiv_symm_comp_toDualEquiv {ι R M : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [AddCommGroup M] [Module R M] [Module.IsReflexive R M] (b : Module.Basis ι R M) :
    b.toDualEquiv.symm.toLinearMap.dualMap ∘ₗ b.toDualEquiv.toLinearMap = (Module.evalEquiv R M).toLinearMap := by
  ext x f;
  -- Since $b.toDual$ and $b.toDualEquiv.symm$ are inverses, we have $b.toDual (b.toDualEquiv.symm f) = f$.
  have h_inv : b.toDual (b.toDualEquiv.symm f) = f := by
    convert LinearEquiv.apply_symm_apply b.toDualEquiv f;
  convert congr_arg ( fun g => g x ) h_inv using 1;
  -- By definition of the dual basis, we know that $(b.toDual x) (b.toDualEquiv.symm f) = f x$.
  simp [Module.Basis.toDual];
  ac_rfl

/--
The composition of the inverse of the dual basis isomorphism with the dual of the dual basis isomorphism is the inverse of the evaluation map.
-/
lemma Module.Basis.toDualEquiv_symm_comp_dualMap_toDualEquiv {ι R M : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [AddCommGroup M] [Module R M] [Module.IsReflexive R M] (b : Module.Basis ι R M) :
    b.toDualEquiv.symm.toLinearMap ∘ₗ b.toDualEquiv.toLinearMap.dualMap = (Module.evalEquiv R M).symm.toLinearMap := by
  simp [ LinearMap.ext_iff ];
  intro x
  obtain ⟨y, hy⟩ : ∃ y, x = (Module.evalEquiv R M).toLinearMap y := by
    exact ⟨ _, Eq.symm <| LinearEquiv.apply_symm_apply ( Module.evalEquiv R M ) x ⟩;
  rw [ hy ];
  simp [ Module.evalEquiv, LinearEquiv.symm_apply_eq ];
  ext; simp [ Module.Dual.eval ] ;
  simp [ Module.Basis.toDual ];
  ac_rfl

@[simp]
theorem dual_dual : M.dual.dual = M := by
  apply dual_unique (M := M.dual) (M' := M)
  intro A B
  calc
    (M.dual A * B).trace = (B * M.dual A).trace := by rw [Matrix.trace_mul_comm]
    _ = (M B * A).trace := by rw [Dual.trace_eq M B A]
    _ = (A * M B).trace := by rw [Matrix.trace_mul_comm]

end MatrixMap

namespace CPTPMap

variable [DecidableEq dIn] [DecidableEq dOut]

def dual (M : CPTPMap dIn dOut) : CPUMap dOut dIn where
  toLinearMap := M.map.dual
  unital := M.TP.dual
  cp := .dual M.cp

theorem dual_pos (M : CPTPMap dIn dOut) {T : HermitianMat dOut ℂ} (hT : 0 ≤ T) :
    0 ≤ M.dual T := by
  exact M.dual.pos_Hermitian hT

/-- The dual of a CPTP map preserves POVMs. Stated here just for two-element POVMs, that is, an
operator `T` between 0 and 1. -/
theorem dual.PTP_POVM (M : CPTPMap dIn dOut) {T : HermitianMat dOut ℂ} (hT : 0 ≤ T ∧ T ≤ 1) :
    (0 ≤ M.dual T ∧ M.dual T ≤ 1) := by
  rcases hT with ⟨hT₁, hT₂⟩
  have hT_psd := HermitianMat.zero_le_iff.mp hT₁
  use M.dual.pos_Hermitian hT₁
  simpa using ContinuousOrderHomClass.map_monotone M.dual hT₂

/-- The defining property of a dual channel, as specialized to `MState.exp_val`. -/
theorem exp_val_Dual (ℰ : CPTPMap dIn dOut) (ρ : MState dIn) (T : HermitianMat dOut ℂ) :
    (ℰ ρ).exp_val T  = ρ.exp_val (ℰ.dual T) := by
  simp only [MState.exp_val, HermitianMat.inner_eq_re_trace, RCLike.re_to_complex]
  congr 1
  apply MatrixMap.Dual.trace_eq

end CPTPMap

section hermDual

--PULLOUT to Bundled.lean. Also use this to improve the definitions in POVM.lean.
def HPMap.ofHermitianMat (f : HermitianMat dIn ℂ →ₗ[ℝ] HermitianMat dOut ℂ) : HPMap dIn dOut where
  toFun x := f (realPart x) + Complex.I • f (imaginaryPart x)
  map_add' x y := by
    ext i j
    have hreal : (f (realPart x + realPart y)) i j =
        (f (realPart x)) i j + (f (realPart y)) i j := by
      change (f (realPart x + realPart y)).mat i j =
        (f (realPart x) + f (realPart y)).mat i j
      exact congrArg (fun A : HermitianMat dOut ℂ => A.mat i j)
        (LinearMap.map_add f (realPart x) (realPart y))
    have himag : (f (imaginaryPart x + imaginaryPart y)) i j =
        (f (imaginaryPart x)) i j + (f (imaginaryPart y)) i j := by
      change (f (imaginaryPart x + imaginaryPart y)).mat i j =
        (f (imaginaryPart x) + f (imaginaryPart y)).mat i j
      exact congrArg (fun A : HermitianMat dOut ℂ => A.mat i j)
        (LinearMap.map_add f (imaginaryPart x) (imaginaryPart y))
    simp [Matrix.add_apply, hreal, himag]
    ring
  map_smul' c m := by
    have h_expand : realPart (c • m) = c.re • realPart m - c.im • imaginaryPart m ∧
      imaginaryPart (c • m) = c.re • imaginaryPart m + c.im • realPart m := by
      exact ⟨realPart_smul c m, imaginaryPart_smul c m⟩
    rw [h_expand.1, h_expand.2]
    ext i j
    have hsub : (f (c.re • realPart m - c.im • imaginaryPart m)) i j =
        c.re * (f (realPart m)) i j - c.im * (f (imaginaryPart m)) i j := by
      have hhm : f (c.re • realPart m - c.im • imaginaryPart m) =
          c.re • f (realPart m) - c.im • f (imaginaryPart m) := by
        calc
          f (c.re • realPart m - c.im • imaginaryPart m) =
              f (c.re • realPart m) - f (c.im • imaginaryPart m) := by
            exact LinearMap.map_sub f (c.re • realPart m) (c.im • imaginaryPart m)
          _ = c.re • f (realPart m) - c.im • f (imaginaryPart m) := by
            congr 1
            · exact LinearMap.map_smul f c.re (realPart m)
            · exact LinearMap.map_smul f c.im (imaginaryPart m)
      change (f (c.re • realPart m - c.im • imaginaryPart m)).mat i j =
        (c.re • f (realPart m) - c.im • f (imaginaryPart m)).mat i j
      rw [congrArg (fun A : HermitianMat dOut ℂ => A.mat i j) hhm]
    have hadd : (f (c.re • imaginaryPart m + c.im • realPart m)) i j =
        c.re * (f (imaginaryPart m)) i j + c.im * (f (realPart m)) i j := by
      have hhm : f (c.re • imaginaryPart m + c.im • realPart m) =
          c.re • f (imaginaryPart m) + c.im • f (realPart m) := by
        calc
          f (c.re • imaginaryPart m + c.im • realPart m) =
              f (c.re • imaginaryPart m) + f (c.im • realPart m) := by
            exact LinearMap.map_add f (c.re • imaginaryPart m) (c.im • realPart m)
          _ = c.re • f (imaginaryPart m) + c.im • f (realPart m) := by
            congr 1
            · exact LinearMap.map_smul f c.re (imaginaryPart m)
            · exact LinearMap.map_smul f c.im (realPart m)
      change (f (c.re • imaginaryPart m + c.im • realPart m)).mat i j =
        (c.re • f (imaginaryPart m) + c.im • f (realPart m)).mat i j
      rw [congrArg (fun A : HermitianMat dOut ℂ => A.mat i j) hhm]
    change (f (c.re • realPart m - c.im • imaginaryPart m)) i j +
        Complex.I * (f (c.re • imaginaryPart m + c.im • realPart m)) i j =
      (c * ((f (realPart m)) i j + Complex.I * (f (imaginaryPart m)) i j))
    rw [hsub, hadd]
    simp only [Complex.ext_iff, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
      add_zero, zero_add, sub_zero]
    constructor <;> ring_nf
  HP _ h := by
    apply Matrix.IsHermitian.add
    · apply HermitianMat.H
    · rw [IsSelfAdjoint.imaginaryPart h]
      have hf0 : f 0 = 0 := map_zero f
      have hf0m : (↑(f 0) : Matrix dOut dOut ℂ) = 0 := congrArg HermitianMat.mat hf0
      change (Complex.I • (↑(f 0) : Matrix dOut dOut ℂ)).IsHermitian
      rw [hf0m]
      simp [Matrix.IsHermitian]

--PULLOUT
omit [Fintype dOut] in
@[simp]
theorem HPMap.linearMap_ofHermitianMat (f : HermitianMat dIn ℂ →ₗ[ℝ] HermitianMat dOut ℂ) :
    LinearMapClass.linearMap (HPMap.ofHermitianMat f) = f := by
  ext1 ⟨x, hx⟩
  ext1
  have hreal : realPart x = ⟨x, hx⟩ := by
    exact (show IsSelfAdjoint x from hx).selfAdjointPart_apply ℝ
  have himag : imaginaryPart x = 0 := by
    exact IsSelfAdjoint.imaginaryPart (show IsSelfAdjoint x from hx)
  change (↑(f (realPart x)) : Matrix dOut dOut ℂ) +
      Complex.I • (↑(f (imaginaryPart x)) : Matrix dOut dOut ℂ) =
    ↑(f ⟨x, hx⟩)
  rw [hreal, himag]
  have hf0 : (↑(f 0) : Matrix dOut dOut ℂ) = 0 :=
    congrArg HermitianMat.mat (map_zero f)
  change (↑(f ⟨x, hx⟩) : Matrix dOut dOut ℂ) +
      Complex.I • (↑(f 0) : Matrix dOut dOut ℂ) = ↑(f ⟨x, hx⟩)
  rw [hf0, smul_zero, add_zero]

--PULLOUT
omit [Fintype dOut] in
@[simp]
theorem HPMap.ofHermitianMat_linearMap (f : HPMap dIn dOut ℂ) :
    ofHermitianMat (LinearMapClass.linearMap f) = f := by
  ext x i j
  simp only [map, ofHermitianMat, instFunLike, LinearMap.coe_coe, HermitianMat.val_eq_coe,
    HermitianMat.mat_mk, LinearMap.coe_mk, AddHom.coe_mk,
    ← map_smul, ← map_add]
  simp only [map_add, map_smul, realPart, imaginaryPart, LinearMap.coe_comp, Function.comp_apply]
  simp only [selfAdjointPart,  LinearMap.coe_mk, AddHom.coe_mk,
    HermitianMat.mat_mk,LinearMap.map_smul_of_tower, skewAdjoint.negISMul]
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring_nf
  rw [Complex.I_sq]
  rw [neg_one_mul, sub_neg_eq_add]
  rw [← Matrix.add_apply]
  rw [← LinearMap.map_add]
  have hdecomp : (⅟2 : ℝ) • (x + star x) +
      (↑((skewAdjointPart ℝ) x) : Matrix dIn dIn ℂ) = x := by
    rw [skewAdjointPart_apply_coe]
    ext a b
    simp [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply]
    ring
  change f.toLinearMap ((⅟2 : ℝ) • (x + star x) +
      (↑((skewAdjointPart ℝ) x) : Matrix dIn dIn ℂ)) i j = f.toLinearMap x i j
  exact congrArg (fun M : Matrix dIn dIn ℂ => f.toLinearMap M i j) hdecomp


variable (f : HPMap dIn dOut) (A : HermitianMat dIn ℂ)

--Can define one for HPMap's that has 'easier' definitional properties, uses the inner product structure,
--doesn't go through Module.Basis the same way. Requires the equivalence between ℝ-linear maps of HermitianMats
--and ℂ-linear maps of matrices.
def HPMap.hermDual : HPMap dOut dIn :=
  HPMap.ofHermitianMat (LinearMapClass.linearMap f).adjoint

@[simp]
theorem HPMap.hermDual_hermDual : f.hermDual.hermDual = f := by
  simp [hermDual]

open RealInnerProductSpace

/-- The defining property of a dual map: inner products are preserved on the opposite argument. -/
theorem HPMap.inner_hermDual (B : HermitianMat dOut ℂ) :
    ⟪f A, B⟫ = ⟪A, f.hermDual B⟫ := by
  change ⟪(LinearMapClass.linearMap f) A, B⟫ =
    ⟪A, (LinearMapClass.linearMap (HPMap.ofHermitianMat
      (LinearMap.adjoint (LinearMapClass.linearMap f)))) B⟫
  rw [HPMap.linearMap_ofHermitianMat]
  exact (LinearMap.adjoint_inner_right (LinearMapClass.linearMap f) A B).symm

/-- The dual of a `IsPositive` map also `IsPositive`. -/
theorem MatrixMap.IsPositive.hermDual (h : MatrixMap.IsPositive f.map) : f.hermDual.map.IsPositive := by
  unfold IsPositive at h ⊢
  intro x hx
  set xH : HermitianMat dOut ℂ := ⟨x, hx.left⟩ with hxH
  have hx' : x = xH := rfl; clear_value xH; subst x; clear hxH
  change Matrix.PosSemidef (f.hermDual xH).mat
  rw [← HermitianMat.zero_le_iff] at hx ⊢
  classical
  rw [HermitianMat.zero_le_iff_inner_pos]
  intro y hy
  rw [HermitianMat.zero_le_iff] at hy
  specialize h hy
  change Matrix.PosSemidef (f y).mat at h
  rw [← HermitianMat.zero_le_iff] at h
  rw [HPMap.inner_hermDual, HPMap.hermDual_hermDual]
  apply HermitianMat.inner_ge_zero hx h

omit [Fintype dIn] [Fintype dOut] in
/-- Construct unitality of an `HPMap` from the identity-preservation equality on Hermitian matrices. -/
theorem HPMap.unital_of_map_one [DecidableEq dIn] [DecidableEq dOut] {f : HPMap dIn dOut ℂ}
    (h : f 1 = 1) : f.map.Unital := by
  rw [HermitianMat.ext_iff] at h
  exact h

/-- A trace-preserving `HPMap` preserves `HermitianMat.trace` on Hermitian inputs. -/
theorem HPMap.trace_eq_of_isTracePreserving (h : MatrixMap.IsTracePreserving f.map)
    (A : HermitianMat dIn ℂ) : (f A).trace = A.trace := by
  rw [HermitianMat.trace_eq_re_trace, HermitianMat.trace_eq_re_trace]
  exact congr(Complex.re $(h A.mat))

/-- The Hermitian dual of a trace-preserving `HPMap` sends the identity to the identity. -/
theorem HPMap.hermDual_map_one_of_tracePreserving [DecidableEq dIn] [DecidableEq dOut]
    (h : MatrixMap.IsTracePreserving f.map) :
    f.hermDual 1 = 1 := by
  open RealInnerProductSpace in
  apply ext_inner_left ℝ
  intro v
  calc
    ⟪v, f.hermDual 1⟫ = ⟪f v, 1⟫ := (HPMap.inner_hermDual f v 1).symm
    _ = ⟪v, 1⟫ := by
      simpa [HermitianMat.inner_one] using HPMap.trace_eq_of_isTracePreserving f h v

/-- The dual of TracePreserving map is *not* trace-preserving, it's *unital*, that is, M*(I) = I. -/
theorem HPMap.hermDual_Unital [DecidableEq dIn] [DecidableEq dOut] (h : MatrixMap.IsTracePreserving f.map) :
    f.hermDual.map.Unital :=
  HPMap.unital_of_map_one (HPMap.hermDual_map_one_of_tracePreserving f h)

alias MatrixMap.IsTracePreserving.hermDual := HPMap.hermDual_Unital

namespace PTPMap

variable [DecidableEq dIn] [DecidableEq dOut]

def hermDual (M : PTPMap dIn dOut) : PUMap dOut dIn where
  toHPMap := M.toHPMap.hermDual
  pos := M.pos.hermDual
  unital := M.TP.hermDual

theorem hermDual_pos (M : PTPMap dIn dOut) {T : HermitianMat dOut ℂ} (hT : 0 ≤ T) :
    0 ≤ M.hermDual T := by
  exact M.hermDual.pos_Hermitian hT

/-- The dual of a PTP map preserves POVMs. Stated here just for two-element POVMs, that is, an
operator `T` between 0 and 1. -/
theorem hermDual.PTP_POVM (M : PTPMap dIn dOut) {T : HermitianMat dOut ℂ} (hT : 0 ≤ T ∧ T ≤ 1) :
    (0 ≤ M.hermDual T ∧ M.hermDual T ≤ 1) := by
  rcases hT with ⟨hT₁, hT₂⟩
  have hT_psd := HermitianMat.zero_le_iff.mp hT₁
  use M.hermDual.pos_Hermitian hT₁
  simpa using ContinuousOrderHomClass.map_monotone M.hermDual hT₂

/-- The defining property of a dual channel, as specialized to `MState.exp_val`. -/
theorem exp_val_hermDual (ℰ : PTPMap dIn dOut) (ρ : MState dIn) (T : HermitianMat dOut ℂ) :
    (ℰ ρ).exp_val T  = ρ.exp_val (ℰ.hermDual T) := by
  simp only [MState.exp_val]
  apply HPMap.inner_hermDual

end PTPMap

end hermDual
