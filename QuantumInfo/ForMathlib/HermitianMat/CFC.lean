/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.ForMathlib.HermitianMat.Inner
import QuantumInfo.ForMathlib.HermitianMat.NonSingular
import QuantumInfo.ForMathlib.Isometry

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice

/-! Matrix operations on HermitianMats with the CFC -/
namespace HermitianMat

noncomputable section CFC

variable {d d₂ 𝕜 : Type*} [Fintype d] [DecidableEq d] [Fintype d₂] [DecidableEq d₂] [RCLike 𝕜]
variable {X : Type*} [TopologicalSpace X]
variable (A : HermitianMat d 𝕜) (f : ℝ → ℝ) (g : ℝ → ℝ) (q r : ℝ)

/- Adding this to `CStarAlgebra` allows `cfc_tac` to use it. -/
omit [Fintype d] [DecidableEq d] in
@[aesop safe apply (rule_sets := [CStarAlgebra])]
theorem isSelfAdjoint : IsSelfAdjoint A.mat := by
  exact A.H

/- Adding this to `fun_prop` allows `cfc_cont_tac` to use it. -/
@[fun_prop]
theorem continuousOn_finite {α β : Type*} (f : α → β) (S : Set α)
    [TopologicalSpace α] [TopologicalSpace β] [T1Space α] [Finite S] : ContinuousOn f S := by
  rw [continuousOn_iff_continuous_restrict]
  exact continuous_of_discreteTopology

@[simp]
theorem conjTranspose_cfc : (cfc f A.mat).conjTranspose = cfc f A.mat := by
  exact cfc_predicate f A.mat

nonrec def cfc : HermitianMat d 𝕜 :=
  ⟨cfc f A.mat, cfc_predicate _ _⟩

@[simp]
theorem mat_cfc : (A.cfc f).mat = _root_.cfc f A.mat := by
  rfl

theorem cfc_eq_cfc_iff_eqOn (f g : ℝ → ℝ) :
    cfc A f = cfc A g ↔ Set.EqOn f g (spectrum ℝ A.mat) := by
  rw [HermitianMat.ext_iff, mat_cfc, mat_cfc]
  exact _root_.cfc_eq_cfc_iff_eqOn A.H

section commute
variable {A B : HermitianMat d 𝕜}

theorem _root_.Commute.cfc_left (hAB : Commute A.mat B.mat) :
    Commute (A.cfc f).mat B.mat := by
  exact hAB.cfc_real f

theorem _root_.Commute.cfc_right (hAB : Commute A.mat B.mat) :
    Commute A.mat (B.cfc f).mat :=
  (hAB.symm.cfc_left f).symm

theorem cfc_commute (f g : ℝ → ℝ) (hAB : Commute A.mat B.mat) :
    Commute (A.cfc f).mat (B.cfc g).mat := by
  exact (hAB.cfc_right g).cfc_left f

theorem cfc_self_commute (A : HermitianMat d 𝕜) (f g : ℝ → ℝ) :
    Commute (A.cfc f).mat (A.cfc g).mat := by
  apply cfc_commute
  rfl

end commute

/-- Reindexing a matrix commutes with applying the CFC. -/
@[simp]
theorem cfc_reindex (e : d ≃ d₂) : (A.reindex e).cfc f = (A.cfc f).reindex e := by
  rw [HermitianMat.ext_iff]
  simp only [mat_cfc, mat_reindex]
  exact Matrix.cfc_reindex f e

/--
Spectral decomposition of `A.cfc f` as a sum of scaled projections (matrix version).
-/
theorem cfc_toMat_eq_sum_smul_proj : (A.cfc f).mat =
    ∑ i, f (A.H.eigenvalues i) • (A.H.eigenvectorUnitary.val * (Matrix.single i i 1) * A.H.eigenvectorUnitary.val.conjTranspose) := by
  rw [A.mat_cfc, A.H.cfc_eq, Matrix.IsHermitian.cfc]
  have h : ( Matrix.diagonal ( RCLike.ofReal ∘ f ∘ Matrix.IsHermitian.eigenvalues A.H ) : Matrix d d 𝕜 ) = ∑ i, f ( A.H.eigenvalues i ) • Matrix.single i i 1 := by
    ext i j ; by_cases hij : i = j <;> simp [ hij ];
    · simp [ Matrix.sum_apply, Matrix.single ];
      simp [ Algebra.smul_def ];
    · rw [Finset.sum_apply, Finset.sum_apply]
      simp_all
  rw [h]
  simp [Matrix.mul_sum, Matrix.sum_mul, Matrix.single, Matrix.mul_assoc]
  congr! 1
  ext j k
  simp [Matrix.mul_apply,Finset.mul_sum, Finset.smul_sum, smul_ite, smul_zero]

--Ensure we get this instance:
/-- info: locallyCompact_of_proper -/
#guard_msgs in
#synth LocallyCompactSpace (HermitianMat d 𝕜)

theorem cfc_eigenvalues (A : HermitianMat d 𝕜) :
    ∃ (e : d ≃ d), (A.cfc f).H.eigenvalues = f ∘ A.H.eigenvalues ∘ e :=
  A.H.cfc_eigenvalues f

/-! Here we give HermitianMat versions of many cfc theorems, like `cfc_id`, `cfc_sub`, `cfc_comp`,
etc. We need these because (as above) `HermitianMat.cfc` is different from `_root_.cfc`. -/

@[simp]
nonrec theorem cfc_id : A.cfc id = A := by
  simpa [HermitianMat.ext_iff] using cfc_id ℝ A.mat

@[simp]
nonrec theorem cfc_id' : A.cfc (·) = A :=
  cfc_id A

nonrec theorem cfc_add : A.cfc (f + g) = A.cfc f + A.cfc g := by
  ext1; exact cfc_add ..

theorem cfc_add_apply : A.cfc (fun x ↦ f x + g x) = A.cfc f + A.cfc g :=
  cfc_add A f g

nonrec theorem cfc_sub : A.cfc (f - g) = A.cfc f - A.cfc g := by
  ext1; exact cfc_sub ..

theorem cfc_sub_apply : A.cfc (fun x ↦ f x - g x) = A.cfc f - A.cfc g :=
  cfc_sub A f g

nonrec theorem cfc_neg : A.cfc (-f) = -A.cfc f := by
  ext1; exact cfc_neg ..

theorem cfc_neg_apply : A.cfc (fun x ↦ -f x) = -A.cfc f :=
  cfc_neg A f

/-- We don't have a direct analog of `cfc_mul`, since we can't generally multiply
to HermitianMat's to get another one, so the theorem statement wouldn't be well-typed.
But, we can say that the matrices are always equal. See `cfc_conj` for the coe-free
analog to multiplication. -/
theorem mat_cfc_mul : (A.cfc (f * g)).mat = (A.cfc f).mat * (A.cfc g).mat := by
  simp only [mat_cfc]
  exact cfc_mul ..

nonrec theorem cfc_comp : A.cfc (g ∘ f) = (A.cfc f).cfc g := by
  ext1; exact cfc_comp ..

theorem cfc_comp_apply : A.cfc (fun x ↦ g (f x)) = (A.cfc f).cfc g :=
  cfc_comp A f g

nonrec theorem cfc_conj : (A.cfc f).conj (A.cfc g) = A.cfc (f * g^2) := by
  ext1
  simp only [conj_apply, mat_cfc, mat_mk, conjTranspose_cfc]
  rw [← cfc_mul, ← cfc_mul, Pi.mul_def, Pi.pow_def]
  grind only

theorem cfc_sq : A.cfc (· ^ 2) = A ^ 2 := by
  ext1
  simp_rw [mat_pow, sq]
  conv_lhs => exact mat_cfc_mul A id id
  rw [cfc_id]

@[simp]
nonrec theorem cfc_const : (A.cfc (fun _ ↦ r)) = r • 1 := by
  ext1
  simp only [mat_cfc, mat_smul, mat_one]
  rw [cfc_const r A.mat]
  exact Algebra.algebraMap_eq_smul_one r

@[simp]
nonrec theorem cfc_const_mul_id : A.cfc (fun x ↦ r * x) = r • A := by
  ext1
  rw [mat_cfc, mat_smul, cfc_const_mul_id r A.mat]

@[simp]
nonrec theorem cfc_const_mul : A.cfc (fun x ↦ r * f x) = r • A.cfc f := by
  rw [← cfc_const_mul_id, ← cfc_comp]
  rfl

@[simp]
nonrec theorem cfc_apply_zero : (0 : HermitianMat d 𝕜).cfc f = f 0 • 1 := by
  simp [HermitianMat.ext_iff, Algebra.algebraMap_eq_smul_one]

@[simp]
nonrec theorem cfc_apply_one : (1 : HermitianMat d 𝕜).cfc f = f 1 • 1 := by
  simp [HermitianMat.ext_iff, Algebra.algebraMap_eq_smul_one]

variable {f g} in
nonrec theorem cfc_congr (hfg : Set.EqOn f g (spectrum ℝ A.mat)) :
    A.cfc f = A.cfc g := by
  ext1
  exact cfc_congr hfg

variable {f g A} in
/-- Version of `cfc_congr` specialized to PSD matrices. -/
nonrec theorem cfc_congr_of_zero_le (hA : 0 ≤ A) (hfg : Set.EqOn f g (Set.Ici 0)) :
    A.cfc f = A.cfc g := by
  refine cfc_congr A (hfg.mono ?_)
  open MatrixOrder in
  exact spectrum_nonneg_of_nonneg (a := A.mat) hA

open ComplexOrder

variable {f g A} in
/-- Version of `cfc_congr` specialized to positive definite matrices. -/
nonrec theorem cfc_congr_of_posDef (hA : A.mat.PosDef) (hfg : Set.EqOn f g (Set.Ioi 0)) :
    A.cfc f = A.cfc g := by
  refine cfc_congr A (hfg.mono ?_)
  rw [A.H.spectrum_real_eq_range_eigenvalues]
  rintro _ ⟨i, rfl⟩
  exact hA.eigenvalues_pos i

@[simp]
theorem cfc_diagonal (g : d → ℝ) : (diagonal 𝕜 g).cfc f = diagonal 𝕜 (f ∘ g) := by
  ext1
  exact Matrix.cfc_diagonal g f

theorem cfc_conj_unitary (U : Matrix.unitaryGroup d 𝕜) :
    (A.conj U.val).cfc f = (A.cfc f).conj U := by
  ext1
  exact Matrix.cfc_conj_unitary f U

theorem zero_le_cfc : 0 ≤ A.cfc f ↔ ∀ i, 0 ≤ f (A.H.eigenvalues i) := by
  open MatrixOrder in
  rw [cfc, ← Subtype.coe_le_coe, ZeroMemClass.coe_zero]
  rw [cfc_nonneg_iff f A.mat, A.H.spectrum_real_eq_range_eigenvalues]
  grind

variable {A f} in
theorem zero_le_cfc_of_zero_le (hA : 0 ≤ A) (hf : ∀ i ≥ 0, 0 ≤ f i) :
    0 ≤ A.cfc f := by
  rw [zero_le_cfc]
  rw [zero_le_iff, A.H.posSemidef_iff_eigenvalues_nonneg] at hA
  exact fun i ↦ hf _ (hA i)

theorem cfc_PosDef : (A.cfc f).mat.PosDef ↔ ∀ i, 0 < f (A.H.eigenvalues i) := by
  rw [(A.cfc f).H.posDef_iff_eigenvalues_pos]
  obtain ⟨e, he⟩ := A.cfc_eigenvalues f
  rw [he]
  refine ⟨fun h i ↦ ?_, fun h i ↦ h (e i)⟩
  simpa using h (e.symm i)

theorem trace_mul_cfc (A : HermitianMat d 𝕜) (f : ℝ → ℝ) :
    (A.mat * (A.cfc f).mat).trace = ∑ i, A.H.eigenvalues i * f (A.H.eigenvalues i) := by
  conv_lhs => rw [A.eq_conj_diagonal]
  rw [cfc_conj_unitary]
  simp [conj, Matrix.mul_assoc, A.H.eigenvectorUnitary.val.trace_mul_comm]
  simp [← Matrix.mul_assoc, Matrix.IsHermitian.eigenvectorUnitary ]

theorem norm_eq_sum_eigenvalues_sq (A : HermitianMat d 𝕜) :
    ‖A‖ ^ 2 = ∑ i, (A.H.eigenvalues i)^2 := by
  rw [← RCLike.ofReal_inj (K := 𝕜), RCLike.ofReal_pow, norm_eq_trace_sq]
  conv_lhs => change (A ^ 2).mat.trace; rw [(A ^ 2).H.trace_eq_sum_eigenvalues]
  simp only [map_sum, map_pow]
  rw [← cfc_sq]
  obtain ⟨e, he⟩ := cfc_eigenvalues (· ^ 2) A
  simp only [he, Function.comp_apply, map_pow]
  exact e.sum_comp (fun x ↦ (algebraMap ℝ 𝕜) (A.H.eigenvalues x) ^ 2)

variable {A} in
theorem lt_smul_of_norm_lt {r : ℝ} (h : ‖A‖ ≤ r) : A ≤ r • 1 := by
  rcases lt_or_ge r 0 with _ | hr
  · have := norm_nonneg A
    order
  rcases isEmpty_or_nonempty d
  · exact le_of_subsingleton
  have h' := (sq_le_sq₀ (by positivity) (by positivity)).mpr h
  rw [norm_eq_sum_eigenvalues_sq] at h'
  nth_rw 1 [← cfc_const A, ← cfc_id A]
  rw [le_iff, ← cfc_sub]
  rw [(HermitianMat.H _).posSemidef_iff_eigenvalues_nonneg]
  intro i; rw [Pi.zero_apply]
  obtain ⟨e, he⟩ := cfc_eigenvalues ((fun x ↦ r) - id) A
  rw [he]; clear he
  dsimp only [Function.comp_apply, Pi.sub_apply, id_eq]
  rw [sub_nonneg]
  apply le_of_sq_le_sq _ hr
  refine le_trans ?_ h'
  exact Finset.single_le_sum (f := fun x ↦ (A.H.eigenvalues x)^2) (by intros; positivity) (Finset.mem_univ _)

theorem ball_subset_Icc : Metric.ball A r ⊆ Set.Icc (A - r • 1) (A + r • 1) := by
  intro x
  simp only [Metric.mem_ball, dist_eq_norm, Set.mem_Icc, tsub_le_iff_right]
  intro h
  constructor
  · rw [← norm_neg] at h
    grw [← lt_smul_of_norm_lt h.le]
    simp
  · grw [← lt_smul_of_norm_lt h.le]
    simp

theorem spectrum_subset_of_mem_Icc (A B : HermitianMat d 𝕜) :
    ∃ a b, ∀ x, A ≤ x ∧ x ≤ B → spectrum ℝ x.mat ⊆ Set.Icc a b := by
  use ⨅ i, A.H.eigenvalues i, ⨆ i, B.H.eigenvalues i
  rintro x ⟨hl, hr⟩
  exact A.H.spectrum_subset_of_mem_Icc B.H hl hr

--TODO: Generalize this to real matrices (really, RCLike) too. The theorem below
-- gives it for complex matrices only.
-- @[fun_prop]
-- protected theorem cfc_continuous {f : ℝ → ℝ} (hf : Continuous f) :
--     Continuous (cfc · f : HermitianMat d 𝕜 → HermitianMat d 𝕜) := by
--   rcases isEmpty_or_nonempty d
--   · proof omitted
--   rw [Metric.continuous_iff] at hf ⊢
--   intro x ε hε
--   have _ : Nonempty (spectrum ℝ x.toMat) := by
--     proof omitted
--   replace hf b := hf b ε hε
--   choose fc hfc₀ hfc using hf
--   let δ : ℝ := ⨆ e : spectrum ℝ x.toMat, fc e
--   refine ⟨δ, ?_, ?_⟩
--   · --This whole block should just be `positivity`. TODO fix.
--     dsimp [δ]
--     --Why doesn't just `classical` make ths happen automatically?
--     replace h_fin := Fintype.ofFinite (spectrum ℝ x.toMat)
--     rw [← Finset.sup'_univ_eq_ciSup, gt_iff_lt, Finset.lt_sup'_iff]
--     simp [hfc₀]
--   intro a ha
--   simp only [dist, AddSubgroupClass.subtype_apply, val_eq_coe, cfc_toMat] at ha ⊢
--   proof omitted

@[fun_prop]
protected theorem cfc_continuous {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (cfc · f : HermitianMat d ℂ → HermitianMat d ℂ) := by
  unfold cfc
  suffices Continuous (fun A : HermitianMat d ℂ ↦ _root_.cfc f A.mat) by
    fun_prop
  have h_compact_cover := LocallyCompactSpace.local_compact_nhds (X := HermitianMat d ℂ)
  apply continuous_of_continuousOn_iUnion_of_isOpen (ι := HermitianMat d ℂ × {x : ℝ // 0 < x})
    (s := fun ab ↦ Metric.ball ab.1 ab.2)
  · rintro ⟨A, r, hr⟩
    apply ContinuousOn.mono ?_ (ball_subset_Icc A r)
    obtain ⟨a, b, hab⟩ := spectrum_subset_of_mem_Icc (A - r • 1) (A + r • 1)
    open ComplexOrder in
    have := ContinuousOn.cfc (A := CStarMatrix d d ℂ) isCompact_Icc f (by fun_prop) hab (fun x _ ↦ x.H)
    exact this
  · simp
  · ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    use ⟨x, 1⟩
    simp

theorem Matrix.PosDef.spectrum_subset_Ioi {d 𝕜 : Type*} [Fintype d] [DecidableEq d] [RCLike 𝕜]
    {A : Matrix d d 𝕜} (hA : A.PosDef) : spectrum ℝ A ⊆ Set.Ioi 0 := by
  --TODO Cleanup. Surely SURELY this is already in Mathlib? (Esp. as an Iff)
  intro x hx
  obtain ⟨v, hv⟩ : ∃ v : d → 𝕜, v ≠ 0 ∧ A.mulVec v = x • v := by
    have h_eigenvalue : ∃ v : d → 𝕜, v ≠ 0 ∧ (A - x • 1).mulVec v = 0 := by
      rw [ spectrum.mem_iff ] at hx;
      simp_all [ Matrix.isUnit_iff_isUnit_det ];
      have := Matrix.exists_mulVec_eq_zero_iff.mpr hx;
      obtain ⟨ v, hv, hv' ⟩ := this; use v; simp_all [ Matrix.sub_mulVec ] ;
      simp_all [ sub_eq_zero, Algebra.algebraMap_eq_smul_one ];
    obtain ⟨ v, hv, hv' ⟩ := h_eigenvalue; use v; simp_all [ sub_eq_iff_eq_add, Matrix.sub_mulVec ] ;
    ext i
    simp [ Matrix.mulVec, dotProduct]
    simp [ Matrix.one_apply]
  have := hA.2 v hv.1
  aesop

/--
If f is a continuous family of functions parameterized by x, then (fun x => A.cfc (f x)) is also continuous.
-/
@[fun_prop]
theorem continuous_cfc_fun {f : X → ℝ → ℝ} (hf : ∀ i, Continuous (f · i)) :
    Continuous (fun x ↦ A.cfc (f x)) := by
  apply Continuous.subtype_mk
  conv => enter [1, x]; apply A.cfc_toMat_eq_sum_smul_proj (f x)
  fun_prop

variable {f : X → ℝ → ℝ} {S : Set X}
/--
ContinuousOn variant for when all the matrices (A x) have a spectrum in a set T, and f is continuous on a set S.
-/
@[fun_prop]
theorem continuousOn_cfc_fun {T : Set ℝ}
  (hf : ∀ i ∈ T, ContinuousOn (f · i) S) (hA : spectrum ℝ A.mat ⊆ T) :
    ContinuousOn (fun x ↦ A.cfc (f x)) S := by
  simp_rw [continuousOn_iff_continuous_restrict] at hf ⊢
  apply Continuous.subtype_mk
  conv => enter [1, x]; apply A.cfc_toMat_eq_sum_smul_proj (f x)
  unfold Set.restrict at hf
  apply continuous_finset_sum _
  rw [A.H.spectrum_real_eq_range_eigenvalues] at hA
  refine fun i _ ↦ Continuous.smul (hf _ (by grind)) (by fun_prop)

/-- Specialization of `continuousOn_cfc_fun` for nonsingular matrices. -/
@[fun_prop]
theorem continuousOn_cfc_fun_nonsingular {f : X → ℝ → ℝ} {S : Set X}
  (hf : ∀ i ≠ 0, ContinuousOn (f · i) S) [NonSingular A] :
    ContinuousOn (fun x ↦ A.cfc (f x)) S := by
  apply continuousOn_cfc_fun (T := {0}ᶜ)
  · exact hf
  · grind [nonSingular_zero_notMem_spectrum]

/-- Specialization of `continuousOn_cfc_fun` for positive semidefinite matrices. -/
@[fun_prop]
theorem continuousOn_cfc_fun_nonneg {f : X → ℝ → ℝ} {S : Set X}
  (hf : ∀ i ≥ 0, ContinuousOn (f · i) S) (hA : 0 ≤ A) :
    ContinuousOn (fun x ↦ A.cfc (f x)) S := by
  apply continuousOn_cfc_fun (T := Set.Ici 0)
  · exact hf
  · rw [zero_le_iff] at hA
    exact hA.pos_of_mem_spectrum

/-- Specialization of `continuousOn_cfc_fun` for positive definite matrices. -/
@[fun_prop]
theorem continuousOn_cfc_fun_posDef {f : X → ℝ → ℝ} {S : Set X}
  (hf : ∀ i > 0, ContinuousOn (f · i) S) (hA : A.mat.PosDef) :
    ContinuousOn (fun x ↦ A.cfc (f x)) S := by
  apply continuousOn_cfc_fun (T := Set.Ioi 0)
  · exact hf
  · exact Matrix.PosDef.spectrum_subset_Ioi hA

variable {A B : HermitianMat d 𝕜} (f : ℝ → ℝ)

/--
The inverse of the CFC is the CFC of the inverse function.
-/
lemma inv_cfc_eq_cfc_inv (hf : ∀ i, f (A.H.eigenvalues i) ≠ 0) :
    (A.cfc f)⁻¹ = A.cfc (fun u ↦ (f u)⁻¹) := by
  suffices (A.cfc f).mat⁻¹ = (A.cfc (fun u ↦ 1 / f u)).mat by
    ext1
    simpa using this
  have h_def : (A.cfc f).mat = ∑ i, f (A.H.eigenvalues i) • (A.H.eigenvectorUnitary.val * (Matrix.single i i 1) * A.H.eigenvectorUnitary.val.conjTranspose) := by
    exact cfc_toMat_eq_sum_smul_proj A f;
  have h_subst : (A.cfc (fun u ↦ 1 / f u)).mat = ∑ i, (1 / f (A.H.eigenvalues i)) • (A.H.eigenvectorUnitary.val * (Matrix.single i i 1) * A.H.eigenvectorUnitary.val.conjTranspose) := by
    exact cfc_toMat_eq_sum_smul_proj A fun u ↦ 1 / f u;
  have h_inv : (A.cfc f).mat * (A.cfc (fun u ↦ 1 / f u)).mat = 1 := by
    -- Since the eigenvectorUnitary is unitary, we have that the product of the projections is the identity matrix.
    have h_unitary : A.H.eigenvectorUnitary.val * A.H.eigenvectorUnitary.val.conjTranspose = 1 := by
      simp [ Matrix.IsHermitian.eigenvectorUnitary ];
    have h_inv : ∀ i j, (A.H.eigenvectorUnitary.val * (Matrix.single i i 1) * A.H.eigenvectorUnitary.val.conjTranspose) * (A.H.eigenvectorUnitary.val * (Matrix.single j j 1) * A.H.eigenvectorUnitary.val.conjTranspose) = if i = j then A.H.eigenvectorUnitary.val * (Matrix.single i i 1) * A.H.eigenvectorUnitary.val.conjTranspose else 0 := by
      simp [ ← Matrix.mul_assoc ];
      intro i j; split_ifs <;> simp_all [ Matrix.mul_assoc, Matrix.mul_eq_one_comm.mp h_unitary ] ;
    simp_all [ Finset.sum_mul _ _ _, Finset.mul_sum ];
    have h_sum : ∑ i, (A.H.eigenvectorUnitary.val * (Matrix.single i i 1) * A.H.eigenvectorUnitary.val.conjTranspose) = A.H.eigenvectorUnitary.val * (∑ i, Matrix.single i i 1) * A.H.eigenvectorUnitary.val.conjTranspose := by
      simp [ Finset.mul_sum _ _ _, Finset.sum_mul, Matrix.mul_assoc ];
    simp_all [ Matrix.single ];
    convert h_unitary using 2;
    ext i j; simp [ Matrix.mul_apply]
    simp [ Matrix.sum_apply, Finset.filter_eq', Finset.filter_and ];
    rw [ Finset.sum_eq_single j ] <;> aesop;
  rw [ Matrix.inv_eq_right_inv h_inv ];

theorem cfc_inv [NonSingular A] : A.cfc (fun u ↦ u⁻¹) = A⁻¹ := by
  simpa using (inv_cfc_eq_cfc_inv id nonSingular_eigenvalue_ne_zero).symm

/-- Matrix power of a positive semidefinite matrix, as given by the elementwise
  real power of the diagonal in a diagonalized form.

  Note that this has the usual `Real.rpow` caveats, such as 0 to the power -1 giving 0. -/
def rpow (A : HermitianMat d 𝕜) (r : ℝ) : HermitianMat d 𝕜 :=
  A.cfc (Real.rpow · r)

instance instRPow : Pow (HermitianMat d 𝕜) ℝ :=
  ⟨rpow⟩

theorem pow_eq_rpow : A ^ r = A.rpow r :=
  rfl

theorem pow_eq_cfc : A ^ r = A.cfc (· ^ r) :=
  rfl

theorem diagonal_pow (f : d → ℝ) :
    (diagonal 𝕜 f) ^ r = diagonal 𝕜 (fun i ↦ (f i) ^ r) := by
  simp [pow_eq_cfc]
  rfl

@[fun_prop]
theorem rpow_const_continuous {r : ℝ} (hr : 0 ≤ r): Continuous (fun A : HermitianMat d ℂ ↦ A ^ r) := by
  exact HermitianMat.cfc_continuous (Real.continuous_rpow_const hr)

@[fun_prop]
theorem const_rpow_continuous_nonsingular [NonSingular A] : Continuous (fun r : ℝ ↦ A ^ r) := by
  rw [← continuousOn_univ]
  apply continuousOn_cfc_fun_nonsingular
  simp only [Real.rpow_eq_pow]
  fun_prop (disch := assumption)

@[fun_prop]
theorem const_rpow_continuous [NonSingular A] : Continuous (fun r : ℝ ↦ A ^ r) := by
  rw [← continuousOn_univ]
  apply continuousOn_cfc_fun_nonsingular
  simp only [Real.rpow_eq_pow]
  fun_prop (disch := assumption)

/--
For a fixed Hermitian matrix A, the function x ↦ A^x is continuous for x > 0.
-/
@[fun_prop]
theorem continuousOn_rpow_pos (A : HermitianMat d ℂ) : ContinuousOn (fun x : ℝ ↦ A ^ x) (Set.Ioi 0) := by
  apply A.continuousOn_cfc_fun (hA := subset_rfl)
  intro i _ x hx
  exact (Real.continuousAt_const_rpow' hx.ne').continuousWithinAt

/--
For a fixed Hermitian matrix A, the function x ↦ A^x is continuous for x < 0.
-/
@[fun_prop]
theorem continuousOn_rpow_neg (A : HermitianMat d ℂ) : ContinuousOn (fun x : ℝ ↦ A ^ x) (Set.Iio 0) := by
  apply A.continuousOn_cfc_fun (hA := subset_rfl)
  intro i _ x hx
  exact (Real.continuousAt_const_rpow' hx.ne).continuousWithinAt

@[simp]
theorem rpow_one : A ^ (1 : ℝ) = A := by
  simp [pow_eq_cfc]

@[simp]
theorem one_rpow : (1 : HermitianMat d 𝕜) ^ r = 1 := by
  rcases isEmpty_or_nonempty d
  · apply Subsingleton.allEq
  · nth_rw 2 [← HermitianMat.cfc_id (1 : HermitianMat d 𝕜)]
    exact HermitianMat.cfc_congr 1 (by simp)

/-- Keeps in line with our simp-normal form for moving reindex outwards. -/
@[simp]
theorem reindex_rpow (e : d ≃ d₂) :
    A.reindex e ^ r = (A ^ r).reindex e := by
  apply A.cfc_reindex

theorem mat_rpow_add (hA : 0 ≤ A) {p q : ℝ} (hpq : p + q ≠ 0) :
    (A ^ (p + q)).mat = (A ^ p).mat * (A ^ q).mat := by
  simp only [pow_eq_cfc, ← mat_cfc_mul, ← HermitianMat.ext_iff]
  exact cfc_congr_of_zero_le hA (fun i hi ↦ Real.rpow_add' hi hpq)

theorem rpow_mul (hA : 0 ≤ A) {p q : ℝ} : A ^ (p * q) = (A ^ p) ^ q := by
  simp only [pow_eq_cfc, ← cfc_comp]
  exact cfc_congr_of_zero_le hA (fun i hi ↦ Real.rpow_mul hi p q)

variable {q r} in
theorem conj_rpow (hA : 0 ≤ A) (hq : q ≠ 0) (hqr : r + 2 * q ≠ 0) :
    (A ^ r).conj (A ^ q) = A ^ (r + 2 * q) := by
  simp only [pow_eq_cfc, cfc_conj]
  refine cfc_congr_of_zero_le hA (fun i hi ↦ ?_)
  rw [pow_two, Real.rpow_add' hi hqr, two_mul, Real.rpow_add' hi (by simpa)]
  rfl

theorem pow_half_mul (hA : 0 ≤ A) :
    (A ^ (1/2 : ℝ)).mat * (A ^ (1/2 : ℝ)).mat = A := by
  rw [← mat_rpow_add hA]
  · norm_num
  · norm_num

theorem rpow_conj_unitary (A : HermitianMat d 𝕜) (U : Matrix.unitaryGroup d 𝕜) (r : ℝ) :
    (HermitianMat.conj U.val A) ^ r = HermitianMat.conj U.val (A ^ r) := by
  exact A.cfc_conj_unitary (· ^ r) U

/-- Matrix logarithm (base e) of a Hermitian matrix, as given by the elementwise
  real logarithm of the diagonal in a diagonalized form, using `Real.log`

  Note that this means that the nullspace of the image includes all of the nullspace of the
  original matrix. This contrasts to the standard definition, which is typically defined for
  positive *definite* matrices, and the nullspace of the image is exactly the
  (λ=1)-eigenspace of the original matrix. (We also get the (λ=-1)-eigenspace here!)

  It coincides with a standard definition if A is positive definite. -/
def log (A : HermitianMat d 𝕜) : HermitianMat d 𝕜 :=
  A.cfc Real.log

def exp (A : HermitianMat d 𝕜) : HermitianMat d 𝕜 :=
  A.cfc Real.exp

theorem _root_.Commute.log_left (hAB : Commute A.mat B.mat) :
    Commute (A.log).mat B.mat := by
  exact hAB.cfc_left Real.log

theorem _root_.Commute.log_right (hAB : Commute A.mat B.mat) :
    Commute A.mat (B.log).mat := by
  exact hAB.cfc_right Real.log

/-- Primed because `Commute.exp_left` refers to `NormedSpace.exp` instead of `HermitianMat.exp`. -/
theorem _root_.Commute.exp_left' (hAB : Commute A.mat B.mat) :
    Commute (A.exp).mat B.mat := by
  exact hAB.cfc_left Real.exp

/-- Primed because `Commute.exp_right` refers to `NormedSpace.exp` instead of `HermitianMat.exp`. -/
theorem _root_.Commute.exp_right' (hAB : Commute A.mat B.mat) :
    Commute A.mat (B.exp).mat := by
  exact hAB.cfc_right Real.exp

@[simp]
theorem reindex_log (e : d ≃ d₂) : (A.reindex e).log = A.log.reindex e :=
  cfc_reindex A Real.log e

@[simp]
theorem reindex_exp (e : d ≃ d₂) : (A.reindex e).exp = A.exp.reindex e :=
  cfc_reindex A Real.exp e

theorem cfc_nonSingular (hf : ∀ i, f (A.H.eigenvalues i) ≠ 0) : NonSingular (A.cfc f) := by
  rw [nonSingular_iff_eigenvalue_ne_zero]
  obtain ⟨e, he⟩ := cfc_eigenvalues f A
  simpa [he] using fun i ↦ hf (e i)

instance nonSingular_exp : NonSingular A.exp := by
  exact cfc_nonSingular Real.exp (fun i ↦ by positivity)

section integral

open MeasureTheory
open scoped Matrix.Norms.Frobenius

omit [DecidableEq d] in
/--
The integral of a Hermitian matrix function commutes with `toMat`.
-/
lemma integral_toMat (A : ℝ → HermitianMat d 𝕜) (T₁ T₂ : ℝ) {μ : Measure ℝ}
  (hA : IntervalIntegrable A μ T₁ T₂) :
    (∫ t in T₁..T₂, A t ∂μ).mat = ∫ t in T₁..T₂, (A t).mat ∂μ := by
  exact ((matₗ (R := ℝ)).intervalIntegral_comp_comm hA).symm

/--
A sum of scaled constant matrices is integrable if the scalar functions are integrable.
-/
lemma intervalIntegrable_sum_smul_const (T₁ T₂ : ℝ) {μ : Measure ℝ} (g : ℝ → d → ℝ)
    (P : d → Matrix d d 𝕜) (hg : ∀ i, IntervalIntegrable (fun t ↦ g t i) μ T₁ T₂) :
    IntervalIntegrable (fun t ↦ ∑ i, g t i • P i) μ T₁ T₂ := by
  simp_all [intervalIntegrable_iff]
  exact integrable_finset_sum _ fun i _ ↦ Integrable.smul_const (hg i) _

/--
A function to Hermitian matrices is integrable iff its matrix values are integrable.
-/
lemma intervalIntegrable_toMat_iff (A : ℝ → HermitianMat d 𝕜) (T₁ T₂ : ℝ) {μ : Measure ℝ} :
    IntervalIntegrable (fun t ↦ (A t).mat) μ T₁ T₂ ↔ IntervalIntegrable A μ T₁ T₂ := by
  --TODO Cleanup
  simp [ intervalIntegrable_iff ];
  constructor <;> intro h;
  · -- Since `toMat` is a linear isometry, the integrability of `A.toMat` implies the integrability of `A`.
    have h_toMat_integrable : IntegrableOn (fun t ↦ (A t).mat) (Set.uIoc T₁ T₂) μ → IntegrableOn A (Set.uIoc T₁ T₂) μ := by
      intro h_toMat_integrable
      have h_toMat_linear : ∃ (L : HermitianMat d 𝕜 →ₗ[ℝ] Matrix d d 𝕜), ∀ x, L x = x.mat := by
        refine' ⟨ _, _ ⟩;
        refine' { .. };
        exacts [ fun x ↦ x.mat, fun x y ↦ rfl, fun m x ↦ rfl, fun x ↦ rfl ];
      obtain ⟨L, hL⟩ := h_toMat_linear;
      have h_toMat_linear : IntegrableOn (fun t ↦ L (A t)) (Set.uIoc T₁ T₂) μ → IntegrableOn A (Set.uIoc T₁ T₂) μ := by
        intro h_toMat_integrable
        have h_toMat_linear : ∃ (L_inv : Matrix d d 𝕜 →ₗ[ℝ] HermitianMat d 𝕜), ∀ x, L_inv (L x) = x := by
          have h_toMat_linear : Function.Injective L := by
            intro x y hxy;
            simp_all only [HermitianMat.ext_iff]
          have h_toMat_linear : ∃ (L_inv : Matrix d d 𝕜 →ₗ[ℝ] HermitianMat d 𝕜), L_inv.comp L = LinearMap.id := by
            exact IsSemisimpleModule.extension_property L h_toMat_linear LinearMap.id;
          exact ⟨ h_toMat_linear.choose, fun x ↦ by simpa using LinearMap.congr_fun h_toMat_linear.choose_spec x ⟩;
        obtain ⟨ L_inv, hL_inv ⟩ := h_toMat_linear;
        have h_toMat_linear : IntegrableOn (fun t ↦ L_inv (L (A t))) (Set.uIoc T₁ T₂) μ := by
          exact ContinuousLinearMap.integrable_comp ( L_inv.toContinuousLinearMap ) h_toMat_integrable;
        aesop;
      aesop;
    exact h_toMat_integrable h;
  · apply h.norm.mono'
    · have := h.aestronglyMeasurable;
      fun_prop
    · filter_upwards with t using le_rfl

/--
The CFC of an integrable function family is integrable.
-/
lemma integrable_cfc (T₁ T₂ : ℝ) (f : ℝ → ℝ → ℝ) {μ : Measure ℝ}
    (hf : ∀ i, IntervalIntegrable (fun t ↦ f t (A.H.eigenvalues i)) μ T₁ T₂) :
    IntervalIntegrable (fun t ↦ A.cfc (f t)) μ T₁ T₂ := by
  have h_expand : ∀ t, (A.cfc (f t)).mat = ∑ i, f t (A.H.eigenvalues i) • (A.H.eigenvectorUnitary.val * (Matrix.single i i 1) * A.H.eigenvectorUnitary.val.conjTranspose) := by
    exact fun t ↦ cfc_toMat_eq_sum_smul_proj A (f t);
  rw [ ← intervalIntegrable_toMat_iff ];
  rw [ funext h_expand ];
  apply intervalIntegrable_sum_smul_const
  exact hf

/--
The integral of the CFC is the CFC of the integral.
-/
lemma integral_cfc_eq_cfc_integral (T₁ T₂ : ℝ) {μ : Measure ℝ} (f : ℝ → ℝ → ℝ)
    (hf : ∀ i, IntervalIntegrable (fun t ↦ f t (A.H.eigenvalues i)) μ T₁ T₂) :
    ∫ t in T₁..T₂, A.cfc (f t) ∂μ = A.cfc (fun u ↦ ∫ t in T₁..T₂, f t u ∂μ) := by
  ext1
  rw [ integral_toMat ];
  · rw [ intervalIntegral.integral_congr fun t ht ↦ HermitianMat.cfc_toMat_eq_sum_smul_proj A ( f t ), intervalIntegral.integral_finset_sum ];
    · rw [ Finset.sum_congr rfl fun i _ ↦ intervalIntegral.integral_smul_const _ _ ];
      exact Eq.symm (cfc_toMat_eq_sum_smul_proj A fun u ↦ ∫ (t : ℝ) in T₁..T₂, f t u ∂μ);
    · simp_all [ intervalIntegrable_iff ];
      exact fun i ↦ ( hf i ).smul_const _
  · exact integrable_cfc T₁ T₂ f hf

end integral
end CFC
