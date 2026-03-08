/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.Finite.Entropy.VonNeumann
import QuantumInfo.Finite.Entropy.Klein

noncomputable section

variable {d d₁ d₂ d₃ : Type*}
variable [Fintype d] [Fintype d₁] [Fintype d₂] [Fintype d₃]
variable [DecidableEq d] [DecidableEq d₁] [DecidableEq d₂] [DecidableEq d₃]
variable {dA dB dC dA₁ dA₂ : Type*}
variable [Fintype dA] [Fintype dB] [Fintype dC] [Fintype dA₁] [Fintype dA₂]
variable [DecidableEq dA] [DecidableEq dB] [DecidableEq dC] [DecidableEq dA₁] [DecidableEq dA₂]
variable {𝕜 : Type*} [RCLike 𝕜]
variable {α : ℝ} {ρ σ : MState d}

open scoped InnerProductSpace RealInnerProductSpace HermitianMat

/-!
To do relative entropies, we start with the _sandwiched Renyi Relative Entropy_ which is a nice general form.
Then instead of proving many theorems (like DPI, relabelling, additivity, etc.) several times, we just prove
it for this one quantity, then it follows for other quantities (like the relative entropy) as a special case.
-/

--PULLOUT to CFC.lean
theorem HermitianMat.spectrum_cfc_eq_image (A : HermitianMat d 𝕜) (f : ℝ → ℝ) :
    spectrum ℝ (A.cfc f).mat = f '' (spectrum ℝ A.mat) := by
  exact cfc_map_spectrum f A.mat

theorem Matrix.IsHermitian.spectrum_rcLike {A : Matrix d d 𝕜} (hA : A.IsHermitian) :
    RCLike.ofReal '' spectrum ℝ A = spectrum 𝕜 A := by
  rw [hA.spectrum_eq_image_range, hA.spectrum_real_eq_range_eigenvalues]

/-- We fix a simp-normal form that, for HermitianMat, we always work in terms
of the real spectrum. -/
@[simp]
theorem HermitianMat.spectrum_rcLike (A : HermitianMat d 𝕜) :
    spectrum 𝕜 A.mat = RCLike.ofReal '' spectrum ℝ A.mat := by
  exact A.H.spectrum_rcLike.symm

theorem HermitianMat.posSemidef_iff_spectrum_Ici (A : HermitianMat d 𝕜) :
    0 ≤ A ↔ spectrum ℝ A.mat ⊆ Set.Ici 0 := by
  rw [zero_le_iff, Matrix.posSemidef_iff_isHermitian_and_spectrum_nonneg]
  simp [A.H, Set.Ici.eq_1]

theorem HermitianMat.posSemidef_iff_spectrum_nonneg (A : HermitianMat d 𝕜) :
    0 ≤ A ↔ ∀ x ∈ spectrum ℝ A.mat, 0 ≤ x := by
  exact A.posSemidef_iff_spectrum_Ici

theorem HermitianMat.ne_zero_iff_ne_zero_spectrum (A : HermitianMat d 𝕜) :
    A ≠ 0 ↔ ∃ x ∈ spectrum ℝ A.mat, x ≠ 0 := by
  constructor;
  · intro h_nonzero
    contrapose! h_nonzero
    simp only [HermitianMat.ext_iff, mat_zero]
    rw [A.H.spectral_theorem]
    ext i j
    simp [Matrix.mul_apply, Matrix.diagonal]
    refine Finset.sum_eq_zero fun x _ ↦ ?_
    simp [h_nonzero _ <| A.H.spectrum_real_eq_range_eigenvalues.symm ▸ Set.mem_range_self _]
  · rintro ⟨x, hx, hx'⟩ h
    simp [h, spectrum, resolventSet, Algebra.algebraMap_eq_smul_one,
      hx', Matrix.isUnit_iff_isUnit_det] at hx

--PULLOUT to CfcOrder.lean
theorem HermitianMat.cfc_pos_of_pos {A : HermitianMat d 𝕜} {f : ℝ → ℝ} (hA : 0 < A)
    (hf : ∀ i > 0, 0 < f i) (hf₂ : 0 ≤ f 0) : 0 < A.cfc f := by
  have h_pos := (posSemidef_iff_spectrum_nonneg A).mp hA.le
  have h_f_pos : ∃ x ∈ spectrum ℝ (A.cfc f).mat, x ≠ 0 := by
    obtain ⟨ x, hx₁, hx₂ ⟩ := ne_zero_iff_ne_zero_spectrum A |>.1 hA.ne'
    exact ⟨ f x, by simpa using HermitianMat.spectrum_cfc_eq_image A f ▸ Set.mem_image_of_mem f hx₁, by cases lt_or_gt_of_ne hx₂ <;> linarith [ hf x ( lt_of_le_of_ne ( h_pos x hx₁ ) ( Ne.symm hx₂ ) ) ] ⟩;
  have h_f_nonneg : 0 ≤ A.cfc f := by
    rw [HermitianMat.posSemidef_iff_spectrum_nonneg];
    rw [ HermitianMat.spectrum_cfc_eq_image ];
    rintro _ ⟨ x, hx, rfl ⟩ ; exact if hx0 : x = 0 then by simpa [ hx0 ] using hf₂ else hf x ( lt_of_le_of_ne ( h_pos x hx ) ( Ne.symm hx0 ) ) |> le_of_lt;
  have h_f_nonzero : A.cfc f ≠ 0 := by
    contrapose! h_f_pos;
    simp [h_f_pos, spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, Algebra.algebraMap_eq_smul_one]
  exact lt_of_le_of_ne h_f_nonneg h_f_nonzero.symm

--PULLOUT to CfcOrder.lean
theorem HermitianMat.rpow_pos {A : HermitianMat d 𝕜} (hA : 0 < A) {p : ℝ} : 0 < A ^ p := by
  convert cfc_pos_of_pos hA _ _
  · exact fun i hi => Real.rpow_pos_of_pos hi _
  · rcases eq_or_ne p 0 with h | h <;> simp [h]

/-
If the range of a Hermitian matrix is contained in its kernel, the matrix is zero.
-/
theorem HermitianMat.range_le_ker_imp_zero {A : HermitianMat d 𝕜}
    (h : LinearMap.range A.mat.toEuclideanLin ≤ LinearMap.ker A.mat.toEuclideanLin) : A = 0 := by
  rw [HermitianMat.ext_iff, mat_zero]
  ext i j
  have hA_sq : (A.mat * A.mat) = 0 := by
    simp_all only [SetLike.le_def, LinearMap.mem_range, LinearMap.mem_ker, forall_exists_index,
      forall_apply_eq_imp_iff]
    simp_all only [← Matrix.ext_iff, Matrix.mul_apply, mat_apply, Matrix.zero_apply]
    intro i j
    specialize h ( EuclideanSpace.single j 1 )
    simp_all only [Matrix.toEuclideanLin, LinearEquiv.trans_apply, LinearEquiv.arrowCongr_apply,
      LinearEquiv.symm_symm, WithLp.linearEquiv_apply, EuclideanSpace.ofLp_single,
      Matrix.toLin'_apply, Matrix.mulVec_single, MulOpposite.op_one, one_smul,
      WithLp.linearEquiv_symm_apply, WithLp.ofLp_toLp, WithLp.toLp_eq_zero] ;
    simpa [ Matrix.mulVec, dotProduct ] using congr_fun h i;
  simp_all only [mat_apply, Matrix.zero_apply]
  replace hA_sq := congr_fun ( congr_fun hA_sq i ) i
  simp_all only [Matrix.mul_apply, mat_apply, Matrix.zero_apply] ;
  -- Since $A$ is Hermitian, we have $A i x * A x i = |A i x|^2$.
  have h_abs : ∀ x, (A i x) * (A x i) = ‖A i x‖ ^ 2 := by
    intro x; have := A.2
    simp_all only [val_eq_coe, sq] ;
    have := congr_fun ( congr_fun this i ) x
    simp_all only [Matrix.star_apply, mat_apply, RCLike.star_def] ;
    simp only [← this, mul_comm, RCLike.norm_conj];
    simp [ ← sq, RCLike.mul_conj ];
  simp_rw [h_abs] at hA_sq
  norm_cast at hA_sq
  simp_all [Finset.sum_eq_zero_iff_of_nonneg]

/--
If ker M ⊆ ker A, then range (A Mᴴ) = range A.
-/
theorem Matrix.range_mul_conjTranspose_of_ker_le_ker {A : Matrix d d 𝕜} {M : Matrix d₂ d 𝕜}
    (h : LinearMap.ker M.toEuclideanLin ≤ LinearMap.ker A.toEuclideanLin) :
    LinearMap.range (A * M.conjTranspose).toEuclideanLin = LinearMap.range A.toEuclideanLin := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    use (M.conjTranspose.toEuclideanLin) y;
    simp [Matrix.toEuclideanLin]
  · intro x hx;
    -- Since $x \in \text{range}(A)$, there exists $y \in \text{range}(Mᴴ)$ such that $A y = x$.
    obtain ⟨y, hy⟩ : ∃ y ∈ LinearMap.range (Matrix.toEuclideanLin (M.conjTranspose)), A.toEuclideanLin y = x := by
      have h_range_MH : LinearMap.range (Matrix.toEuclideanLin (M.conjTranspose)) = (LinearMap.ker (Matrix.toEuclideanLin M))ᗮ := by
        have h_orthogonal : (LinearMap.range (Matrix.toEuclideanLin (M.conjTranspose)))ᗮ = LinearMap.ker (Matrix.toEuclideanLin M) := by
          ext x;
          simp only [toEuclideanLin, LinearEquiv.trans_apply, Submodule.mem_orthogonal',
            LinearMap.mem_range, LinearEquiv.arrowCongr_apply, LinearEquiv.symm_symm,
            WithLp.linearEquiv_apply, toLin'_apply, WithLp.linearEquiv_symm_apply,
            forall_exists_index, forall_apply_eq_imp_iff, LinearMap.mem_ker, WithLp.toLp_eq_zero];
          simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, PiLp.ofLp_apply,
            PiLp.toLp_apply, mulVec, conjTranspose_apply, RCLike.star_def, Pi.star_apply];
          simp only [funext_iff, mulVec, dotProduct, PiLp.ofLp_apply, Pi.zero_apply];
          constructor <;> intro h;
          · intro i; specialize h ( Pi.single i 1 )
            simp_all only [LinearMap.mem_range] ;
            simp_all only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
              Finset.mem_univ, ↓reduceIte];
            simpa [ ← map_sum, ← map_mul ] using congr_arg Star.star h;
          · simp [ mul_comm, mul_left_comm, Finset.mul_sum]
            intro a
            rw [Finset.sum_comm]
            simp only [← Finset.mul_sum]
            simp_all [← map_mul, ← map_sum ];
        rw [← h_orthogonal, Submodule.orthogonal_orthogonal]
      obtain ⟨ y, rfl ⟩ := hx;
      -- Since $y$ is in the range of $Mᴴ$, we can write $y$ as $y = y_1 + y_2$ where $y_1 \in \text{range}(Mᴴ)$ and $y_2 \in \text{ker}(M)$.
      obtain ⟨y1, y2, hy1, hy2, hy⟩ : ∃ y1 y2 : EuclideanSpace 𝕜 d, y1 ∈ LinearMap.range (Matrix.toEuclideanLin (M.conjTranspose)) ∧ y2 ∈ LinearMap.ker (Matrix.toEuclideanLin M) ∧ y = y1 + y2 := by
        have h_decomp : ∀ y : EuclideanSpace 𝕜 d, ∃ y1 ∈ LinearMap.range (Matrix.toEuclideanLin (M.conjTranspose)), ∃ y2 ∈ LinearMap.ker (Matrix.toEuclideanLin M), y = y1 + y2 := by
          intro y
          have h_decomp : y ∈ (LinearMap.range (Matrix.toEuclideanLin (M.conjTranspose))) ⊔ (LinearMap.ker (Matrix.toEuclideanLin M)) := by
            rw [ h_range_MH ];
            rw [ sup_comm, Submodule.sup_orthogonal_of_hasOrthogonalProjection ];
            exact Submodule.mem_top;
          rw [ Submodule.mem_sup ] at h_decomp ; tauto;
        exact ⟨ _, _, h_decomp y |> Classical.choose_spec |> And.left, h_decomp y |> Classical.choose_spec |> And.right |> Classical.choose_spec |> And.left, h_decomp y |> Classical.choose_spec |> And.right |> Classical.choose_spec |> And.right ⟩;
      exact ⟨ y1, hy1, by rw [ hy, map_add, LinearMap.mem_ker.mp ( h hy2 ) ] ; simp ⟩;
    obtain ⟨ z, rfl ⟩ := hy.1;
    exact ⟨ z, by simpa [ Matrix.toEuclideanLin ] using hy.2 ⟩

--PULLOUT to HermitianMat/Order.lean
theorem HermitianMat.conj_ne_zero {A : HermitianMat d 𝕜} {M : Matrix d₂ d 𝕜} (hA : A ≠ 0)
    (h : LinearMap.ker M.toEuclideanLin ≤ A.ker) : A.conj M ≠ 0 := by
  by_contra h_contra
  have h_range : LinearMap.range A.mat.toEuclideanLin ≤ LinearMap.ker A.mat.toEuclideanLin := by
    have h_range : LinearMap.range (A.mat * M.conjTranspose).toEuclideanLin ≤ LinearMap.ker M.toEuclideanLin := by
      rintro x ⟨y, rfl⟩
      replace h_contra := congr($(h_contra).mat)
      simp_all [Matrix.toEuclideanLin_apply, Matrix.mul_assoc]
    rw [← Matrix.range_mul_conjTranspose_of_ker_le_ker h]
    exact h_range.trans h
  exact hA (range_le_ker_imp_zero h_range)

theorem HermitianMat.conj_ne_zero_iff {A : HermitianMat d 𝕜} {M : Matrix d₂ d 𝕜}
    (h : LinearMap.ker M.toEuclideanLin ≤ A.ker) : A.conj M ≠ 0 ↔ A ≠ 0  := by
  refine ⟨?_, (conj_ne_zero · h)⟩
  intro h rfl; simp at h--should be grind[= map_zero] but I don't know why. TODO.

--PULLOUT to HermitianMat/Order.lean
theorem HermitianMat.conj_pos {A : HermitianMat d 𝕜} {M : Matrix d₂ d 𝕜} (hA : 0 < A)
    (h : LinearMap.ker M.toEuclideanLin ≤ A.ker) : 0 < A.conj M := by
  exact (A.conj_nonneg M hA.le).lt_of_ne' (A.conj_ne_zero hA.ne' h)

--PULLOUT to MState.lean. TODO: Rename to `pos`, and rename the existing `MState.pos` to `nonneg`.
theorem MState.pos' {ρ : MState d} : 0 < ρ.M := by
  apply ρ.zero_le.lt_of_ne'
  intro h
  have := ρ.tr
  simp [h] at this

lemma HermitianMat.mulVec_eq_zero_iff_inner_eigenvector_zero
    (A : HermitianMat d ℂ) (x : EuclideanSpace ℂ d) :
    A.mat.mulVec x = 0 ↔ ∀ i, A.H.eigenvalues i ≠ 0 → inner ℂ (A.H.eigenvectorBasis i) x = 0 := by
  constructor <;> intro h
  · simp only [ne_eq]
    intro i hi; have := A.2;
    simp_all only [val_eq_coe] ;
    have := Matrix.IsHermitian.mulVec_eigenvectorBasis A.2 i;
    replace this := congr_arg ( fun y => inner ℂ y x ) this
    simp only [val_eq_coe, CStarModule.inner_smul_left_real, Complex.real_smul] at this;
    rename_i this1
    simp only [selfAdjoint, AddSubgroup.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
      Set.mem_setOf_eq] at this1
    simp only [IsSelfAdjoint] at this1
    simp only [inner, Matrix.mulVec, dotProduct, mat_apply, PiLp.ofLp_apply, map_sum,
      map_mul] at this ⊢
    simp only [funext_iff, Pi.zero_apply, ← Matrix.ext_iff, Matrix.star_apply, mat_apply,
      RCLike.star_def] at this this1 h
    simp_all only [Matrix.mulVec, dotProduct, mat_apply, mul_comm, Finset.mul_sum, mul_left_comm];
    rw [ Finset.sum_comm ] at this
    simp_all only [← mul_assoc, ← Finset.sum_mul, zero_mul, Finset.sum_const_zero] ;
    rw [ eq_comm ] at this
    simp_all only [mul_assoc] ;
    rw [ ← Finset.sum_congr rfl fun _ _ => by rw [ mul_left_comm ] ] at this
    simp_all [← Finset.mul_sum]
  · ext i
    replace this := congr_arg ( fun m => m.mulVec x i ) A.H.spectral_theorem
    simp_all only [ne_eq, Matrix.mulVec, mat_apply, Complex.coe_algebraMap,
      Matrix.mul_assoc, Pi.zero_apply];
    simp_all only [dotProduct, Matrix.mul_apply, Matrix.IsHermitian.eigenvectorUnitary_apply,
      PiLp.ofLp_apply, Matrix.star_apply, RCLike.star_def];
    simp_all only [Matrix.diagonal, Function.comp_apply, Matrix.of_apply, ite_mul,
      zero_mul, Finset.sum_ite_eq, ↓reduceIte, mul_left_comm, Finset.sum_mul, mul_assoc];
    rw [ Finset.sum_comm ];
    refine' Finset.sum_eq_zero fun j hj => _;
    by_cases h2 : A.H.eigenvalues j = 0
    · simp_all only [mul_comm, mul_left_comm, Finset.mem_univ, Complex.ofReal_zero, zero_mul,
        mul_zero, Finset.sum_const_zero];
    simp_all only [mul_comm, mul_left_comm, Finset.mem_univ];
    convert congr_arg (fun y => A.H.eigenvalues j * (A.H.eigenvectorBasis j i) * y) (h j h2) using 1
    · simp [mul_comm, mul_left_comm, Finset.mul_sum, inner]
    · ring

lemma HermitianMat.cfc_mulVec_expansion (A : HermitianMat d ℂ) (f : ℝ → ℝ) (x : EuclideanSpace ℂ d) :
    (A.cfc f).mat.mulVec x = ∑ i, (f (A.H.eigenvalues i) : ℂ) • inner ℂ (A.H.eigenvectorBasis i) x • A.H.eigenvectorBasis i := by
  have h_apply : ∀ i, (Matrix.mulVec (A.H.eigenvectorUnitary.val * (Matrix.single i i 1) * A.H.eigenvectorUnitary.val.conjTranspose) x) = (⟪(A.H.eigenvectorBasis i), x⟫_ℂ) • (A.H.eigenvectorBasis i) := by
    intro i
    have h_apply : (Matrix.mulVec (A.H.eigenvectorUnitary.val * (Matrix.single i i 1) * A.H.eigenvectorUnitary.val.conjTranspose) x) = (A.H.eigenvectorUnitary.val * (Matrix.single i i 1) * A.H.eigenvectorUnitary.val.conjTranspose).mulVec x := by
      rfl;
    ext j; simp [ Matrix.mulVec, dotProduct, inner ]
    ring_nf
    simp [ Matrix.mul_apply, Matrix.single, Finset.sum_mul _ _ _ ]
    ring_nf
    rw [ Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_eq_single i ( by aesop ) ( by aesop ) ]
    simp [ mul_comm, mul_left_comm ]
  have h_apply : (A.cfc f).mat = ∑ i, (f (A.H.eigenvalues i) : ℂ) • (A.H.eigenvectorUnitary.val * (Matrix.single i i 1) * A.H.eigenvectorUnitary.val.conjTranspose) := by
    exact cfc_toMat_eq_sum_smul_proj A f;
  simp only [h_apply, Complex.coe_smul];
  simp only [mul_assoc, ← ‹∀ i, _›];
  ext i; simp only [Matrix.mulVec, dotProduct] ;
  simp only [Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul, Finset.sum_mul];
  rw [ Finset.sum_apply ];
  rw [ Finset.sum_comm ];
  simp only [mul_assoc, PiLp.smul_apply, Matrix.mulVec, dotProduct, Complex.real_smul,
    Finset.mul_sum]

section ker_cfc

variable {A : HermitianMat d ℂ} {f : ℝ → ℝ} {s : Set ℝ}

lemma HermitianMat.ker_cfc_le_ker_on_set
    (hs : spectrum ℝ A.mat ⊆ s)
    (h : ∀ i ∈ s, f i = 0 → i = 0) :
    (A.cfc f).ker ≤ A.ker := by
  intro x hx
  have h_f_nonzero : ∀ i, A.H.eigenvalues i ≠ 0 → f (A.H.eigenvalues i) ≠ 0 := by
    refine fun i hi => fun hi' => hi (h _ ?_ hi')
    rw [A.H.spectrum_real_eq_range_eigenvalues] at hs
    grind only [= Set.mem_range, = Set.subset_def]
  apply (A.mulVec_eq_zero_iff_inner_eigenvector_zero x).mpr
  intro i hi
  have h_coeff : (f (A.H.eigenvalues i) : ℂ) • inner ℂ (A.H.eigenvectorBasis i) x = 0 := by
    have h_coeff : ∑ j, (f (A.H.eigenvalues j) : ℂ) • inner ℂ (A.H.eigenvectorBasis j) x • A.H.eigenvectorBasis j = 0 := by
      convert congr_arg ( fun y => y ) ( show ( A.cfc f ).mat.mulVec x = 0 from by simpa [ Matrix.mulVec ] using hx ) using 1;
      convert A.cfc_mulVec_expansion f x |> Eq.symm using 1;
    apply_fun (fun y => inner ℂ (A.H.eigenvectorBasis i) y) at h_coeff;
    simp_all [ orthonormal_iff_ite.mp ( A.H.eigenvectorBasis.orthonormal ) ];
  exact smul_eq_zero.mp h_coeff |> Or.resolve_left <| mod_cast h_f_nonzero i hi

lemma HermitianMat.ker_cfc_le_ker (h : ∀ i, f i = 0 → i = 0) :
    (A.cfc f).ker ≤ A.ker := by
  exact ker_cfc_le_ker_on_set (Set.subset_univ _) (by simpa using h)

lemma HermitianMat.ker_cfc_le_ker_nonneg (hA : 0 ≤ A) (h : ∀ i ≥ 0, f i = 0 → i = 0) :
    (A.cfc f).ker ≤ A.ker := by
  rw [posSemidef_iff_spectrum_Ici] at hA
  exact ker_cfc_le_ker_on_set hA h

lemma HermitianMat.ker_le_ker_cfc_on_set (hs : spectrum ℝ A.mat ⊆ s) (h : ∀ i ∈ s, i = 0 → f i = 0) :
    A.ker ≤ (A.cfc f).ker := by
  intro x hx;
  have h_inner_zero : ∀ i, f (A.H.eigenvalues i) ≠ 0 → inner ℂ (A.H.eigenvectorBasis i) x = 0 := by
    intro i hi
    have h_inner_zero : A.H.eigenvalues i ≠ 0 := by
      refine fun hi' => hi <| h _ ?_ hi'
      rw [A.H.spectrum_real_eq_range_eigenvalues] at hs
      grind only [= Set.mem_range, = Set.subset_def]
    exact HermitianMat.mulVec_eq_zero_iff_inner_eigenvector_zero A x |>.1 hx i h_inner_zero;
  have h_inner_zero : (A.cfc f).mat.mulVec x = 0 := by
    rw [HermitianMat.cfc_mulVec_expansion];
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hi : f ( A.H.eigenvalues i ) = 0
    · simp_all only [ne_eq, Finset.mem_univ, Complex.coe_smul, smul_eq_zero, true_or]
    · simp_all only [ne_eq, Finset.mem_univ, not_false_eq_true, zero_smul, smul_zero]
  exact h_inner_zero

lemma HermitianMat.ker_le_ker_cfc (h : ∀ i, i = 0 → f i = 0) :
    A.ker ≤ (A.cfc f).ker := by
  exact ker_le_ker_cfc_on_set (Set.subset_univ _) (by simpa using h)

lemma HermitianMat.ker_le_ker_cfc_nonneg (hA : 0 ≤ A) (h : ∀ i ≥ 0, i = 0 → f i = 0) :
    A.ker ≤ (A.cfc f).ker := by
  rw [posSemidef_iff_spectrum_Ici] at hA
  exact ker_le_ker_cfc_on_set hA h

--PULLOUT to HermitianMat/CFC.lean
theorem HermitianMat.ker_cfc_eq_ker (h : ∀ i, f i = 0 ↔ i = 0) :
    (A.cfc f).ker = A.ker := by
  refine le_antisymm (ker_cfc_le_ker ?_) (ker_le_ker_cfc ?_)
  <;> grind only

--PULLOUT to HermitianMat/CFC.lean
theorem HermitianMat.ker_cfc_eq_ker_nonneg (hA : 0 ≤ A) (h : ∀ i ≥ 0, f i = 0 ↔ i = 0) :
    (A.cfc f).ker = A.ker := by
  refine le_antisymm (ker_cfc_le_ker_nonneg hA ?_) (ker_le_ker_cfc_nonneg hA ?_)
  <;> grind only

--PULLOUT to HermitianMat/CFC.lean
theorem HermitianMat.ker_rpow_eq_of_nonneg {A : HermitianMat d ℂ} {p : ℝ} (hA : 0 ≤ A) (hp : p ≠ 0):
    (A ^ p).ker = A.ker := by
  apply A.ker_cfc_eq_ker_nonneg hA
  grind [Real.rpow_eq_zero_iff_of_nonneg, Real.rpow_eq_pow]

theorem HermitianMat.ker_rpow_le_of_nonneg {A : HermitianMat d ℂ} {p : ℝ} (hA : 0 ≤ A):
    (A ^ p).ker ≤ A.ker := by
  apply A.ker_cfc_le_ker_nonneg hA
  grind [Real.rpow_eq_zero_iff_of_nonneg, Real.rpow_eq_pow]

theorem inner_log_sub_log_nonneg (h : σ.M.ker ≤ ρ.M.ker) :
    0 ≤ ⟪ρ.M, ρ.M.log - σ.M.log⟫ := by
  simpa [HermitianMat.log] using
    HermitianMat.klein_inequality ρ.M σ.M ρ.zero_le σ.zero_le ρ.tr σ.tr h

/-- The Sandwiched Renyi Relative Entropy, defined with ln (nits). Note that at `α = 1` this definition
  switch to the standard Relative Entropy, for continuity.

The general analytic theory away from `α = 1` is not yet fully formalized in this file, so we package
the real-valued formula with `ENNReal.ofReal` instead of proving a global nonnegativity theorem here. -/
def SandwichedRelRentropy (α : ℝ) (ρ σ : MState d) : ENNReal :=
  open Classical in
  if _h : σ.M.ker ≤ ρ.M.ker
  then ENNReal.ofReal <| if α = 1 then
      ⟪ρ.M, ρ.M.log - σ.M.log⟫
    else
      ((ρ.M.conj (σ.M ^ ((1 - α)/(2 * α)) ).mat) ^ α).trace.log / (α - 1)
  else ⊤

notation "D̃_" α "(" ρ "‖" σ ")" => SandwichedRelRentropy α ρ σ

/-- The quantum relative entropy `𝐃(ρ‖σ) := Tr[ρ (log ρ - log σ)]`. Also called
the Umegaki quantum relative entropy, when it's necessary to distinguish from other
relative entropies. -/
def qRelativeEnt (ρ σ : MState d) : ENNReal :=
  D̃_1(ρ‖σ)

notation "𝐃(" ρ "‖" σ ")" => qRelativeEnt ρ σ

section additivity

--TODO Cleanup. Ugh.

/--
If the kernels of the components are contained, then the kernel of the Kronecker product is contained.
-/
lemma ker_kron_le_of_le {d₁ d₂ : Type*} [Fintype d₁] [Fintype d₂] [DecidableEq d₁] [DecidableEq d₂]
    (A C : Matrix d₁ d₁ ℂ) (B D : Matrix d₂ d₂ ℂ)
    (hA : LinearMap.ker A.toEuclideanLin ≤ LinearMap.ker C.toEuclideanLin)
    (hB : LinearMap.ker B.toEuclideanLin ≤ LinearMap.ker D.toEuclideanLin) :
    LinearMap.ker (A.kronecker B).toEuclideanLin ≤ LinearMap.ker (C.kronecker D).toEuclideanLin := by
  intro x hx
  simp only [Matrix.kronecker, LinearMap.mem_ker, Matrix.toEuclideanLin_apply,
    WithLp.toLp_eq_zero] at hx ⊢
  -- By definition of Kronecker product, we know that $(A \otimes B)x = 0$ if and only if for all $i$ and $j$, $\sum_{k,l} A_{ik} B_{jl} x_{kl} = 0$.
  have h_kronecker : ∀ i j, ∑ k, A i k • ∑ l, B j l • x (k, l) = 0 := by
    intro i j
    replace hx := congr_fun hx ( i, j )
    simp only [Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, PiLp.ofLp_apply,
      Pi.zero_apply, smul_eq_mul, Finset.mul_sum] at hx ⊢
    rw [ ← Finset.sum_product' ]
    simpa only [mul_assoc, Finset.univ_product_univ] using hx
  -- Apply the hypothesis `hA` to each term in the sum.
  have h_apply_hA : ∀ i j, ∑ k, C i k • ∑ l, B j l • x (k, l) = 0 := by
    intro i j
    specialize hA ( show ( fun k => ∑ l, B j l • x ( k, l ) ) ∈ LinearMap.ker ( Matrix.toEuclideanLin A ) from ?_ )
    · simp_all only [smul_eq_mul, LinearMap.mem_ker]
      ext i_1 : 1
      simp_all only [PiLp.zero_apply]
      apply h_kronecker
    · exact congr_fun hA i
  ext ⟨ i, j ⟩
  simp only [smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, PiLp.ofLp_apply,
    Pi.zero_apply] at h_kronecker h_apply_hA ⊢
  have h_apply_hB : ∑ l, D j l • ∑ k, C i k • x (k, l) = 0 := by
    specialize hB
    simp_all only [funext_iff, Pi.zero_apply, Prod.forall, smul_eq_mul]
    have := hB ( show ( fun l => ∑ k, C i k * x ( k, l ) ) ∈ LinearMap.ker ( Matrix.toEuclideanLin B ) from ?_ )
    · simp_all only [LinearMap.mem_ker] ;
      exact congr_fun this j
    · ext j
      specialize h_apply_hA i j
      simp_all [ Matrix.mulVec, dotProduct, Finset.mul_sum ] ;
      convert h_apply_hA using 1
      simp only [Matrix.toEuclideanLin, LinearEquiv.trans_apply, LinearEquiv.arrowCongr_apply,
        LinearEquiv.symm_symm, WithLp.linearEquiv_apply, Matrix.toLin'_apply,
        WithLp.linearEquiv_symm_apply, PiLp.toLp_apply];
      simp only [Matrix.mulVec, dotProduct, PiLp.ofLp_apply, Finset.mul_sum, mul_left_comm];
      rw [Finset.sum_comm]
  rw [← h_apply_hB]
  simp only [mul_comm, mul_left_comm]
  simp only [smul_eq_mul, Finset.mul_sum]
  rw [ Finset.sum_sigma' ];
  refine' Finset.sum_bij ( fun x _ => ⟨ x.2, x.1 ⟩ ) _ _ _ _ <;> simp [mul_left_comm ]

--TODO: Generalize to arbitrary PSD matrices.
/--
If the kernel of a product state is contained in another, the left component kernel is contained.
-/
lemma ker_le_of_ker_kron_le_left (ρ₁ σ₁ : MState d₁) (ρ₂ σ₂ : MState d₂)
  (h : (σ₁ ⊗ᴹ σ₂).M.ker ≤ (ρ₁ ⊗ᴹ ρ₂).M.ker) :
    σ₁.M.ker ≤ ρ₁.M.ker := by
  intro u hu
  obtain ⟨v, hv⟩ : ∃ v : d₂ → ℂ, v ∉ (σ₂ :HermitianMat d₂ ℂ).ker ∧ v ∉ (ρ₂ :HermitianMat d₂ ℂ).ker := by
    have h_union : (σ₂ : HermitianMat d₂ ℂ).ker ≠ ⊤ ∧ (ρ₂ : HermitianMat d₂ ℂ).ker ≠ ⊤ := by
      constructor <;> intro h_top;
      · have h_contra : σ₂.M = 0 := by
          ext1
          simp_all [ Submodule.eq_top_iff'];
          ext i j; specialize h_top ( EuclideanSpace.single j 1 )
          simp_all
          replace h_top := congr_fun h_top i
          simp_all
          convert h_top using 1;
          erw [ Matrix.toEuclideanLin_apply ] ; aesop;
        exact σ₂.pos'.ne' h_contra;
      · have h_contra : ρ₂.M = 0 := by
          ext i j; simp_all [ Submodule.eq_top_iff' ] ;
          convert congr_fun ( h_top ( Pi.single j 1 ) ) i using 1 ; simp
          simp [ HermitianMat.lin ];
          simp [ Matrix.toEuclideanLin, Matrix.mulVec, dotProduct ];
          rw [ Finset.sum_eq_single j ] <;> aesop;
        exact ρ₂.pos'.ne' h_contra;
    have h_union : ∀ (U V : Submodule ℂ (EuclideanSpace ℂ d₂)), U ≠ ⊤ → V ≠ ⊤ → ∃ v : EuclideanSpace ℂ d₂, v ∉ U ∧ v ∉ V := by
      intros U V hU hV;
      by_contra h_contra;
      have h_union : U ⊔ V = ⊤ := by
        ext v
        simp only [Submodule.mem_top, iff_true]
        by_cases hvU : v ∈ U <;> by_cases hvV : v ∈ V <;> simp_all [ Submodule.mem_sup ];
        · exact ⟨ v, hvU, 0, by simp, by simp ⟩;
        · exact ⟨ v, hvU, 0, by simp, by simp ⟩;
        · exact ⟨ 0, by simp, v, h_contra v hvU, by simp ⟩;
      have h_union : ∃ v : EuclideanSpace ℂ d₂, v ∉ U ∧ v ∈ V := by
        have h_union : ∃ v : EuclideanSpace ℂ d₂, v ∈ V ∧ v ∉ U := by
          have h_not_subset : ¬V ≤ U := by
            exact fun h => hU <| by rw [ eq_top_iff ] ; exact h_union ▸ sup_le ( by tauto ) h;
          exact Set.not_subset.mp h_not_subset;
        exact ⟨ h_union.choose, h_union.choose_spec.2, h_union.choose_spec.1 ⟩;
      obtain ⟨ v, hv₁, hv₂ ⟩ := h_union;
      obtain ⟨ w, hw₁, hw₂ ⟩ : ∃ w : EuclideanSpace ℂ d₂, w ∉ V ∧ w ∈ U := by
        obtain ⟨ w, hw ⟩ := ( show ∃ w : EuclideanSpace ℂ d₂, w ∉ V from by simpa [ Submodule.eq_top_iff' ] using hV ) ; use w; simp_all [ Submodule.eq_top_iff' ] ;
        exact Classical.not_not.1 fun hw' => hw <| h_contra _ hw';
      have h_union : v + w ∉ U ∧ v + w ∉ V := by
        exact ⟨ fun h => hv₁ <| by simpa using U.sub_mem h hw₂, fun h => hw₁ <| by simpa using V.sub_mem h hv₂ ⟩;
      exact h_contra ⟨ v + w, h_union.1, h_union.2 ⟩;
    exact h_union _ _ ( by tauto ) ( by tauto );
  -- Consider $z = u \otimes v$.
  set z : EuclideanSpace ℂ (d₁ × d₂) := fun p => u p.1 * v p.2;
  have hz : z ∈ (σ₁ ⊗ᴹ σ₂ : HermitianMat (d₁ × d₂) ℂ).ker := by
    ext ⟨i, j⟩
    simp [z]
    have h_kronecker : ∀ (A : Matrix d₁ d₁ ℂ) (B : Matrix d₂ d₂ ℂ) (u : d₁ → ℂ) (v : d₂ → ℂ), (A.kronecker B).mulVec (fun p => u p.1 * v p.2) = fun p => (A.mulVec u) p.1 * (B.mulVec v) p.2 := by
      intro A B u v; ext ⟨ i, j ⟩ ; simp [ Matrix.mulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm ] ;
      exact Fintype.sum_prod_type_right fun x => A i x.1 * (B j x.2 * (u x.1 * v x.2));
    convert congr_fun ( h_kronecker σ₁.1.mat σ₂.1.mat u v ) ( i, j ) using 1 ; simp
    exact Or.inl ( by simpa [ Matrix.mulVec ] using congr_fun hu i );
  have hz' : z ∈ (ρ₁ ⊗ᴹ ρ₂ : HermitianMat (d₁ × d₂) ℂ).ker := by
    exact h hz;
  have hz'' : ∀ a b, (ρ₁.M.val.mulVec u) a * (ρ₂.M.val.mulVec v) b = 0 := by
    intro a b
    have hz'' : (ρ₁.M.val.mulVec u) a * (ρ₂.M.val.mulVec v) b = ((ρ₁ ⊗ᴹ ρ₂ : HermitianMat (d₁ × d₂) ℂ).val.mulVec z) (a, b) := by
      simp [ Matrix.mulVec, dotProduct];
      simp [  Finset.sum_mul, mul_assoc, mul_comm];
      simp [ z, Finset.mul_sum, mul_assoc, mul_left_comm ];
      erw [ Finset.sum_product ] ; simp
      exact rfl;
    exact hz''.trans ( by simpa using congr_fun hz' ( a, b ) );
  ext a; specialize hz'' a; simp_all [ Matrix.mulVec, dotProduct ] ;
  contrapose! hv;
  intro hv'; ext b; specialize hz'' b; simp_all
  exact hz''.resolve_left ( by simpa [ Matrix.mulVec, dotProduct ] using hv )


--TODO: Generalize to arbitrary PSD matrices.
--TODO: Rewrite the proof using the `ker_le_of_ker_kron_le_left` lemma, and the fact that
-- there's a unitary whose conjugation swaps the kronecker product.
/--
If the kernel of a product state is contained in another, the right component kernel is contained.
-/
lemma ker_le_of_ker_kron_le_right (ρ₁ σ₁ : MState d₁) (ρ₂ σ₂ : MState d₂)
  (h : (σ₁ ⊗ᴹ σ₂).M.ker ≤ (ρ₁ ⊗ᴹ ρ₂).M.ker) :
    σ₂.M.ker ≤ ρ₂.M.ker := by
  intro v hv;
  have h_z : ∃ u : EuclideanSpace ℂ d₁, u ≠ 0 ∧ u ∉ σ₁.M.ker ∧ u ∉ ρ₁.M.ker := by
    have h_z : σ₁.M.ker ≠ ⊤ ∧ ρ₁.M.ker ≠ ⊤ := by
      have h_ker_ne_top : ∀ (ρ : MState d₁), ρ.M.ker ≠ ⊤ := by
        intro ρ hρ_top
        have h_contra : ρ.M = 0 := by
          ext i j
          simp_all [ Submodule.eq_top_iff' ] ;
          convert congr_fun ( hρ_top ( EuclideanSpace.single j 1 ) ) i using 1
          simp
          erw [ Matrix.toEuclideanLin_apply ] ; aesop;
        exact ρ.pos'.ne' h_contra;
      exact ⟨ h_ker_ne_top σ₁, h_ker_ne_top ρ₁ ⟩;
    have h_z : ∃ u : EuclideanSpace ℂ d₁, u ∉ σ₁.M.ker ∧ u ∉ ρ₁.M.ker := by
      have h_z : ∀ (U V : Submodule ℂ (EuclideanSpace ℂ d₁)), U ≠ ⊤ → V ≠ ⊤ → ∃ u : EuclideanSpace ℂ d₁, u ∉ U ∧ u ∉ V := by
        intro U V hU hV
        by_contra h_contra
        push_neg at h_contra;
        have h_union : ∃ u : EuclideanSpace ℂ d₁, u ∉ U ∧ u ∈ V := by
          exact Exists.elim ( show ∃ u : EuclideanSpace ℂ d₁, u ∉ U from by simpa [ Submodule.eq_top_iff' ] using hU ) fun u hu => ⟨ u, hu, h_contra u hu ⟩;
        obtain ⟨ u, hu₁, hu₂ ⟩ := h_union;
        have h_union : ∀ v : EuclideanSpace ℂ d₁, v ∈ U → v + u ∈ V := by
          intro v hv; specialize h_contra ( v + u ) ; simp_all [ Submodule.add_mem_iff_right ] ;
        have h_union : ∀ v : EuclideanSpace ℂ d₁, v ∈ U → v ∈ V := by
          exact fun v hv => by simpa using V.sub_mem ( h_union v hv ) hu₂;
        exact hV ( eq_top_iff.mpr fun x hx => by by_cases hxU : x ∈ U <;> aesop );
      exact h_z _ _ ( by tauto ) ( by tauto );
    exact ⟨ h_z.choose, by intro h; simpa [ h ] using h_z.choose_spec.1, h_z.choose_spec.1, h_z.choose_spec.2 ⟩;
  obtain ⟨ u, hu₁, hu₂, hu₃ ⟩ := h_z;
  -- Consider the vector $z = u \otimes v$.
  set z : EuclideanSpace ℂ (d₁ × d₂) := fun p => u p.1 * v p.2;
  have hz : z ∈ (σ₁ ⊗ᴹ σ₂).M.ker := by
    -- By definition of $z$, we have $(σ₁ ⊗ σ₂).mat.mulVec z = σ₁.mat.mulVec u ⊗ σ₂.mat.mulVec v$.
    have hz_mul : (σ₁ ⊗ᴹ σ₂).M.mat.mulVec z = fun p => (σ₁.M.mat.mulVec u) p.1 * (σ₂.M.mat.mulVec v) p.2 := by
      ext p; simp [z, Matrix.mulVec]
      simp [ dotProduct, Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_comm, mul_left_comm ];
      rw [ ← Finset.sum_product' ];
      refine' Finset.sum_bij ( fun x _ => ( x.2, x.1 ) ) _ _ _ _ <;> simp;
      exact fun a b => Or.inl <| Or.inl <| rfl;
    simp_all [ funext_iff, Matrix.mulVec ];
    ext ⟨ a, b ⟩ ; specialize hz_mul a b
    simp_all [ dotProduct] ;
    convert hz_mul using 1;
    simp_all only [zero_eq_mul]
    exact Or.inr ( by simpa [ Matrix.mulVec, dotProduct ] using congr_fun hv b );
  have hz' : z ∈ (ρ₁ ⊗ᴹ ρ₂).M.ker := by
    exact h hz;
  have hz'' : ∀ i j, (ρ₁.M.val.mulVec u) i * (ρ₂.M.val.mulVec v) j = 0 := by
    intro i j;
    have hz'' : (ρ₁.M.val.kronecker ρ₂.M.val).mulVec (fun p => u p.1 * v p.2) (i, j) = (ρ₁.M.val.mulVec u) i * (ρ₂.M.val.mulVec v) j := by
      simp [ Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm ];
      simp [ mul_assoc, Finset.mul_sum, Finset.sum_mul ];
      rw [ ← Finset.sum_product' ];
      refine' Finset.sum_bij ( fun x _ => ( x.2, x.1 ) ) _ _ _ _ <;> simp;
      exact fun _ _ => Or.inl <| Or.inl rfl;
    exact hz''.symm.trans ( by simpa using congr_fun hz' ( i, j ) );
  contrapose! hz'';
  obtain ⟨ i, hi ⟩ := Function.ne_iff.mp ( show ρ₁.M.val.mulVec u ≠ 0 from fun h => hu₃ <| by simpa [ h ] )
  obtain ⟨ j, hj ⟩ := Function.ne_iff.mp ( show ρ₂.M.val.mulVec v ≠ 0 from fun h => hz'' <| by simpa [ h ] )
  use i, j
  aesop;

/--
The kernel of a product state is contained in another product state's kernel iff the individual
kernels are contained.
-/
lemma ker_prod_le_iff (ρ₁ σ₁ : MState d₁) (ρ₂ σ₂ : MState d₂) :
    (σ₁ ⊗ᴹ σ₂).M.ker ≤ (ρ₁ ⊗ᴹ ρ₂).M.ker ↔ σ₁.M.ker ≤ ρ₁.M.ker ∧ σ₂.M.ker ≤ ρ₂.M.ker := by
  constructor <;> intro h;
  · exact ⟨ ker_le_of_ker_kron_le_left ρ₁ σ₁ ρ₂ σ₂ h, ker_le_of_ker_kron_le_right ρ₁ σ₁ ρ₂ σ₂ h ⟩;
  · convert ker_kron_le_of_le _ _ _ _ h.1 h.2 using 1

--TODO: Generalize to RCLike.
omit [DecidableEq d₁] [DecidableEq d₂] in
lemma HermitianMat.inner_kron
    (A : HermitianMat d₁ ℂ) (B : HermitianMat d₂ ℂ) (C : HermitianMat d₁ ℂ) (D : HermitianMat d₂ ℂ) :
    ⟪A ⊗ₖ B, C ⊗ₖ D⟫ = ⟪A, C⟫ * ⟪B, D⟫ := by
  -- Apply the property of the trace of Kronecker products.
  have h_trace_kron : ∀ (A₁ B₁ : Matrix d₁ d₁ ℂ) (A₂ B₂ : Matrix d₂ d₂ ℂ), Matrix.trace (Matrix.kroneckerMap (· * ·) A₁ A₂ * Matrix.kroneckerMap (· * ·) B₁ B₂) = Matrix.trace (A₁ * B₁) * Matrix.trace (A₂ * B₂) := by
    intro A₁ B₁ A₂ B₂
    rw [← Matrix.mul_kronecker_mul, Matrix.trace_kronecker]
  simp_all only [inner, IsMaximalSelfAdjoint.RCLike_selfadjMap, kronecker_mat, RCLike.mul_re,
    RCLike.re_to_complex, RCLike.im_to_complex, sub_eq_self, mul_eq_zero];
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, mat_apply, Complex.im_sum,
    Complex.mul_im];
  left;
  have h_symm : ∀ x x_1, (A x x_1).re * (C x_1 x).im + (A x x_1).im * (C x_1 x).re = -((A x_1 x).re * (C x x_1).im + (A x_1 x).im * (C x x_1).re) := by
    intro x y; have := congr_fun ( congr_fun A.2 y ) x; have := congr_fun ( congr_fun C.2 y ) x; simp_all [ Complex.ext_iff ] ;
    grind;
  have h_sum_zero : ∑ x, ∑ x_1, ((A x x_1).re * (C x_1 x).im + (A x x_1).im * (C x_1 x).re) = ∑ x, ∑ x_1, -((A x x_1).re * (C x_1 x).im + (A x x_1).im * (C x_1 x).re) := by
    rw [ Finset.sum_comm ];
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => h_symm _ _ ▸ rfl;
  norm_num [ Finset.sum_add_distrib ] at * ; linarith

lemma HermitianMat.supportProj_mul_self (A : HermitianMat d ℂ) :
    A.supportProj.mat * A.mat = A.mat := by
  have h_supportProj_mul_A : ∀ (v : d → ℂ), (A.supportProj.val.mulVec (A.val.mulVec v)) = (A.val.mulVec v) := by
    intro v
    have h_range : A.val.mulVec v ∈ LinearMap.range A.val.toEuclideanLin := by
      exact ⟨ v, rfl ⟩
    have h_supportProj_mul_A : ∀ (v : EuclideanSpace ℂ d), v ∈ LinearMap.range A.val.toEuclideanLin → (A.supportProj.val.toEuclideanLin v) = v := by
      intro v hv
      have h_supportProj_mul_A : (A.supportProj.val.toEuclideanLin v) = (Submodule.orthogonalProjection (LinearMap.range A.val.toEuclideanLin) v) := by
        simp only [Matrix.toEuclideanLin, supportProj, val_eq_coe, LinearEquiv.trans_apply,
          LinearEquiv.arrowCongr_apply, LinearEquiv.symm_symm, WithLp.linearEquiv_apply,
          Matrix.toLin'_apply, WithLp.linearEquiv_symm_apply,
          Submodule.coe_orthogonalProjection_apply];
        simp only [projector, ContinuousLinearMap.coe_comp, Submodule.coe_subtypeL, mat_mk];
        simp only [LinearMap.toMatrix, OrthonormalBasis.coe_toBasis_repr, LinearEquiv.trans_apply,
          LinearMap.toMatrix'_mulVec, LinearEquiv.arrowCongr_apply, LinearMap.comp_apply,
          ContinuousLinearMap.coe_coe, Submodule.subtype_apply,
          Submodule.coe_orthogonalProjection_apply];
        exact rfl
      rw [h_supportProj_mul_A]
      exact Submodule.eq_starProjection_of_mem_of_inner_eq_zero (by simpa using hv) (by simp)
    convert h_supportProj_mul_A _ h_range using 1;
  exact Matrix.toLin'.injective ( LinearMap.ext fun v => by simpa using h_supportProj_mul_A v )

lemma HermitianMat.inner_supportProj_self (A : HermitianMat d ℂ) :
    ⟪A, A.supportProj⟫ = A.trace := by
  simp only [trace, IsMaximalSelfAdjoint.RCLike_selfadjMap, Matrix.trace, Matrix.diag_apply,
    mat_apply, map_sum, RCLike.re_to_complex]
  simp only [inner, IsMaximalSelfAdjoint.RCLike_selfadjMap, RCLike.re_to_complex];
  convert congr_arg Complex.re ( congr_arg Matrix.trace ( HermitianMat.supportProj_mul_self A ) ) using 1;
  · simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, mat_apply, Complex.re_sum,
      Complex.mul_re, Finset.sum_sub_distrib, mul_comm];
    exact congrArg₂ _ ( Finset.sum_comm ) ( Finset.sum_comm );
  · simp only [Matrix.trace, Matrix.diag_apply, mat_apply, Complex.re_sum]

lemma HermitianMat.mul_supportProj_of_ker_le (A B : HermitianMat d ℂ)
  (h : LinearMap.ker B.lin ≤ LinearMap.ker A.lin) :
    A.mat * B.supportProj.mat = A.mat := by
  -- Since $B.supportProj$ is the projection onto $range B$, we have $B.supportProj * B.mat = B.mat$.
  have h_supportProj_mul_B : B.supportProj.mat * B.mat = B.mat := by
    exact supportProj_mul_self B;
  have h_range_A_subset_range_B : LinearMap.range A.lin ≤ LinearMap.range B.lin := by
    have h_orthogonal_complement : LinearMap.range (B.lin : EuclideanSpace ℂ d →ₗ[ℂ] EuclideanSpace ℂ d) = (LinearMap.ker (B.lin : EuclideanSpace ℂ d →ₗ[ℂ] EuclideanSpace ℂ d))ᗮ := by
      have h_orthogonal_complement : ∀ (T : EuclideanSpace ℂ d →ₗ[ℂ] EuclideanSpace ℂ d), T = T.adjoint → LinearMap.range T = (LinearMap.ker T)ᗮ := by
        intro T hT;
        refine' Submodule.eq_of_le_of_finrank_eq _ _;
        · intro x hx
          obtain ⟨y, hy⟩ := hx
          have h_orthogonal : ∀ z ∈ LinearMap.ker T, inner ℂ x z = 0 := by
            intro z hz
            have h_orthogonal : inner ℂ (T y) z = inner ℂ y (T.adjoint z) := by
              rw [ LinearMap.adjoint_inner_right ];
            simp [ ← hT ] at h_orthogonal ⊢
            aesop ( simp_config := { singlePass := true } );
          exact (Submodule.mem_orthogonal' (LinearMap.ker T) x).mpr h_orthogonal;
        · have := LinearMap.finrank_range_add_finrank_ker T;
          have := Submodule.finrank_add_finrank_orthogonal ( LinearMap.ker T );
          linarith;
      apply h_orthogonal_complement;
      ext
      simp
    have h_orthogonal_complement_A : LinearMap.range (A.lin : EuclideanSpace ℂ d →ₗ[ℂ] EuclideanSpace ℂ d) ≤ (LinearMap.ker (A.lin : EuclideanSpace ℂ d →ₗ[ℂ] EuclideanSpace ℂ d))ᗮ := by
      intro x hx;
      intro y hy
      simp_all only [LinearMap.mem_range, ContinuousLinearMap.coe_coe, LinearMap.mem_ker]
      obtain ⟨ z, rfl ⟩ := hx;
      have h_orthogonal_complement_A : ∀ (y z : EuclideanSpace ℂ d), ⟪y, A.lin z⟫_ℂ = ⟪A.lin y, z⟫_ℂ := by
        simp
      rw [ h_orthogonal_complement_A, hy, inner_zero_left ];
    exact h_orthogonal_complement.symm ▸ le_trans h_orthogonal_complement_A ( Submodule.orthogonal_le h );
  -- Since $B.supportProj$ is the projection onto $range B$, and $range A \subseteq range B$, we have $B.supportProj * A = A$.
  have h_supportProj_mul_A : ∀ (v : EuclideanSpace ℂ d), B.supportProj.mat.mulVec (A.mat.mulVec v) = A.mat.mulVec v := by
    intro v
    have hv_range_B : A.mat.mulVec v ∈ LinearMap.range B.lin := by
      exact h_range_A_subset_range_B ( Set.mem_range_self v );
    obtain ⟨ w, hw ⟩ := hv_range_B;
    replace h_supportProj_mul_B := congr_arg ( fun m => m.mulVec w ) h_supportProj_mul_B
    simpa only [← hw, ← Matrix.mulVec_mulVec] using h_supportProj_mul_B
  -- By definition of matrix multiplication, if B.supportProj * A * v = A * v for all vectors v, then B.supportProj * A = A.
  have h_matrix_eq : ∀ (M N : Matrix d d ℂ), (∀ v : EuclideanSpace ℂ d, M.mulVec (N.mulVec v) = N.mulVec v) → M * N = N := by
    intro M N hMN; ext i j; specialize hMN ( Pi.single j 1 ) ; replace hMN := congr_fun hMN i; aesop;
  apply_fun Matrix.conjTranspose at *; aesop;
  exact fun M N hMN => by simpa using congr_arg Matrix.conjTranspose hMN;

lemma HermitianMat.inner_supportProj_of_ker_le (A B : HermitianMat d ℂ)
  (h : LinearMap.ker B.lin ≤ LinearMap.ker A.lin) :
    ⟪A, B.supportProj⟫ = A.trace := by
  rw [inner_def, mul_supportProj_of_ker_le A B h, trace]

attribute [fun_prop] ContinuousAt.rpow

lemma continuousOn_rpow_uniform {K : Set ℝ} (hK : IsCompact K) :
    ContinuousOn (fun r : ℝ ↦ UniformOnFun.ofFun {K} (fun t : ℝ ↦ t ^ r)) (Set.Ioi 0) := by
  refine continuousOn_of_forall_continuousAt fun r hr => ?_
  rw [Set.mem_Ioi] at hr
  apply UniformOnFun.tendsto_iff_tendstoUniformlyOn.mpr
  simp only [Set.mem_singleton_iff, UniformOnFun.toFun_ofFun, Metric.tendstoUniformlyOn_iff,
    Function.comp_apply, forall_eq]
  intro ε hεpos;
  have h_unif_cont : UniformContinuousOn (fun (p : ℝ × ℝ) => p.1 ^ p.2) (K ×ˢ Set.Icc (r / 2) (r * 2)) := by
    apply IsCompact.uniformContinuousOn_of_continuous
    · exact hK.prod CompactIccSpace.isCompact_Icc
    · refine continuousOn_of_forall_continuousAt fun p ⟨hp₁, ⟨hp₂₁, hp₂₂⟩⟩ ↦ ?_
      have _ : p.1 ≠ 0 ∨ 0 < p.2 := by right; linarith
      fun_prop (disch := assumption)
  rw [Metric.uniformContinuousOn_iff] at h_unif_cont
  obtain ⟨δ, hδpos, H⟩ := h_unif_cont ε hεpos
  filter_upwards [Ioo_mem_nhds (show r / 2 < r by linarith) (show r < r * 2 by linarith), Ioo_mem_nhds (show r - δ < r by linarith) (show r < r + δ by linarith)] with n ⟨_, _⟩ ⟨_, _⟩ x hx
  refine H (x, r) ⟨hx, ?_⟩ (x, n) ⟨hx, ?_⟩ ?_
  · constructor <;> linarith
  · constructor <;> linarith
  · have : |r - n| < δ := abs_lt.mpr ⟨by linarith, by linarith⟩
    simpa

theorem sandwichedRelRentropy_additive_alpha_one_aux (ρ₁ σ₁ : MState d₁) (ρ₂ σ₂ : MState d₂)
  (h1 : σ₁.M.ker ≤ ρ₁.M.ker) (h2 : σ₂.M.ker ≤ ρ₂.M.ker) :
    ⟪(ρ₁ ⊗ᴹ ρ₂).M, (ρ₁ ⊗ᴹ ρ₂).M.log - (σ₁ ⊗ᴹ σ₂).M.log⟫ =
    ⟪ρ₁.M, ρ₁.M.log - σ₁.M.log⟫_ℝ + ⟪ρ₂.M, ρ₂.M.log - σ₂.M.log⟫ := by
  have h_log_kron : (ρ₁ ⊗ᴹ ρ₂).M.log = ρ₁.M.log ⊗ₖ ρ₂.M.supportProj + ρ₁.M.supportProj ⊗ₖ ρ₂.M.log ∧ (σ₁ ⊗ᴹ σ₂).M.log = σ₁.M.log ⊗ₖ σ₂.M.supportProj + σ₁.M.supportProj ⊗ₖ σ₂.M.log := by
    constructor <;> apply HermitianMat.log_kron_with_proj;
  have h_inner_supportProj : ∀ (A : HermitianMat d₁ ℂ) (B : HermitianMat d₂ ℂ), ⟪A ⊗ₖ B, ρ₁ ⊗ᴹ ρ₂⟫ = ⟪A, ρ₁⟫ * ⟪B, ρ₂⟫ := by
    exact fun A B => HermitianMat.inner_kron A B ρ₁ ρ₂;
  simp only [HermitianMat.ker] at h1 h2
  simp_all only [inner_sub_right, inner_add_right, real_inner_comm,
    HermitianMat.inner_supportProj_self, MState.tr, mul_one, one_mul,
    HermitianMat.inner_supportProj_of_ker_le]
  abel

/--
The Sandwiched Renyi Relative entropy is additive for α=1 (standard relative entropy).
-/
private theorem sandwichedRelRentropy_additive_alpha_one (ρ₁ σ₁ : MState d₁) (ρ₂ σ₂ : MState d₂) :
    D̃_ 1(ρ₁ ⊗ᴹ ρ₂‖σ₁ ⊗ᴹ σ₂) = D̃_ 1(ρ₁‖σ₁) + D̃_ 1(ρ₂‖σ₂) := by
  by_cases h1 : σ₁.M.ker ≤ ρ₁.M.ker
  <;> by_cases h2 : σ₂.M.ker ≤ ρ₂.M.ker
  · simp only [SandwichedRelRentropy, ↓reduceIte, ↓reduceDIte, h1, h2]
    have h12 : (σ₁ ⊗ᴹ σ₂).M.ker ≤ (ρ₁ ⊗ᴹ ρ₂).M.ker :=
      (ker_prod_le_iff ρ₁ σ₁ ρ₂ σ₂).2 ⟨h1, h2⟩
    have hnonneg1 : 0 ≤ ⟪ρ₁.M, ρ₁.M.log - σ₁.M.log⟫ :=
      inner_log_sub_log_nonneg h1
    have hnonneg2 : 0 ≤ ⟪ρ₂.M, ρ₂.M.log - σ₂.M.log⟫ :=
      inner_log_sub_log_nonneg h2
    simp only [h12, ↓reduceDIte]
    rw [sandwichedRelRentropy_additive_alpha_one_aux ρ₁ σ₁ ρ₂ σ₂ h1 h2]
    rw [ENNReal.ofReal_add hnonneg1 hnonneg2]
  · have h12 : ¬ (σ₁ ⊗ᴹ σ₂).M.ker ≤ (ρ₁ ⊗ᴹ ρ₂).M.ker := by
      intro h12
      exact h2 (ker_le_of_ker_kron_le_right ρ₁ σ₁ ρ₂ σ₂ h12)
    simp [SandwichedRelRentropy, h1, h2, h12]
  · have h12 : ¬ (σ₁ ⊗ᴹ σ₂).M.ker ≤ (ρ₁ ⊗ᴹ ρ₂).M.ker := by
      intro h12
      exact h1 (ker_le_of_ker_kron_le_left ρ₁ σ₁ ρ₂ σ₂ h12)
    simp [SandwichedRelRentropy, h1, h2, h12]
  · have h12 : ¬ (σ₁ ⊗ᴹ σ₂).M.ker ≤ (ρ₁ ⊗ᴹ ρ₂).M.ker := by
      intro h12
      exact h1 (ker_le_of_ker_kron_le_left ρ₁ σ₁ ρ₂ σ₂ h12)
    simp [SandwichedRelRentropy, h1, h2, h12]

end additivity

/-- The quantum relative entropy is additive when the inputs are product states -/
@[simp]
theorem qRelativeEnt_additive (ρ₁ σ₁ : MState d₁) (ρ₂ σ₂ : MState d₂) :
    𝐃(ρ₁ ⊗ᴹ ρ₂‖σ₁ ⊗ᴹ σ₂) = 𝐃(ρ₁‖σ₁) + 𝐃(ρ₂‖σ₂) := by
  --or `simp [SandwichedRelRentropy]`.
  exact sandwichedRelRentropy_additive_alpha_one ρ₁ σ₁ ρ₂ σ₂

@[simp]
theorem sandwichedRelRentropy_relabel (ρ σ : MState d) (e : d₂ ≃ d) :
    D̃_ α(ρ.relabel e‖σ.relabel e) = D̃_ α(ρ‖σ) := by
  simp only [SandwichedRelRentropy, MState.relabel_M]
  rw! [HermitianMat.ker_reindex_le_iff] --Why doesn't this `simp`? Because it's an if condition, I'm guessing
  simp [HermitianMat.conj_submatrix]

@[simp]
theorem sandwichedRelRentropy_self (hα : 0 < α) (ρ : MState d) :
  --Technically this holds for all α except for `-1` and `0`. But those are stupid.
  --TODO: Maybe SandwichedRelRentropy should actually be defined differently for α = 0?
    D̃_ α(ρ‖ρ) = 0 := by
  have htrace :
      ((ρ.M.conj (ρ.M ^ ((1 - α) / (2 * α))).mat) ^ α).trace = 1 := by
    rw [HermitianMat.pow_eq_cfc, HermitianMat.pow_eq_cfc]
    nth_rw 2 [← HermitianMat.cfc_id ρ.M]
    rw [HermitianMat.cfc_conj, ← HermitianMat.cfc_comp]
    conv =>
      enter [1, 1]
      equals ρ.M.cfc id =>
        apply HermitianMat.cfc_congr_of_zero_le ρ.zero_le
        intro i (hi : 0 ≤ i)
        simp
        rw [← Real.rpow_mul_natCast hi, ← Real.rpow_one_add' hi]
        · rw [← Real.rpow_mul hi]
          field_simp
          ring_nf
          exact Real.rpow_one i
        · field_simp
          ring_nf
          positivity
    simp
  simp [SandwichedRelRentropy, htrace]

@[aesop (rule_sets := [finiteness]) unsafe apply]
theorem sandwichedRelEntropy_ne_top {ρ σ : MState d} [σ.M.NonSingular] : D̃_ α(ρ‖σ) ≠ ⊤ := by
  simp [SandwichedRelRentropy, HermitianMat.nonSingular_ker_bot]

/-- Quantum relative entropy as `Tr[ρ (log ρ - log σ)]` when supports are correct. -/
theorem qRelativeEnt_ker {ρ σ : MState d} (h : σ.M.ker ≤ ρ.M.ker) :
    𝐃(ρ‖σ).toEReal = ⟪ρ.M, ρ.M.log - σ.M.log⟫ := by
  simp [qRelativeEnt, SandwichedRelRentropy, h, inner_log_sub_log_nonneg]

open Classical in
theorem qRelativeEnt_eq_neg_Sᵥₙ_add (ρ σ : MState d) :
    (qRelativeEnt ρ σ).toEReal = -(Sᵥₙ ρ : EReal) +
      if σ.M.ker ≤ ρ.M.ker then (-⟪ρ.M, σ.M.log⟫ : EReal) else (⊤ : EReal) := by
  by_cases h : σ.M.ker ≤ ρ.M.ker
  · simp [h, Sᵥₙ_eq_neg_trace_log, qRelativeEnt_ker, inner_sub_right]
    rw [real_inner_comm, sub_eq_add_neg]
  · simp [h]
    exact dif_neg h

/-- The quantum relative entropy is unchanged by `MState.relabel` -/
@[simp]
theorem qRelativeEnt_relabel (ρ σ : MState d) (e : d₂ ≃ d) :
    𝐃(ρ.relabel e‖σ.relabel e) = 𝐃(ρ‖σ) := by
  simp [qRelativeEnt]

@[simp]
theorem sandwichedRelRentropy_of_unique [Unique d] (ρ σ : MState d) :
    D̃_α(ρ‖σ) = 0 := by
  rcases Subsingleton.allEq ρ default
  rcases Subsingleton.allEq σ default
  simp [SandwichedRelRentropy]

@[simp]
theorem qRelEntropy_of_unique [Unique d] (ρ σ : MState d) :
    𝐃(ρ‖σ) = 0 := by
  exact sandwichedRelRentropy_of_unique ρ σ

theorem sandwichedRelRentropy_heq_congr
      {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
      {ρ₁ σ₁ : MState d₁} {ρ₂ σ₂ : MState d₂} (hd : d₁ = d₂) (hρ : ρ₁ ≍ ρ₂) (hσ : σ₁ ≍ σ₂) :
    D̃_ α(ρ₁‖σ₁) = D̃_ α(ρ₂‖σ₂) := by
  --Why does this thm need to exist? Why not just `subst d₁` and `simp [heq_eq_eq]`? Well, even though d₁
  --and d₂ are equal, we then end up with two distinct instances of `Fintype d₁` and `DecidableEq d₁`,
  --and ρ₁ and ρ₂ refer to them each and so have different types. And then we'd need to `subst` those away
  --too. This is kind of tedious, so it's better to just have this theorem around.
  rw [heq_iff_exists_eq_cast] at hρ hσ
  obtain ⟨_, rfl⟩ := hρ
  obtain ⟨_, rfl⟩ := hσ
  simp [← MState.relabel_cast _ hd]

@[gcongr]
theorem sandwichedRelRentropy_congr {α : ℝ}
      {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
      {ρ₁ σ₁ : MState d₁} {ρ₂ σ₂ : MState d₂} (hd : d₁ = d₂)
        (hρ : ρ₁ = ρ₂.relabel (Equiv.cast hd)) (hσ : σ₁ = σ₂.relabel (Equiv.cast hd)) :
    D̃_ α(ρ₁‖σ₁) = D̃_ α(ρ₂‖σ₂) := by
  subst ρ₁ σ₁
  simp

@[gcongr]
theorem qRelEntropy_heq_congr {d₁ d₂ : Type u} [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂]
      {ρ₁ σ₁ : MState d₁} {ρ₂ σ₂ : MState d₂} (hd : d₁ = d₂) (hρ : ρ₁ ≍ ρ₂) (hσ : σ₁ ≍ σ₂) :
    𝐃(ρ₁‖σ₁) = 𝐃(ρ₂‖σ₂) := by
  exact sandwichedRelRentropy_heq_congr hd hρ hσ

/-- Quantum relative entropy when `σ` has full rank. -/
theorem qRelativeEnt_rank {ρ σ : MState d} [σ.M.NonSingular] :
    (𝐃(ρ‖σ) : EReal) = ⟪ρ.M, ρ.M.log - σ.M.log⟫ := by
  apply qRelativeEnt_ker
  simp [HermitianMat.nonSingular_ker_bot]

@[simp]
theorem qRelEntropy_self (ρ : MState d) : 𝐃(ρ‖ρ) = 0 := by
  simp [qRelativeEnt]

@[aesop (rule_sets := [finiteness]) unsafe apply]
theorem qRelativeEnt_ne_top {ρ σ : MState d} [σ.M.NonSingular] : 𝐃(ρ‖σ) ≠ ⊤ := by
  rw [qRelativeEnt]
  finiteness
