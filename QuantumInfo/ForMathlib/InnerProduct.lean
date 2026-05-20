import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Inner-product geometry helpers

These lemmas package elementary facts about the kernel
`1 - ‖⟪ψ, φ⟫‖ ^ 2` and the projection of a vector onto the orthogonal
complement of a normalized vector.
-/

open scoped InnerProductSpace

namespace InnerProductGeometry

/-- For normalized vectors, `1 - ‖⟪ψ, φ⟫‖ ^ 2` lies in `[0, 1]`. -/
theorem kernel_from_inner_product
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ψ φ : V) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    0 ≤ 1 - ‖@inner ℂ V _ ψ φ‖ ^ 2 ∧
    1 - ‖@inner ℂ V _ ψ φ‖ ^ 2 ≤ 1 := by
  constructor
  · have hcs := norm_inner_le_norm (𝕜 := ℂ) ψ φ
    rw [hψ, hφ, mul_one] at hcs
    have hsq : ‖@inner ℂ V _ ψ φ‖ ^ 2 ≤ 1 := by
      rw [sq_le_one_iff₀ (norm_nonneg _)]
      exact hcs
    linarith
  · linarith [sq_nonneg (‖@inner ℂ V _ ψ φ‖)]

/-- The kernel vanishes on a normalized vector paired with itself. -/
theorem kernel_reflexive
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ψ : V) (hψ : ‖ψ‖ = 1) :
    1 - ‖@inner ℂ V _ ψ ψ‖ ^ 2 = 0 := by
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
  simp [hψ]

/-- The kernel is symmetric. -/
theorem kernel_symmetric
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ψ φ : V) :
    1 - ‖@inner ℂ V _ ψ φ‖ ^ 2 = 1 - ‖@inner ℂ V _ φ ψ‖ ^ 2 := by
  congr 1
  rw [sq, sq, norm_inner_symm]

/-- Kernel value `1` implies orthogonality. -/
theorem kernel_eq_one_implies_orthogonal
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ψ φ : V) (hK : 1 - ‖@inner ℂ V _ ψ φ‖ ^ 2 = 1) :
    @inner ℂ V _ ψ φ = 0 := by
  have hsq : ‖@inner ℂ V _ ψ φ‖ ^ 2 = 0 := by linarith
  have hnorm : ‖@inner ℂ V _ ψ φ‖ = 0 := by
    exact_mod_cast sq_eq_zero_iff.mp hsq
  exact norm_eq_zero.mp hnorm

/-- Orthogonality implies kernel value `1`. -/
theorem orthogonal_implies_kernel_eq_one
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ψ φ : V) (horth : @inner ℂ V _ ψ φ = 0) :
    1 - ‖@inner ℂ V _ ψ φ‖ ^ 2 = 1 := by
  rw [horth, norm_zero, sq, mul_zero, sub_zero]

/-- Kernel value `1` is equivalent to orthogonality. -/
theorem kernel_eq_one_iff_orthogonal
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ψ φ : V) :
    1 - ‖@inner ℂ V _ ψ φ‖ ^ 2 = 1 ↔ @inner ℂ V _ ψ φ = 0 :=
  ⟨kernel_eq_one_implies_orthogonal ψ φ, orthogonal_implies_kernel_eq_one ψ φ⟩

/-- For the standard basis of `EuclideanSpace ℂ (Fin n)`, the kernel is `1 - δᵢⱼ`. -/
theorem kernel_standard_basis (n : ℕ) (i j : Fin n) :
    1 - ‖@inner ℂ (EuclideanSpace ℂ (Fin n)) _
      (EuclideanSpace.single i (1 : ℂ))
      (EuclideanSpace.single j (1 : ℂ))‖ ^ 2 =
    if i = j then (0 : ℝ) else 1 := by
  have hON := EuclideanSpace.orthonormal_single (𝕜 := ℂ) (ι := Fin n)
  have hinner := orthonormal_iff_ite.mp hON i j
  rw [hinner]
  split <;> simp

/-- The squared norm of the component of `ψ` orthogonal to normalized `φ`. -/
theorem projection_norm_sq
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ψ φ : V) (hφ : ‖φ‖ = 1) :
    ‖ψ - (@inner ℂ V _ φ ψ) • φ‖ ^ 2 = ‖ψ‖ ^ 2 - ‖@inner ℂ V _ φ ψ‖ ^ 2 := by
  set c := @inner ℂ V _ φ ψ with hc_def
  rw [norm_sub_sq (𝕜 := ℂ)]
  have h_inner_smul : @inner ℂ V _ ψ (c • φ) = c * @inner ℂ V _ ψ φ :=
    inner_smul_right ψ φ c
  have h_conj : @inner ℂ V _ ψ φ = starRingEnd ℂ c := by
    rw [hc_def]
    exact (@inner_conj_symm ℂ V _ _ _ ψ φ).symm
  have h_mul_conj : c * starRingEnd ℂ c = ↑‖c‖ ^ 2 := RCLike.mul_conj c
  have h_norm_smul : ‖c • φ‖ ^ 2 = ‖c‖ ^ 2 := by
    rw [norm_smul, mul_pow, hφ, one_pow, mul_one]
  rw [h_inner_smul, h_conj, h_mul_conj, h_norm_smul]
  have hre : RCLike.re ((↑‖c‖ : ℂ) ^ 2) = ‖c‖ ^ 2 :=
    RCLike.re_ofReal_pow ‖c‖ 2
  rw [hre]
  ring

/-- For normalized vectors, the kernel equals the squared distance from `ψ`
to the ray through `φ`. -/
theorem kernel_eq_projection_distance
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ψ φ : V) (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) :
    1 - ‖@inner ℂ V _ φ ψ‖ ^ 2 = ‖ψ - (@inner ℂ V _ φ ψ) • φ‖ ^ 2 := by
  rw [projection_norm_sq ψ φ hφ, hψ, one_pow]

/-- The projected residual is orthogonal to the normalized vector being projected onto. -/
theorem projection_orthogonal
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (ψ φ : V) (hφ : ‖φ‖ = 1) :
    @inner ℂ V _ φ (ψ - (@inner ℂ V _ φ ψ) • φ) = 0 := by
  rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
  simp [hφ]

end InnerProductGeometry
