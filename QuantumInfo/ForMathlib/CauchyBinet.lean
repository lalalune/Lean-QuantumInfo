import Mathlib
import Mathlib.LinearAlgebra.Alternating.Basic

open Matrix BigOperators Finset Equiv Function

variable {R : Type*} [CommRing R]

namespace Matrix

local notation "ε " σ:arg => ((Perm.sign σ : ℤ) : R)

theorem det_mul_aux_rect {m n : ℕ} [DecidableEq (Fin m)] [DecidableEq (Fin n)] 
    {M : Matrix (Fin m) (Fin n) R} {N : Matrix (Fin n) (Fin m) R} {p : Fin m → Fin n} (H : ¬Function.Injective p) :
    (∑ σ : Perm (Fin m), ε σ * ∏ x, M (σ x) (p x) * N (p x) x) = 0 := by
  obtain ⟨i, j, hij1, hij2⟩ : ∃ i j, p i = p j ∧ i ≠ j := by
    by_contra h
    push_neg at h
    exact H h
  exact
    sum_involution (fun σ _ => σ * Equiv.swap i j)
      (fun σ _ => by
        have : (∏ x, M (σ x) (p x)) = ∏ x, M ((σ * Equiv.swap i j) x) (p x) :=
          Fintype.prod_equiv (Equiv.swap i j) _ _ (by simp [Equiv.apply_swap_eq_self hij1])
        simp [this, Perm.sign_swap hij2, -Equiv.Perm.sign_swap', prod_mul_distrib])
      (fun σ _ _ => (not_congr mul_swap_eq_iff).mpr hij2) 
      (fun _ _ => mem_univ _) 
      (fun σ _ => mul_swap_involutive i j σ)

/-- The subset index domain sum transformation step. -/
theorem det_mul_eq_sum_injective_functions {m n : ℕ} (M : Matrix (Fin m) (Fin n) R) (N : Matrix (Fin n) (Fin m) R) :
    (M * N).det = ∑ p ∈ (Finset.univ : Finset (Fin m → Fin n)).filter Injective, 
      ∑ σ : Perm (Fin m), ε σ * ∏ i, M (σ i) (p i) * N (p i) i := by
  calc
    (M * N).det = ∑ p : Fin m → Fin n, ∑ σ : Perm (Fin m), ε σ * ∏ i, M (σ i) (p i) * N (p i) i := by
      simp only [Matrix.det_apply', Matrix.mul_apply, prod_univ_sum, mul_sum, Fintype.piFinset_univ]
      rw [Finset.sum_comm]
    _ = ∑ p ∈ (Finset.univ : Finset (Fin m → Fin n)).filter Injective, ∑ σ : Perm (Fin m), ε σ * ∏ i, M (σ i) (p i) * N (p i) i := by
      refine (sum_subset (filter_subset _ _) fun p _ hinj ↦ det_mul_aux_rect ?_).symm
      simpa only [mem_filter, mem_univ, true_and] using hinj

/-- The set of subsets of size m in Fin n -/
def subsets (n m : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Finset (Fin n))).filter (fun s => s.card = m)

/-- A concrete choice of ordering for each subset. -/
noncomputable def subset_order_fun {n m : ℕ} (s : Finset (Fin n)) (hs : s.card = m) : Fin m → Fin n :=
  fun j => (s.orderIsoOfFin hs j).val

/--
Cauchy Binet formula for `m x n` times `n x m` matrices where `m` is the subset size.
This expresses it using subset sums and determinants.

The proof partitions injective functions p : Fin m → Fin n by their range S:
- For each k-element subset S, the injective functions with range S are exactly
  compositions (subset_order_fun S) ∘ τ for permutations τ.
- The sum over (S, τ, σ) can be factored into det(A_S) * det(B_S).
-/
lemma cauchy_binet {n m : ℕ} (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin m) R) :
    (A * B).det = ∑ s ∈ (subsets n m).attach,
      (A.submatrix id (subset_order_fun s.val (Finset.mem_filter.mp s.property).2)).det *
      (B.submatrix (subset_order_fun s.val (Finset.mem_filter.mp s.property).2) id).det := by
  let InjectiveFns (n m : ℕ) := {p : Fin m → Fin n // Injective p}
  let SubsetPerms (n m : ℕ) := {s // s ∈ subsets n m} × Perm (Fin m)

  have hsubset_order_fun_injective :
      ∀ {n m : ℕ} (s : Finset (Fin n)) (hs : s.card = m),
        Function.Injective (subset_order_fun s hs) := by
    intro n m s hs i j hij
    apply (s.orderIsoOfFin hs).injective
    apply Subtype.ext
    simpa [subset_order_fun] using hij

  have himage_subset_order_fun_univ :
      ∀ {n m : ℕ} (s : Finset (Fin n)) (hs : s.card = m),
        Finset.image (subset_order_fun s hs) Finset.univ = s := by
    intro n m s hs
    apply Finset.coe_injective
    ext x
    constructor
    · intro hx
      rcases Finset.mem_image.mp hx with ⟨i, -, rfl⟩
      exact (s.orderIsoOfFin hs i).2
    · intro hx
      refine Finset.mem_image.mpr ?_
      refine ⟨(s.orderIsoOfFin hs).symm ⟨x, hx⟩, Finset.mem_univ _, ?_⟩
      exact congrArg Subtype.val ((s.orderIsoOfFin hs).apply_symm_apply ⟨x, hx⟩)

  let injectiveToSubsetPermFun :
      ∀ {n m : ℕ}, InjectiveFns n m → SubsetPerms n m := by
    intro n m p
    let s : Finset (Fin n) := Finset.image p.1 Finset.univ
    have hs_card : s.card = m := by
      simpa [s] using (Finset.card_image_of_injective Finset.univ p.2)
    have hs_mem : s ∈ subsets n m := by
      simp [subsets, hs_card]
    let τf : Fin m → Fin m := fun i =>
      (s.orderIsoOfFin hs_card).symm ⟨p.1 i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
    have hτf_inj : Injective τf := by
      intro i j hij
      apply p.2
      have hi : subset_order_fun s hs_card (τf i) = p.1 i := by
        exact congrArg Subtype.val ((s.orderIsoOfFin hs_card).apply_symm_apply
          ⟨p.1 i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩)
      have hj : subset_order_fun s hs_card (τf j) = p.1 j := by
        exact congrArg Subtype.val ((s.orderIsoOfFin hs_card).apply_symm_apply
          ⟨p.1 j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩)
      rw [← hi, ← hj, hij]
    exact (⟨s, hs_mem⟩, Equiv.ofBijective τf ((Finite.injective_iff_bijective).mp hτf_inj))

  let subsetPermToInjectiveFun :
      ∀ {n m : ℕ}, SubsetPerms n m → InjectiveFns n m := by
    intro n m st
    refine ⟨subset_order_fun st.1.1 (Finset.mem_filter.mp st.1.2).2 ∘ st.2, ?_⟩
    exact (hsubset_order_fun_injective _ _).comp st.2.injective

  have hsubsetPermToInjectiveFun_bijective :
      ∀ {n m : ℕ}, Function.Bijective (subsetPermToInjectiveFun (n := n) (m := m)) := by
    intro n m
    constructor
    · intro st₁ st₂ h
      rcases st₁ with ⟨S, τ⟩
      rcases st₂ with ⟨T, ρ⟩
      have hfun : subset_order_fun S.1 (Finset.mem_filter.mp S.2).2 ∘ τ =
          subset_order_fun T.1 (Finset.mem_filter.mp T.2).2 ∘ ρ := congrArg Subtype.val h
      have himage :
          Finset.image (subset_order_fun S.1 (Finset.mem_filter.mp S.2).2 ∘ τ) Finset.univ =
          Finset.image (subset_order_fun T.1 (Finset.mem_filter.mp T.2).2 ∘ ρ) Finset.univ := by
        exact congrArg (fun p : Fin m → Fin n => Finset.image p Finset.univ) hfun
      have hS0 : S.1 = T.1 := by
        rw [← Finset.image_image, Finset.image_univ_equiv, himage_subset_order_fun_univ] at himage
        rw [← Finset.image_image, Finset.image_univ_equiv, himage_subset_order_fun_univ] at himage
        exact himage
      have hS : S = T := Subtype.ext hS0
      subst hS
      have hτρ : τ = ρ := by
        ext i
        exact congrArg Fin.val ((hsubset_order_fun_injective _ _) (congrFun hfun i))
      simp [hτρ]
    · intro p
      refine ⟨injectiveToSubsetPermFun p, ?_⟩
      ext i
      simp [injectiveToSubsetPermFun, subsetPermToInjectiveFun, subset_order_fun]

  have hpermToInjectiveSelf_bijective :
      ∀ {m : ℕ},
        Function.Bijective
          (fun τ : Perm (Fin m) => (⟨(τ : Fin m → Fin m), τ.injective⟩ : InjectiveFns m m)) := by
    intro m
    constructor
    · intro τ ρ h
      ext i
      exact congrArg Fin.val (congrFun (congrArg Subtype.val h) i)
    · intro p
      refine ⟨Equiv.ofBijective p.1 ((Finite.injective_iff_bijective).mp p.2), ?_⟩
      ext i
      rfl

  have hsum_over_perms_eq_submatrix_det_product :
      ∀ {n m : ℕ} (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin m) R)
        (s : {s // s ∈ subsets n m}),
        (∑ τ : Perm (Fin m),
          ∑ σ : Perm (Fin m), ε σ *
            ∏ i, A (σ i) ((subset_order_fun s.1 (Finset.mem_filter.mp s.2).2 ∘ τ) i) *
              B (((subset_order_fun s.1 (Finset.mem_filter.mp s.2).2 ∘ τ) i)) i)
          = (A.submatrix id (subset_order_fun s.1 (Finset.mem_filter.mp s.2).2)).det *
              (B.submatrix (subset_order_fun s.1 (Finset.mem_filter.mp s.2).2) id).det := by
    intro n m A B s
    let ord := subset_order_fun s.1 (Finset.mem_filter.mp s.2).2
    let As : Matrix (Fin m) (Fin m) R := A.submatrix id ord
    let Bs : Matrix (Fin m) (Fin m) R := B.submatrix ord id
    calc
      (∑ τ : Perm (Fin m),
        ∑ σ : Perm (Fin m), ε σ * ∏ i, A (σ i) (ord (τ i)) * B (ord (τ i)) i)
          = ∑ p : InjectiveFns m m,
              ∑ σ : Perm (Fin m), ε σ * ∏ i, As (σ i) (p.1 i) * Bs (p.1 i) i := by
            exact Fintype.sum_bijective
              (fun τ : Perm (Fin m) => (⟨(τ : Fin m → Fin m), τ.injective⟩ : InjectiveFns m m))
              hpermToInjectiveSelf_bijective
              (fun τ => ∑ σ : Perm (Fin m), ε σ * ∏ i, A (σ i) (ord (τ i)) * B (ord (τ i)) i)
              (fun p => ∑ σ : Perm (Fin m), ε σ * ∏ i, As (σ i) (p.1 i) * Bs (p.1 i) i)
              (by intro τ; simp [As, Bs, ord])
      _ = ∑ p ∈ (Finset.univ : Finset (Fin m → Fin m)).filter Injective,
            ∑ σ : Perm (Fin m), ε σ * ∏ i, As (σ i) (p i) * Bs (p i) i := by
            change
              (∑ p : {p : Fin m → Fin m // Injective p},
                ∑ σ : Perm (Fin m), ε σ * ∏ i, As (σ i) (p.1 i) * Bs (p.1 i) i)
                = ∑ p ∈ (Finset.univ : Finset (Fin m → Fin m)).filter Injective,
                    ∑ σ : Perm (Fin m), ε σ * ∏ i, As (σ i) (p i) * Bs (p i) i
            rw [← Finset.sum_subtype_eq_sum_filter]
            simp only [subtype_univ]
      _ = (As * Bs).det := by
            symm
            exact det_mul_eq_sum_injective_functions As Bs
      _ = As.det * Bs.det := by
            rw [Matrix.det_mul]
      _ = (A.submatrix id ord).det * (B.submatrix ord id).det := by
            rfl

  rw [det_mul_eq_sum_injective_functions, ← Finset.sum_subtype_eq_sum_filter]
  simp only [subtype_univ]
  calc
    ∑ p : InjectiveFns n m, ∑ σ : Perm (Fin m), ε σ * ∏ i, A (σ i) (p.1 i) * B (p.1 i) i
      = ∑ st : SubsetPerms n m,
          ∑ σ : Perm (Fin m), ε σ *
            ∏ i, A (σ i) ((subsetPermToInjectiveFun st).1 i) * B ((subsetPermToInjectiveFun st).1 i) i := by
          symm
          exact Fintype.sum_bijective (subsetPermToInjectiveFun (n := n) (m := m))
            hsubsetPermToInjectiveFun_bijective
            (fun st => ∑ σ : Perm (Fin m), ε σ *
              ∏ i, A (σ i) ((subsetPermToInjectiveFun st).1 i) * B ((subsetPermToInjectiveFun st).1 i) i)
            (fun p => ∑ σ : Perm (Fin m), ε σ * ∏ i, A (σ i) (p.1 i) * B (p.1 i) i)
            (by intro st; rfl)
    _ = ∑ s : {s // s ∈ subsets n m},
          ∑ τ : Perm (Fin m),
            ∑ σ : Perm (Fin m), ε σ *
              ∏ i, A (σ i) ((subset_order_fun s.1 (Finset.mem_filter.mp s.2).2 ∘ τ) i) *
                B (((subset_order_fun s.1 (Finset.mem_filter.mp s.2).2 ∘ τ) i)) i := by
          rw [Fintype.sum_prod_type]
    _ = ∑ s : {s // s ∈ subsets n m},
          (A.submatrix id (subset_order_fun s.1 (Finset.mem_filter.mp s.2).2)).det *
          (B.submatrix (subset_order_fun s.1 (Finset.mem_filter.mp s.2).2) id).det := by
          refine Fintype.sum_congr _ _ ?_
          intro s
          exact hsum_over_perms_eq_submatrix_det_product A B s
    _ = ∑ s ∈ (subsets n m).attach,
          (A.submatrix id (subset_order_fun s.val (Finset.mem_filter.mp s.property).2)).det *
          (B.submatrix (subset_order_fun s.val (Finset.mem_filter.mp s.property).2) id).det := by
          simp

end Matrix
