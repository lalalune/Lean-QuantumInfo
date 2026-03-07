/-
Copyright (c) 2026. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Antigravity
-/
import Mathlib
import QuantumInfo.ForMathlib.CauchyBinet

open Matrix BigOperators Finset

variable {R : Type*} [CommRing R]

namespace Matrix

/-- The `k`-th compound matrix of an `n x m` matrix. It is indexed by subsets of size `k`. -/
noncomputable def compound {n m : ℕ} (k : ℕ) (A : Matrix (Fin n) (Fin m) R) :
    Matrix (subsets n k) (subsets m k) R := fun I J => 
  (A.submatrix (subset_order_fun I.val (Finset.mem_filter.mp I.property).2) 
               (subset_order_fun J.val (Finset.mem_filter.mp J.property).2)).det

lemma compound_mul {n m p : ℕ} {k : ℕ} (A : Matrix (Fin n) (Fin m) R) (B : Matrix (Fin m) (Fin p) R) :
    compound k (A * B) = compound k A * compound k B := by
  ext I J
  simp only [compound, Matrix.mul_apply]
  -- Let f = subset_order_fun for I, g = subset_order_fun for J
  let f := subset_order_fun I.val (Finset.mem_filter.mp I.property).2
  let g := subset_order_fun J.val (Finset.mem_filter.mp J.property).2
  -- (A * B).submatrix f g = A.submatrix f id * B.submatrix id g by submatrix_mul
  have h1 : (A * B).submatrix f g = A.submatrix f id * B.submatrix id g := by
    rw [submatrix_mul A B f id g Function.bijective_id]
  rw [h1]
  -- Now apply Cauchy-Binet: det(A' * B') = ∑ S, det(A'.submatrix id order_S) * det(B'.submatrix order_S id)
  rw [cauchy_binet]
  -- The sum is over subsets of m of size k
  apply Finset.sum_congr rfl
  intro K _
  -- Show that each term matches
  -- det((A.submatrix f id).submatrix id (order K)) = det(A.submatrix f (order K))
  -- det((B.submatrix id g).submatrix (order K) id) = det(B.submatrix (order K) g)
  have hA : (A.submatrix f id).submatrix id (subset_order_fun K.val (Finset.mem_filter.mp K.property).2) =
            A.submatrix f (subset_order_fun K.val (Finset.mem_filter.mp K.property).2) := by
    simp [submatrix_submatrix]
  have hB : (B.submatrix id g).submatrix (subset_order_fun K.val (Finset.mem_filter.mp K.property).2) id =
            B.submatrix (subset_order_fun K.val (Finset.mem_filter.mp K.property).2) g := by
    simp [submatrix_submatrix]
  rw [hA, hB]

-- Adjoint preserves compound matrices
lemma compound_conjTranspose {n m k : ℕ} (A : Matrix (Fin n) (Fin m) ℂ) :
    compound k (Aᴴ) = (compound k A)ᴴ := by
  ext I J
  simp only [compound, conjTranspose_apply]
  -- LHS: det((Aᴴ).submatrix f g) where f = subset_order_fun I, g = subset_order_fun J
  -- conjTranspose_submatrix says (A.submatrix r c)ᴴ = Aᴴ.submatrix c r
  -- So Aᴴ.submatrix f g = (A.submatrix g f)ᴴ
  simp only [← conjTranspose_submatrix]
  -- Now we have det((A.submatrix (subset_order_fun J ...) (subset_order_fun I ...))ᴴ)
  -- Using det_conjTranspose: det(Mᴴ) = star(det M)
  rw [det_conjTranspose]
  -- This gives star(det(A.submatrix ... ...)) which matches RHS

-- If A is Hermitian, compound A is Hermitian
lemma compound_isHermitian {n k : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (h : A.IsHermitian) :
    (compound k A).IsHermitian := by
  -- IsHermitian means (compound k A)ᴴ = compound k A
  rw [Matrix.IsHermitian, ← compound_conjTranspose, h.eq]

end Matrix
