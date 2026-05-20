/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.Finite.CPTPMap
import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm

noncomputable section

open BigOperators
open ComplexConjugate
open Kronecker
open scoped Matrix ComplexOrder

variable {d d₂ : Type*} [Fintype d] [DecidableEq d] [Fintype d₂] (ρ σ : MState d)

--We put all of the fidelity defs and theorems in the MState namespace so that they have the
--nice . syntax, i.e. `ρ.fidelity σ = 1 ↔ ρ = σ`.
namespace MState

/-- The fidelity of two quantum states. This is the quantum version of the Bhattacharyya coefficient. -/
def fidelity (ρ σ : MState d) : ℝ :=
  ((σ.M.conj ρ.M.sqrt.mat) ^ (1/2 : ℝ)).trace

theorem fidelity_ge_zero : 0 ≤ fidelity ρ σ := by
  -- Apply `HermitianMat.trace_nonneg` to the term inside the square root.
    have h_trace_nonneg : 0 ≤ (σ.M.conj ρ.M.sqrt.mat) ^ (1 / 2 : ℝ) := by
      apply HermitianMat.rpow_nonneg
      apply HermitianMat.conj_nonneg _ σ.zero_le
    -- Apply the fact that the trace of a positive semidefinite matrix is non-negative.
    apply HermitianMat.trace_nonneg; assumption

--PULLOUT, CLEANUP
/-
The square root of the positive semidefinite matrix of a state `ρ` is equal to `ρ` raised to the power of 1/2.
-/
theorem pos_sqrt_eq_rpow {d : Type*} [Fintype d] [DecidableEq d] (ρ : MState d) :
    ρ.M.sqrt.mat = (ρ.M ^ (1/2 : ℝ)).mat := by
  rw [HermitianMat.sqrt_eq_cfc_rpow_half, HermitianMat.rpow_eq_cfc]

private theorem traceNorm_eq_sum_sqrt_eigenvalues (A : Matrix d d ℂ) :
    A.traceNorm =
      ∑ i : d, Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues i) := by
  open MatrixOrder in
  let H : HermitianMat d ℂ := ⟨Aᴴ * A, Matrix.isHermitian_conjTranspose_mul_self A⟩
  have hH_nonneg : 0 ≤ H.mat := by
    exact Matrix.nonneg_iff_posSemidef.mpr (Matrix.posSemidef_conjTranspose_mul_self A)
  have hsqrt : CFC.sqrt (Aᴴ * A) = (H.cfc Real.sqrt).mat := by
    change CFC.sqrt H.mat = (H.cfc Real.sqrt).mat
    rw [HermitianMat.mat_cfc]
    rw [← cfcₙ_eq_cfc, ← CFC.sqrt_eq_real_sqrt H.mat hH_nonneg]
  calc
    A.traceNorm = RCLike.re ((CFC.sqrt (Aᴴ * A)).trace) := rfl
    _ = RCLike.re (((H.cfc Real.sqrt).mat).trace) := by rw [hsqrt]
    _ = (H.cfc Real.sqrt).trace := by rw [← HermitianMat.trace_eq_re_trace]
    _ = ∑ i : d, Real.sqrt (H.H.eigenvalues i) := H.trace_cfc_eq Real.sqrt

private theorem traceNorm_conjTranspose (A : Matrix d d ℂ) :
    Aᴴ.traceNorm = A.traceNorm := by
  rw [traceNorm_eq_sum_sqrt_eigenvalues (A := Aᴴ),
    traceNorm_eq_sum_sqrt_eigenvalues (A := A)]
  have h_eigenvalues :
      (Matrix.isHermitian_conjTranspose_mul_self Aᴴ).eigenvalues =
        (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues := by
    rw [Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff]
    change (Aᴴᴴ * Aᴴ).charpoly = (Aᴴ * A).charpoly
    simpa using Matrix.charpoly_mul_comm A Aᴴ
  rw [h_eigenvalues]

private theorem traceNorm_unitary_conj (A : Matrix d d ℂ) (U : 𝐔[d]) :
    (U.val * A * (U.val)ᴴ).traceNorm = A.traceNorm := by
  have hUstarU : (U.val)ᴴ * U.val = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using U.2.1
  rw [traceNorm_eq_sum_sqrt_eigenvalues (A := U.val * A * (U.val)ᴴ),
    traceNorm_eq_sum_sqrt_eigenvalues (A := A)]
  have h_mul :
      (U.val * A * (U.val)ᴴ)ᴴ * (U.val * A * (U.val)ᴴ) =
        U.val * (Aᴴ * A) * (U.val)ᴴ := by
    calc
      (U.val * A * (U.val)ᴴ)ᴴ * (U.val * A * (U.val)ᴴ)
          = (U.val * Aᴴ * (U.val)ᴴ) * (U.val * A * (U.val)ᴴ) := by
              simp [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = U.val * (Aᴴ * ((U.val)ᴴ * (U.val * (A * (U.val)ᴴ)))) := by
              simp [Matrix.mul_assoc]
      _ = U.val * (Aᴴ * (((U.val)ᴴ * U.val) * (A * (U.val)ᴴ))) := by
              rw [Matrix.mul_assoc]
      _ = U.val * (Aᴴ * (A * (U.val)ᴴ)) := by
              rw [hUstarU]
              simp
      _ = U.val * (Aᴴ * A) * (U.val)ᴴ := by
              simp [Matrix.mul_assoc]
  have h_eigenvalues :
      (Matrix.isHermitian_conjTranspose_mul_self (U.val * A * (U.val)ᴴ)).eigenvalues =
        (Matrix.isHermitian_conjTranspose_mul_self A).eigenvalues := by
    rw [Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff]
    change ((U.val * A * (U.val)ᴴ)ᴴ * (U.val * A * (U.val)ᴴ)).charpoly =
      (Aᴴ * A).charpoly
    rw [h_mul]
    rw [show U.val * (Aᴴ * A) * (U.val)ᴴ = U.val * ((Aᴴ * A) * (U.val)ᴴ) by
      simp [Matrix.mul_assoc]]
    rw [Matrix.charpoly_mul_comm]
    simp [Matrix.mul_assoc, hUstarU]
  rw [h_eigenvalues]

/-- A state has perfect fidelity with itself. -/
theorem fidelity_self_eq_one : fidelity ρ ρ = 1 := by
  -- Now use the given definition to simplify the expression.
  have h_simp : ((ρ.M.conj (ρ.M.sqrt.mat)) ^ (1/2 : ℝ)).trace =
      ((ρ.M.conj ((ρ.M ^ (1/2 : ℝ)).mat)) ^ (1/2 : ℝ)).trace := by
    rw [pos_sqrt_eq_rpow]
  have h_simp2 : (ρ.M.conj ((ρ.M ^ (1/2 : ℝ)).mat)) = ρ.M ^ (1 + 2 * (1/2) : ℝ) := by
    convert HermitianMat.conj_rpow _ _ _
    · norm_num
    · exact ρ.zero_le
    · norm_num
    · norm_num
  have h_simp3 : ((ρ.M ^ (1 + 2 * (1/2) : ℝ)) ^ (1/2 : ℝ)) = ρ.M ^ (1 : ℝ) := by
    rw [ ← HermitianMat.rpow_mul ]
    norm_num
    exact ρ.zero_le
  unfold MState.fidelity; aesop

private theorem fidelity_eq_traceNorm_half_mul (ρ σ : MState d) :
    fidelity ρ σ = (((σ.M ^ (1/2 : ℝ)).mat) * ((ρ.M ^ (1/2 : ℝ)).mat)).traceNorm := by
  open MatrixOrder in
  let X : Matrix d d ℂ := ((σ.M ^ (1/2 : ℝ)).mat) * ((ρ.M ^ (1/2 : ℝ)).mat)
  let P : HermitianMat d ℂ := σ.M.conj ρ.M.sqrt.mat
  have hP_nonneg : 0 ≤ P := by
    simpa [P] using HermitianMat.conj_nonneg ρ.M.sqrt.mat σ.zero_le
  have hX : Xᴴ * X = P.mat := by
    calc
      Xᴴ * X
          = ((ρ.M ^ (1/2 : ℝ)).mat) *
              (((σ.M ^ (1/2 : ℝ)).mat) * (((σ.M ^ (1/2 : ℝ)).mat) * ((ρ.M ^ (1/2 : ℝ)).mat))) := by
              simp [X, Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = ((ρ.M ^ (1/2 : ℝ)).mat) *
            ((((σ.M ^ (1/2 : ℝ)).mat) * ((σ.M ^ (1/2 : ℝ)).mat)) * ((ρ.M ^ (1/2 : ℝ)).mat)) := by
              simp [Matrix.mul_assoc]
      _ = ((ρ.M ^ (1/2 : ℝ)).mat) * (σ.M.mat * ((ρ.M ^ (1/2 : ℝ)).mat)) := by
              rw [HermitianMat.pow_half_mul σ.zero_le]
      _ = P.mat := by
              simp [P, pos_sqrt_eq_rpow, HermitianMat.conj_apply_mat, Matrix.mul_assoc]
  have hpow_eq : P ^ (1/2 : ℝ) = P.cfc Real.sqrt := by
    rw [HermitianMat.rpow_eq_cfc]
    exact P.cfc_congr_of_zero_le hP_nonneg (fun x hx => by rw [Real.sqrt_eq_rpow])
  have hcfc : _root_.cfc Real.sqrt P.mat = CFC.sqrt P.mat := by
    rw [← cfcₙ_eq_cfc, ← CFC.sqrt_eq_real_sqrt P.mat
      (show 0 ≤ P.mat by
        exact Matrix.nonneg_iff_posSemidef.mpr (HermitianMat.zero_le_iff.mp hP_nonneg))]
  have hmat_eq : (P ^ (1/2 : ℝ)).mat = CFC.sqrt (Xᴴ * X) := by
    rw [hpow_eq, HermitianMat.mat_cfc, hcfc, hX]
  unfold MState.fidelity Matrix.traceNorm
  rw [pos_sqrt_eq_rpow, HermitianMat.trace_eq_re_trace]
  have hPdef : σ.M.conj ((ρ.M ^ (1/2 : ℝ)).mat) = P := by
    change σ.M.conj ((ρ.M ^ (1/2 : ℝ)).mat) = σ.M.conj ρ.M.sqrt.mat
    rw [← pos_sqrt_eq_rpow]
  rw [hPdef, hmat_eq]

/-- Fidelity is symmetric in its two state arguments. -/
theorem fidelity_comm : fidelity ρ σ = fidelity σ ρ := by
  rw [fidelity_eq_traceNorm_half_mul (ρ := ρ) (σ := σ),
    fidelity_eq_traceNorm_half_mul (ρ := σ) (σ := ρ)]
  let X : Matrix d d ℂ := ((σ.M ^ (1/2 : ℝ)).mat) * ((ρ.M ^ (1/2 : ℝ)).mat)
  have hX :
      Xᴴ = ((ρ.M ^ (1/2 : ℝ)).mat) * ((σ.M ^ (1/2 : ℝ)).mat) := by
    simp [X, Matrix.conjTranspose_mul]
  calc
    (((σ.M ^ (1/2 : ℝ)).mat) * ((ρ.M ^ (1/2 : ℝ)).mat)).traceNorm
        = X.traceNorm := rfl
    _ = Xᴴ.traceNorm := (traceNorm_conjTranspose (A := X)).symm
    _ = (((ρ.M ^ (1/2 : ℝ)).mat) * ((σ.M ^ (1/2 : ℝ)).mat)).traceNorm := by rw [hX]

/-- Fidelity is invariant under applying the same unitary conjugation to both states. -/
@[simp]
theorem fidelity_U_conj (U : 𝐔[d]) : fidelity (ρ.U_conj U) (σ.U_conj U) = fidelity ρ σ := by
  rw [fidelity_eq_traceNorm_half_mul (ρ := ρ.U_conj U) (σ := σ.U_conj U),
    fidelity_eq_traceNorm_half_mul (ρ := ρ) (σ := σ)]
  have hσ :
      ((σ.U_conj U).M ^ (1/2 : ℝ)).mat =
        U.val * ((σ.M ^ (1/2 : ℝ)).mat) * (U.val)ᴴ := by
    change ((σ.M.conj U.val) ^ (1/2 : ℝ)).mat =
      U.val * ((σ.M ^ (1/2 : ℝ)).mat) * (U.val)ᴴ
    rw [HermitianMat.rpow_conj_unitary]
    rfl
  have hρ :
      ((ρ.U_conj U).M ^ (1/2 : ℝ)).mat =
        U.val * ((ρ.M ^ (1/2 : ℝ)).mat) * (U.val)ᴴ := by
    change ((ρ.M.conj U.val) ^ (1/2 : ℝ)).mat =
      U.val * ((ρ.M ^ (1/2 : ℝ)).mat) * (U.val)ᴴ
    rw [HermitianMat.rpow_conj_unitary]
    rfl
  rw [hσ, hρ]
  have hUstarU : (U.val)ᴴ * U.val = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using U.2.1
  have hprod :
      (U.val * ((σ.M ^ (1/2 : ℝ)).mat) * (U.val)ᴴ) *
          (U.val * ((ρ.M ^ (1/2 : ℝ)).mat) * (U.val)ᴴ) =
        U.val * (((σ.M ^ (1/2 : ℝ)).mat) * ((ρ.M ^ (1/2 : ℝ)).mat)) *
          (U.val)ᴴ := by
    calc
      (U.val * ((σ.M ^ (1/2 : ℝ)).mat) * (U.val)ᴴ) *
          (U.val * ((ρ.M ^ (1/2 : ℝ)).mat) * (U.val)ᴴ)
          = U.val * (((σ.M ^ (1/2 : ℝ)).mat) *
              ((U.val)ᴴ * (U.val * (((ρ.M ^ (1/2 : ℝ)).mat) * (U.val)ᴴ)))) := by
              simp [Matrix.mul_assoc]
      _ = U.val * (((σ.M ^ (1/2 : ℝ)).mat) *
            (((U.val)ᴴ * U.val) * (((ρ.M ^ (1/2 : ℝ)).mat) * (U.val)ᴴ))) := by
              rw [Matrix.mul_assoc]
      _ = U.val * (((σ.M ^ (1/2 : ℝ)).mat) *
            (((ρ.M ^ (1/2 : ℝ)).mat) * (U.val)ᴴ)) := by
              rw [hUstarU]
              simp
      _ = U.val * (((σ.M ^ (1/2 : ℝ)).mat) * ((ρ.M ^ (1/2 : ℝ)).mat)) *
          (U.val)ᴴ := by
              simp [Matrix.mul_assoc]
  rw [hprod]
  exact traceNorm_unitary_conj
    (A := ((σ.M ^ (1/2 : ℝ)).mat) * ((ρ.M ^ (1/2 : ℝ)).mat)) (U := U)

/-- The Fubini-Study angle induced by fidelity. -/
def fubiniStudyDist (ρ σ : MState d) : ℝ :=
  Real.arccos (fidelity ρ σ)

/-- The remaining triangle-inequality statement needed for the Fubini-Study metric. -/
def fubiniStudy_triangle_statement : Prop :=
  ∀ ρ σ τ : MState d,
    fubiniStudyDist ρ τ ≤ fubiniStudyDist ρ σ + fubiniStudyDist σ τ

/-- Uhlmann's theorem as the remaining purification-maximization statement. -/
def uhlmann_statement (ρ σ : MState d) : Prop :=
  IsGreatest
    {x : ℝ | ∃ ψ φ : Ket (d × d),
      (MState.pure ψ).traceRight = ρ ∧
      (MState.pure φ).traceRight = σ ∧
      x = ‖Braket.dot (ψ : Bra (d × d)) φ‖}
    (fidelity ρ σ)

end MState
