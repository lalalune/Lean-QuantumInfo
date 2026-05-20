/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/

import QuantumInfo.ForMathlib.HermitianMat.CFC
import QuantumInfo.ForMathlib.HermitianMat.Order
import QuantumInfo.ForMathlib.Misc

/-!
Facts connecting matrices, their ordering, and when they commute or not. This probably could be
reorganized to belong in other files better, but in the absence of a clear import hierarchy this
seems okay for now.
-/

variable {d 𝕜 : Type*} [Fintype d] [DecidableEq d] [RCLike 𝕜]
variable {A B : HermitianMat d 𝕜} {f g : ℝ → ℝ}

theorem Commute.exists_HermitianMat_cfc (hAB : Commute A.mat B.mat) :
    ∃ C : HermitianMat d 𝕜, (∃ f : ℝ → ℝ, A = C.cfc f) ∧ (∃ g : ℝ → ℝ, B = C.cfc g) := by
  obtain ⟨C, ⟨g₁, hg₁⟩, ⟨g₂, hg₂⟩⟩ := hAB.exists_cfc A.H B.H
  by_cases hC : C.IsHermitian
  · use ⟨C, hC⟩
    constructor
    · exact ⟨g₁, by simp [HermitianMat.ext_iff, hg₁]⟩
    · exact ⟨g₂, by simp [HermitianMat.ext_iff, hg₂]⟩
  · change ¬(IsSelfAdjoint C) at hC
    rw [cfc_apply_of_not_predicate C hC] at hg₁ hg₂
    use 0
    constructor
    · exact ⟨0, by simp [HermitianMat.ext_iff, hg₁]⟩
    · exact ⟨0, by simp [HermitianMat.ext_iff, hg₂]⟩

namespace HermitianMat

open ComplexOrder

theorem cfc_le_cfc_of_PosDef (hfg : ∀ i, 0 < i → f i ≤ g i) (hA : A.mat.PosDef) :
    A.cfc f ≤ A.cfc g := by
  rw [← sub_nonneg, ← HermitianMat.cfc_sub, HermitianMat.zero_le_cfc]
  intro i
  rw [Pi.sub_apply, sub_nonneg]
  rw [A.H.posDef_iff_eigenvalues_pos] at hA
  apply hfg
  apply hA

/-- Each scalar value used by the CFC is in the spectrum of the resulting matrix. -/
theorem spectrum_cfc_eigenvalue_mem (A : HermitianMat d 𝕜) (f : ℝ → ℝ) (i : d) :
    f (A.H.eigenvalues i) ∈ spectrum ℝ (A.cfc f).mat := by
  rw [A.spectrum_cfc_eq_image f]
  exact ⟨A.H.eigenvalues i, by
    rw [A.H.spectrum_real_eq_range_eigenvalues]
    exact Set.mem_range_self i, rfl⟩

/--
Monotonicity of the CFC for commuting Hermitian matrices, assuming `f` is monotone on a
set containing both spectra.
-/
theorem cfc_le_cfc_of_commute_monoOn_of_spectrum_subset {s : Set ℝ}
    (hf : MonotoneOn f s) (hA : spectrum ℝ A.mat ⊆ s) (hB : spectrum ℝ B.mat ⊆ s)
    (hAB₁ : Commute A.mat B.mat) (hAB₂ : A ≤ B) :
    A.cfc f ≤ B.cfc f := by
  obtain ⟨C, ⟨g₁, rfl⟩, ⟨g₂, rfl⟩⟩ := hAB₁.exists_HermitianMat_cfc
  rw [← C.cfc_comp, ← C.cfc_comp]
  rw [← sub_nonneg, ← C.cfc_sub, C.zero_le_cfc] at hAB₂ ⊢
  intro i
  simp only [Pi.sub_apply, Function.comp_apply, sub_nonneg]
  exact hf (hA (C.spectrum_cfc_eigenvalue_mem g₁ i))
    (hB (C.spectrum_cfc_eigenvalue_mem g₂ i)) (by simpa using hAB₂ i)

/--
Closed-interval specialization of `cfc_le_cfc_of_commute_monoOn_of_spectrum_subset`.
The spectral hypotheses are explicit so this can be used with any interval-bounding API.
-/
theorem cfc_le_cfc_of_commute_monoOn_Icc {a b : ℝ} (hf : MonotoneOn f (Set.Icc a b))
    (hA : spectrum ℝ A.mat ⊆ Set.Icc a b) (hB : spectrum ℝ B.mat ⊆ Set.Icc a b)
    (hAB₁ : Commute A.mat B.mat) (hAB₂ : A ≤ B) :
    A.cfc f ≤ B.cfc f :=
  cfc_le_cfc_of_commute_monoOn_of_spectrum_subset hf hA hB hAB₁ hAB₂

/-- Strictly monotone functions give the same commuting CFC order theorem. -/
theorem cfc_le_cfc_of_commute_strictMonoOn_of_spectrum_subset {s : Set ℝ}
    (hf : StrictMonoOn f s) (hA : spectrum ℝ A.mat ⊆ s) (hB : spectrum ℝ B.mat ⊆ s)
    (hAB₁ : Commute A.mat B.mat) (hAB₂ : A ≤ B) :
    A.cfc f ≤ B.cfc f :=
  cfc_le_cfc_of_commute_monoOn_of_spectrum_subset hf.monotoneOn hA hB hAB₁ hAB₂

/-- Closed-interval specialization for strictly monotone scalar functions. -/
theorem cfc_le_cfc_of_commute_strictMonoOn_Icc {a b : ℝ}
    (hf : StrictMonoOn f (Set.Icc a b)) (hA : spectrum ℝ A.mat ⊆ Set.Icc a b)
    (hB : spectrum ℝ B.mat ⊆ Set.Icc a b) (hAB₁ : Commute A.mat B.mat)
    (hAB₂ : A ≤ B) :
    A.cfc f ≤ B.cfc f :=
  cfc_le_cfc_of_commute_strictMonoOn_of_spectrum_subset hf hA hB hAB₁ hAB₂

/-- Positive-definite specialization on `(0, ∞)`. -/
theorem cfc_le_cfc_of_commute_monoOn (hf : MonotoneOn f (Set.Ioi 0))
  (hAB₁ : Commute A.mat B.mat) (hAB₂ : A ≤ B) (hA : A.mat.PosDef) (hB : B.mat.PosDef) :
    A.cfc f ≤ B.cfc f :=
  cfc_le_cfc_of_commute_monoOn_of_spectrum_subset hf (Matrix.PosDef.spectrum_subset_Ioi hA)
    (Matrix.PosDef.spectrum_subset_Ioi hB) hAB₁ hAB₂

/-- Positive-definite specialization on `(0, ∞)` for strictly monotone scalar functions. -/
theorem cfc_le_cfc_of_commute_strictMonoOn (hf : StrictMonoOn f (Set.Ioi 0))
    (hAB₁ : Commute A.mat B.mat) (hAB₂ : A ≤ B) (hA : A.mat.PosDef)
    (hB : B.mat.PosDef) :
    A.cfc f ≤ B.cfc f :=
  cfc_le_cfc_of_commute_monoOn hf.monotoneOn hAB₁ hAB₂ hA hB

/-- Specialization of the commuting CFC order theorem to globally monotone scalar functions. -/
theorem cfc_le_cfc_of_commute (hf : Monotone f) (hAB₁ : Commute A.mat B.mat) (hAB₂ : A ≤ B) :
    A.cfc f ≤ B.cfc f :=
  cfc_le_cfc_of_commute_monoOn_of_spectrum_subset (s := Set.univ) (hf.monotoneOn _)
    (Set.subset_univ _) (Set.subset_univ _) hAB₁ hAB₂

/-- Specialization of the commuting CFC order theorem to globally strictly monotone functions. -/
theorem cfc_le_cfc_of_commute_strictMono (hf : StrictMono f)
    (hAB₁ : Commute A.mat B.mat) (hAB₂ : A ≤ B) :
    A.cfc f ≤ B.cfc f :=
  cfc_le_cfc_of_commute hf.monotone hAB₁ hAB₂

omit [Fintype d] [DecidableEq d] in
/-- Positive definiteness is preserved when increasing in the Loewner order. -/
theorem posDef_of_posDef_le (hA : A.mat.PosDef) (hAB : A ≤ B) : B.mat.PosDef := by
  have hdiff : (B - A).mat.PosSemidef := HermitianMat.le_iff.mp hAB
  have hsum : (A.mat + (B - A).mat).PosDef := Matrix.PosDef.add_posSemidef hA hdiff
  convert hsum using 1
  ext i j
  simp [sub_eq_add_neg]

-- The noncommutative monotonicity statement belongs here, but the right hypothesis is
-- operator monotonicity/operator concavity on positive operators, not the placeholder `False`
-- assumption that used to stand here. Until that theory is formalized, we keep only the
-- commuting and pointwise-PosDef lemmas above.

/-- Monotonicity of log on commuting operators. -/
theorem log_le_log_of_commute (hAB₁ : Commute A.mat B.mat) (hAB₂ : A ≤ B) (hA : A.mat.PosDef) :
    A.log ≤ B.log := by
  refine HermitianMat.cfc_le_cfc_of_commute_monoOn ?_ hAB₁ hAB₂ hA ?_
  · exact Real.strictMonoOn_log.monotoneOn
  · exact HermitianMat.posDef_of_posDef_le hA hAB₂

/-- Monotonicity of exp on commuting operators. -/
theorem le_of_exp_commute (hAB₁ : Commute A.mat B.mat) (hAB₂ : A.exp ≤ B.exp) :
    A ≤ B := by
  have hA : A = (A.exp).log := by simp [exp, log, ← HermitianMat.cfc_comp]
  have hB : B = (B.exp).log := by simp [exp, log, ← HermitianMat.cfc_comp]
  rw [hA, hB]
  apply HermitianMat.log_le_log_of_commute
  · apply HermitianMat.cfc_commute
    exact hAB₁
  · exact hAB₂
  · rw [exp, HermitianMat.cfc_PosDef]
    intro
    positivity

/-
The real-power and sandwich lemmas live in `HermitianMat.Rpow`, where the
`Pow (HermitianMat _ _) ℝ` instance is defined. Keeping copies here would create
an import cycle and force this module to depend on an instance it cannot import.
-/
end HermitianMat
