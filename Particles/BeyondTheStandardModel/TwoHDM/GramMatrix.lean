/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Particles.BeyondTheStandardModel.TwoHDM.Basic
import Particles.StandardModel.HiggsBoson.Basic

/-!

# The Gram matrix and Gram vector for the two Higgs doublet model

This file provides the API needed by `Potential.lean`:
* the Gram matrix
* the Gram vector
* basic component identities
* the forward cone inequality
* surjectivity of the Gram vector onto the forward cone

-/
namespace TwoHiggsDoublet

open StandardModel
open Complex
open InnerProductSpace

/-- The Gram matrix of a two-Higgs-doublet configuration. -/
noncomputable def gramMatrix (H : TwoHiggsDoublet) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![⟪H.Φ1, H.Φ1⟫_ℂ, ⟪H.Φ2, H.Φ1⟫_ℂ; ⟪H.Φ1, H.Φ2⟫_ℂ, ⟪H.Φ2, H.Φ2⟫_ℂ]

/-- The real Gram-vector coordinates used in the potential analysis. -/
noncomputable def gramVector (H : TwoHiggsDoublet) : Fin 1 ⊕ Fin 3 → ℝ
  | Sum.inl 0 => ‖H.Φ1‖ ^ 2 + ‖H.Φ2‖ ^ 2
  | Sum.inr 0 => 2 * (⟪H.Φ1, H.Φ2⟫_ℂ).re
  | Sum.inr 1 => 2 * (⟪H.Φ1, H.Φ2⟫_ℂ).im
  | Sum.inr 2 => ‖H.Φ1‖ ^ 2 - ‖H.Φ2‖ ^ 2

@[simp]
lemma gramVector_inl_zero_eq (H : TwoHiggsDoublet) :
    H.gramVector (Sum.inl 0) = ‖H.Φ1‖ ^ 2 + ‖H.Φ2‖ ^ 2 := by
  simp [gramVector]

@[simp]
lemma gramVector_inr_zero_eq (H : TwoHiggsDoublet) :
    H.gramVector (Sum.inr 0) = 2 * (⟪H.Φ1, H.Φ2⟫_ℂ).re := by
  simp [gramVector]

@[simp]
lemma gramVector_inr_one_eq (H : TwoHiggsDoublet) :
    H.gramVector (Sum.inr 1) = 2 * (⟪H.Φ1, H.Φ2⟫_ℂ).im := by
  simp [gramVector]

@[simp]
lemma gramVector_inr_two_eq (H : TwoHiggsDoublet) :
    H.gramVector (Sum.inr 2) = ‖H.Φ1‖ ^ 2 - ‖H.Φ2‖ ^ 2 := by
  simp [gramVector]

lemma normSq_Φ1_eq_gramVector (H : TwoHiggsDoublet) :
    ‖H.Φ1‖ ^ 2 = (1 / 2 : ℝ) * (H.gramVector (Sum.inl 0) + H.gramVector (Sum.inr 2)) := by
  rw [gramVector_inl_zero_eq, gramVector_inr_two_eq]
  ring

lemma normSq_Φ2_eq_gramVector (H : TwoHiggsDoublet) :
    ‖H.Φ2‖ ^ 2 = (1 / 2 : ℝ) * (H.gramVector (Sum.inl 0) - H.gramVector (Sum.inr 2)) := by
  rw [gramVector_inl_zero_eq, gramVector_inr_two_eq]
  ring

lemma Φ1_inner_Φ2_eq_gramVector (H : TwoHiggsDoublet) :
    (⟪H.Φ1, H.Φ2⟫_ℂ) = (1 / 2 : ℝ) * (H.gramVector (Sum.inr 0) +
    Complex.I * H.gramVector (Sum.inr 1)) := by
  rw [gramVector_inr_zero_eq, gramVector_inr_one_eq]
  apply Complex.ext <;> simp <;> ring

lemma Φ2_inner_Φ1_eq_gramVector (H : TwoHiggsDoublet) :
    (⟪H.Φ2, H.Φ1⟫_ℂ) = (1 / 2 : ℝ) * (H.gramVector (Sum.inr 0) -
    Complex.I * H.gramVector (Sum.inr 1)) := by
  rw [show ⟪H.Φ2, H.Φ1⟫_ℂ = conj ⟪H.Φ1, H.Φ2⟫_ℂ by rw [← inner_conj_symm]]
  rw [Φ1_inner_Φ2_eq_gramVector]
  apply Complex.ext <;> simp <;> ring

lemma gramVector_inl_nonneg (H : TwoHiggsDoublet) :
    0 ≤ H.gramVector (Sum.inl 0) := by
  rw [gramVector_inl_zero_eq]
  positivity

lemma gramVector_inr_sum_sq_le_inl (H : TwoHiggsDoublet) :
    ∑ μ : Fin 3, H.gramVector (Sum.inr μ) ^ 2 ≤ H.gramVector (Sum.inl 0) ^ 2 := by
  have h_inner : ‖⟪H.Φ1, H.Φ2⟫_ℂ‖ ^ 2 ≤ ‖H.Φ1‖ ^ 2 * ‖H.Φ2‖ ^ 2 := by
    have hle : ‖⟪H.Φ1, H.Φ2⟫_ℂ‖ ≤ ‖H.Φ1‖ * ‖H.Φ2‖ :=
      norm_inner_le_norm (𝕜 := ℂ) H.Φ1 H.Φ2
    nlinarith [hle, norm_nonneg (⟪H.Φ1, H.Φ2⟫_ℂ), norm_nonneg H.Φ1, norm_nonneg H.Φ2]
  have h_reim : (⟪H.Φ1, H.Φ2⟫_ℂ).re ^ 2 + (⟪H.Φ1, H.Φ2⟫_ℂ).im ^ 2 =
      ‖⟪H.Φ1, H.Φ2⟫_ℂ‖ ^ 2 := by
    have h₁ : Complex.normSq (⟪H.Φ1, H.Φ2⟫_ℂ) = ‖⟪H.Φ1, H.Φ2⟫_ℂ‖ ^ 2 :=
      Complex.normSq_eq_norm_sq (⟪H.Φ1, H.Φ2⟫_ℂ)
    have h₂ : Complex.normSq (⟪H.Φ1, H.Φ2⟫_ℂ) =
        (⟪H.Φ1, H.Φ2⟫_ℂ).re * (⟪H.Φ1, H.Φ2⟫_ℂ).re +
        (⟪H.Φ1, H.Φ2⟫_ℂ).im * (⟪H.Φ1, H.Φ2⟫_ℂ).im :=
      Complex.normSq_apply (⟪H.Φ1, H.Φ2⟫_ℂ)
    nlinarith [h₁, h₂]
  rw [Fin.sum_univ_three]
  rw [gramVector_inr_zero_eq, gramVector_inr_one_eq, gramVector_inr_two_eq, gramVector_inl_zero_eq]
  nlinarith [h_inner, h_reim]

lemma gramVector_surjective (v : Fin 1 ⊕ Fin 3 → ℝ) (hv₀ : 0 ≤ v (Sum.inl 0))
    (hv_sum : ∑ μ : Fin 3, v (Sum.inr μ) ^ 2 ≤ v (Sum.inl 0) ^ 2) :
    ∃ H : TwoHiggsDoublet, H.gramVector = v := by
  let K0 : ℝ := v (Sum.inl 0)
  let K1 : ℝ := v (Sum.inr 0)
  let K2 : ℝ := v (Sum.inr 1)
  let K3 : ℝ := v (Sum.inr 2)
  let a : ℝ := (K0 + K3) / 2
  let d : ℝ := (K0 - K3) / 2
  let c : ℂ := ((K1 : ℂ) + (K2 : ℂ) * I) / 2

  have hK3_sq : K3 ^ 2 ≤ K0 ^ 2 := by
    have hv_sum' : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 ≤ K0 ^ 2 := by
      simpa [K0, K1, K2, K3, Fin.sum_univ_three] using hv_sum
    nlinarith [hv_sum']
  have hK3_le : K3 ≤ K0 := by nlinarith [hK3_sq, hv₀]
  have hK3_ge : -K0 ≤ K3 := by nlinarith [hK3_sq, hv₀]
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    nlinarith [hK3_ge]
  have hd_nonneg : 0 ≤ d := by
    dsimp [d]
    nlinarith [hK3_le]

  have hc_sq : ‖c‖ ^ 2 = (K1 ^ 2 + K2 ^ 2) / 4 := by
    have h₁ : Complex.normSq c = ‖c‖ ^ 2 := Complex.normSq_eq_norm_sq c
    have h₂ : Complex.normSq c = c.re * c.re + c.im * c.im := Complex.normSq_apply c
    have h₃ : c.re = K1 / 2 := by simp [c]
    have h₄ : c.im = K2 / 2 := by simp [c]
    nlinarith [h₁, h₂, h₃, h₄]
  have had : a * d = (K0 ^ 2 - K3 ^ 2) / 4 := by
    dsimp [a, d]
    ring
  have hc_le : ‖c‖ ^ 2 ≤ a * d := by
    have hv_aux : K1 ^ 2 + K2 ^ 2 ≤ K0 ^ 2 - K3 ^ 2 := by
      have hv_sum' : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 ≤ K0 ^ 2 := by
        simpa [K0, K1, K2, K3, Fin.sum_univ_three] using hv_sum
      nlinarith [hv_sum']
    rw [hc_sq, had]
    nlinarith [hv_aux]

  by_cases ha0 : a = 0
  · have hK3_eq : K3 = -K0 := by
      dsimp [a] at ha0
      nlinarith [ha0]
    have hK1_zero : K1 = 0 := by
      have hv_sum' : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 ≤ K0 ^ 2 := by
        simpa [K0, K1, K2, K3, Fin.sum_univ_three] using hv_sum
      nlinarith [hv_sum', hK3_eq]
    have hK2_zero : K2 = 0 := by
      have hv_sum' : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 ≤ K0 ^ 2 := by
        simpa [K0, K1, K2, K3, Fin.sum_univ_three] using hv_sum
      nlinarith [hv_sum', hK3_eq]
    let H : TwoHiggsDoublet := ⟨HiggsVec.ofReal 0, HiggsVec.ofReal K0⟩
    refine ⟨H, ?_⟩
    ext μ
    fin_cases μ
    · simp [H, K0, gramVector, HiggsVec.ofReal_normSq, hv₀]
    · simp [H, K1, K2, K3, gramVector, hK1_zero, hK2_zero]
    · simp [H, K1, K2, K3, gramVector, hK1_zero, hK2_zero]
    · simp [H, K0, K3, gramVector, HiggsVec.ofReal_normSq, hv₀, hK3_eq]
  · have ha_pos : 0 < a := lt_of_le_of_ne ha_nonneg ha0
    have hsqrt_a_ne : (Real.sqrt a : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_ne_zero'.2 ha_pos)
    have hc_div_le : ‖c‖ ^ 2 / a ≤ d := by
      exact (div_le_iff ha_pos).2 (by nlinarith [hc_le])
    have hrad_nonneg : 0 ≤ d - ‖c‖ ^ 2 / a := by nlinarith [hc_div_le]

    let φ1 : HiggsVec := !₂[Real.sqrt a, 0]
    let φ2 : HiggsVec := !₂[c / (Real.sqrt a : ℂ), Real.sqrt (d - ‖c‖ ^ 2 / a)]
    let H : TwoHiggsDoublet := ⟨φ1, φ2⟩

    have hφ1_norm : ‖φ1‖ ^ 2 = a := by
      simp [φ1, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two, Real.sq_sqrt (le_of_lt ha_pos)]
    have hdiv_norm : ‖c / (Real.sqrt a : ℂ)‖ ^ 2 = ‖c‖ ^ 2 / a := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_div, Complex.normSq_eq_norm_sq,
        Complex.normSq_eq_norm_sq]
      simp [Complex.normSq_ofReal, Real.sq_sqrt (le_of_lt ha_pos)]
    have hφ2_norm : ‖φ2‖ ^ 2 = d := by
      rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
      simp [φ2, hdiv_norm, hrad_nonneg, Complex.norm_real, Real.sq_sqrt hrad_nonneg]
      nlinarith
    have hinner : ⟪φ1, φ2⟫_ℂ = c := by
      simp [φ1, φ2, PiLp.inner_apply, Fin.sum_univ_two, hsqrt_a_ne]

    have hK0 : a + d = K0 := by
      dsimp [a, d]
      ring
    have hK3 : a - d = K3 := by
      dsimp [a, d]
      ring

    refine ⟨H, ?_⟩
    ext μ
    fin_cases μ
    · rw [gramVector_inl_zero_eq, hφ1_norm, hφ2_norm]
      exact hK0
    · rw [gramVector_inr_zero_eq, hinner]
      simp [c, K1]
    · rw [gramVector_inr_one_eq, hinner]
      simp [c, K2]
    · rw [gramVector_inr_two_eq, hφ1_norm, hφ2_norm]
      exact hK3

end TwoHiggsDoublet
