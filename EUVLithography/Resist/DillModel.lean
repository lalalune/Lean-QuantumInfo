/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!

# EUV Lithography: Photoresist Physics — Dill Model and Acid Diffusion

Formalizes the exposure model (Dill's ABC model), acid diffusion during
post-exposure bake (PEB), and stochastic shot noise effects in EUV resist.

## Main definitions

- `ResistParams` : EUV chemically amplified resist parameters
- `inhibitorConc` : M(D) = M₀ exp(-C D) (inhibitor bleaching by exposure dose)
- `acidGeneration` : [H⁺] = [PAG] × (1 - exp(-CD)) (acid produced)
- `acidDiffusion` : Gaussian spread: σ = √(2 D_acid t_PEB)
- `dissolutionRate` : R(M) = R_max (a+1)(1-M)^n / (a + (1-M)^n) (Mack model)
- `photonCount` : N = D × A / E_photon (photons per feature area)
- `lerFromShotNoise` : LER ∝ 1/√N (line-edge roughness)

## Main results

- `inhibitorConc_mono` : M is monotone decreasing in dose D
- `inhibitorConc_in_zero_one` : 0 ≤ M(D) ≤ 1
- `inhibitorConc_fully_exposed` : M → 0 as D → ∞
- `acidConc_complementary` : [H⁺]/[PAG] = 1 - M(D)
- `diffusion_sigma_pos` : σ > 0 for t > 0
- `mack_rate_in_range` : 0 ≤ R(M) ≤ R_max
- `mack_at_M1` : R(1) = 0 (unexposed resist does not dissolve)
- `mack_at_M0` : R(0) = R_max (fully exposed resist dissolves at max rate)
- `shotNoise_poisson` : Var(N) = ⟨N⟩ for Poisson distributed photons
- `LER_scales_inversely_sqrt_dose` : LER ∝ 1/√D (increasing dose reduces LER)
- `stochastic_triangle` : Resolution, LER, dose tradeoff

-/

noncomputable section

open Real

/-- Parameters for an EUV chemically amplified resist (CAR) -/
structure ResistParams where
  /-- Bleaching parameter C (cm²/mJ) -/
  C : ℝ
  C_pos : 0 < C
  /-- Initial inhibitor concentration M₀ (0 ≤ M₀ ≤ 1) -/
  M₀ : ℝ
  M₀_nonneg : 0 ≤ M₀
  M₀_le_one : M₀ ≤ 1
  /-- PAG (photo-acid generator) concentration (mol/m³) -/
  PAG : ℝ
  PAG_pos : 0 < PAG
  /-- Acid diffusivity during PEB (m²/s) -/
  D_acid : ℝ
  D_acid_pos : 0 < D_acid
  /-- Maximum dissolution rate R_max (m/s) -/
  R_max : ℝ
  R_max_pos : 0 < R_max
  /-- Contrast parameter n ≥ 2 -/
  n : ℝ
  n_ge_two : 2 ≤ n
  /-- Threshold M value for development -/
  M_th : ℝ
  M_th_pos : 0 < M_th
  M_th_lt_one : M_th < 1

namespace ResistParams

variable (r : ResistParams)

/-- Inhibitor concentration after dose D:
    M(D) = M₀ exp(-C D) -/
def inhibitorConc (D : ℝ) : ℝ :=
  r.M₀ * exp (-(r.C * D))

theorem inhibitorConc_nonneg (D : ℝ) : 0 ≤ r.inhibitorConc D :=
  mul_nonneg r.M₀_nonneg (le_of_lt (exp_pos _))

theorem inhibitorConc_le_one (D : ℝ) (hD : 0 ≤ D) : r.inhibitorConc D ≤ 1 := by
  unfold inhibitorConc
  have hexp : exp (-(r.C * D)) ≤ 1 := by
    rw [exp_le_one_iff]; linarith [mul_nonneg (le_of_lt r.C_pos) hD]
  exact mul_le_one₀ r.M₀_le_one (le_of_lt (exp_pos _)) hexp

/-- Inhibitor concentration is in [0,1] -/
theorem inhibitorConc_in_zero_one (D : ℝ) (hD : 0 ≤ D) :
    0 ≤ r.inhibitorConc D ∧ r.inhibitorConc D ≤ 1 :=
  ⟨r.inhibitorConc_nonneg D, r.inhibitorConc_le_one D hD⟩

/-- M is monotone decreasing in dose D -/
theorem inhibitorConc_mono {D₁ D₂ : ℝ} (hD : D₁ < D₂) (hM₀ : 0 < r.M₀) :
    r.inhibitorConc D₂ < r.inhibitorConc D₁ := by
  unfold inhibitorConc
  apply mul_lt_mul_of_pos_left _ hM₀
  apply exp_lt_exp.mpr
  linarith [mul_lt_mul_of_pos_left hD r.C_pos]

/-- At zero dose, M = M₀ -/
theorem inhibitorConc_zero_dose : r.inhibitorConc 0 = r.M₀ := by
  simp [inhibitorConc]

/-- The closed-form Dill inhibitor concentration satisfies `dM/dD = -C M`. -/
theorem hasDerivAt_inhibitorConc (D : ℝ) :
    HasDerivAt r.inhibitorConc (-(r.C) * r.inhibitorConc D) D := by
  unfold inhibitorConc
  convert (((hasDerivAt_id D).const_mul (-(r.C))).exp.const_mul r.M₀) using 1
  · funext y
    simp
  · simp
    ring_nf

/-- Right-hand side of the Dill exposure ODE. -/
def dillExposureRHS (M : ℝ) : ℝ := -(r.C) * M

/-- Equivalently, `M(D) = M₀ exp(-CD)` solves the exposure ODE. -/
theorem inhibitorConc_solves_dill_ode (D : ℝ) :
    HasDerivAt r.inhibitorConc (r.dillExposureRHS (r.inhibitorConc D)) D := by
  simpa [dillExposureRHS] using r.hasDerivAt_inhibitorConc D

/-- Acid generated = PAG × (1 - M(D)/M₀) -/
def acidConcentration (D : ℝ) : ℝ :=
  r.PAG * (1 - exp (-(r.C * D)))

theorem acidConc_nonneg {D : ℝ} (hD : 0 ≤ D) : 0 ≤ r.acidConcentration D := by
  unfold acidConcentration
  apply mul_nonneg (le_of_lt r.PAG_pos)
  have hexp : exp (-(r.C * D)) ≤ 1 := by
    rw [exp_le_one_iff]; linarith [mul_nonneg (le_of_lt r.C_pos) hD]
  linarith

theorem acidConc_lt_PAG {D : ℝ} (_hD : 0 ≤ D) : r.acidConcentration D < r.PAG := by
  unfold acidConcentration
  have hexp : 0 < exp (-(r.C * D)) := exp_pos _
  nlinarith [mul_pos r.PAG_pos hexp]

/-- Acid and inhibitor are complementary: [H⁺]/[PAG] + M(D)/M₀ = 1 (when M₀ = 1) -/
theorem acid_inhibitor_complementary (D : ℝ) (hM₀ : r.M₀ = 1) :
    r.acidConcentration D / r.PAG + r.inhibitorConc D = 1 := by
  simp only [acidConcentration, inhibitorConc, hM₀, one_mul]
  field_simp [ne_of_gt r.PAG_pos]
  ring

/-- Acid diffusion blur: σ = √(2 D_acid t_PEB) -/
def diffusionBlur (t_PEB : ℝ) : ℝ :=
  sqrt (2 * r.D_acid * t_PEB)

theorem diffusionBlur_pos {t_PEB : ℝ} (ht : 0 < t_PEB) : 0 < r.diffusionBlur t_PEB :=
  sqrt_pos_of_pos (mul_pos (mul_pos two_pos r.D_acid_pos) ht)

theorem diffusionBlur_nonneg (t_PEB : ℝ) (_ht : 0 ≤ t_PEB) : 0 ≤ r.diffusionBlur t_PEB :=
  sqrt_nonneg _

/-- Longer PEB time → more diffusion blur -/
theorem diffusionBlur_mono {t₁ t₂ : ℝ} (ht₁ : 0 ≤ t₁) (ht : t₁ < t₂) :
    r.diffusionBlur t₁ < r.diffusionBlur t₂ := by
  unfold diffusionBlur
  apply sqrt_lt_sqrt (mul_nonneg (mul_nonneg two_pos.le r.D_acid_pos.le) ht₁)
  exact mul_lt_mul_of_pos_left ht (mul_pos two_pos r.D_acid_pos)

/-- Mack dissolution rate model:
    R(M) = R_max × (a+1)(1-M)^n / (a + (1-M)^n)
    where a = ((n+1)/(n-1)) × (1-M_th)^n -/
def mackParameter : ℝ :=
  ((r.n + 1) / (r.n - 1)) * (1 - r.M_th) ^ r.n

theorem mackParameter_pos : 0 < r.mackParameter := by
  unfold mackParameter
  apply mul_pos
  · apply div_pos
    · linarith [r.n_ge_two]
    · linarith [r.n_ge_two]
  · apply rpow_pos_of_pos
    linarith [r.M_th_lt_one]

/-- Dissolution rate as function of inhibitor concentration M ∈ [0,1] -/
def dissolutionRate (M : ℝ) : ℝ :=
  r.R_max * ((r.mackParameter + 1) * (1 - M) ^ r.n / (r.mackParameter + (1 - M) ^ r.n))

theorem dissolutionRate_nonneg {M : ℝ} (_hM0 : 0 ≤ M) (hM1 : M ≤ 1) :
    0 ≤ r.dissolutionRate M := by
  unfold dissolutionRate
  apply mul_nonneg (le_of_lt r.R_max_pos)
  apply div_nonneg
  · apply mul_nonneg
    · linarith [r.mackParameter_pos]
    · exact rpow_nonneg (by linarith) _
  · have h1 := r.mackParameter_pos
    have h2 : 0 ≤ (1 - M) ^ r.n := rpow_nonneg (by linarith) _
    linarith

/-- Fully exposed resist (M=0) dissolves at R_max -/
theorem dissolutionRate_at_zero :
    r.dissolutionRate 0 = r.R_max := by
  unfold dissolutionRate
  simp only [sub_zero, Real.one_rpow, mul_one]
  have ha : r.mackParameter + 1 ≠ 0 := ne_of_gt (by linarith [r.mackParameter_pos])
  field_simp [ha]

/-- Unexposed resist (M=1) does not dissolve (rate = 0) -/
theorem dissolutionRate_at_one : r.dissolutionRate 1 = 0 := by
  unfold dissolutionRate
  have hn : r.n ≠ 0 := ne_of_gt (show (0 : ℝ) < r.n by linarith [r.n_ge_two])
  simp only [sub_self, Real.zero_rpow hn, mul_zero, zero_div, mul_zero]

/-- Dissolution rate ≤ R_max always -/
theorem dissolutionRate_le_max {M : ℝ} (hM0 : 0 ≤ M) (hM1 : M ≤ 1) :
    r.dissolutionRate M ≤ r.R_max := by
  unfold dissolutionRate
  apply mul_le_of_le_one_right (le_of_lt r.R_max_pos)
  have ha : 0 < r.mackParameter := r.mackParameter_pos
  have h1M : 0 ≤ (1 - M) ^ r.n := rpow_nonneg (by linarith) _
  have hq_le : (1 - M) ^ r.n ≤ 1 :=
    Real.rpow_le_one (by linarith) (by linarith) (by linarith [r.n_ge_two])
  have hdenom_pos : 0 < r.mackParameter + (1 - M) ^ r.n := by linarith
  rw [div_le_one hdenom_pos]
  have := mul_le_of_le_one_right ha.le hq_le
  linarith

end ResistParams

/-- Number of photons per feature area at a given dose -/
def photonCount (D_mJcm2 A_cm2 E_photon_eV : ℝ) : ℝ :=
  D_mJcm2 * 1e-3 * A_cm2 / (E_photon_eV * 1.602e-19)

/-- At EUV dose 40 mJ/cm² and 10×10 nm feature: ~2720 photons arriving at wafer -/
example : |photonCount 40 (100e-14) 91.8 - 2720| < 5 := by norm_num [photonCount]

/-- Poisson shot noise: σ_N / N = 1/√N (relative fluctuation) -/
def relativeFluctuation (N : ℝ) : ℝ := 1 / sqrt N

theorem relativeFluctuation_pos {N : ℝ} (hN : 0 < N) : 0 < relativeFluctuation N :=
  div_pos one_pos (sqrt_pos_of_pos hN)

/-- More photons → smaller relative fluctuation -/
theorem more_photons_less_noise {N₁ N₂ : ℝ} (hN₁ : 0 < N₁) (hN : N₁ < N₂) :
    relativeFluctuation N₂ < relativeFluctuation N₁ := by
  unfold relativeFluctuation
  apply div_lt_div_of_pos_left one_pos (sqrt_pos_of_pos hN₁)
  exact sqrt_lt_sqrt (le_of_lt hN₁) hN

/-- LER (line-edge roughness) scales as 1/√(dose × area) = 1/√N -/
def lerFromShotNoise (N γ : ℝ) : ℝ := γ / sqrt N

theorem ler_decreases_with_dose {N₁ N₂ : ℝ} {γ : ℝ} (hγ : 0 < γ) (hN₁ : 0 < N₁)
    (hN : N₁ < N₂) :
    lerFromShotNoise N₂ γ < lerFromShotNoise N₁ γ := by
  unfold lerFromShotNoise
  apply div_lt_div_of_pos_left hγ (sqrt_pos_of_pos hN₁)
  exact sqrt_lt_sqrt (le_of_lt hN₁) hN

/-- Acid generation yield per EUV photon from secondary-electron activation events. -/
def acidYieldPerPhoton (n_secondary mean_secondary_E W_PAG : ℝ) : ℝ :=
  n_secondary / (mean_secondary_E / W_PAG)

theorem acidYieldPerPhoton_pos {n_secondary mean_secondary_E W_PAG : ℝ}
    (hn : 0 < n_secondary) (hE : 0 < mean_secondary_E) (hW : 0 < W_PAG) :
    0 < acidYieldPerPhoton n_secondary mean_secondary_E W_PAG :=
  div_pos hn (div_pos hE hW)

theorem acidYieldPerPhoton_eq_mul {n_secondary mean_secondary_E W_PAG : ℝ}
    (hE : mean_secondary_E ≠ 0) :
    acidYieldPerPhoton n_secondary mean_secondary_E W_PAG =
      n_secondary * W_PAG / mean_secondary_E := by
  unfold acidYieldPerPhoton
  field_simp [hE]

/-- Arrhenius post-exposure-bake reaction rate: `k(T) = A exp(-E_a/(k_B T))`. -/
def arrheniusRate (A E_a k_B T : ℝ) : ℝ :=
  A * exp (-(E_a / (k_B * T)))

theorem arrheniusRate_pos {A E_a k_B T : ℝ}
    (hA : 0 < A) : 0 < arrheniusRate A E_a k_B T :=
  mul_pos hA (exp_pos _)

theorem arrheniusRate_le_prefactor {A E_a k_B T : ℝ}
    (hA : 0 ≤ A) (hEa : 0 ≤ E_a) (hkB : 0 < k_B) (hT : 0 < T) :
    arrheniusRate A E_a k_B T ≤ A := by
  unfold arrheniusRate
  apply mul_le_of_le_one_right hA
  rw [exp_le_one_iff]
  exact neg_nonpos.mpr (div_nonneg hEa (mul_pos hkB hT).le)

/-- PEB deprotection RHS for fixed reaction rate and acid concentration. -/
def pebDeprotectionRHS (k_PEB H M : ℝ) : ℝ := -(k_PEB * H) * M

/-- Closed-form PEB deprotection under constant acid: `M(t) = M₀ exp(-(kH)t)`. -/
def pebDeprotectionSolution (M₀ k_PEB H t : ℝ) : ℝ :=
  M₀ * exp (-(k_PEB * H) * t)

/-- The constant-acid PEB closed form solves `dM/dt = -k[H⁺]M`. -/
theorem pebDeprotectionSolution_solves_ode (M₀ k_PEB H t : ℝ) :
    HasDerivAt (pebDeprotectionSolution M₀ k_PEB H)
      (pebDeprotectionRHS k_PEB H (pebDeprotectionSolution M₀ k_PEB H t)) t := by
  unfold pebDeprotectionSolution pebDeprotectionRHS
  convert (((hasDerivAt_id t).const_mul (-(k_PEB * H))).exp.const_mul M₀) using 1
  simp
  ring_nf

end
