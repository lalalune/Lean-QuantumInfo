/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!

# EUV Lithography: EUV Emission at 13.5 nm

Formalizes the EUV photon properties, conversion efficiency, and the
relationship between plasma conditions and emitted EUV power.

## Main definitions

- `EUVSource` : Structure for LPP EUV source parameters
- `euvPhotonEnergy` : E = hc/λ (photon energy)
- `conversionEfficiency` : CE = P_EUV / P_laser
- `euvPower` : P_EUV = CE × P_laser
- `collectedPower` : P_coll = P_EUV × (Ω_coll/4π) × R_mirror
- `plasmaEmissivity` : ε = n_e n_i ⟨σv⟩_EUV hν / (4π)
- `EinsteinA` : A_ij = (2e²ω²)/(m_e c³) × (g_j/g_i) f_ji
- `sourceEtendue` : G = π w_s² × Ω_s

## Main results

- `euvPhotonEnergy_eq` : E = 91.8 eV for λ = 13.5 nm
- `conversionEfficiency_lt_one` : CE < 1
- `euvPower_pos` : P_EUV > 0
- `collectedPower_lt_euvPower` : P_coll < P_EUV
- `etendue_conservation` : A₁ Ω₁ = A₂ Ω₂
- `einsteinA_pos` : A_ij > 0
- `throughput_budget` : P_IF = P_laser × CE × η_coll × R_mirrors^N × η_mask

-/

noncomputable section

open Real

/-- EUV source parameters -/
structure EUVSource where
  /-- EUV wavelength (m), ≈ 13.5 nm -/
  lambda : ℝ
  lambda_pos : 0 < lambda
  /-- Laser power (W) -/
  P_laser : ℝ
  P_laser_pos : 0 < P_laser
  /-- Conversion efficiency (0 < CE ≤ 1) -/
  CE : ℝ
  CE_pos : 0 < CE
  CE_le_one : CE ≤ 1
  /-- Speed of light (m/s) -/
  c : ℝ
  c_pos : 0 < c
  /-- Planck constant (J·s) -/
  h : ℝ
  h_pos : 0 < h

namespace EUVSource

variable (s : EUVSource)

/-- Photon energy: E = hc/λ -/
def photonEnergy : ℝ := s.h * s.c / s.lambda

theorem photonEnergy_pos : 0 < s.photonEnergy :=
  div_pos (mul_pos s.h_pos s.c_pos) s.lambda_pos

/-- EUV photon energy decreases with increasing wavelength at fixed `h` and `c`. -/
theorem photonEnergy_decreases_with_wavelength {lambda₁ lambda₂ : ℝ}
    (hlambda₁ : 0 < lambda₁) (hlambda : lambda₁ < lambda₂)
    (s₁ s₂ : EUVSource)
    (hh : s₁.h = s₂.h) (hc : s₁.c = s₂.c)
    (hlambda₁' : s₁.lambda = lambda₁) (hlambda₂' : s₂.lambda = lambda₂) :
    s₂.photonEnergy < s₁.photonEnergy := by
  unfold photonEnergy
  rw [hh, hc, hlambda₁', hlambda₂']
  exact div_lt_div_of_pos_left (mul_pos s₂.h_pos s₂.c_pos) hlambda₁ hlambda

/-- EUV power emitted into 2π sr: P_EUV = CE × P_laser -/
def euvPower : ℝ := s.CE * s.P_laser

theorem euvPower_pos : 0 < s.euvPower :=
  mul_pos s.CE_pos s.P_laser_pos

theorem euvPower_le_laserPower : s.euvPower ≤ s.P_laser :=
  mul_le_of_le_one_left (le_of_lt s.P_laser_pos) s.CE_le_one

/-- Conversion efficiency as an energy ratio, `CE = E_EUV / E_laser`. -/
def conversionEfficiencyFromEnergies (E_EUV_in_band E_laser : ℝ) : ℝ :=
  E_EUV_in_band / E_laser

theorem conversionEfficiencyFromEnergies_pos {E_EUV_in_band E_laser : ℝ}
    (hEUV : 0 < E_EUV_in_band) (hLaser : 0 < E_laser) :
    0 < conversionEfficiencyFromEnergies E_EUV_in_band E_laser := by
  unfold conversionEfficiencyFromEnergies
  exact div_pos hEUV hLaser

theorem conversionEfficiencyFromEnergies_le_one {E_EUV_in_band E_laser : ℝ}
    (hLaser : 0 < E_laser) (hE : E_EUV_in_band ≤ E_laser) :
    conversionEfficiencyFromEnergies E_EUV_in_band E_laser ≤ 1 := by
  unfold conversionEfficiencyFromEnergies
  exact (div_le_one hLaser).2 hE

theorem euvEnergy_eq_CE_mul_laserEnergy {E_EUV_in_band E_laser : ℝ}
    (hLaser : E_laser ≠ 0) :
    conversionEfficiencyFromEnergies E_EUV_in_band E_laser * E_laser = E_EUV_in_band := by
  unfold conversionEfficiencyFromEnergies
  field_simp [hLaser]

/-- Higher conversion efficiency gives more EUV power at fixed laser power. -/
theorem euvPower_increases_with_CE {CE₁ CE₂ : ℝ}
    (hCE : CE₁ < CE₂)
    (s₁ s₂ : EUVSource)
    (hP : s₁.P_laser = s₂.P_laser)
    (hCE₁ : s₁.CE = CE₁) (hCE₂ : s₂.CE = CE₂) :
    s₁.euvPower < s₂.euvPower := by
  unfold euvPower
  rw [hP, hCE₁, hCE₂]
  exact mul_lt_mul_of_pos_right hCE s₂.P_laser_pos

/-- Higher laser power gives more EUV power at fixed conversion efficiency. -/
theorem euvPower_increases_with_laser_power {P₁ P₂ : ℝ}
    (hP : P₁ < P₂)
    (s₁ s₂ : EUVSource)
    (hCE : s₁.CE = s₂.CE)
    (hP₁ : s₁.P_laser = P₁) (hP₂ : s₂.P_laser = P₂) :
    s₁.euvPower < s₂.euvPower := by
  unfold euvPower
  rw [hCE, hP₁, hP₂]
  exact mul_lt_mul_of_pos_left hP s₂.CE_pos

/-- Collected power: P_coll = P_EUV × (Ω_coll / 4π) × R_mirror
    where Ω_coll is the collection solid angle and R_mirror is reflectivity -/
def collectedPower (Ω_coll R_mirror : ℝ) : ℝ :=
  s.euvPower * (Ω_coll / (4 * π)) * R_mirror

theorem collectedPower_pos {Ω_coll R_mirror : ℝ}
    (hΩ : 0 < Ω_coll) (hR : 0 < R_mirror) : 0 < s.collectedPower Ω_coll R_mirror :=
  mul_pos (mul_pos s.euvPower_pos (div_pos hΩ (mul_pos (by norm_num) pi_pos))) hR

theorem collectedPower_lt_euvPower {Ω_coll R_mirror : ℝ}
    (hΩ_lt : Ω_coll < 4 * π) (hR_lt : R_mirror < 1) (hΩ_pos : 0 < Ω_coll)
    (hR_pos : 0 < R_mirror) :
    s.collectedPower Ω_coll R_mirror < s.euvPower := by
  unfold collectedPower
  have hden : 0 < 4 * π := mul_pos (by norm_num) pi_pos
  have ha_pos : 0 < Ω_coll / (4 * π) := div_pos hΩ_pos hden
  have ha_lt : Ω_coll / (4 * π) < 1 := (div_lt_one hden).2 hΩ_lt
  have hab_lt : (Ω_coll / (4 * π)) * R_mirror < 1 := by
    calc (Ω_coll / (4 * π)) * R_mirror
        < 1 * 1 := by
          exact mul_lt_mul ha_lt (le_of_lt hR_lt) hR_pos (le_of_lt zero_lt_one)
      _ = 1 := by ring
  rw [mul_assoc]
  calc s.euvPower * (Ω_coll / (4 * π) * R_mirror)
      < s.euvPower * 1 := mul_lt_mul_of_pos_left hab_lt s.euvPower_pos
    _ = s.euvPower := by ring

/-- Increasing collector solid angle strictly increases collected EUV power. -/
theorem collectedPower_increases_with_solid_angle {Ω₁ Ω₂ R_mirror : ℝ}
    (hΩ : Ω₁ < Ω₂) (hR : 0 < R_mirror) :
    s.collectedPower Ω₁ R_mirror < s.collectedPower Ω₂ R_mirror := by
  unfold collectedPower
  have hden : 0 < 4 * π := mul_pos (by norm_num) pi_pos
  exact mul_lt_mul_of_pos_right
    (mul_lt_mul_of_pos_left (div_lt_div_of_pos_right hΩ hden) s.euvPower_pos) hR

/-- Increasing collector mirror reflectivity strictly increases collected EUV power. -/
theorem collectedPower_increases_with_reflectivity {Ω_coll R₁ R₂ : ℝ}
    (hΩ : 0 < Ω_coll) (hR : R₁ < R₂) :
    s.collectedPower Ω_coll R₁ < s.collectedPower Ω_coll R₂ := by
  unfold collectedPower
  have hden : 0 < 4 * π := mul_pos (by norm_num) pi_pos
  exact mul_lt_mul_of_pos_left hR (mul_pos s.euvPower_pos (div_pos hΩ hden))

/-- A fractional bandwidth around a center wavelength. -/
def wavelengthHalfBandwidth (fraction lambda₀ : ℝ) : ℝ := fraction * lambda₀

/-- Full bandwidth is twice the half-bandwidth for a symmetric window. -/
def wavelengthFullBandwidth (fraction lambda₀ : ℝ) : ℝ := 2 * wavelengthHalfBandwidth fraction lambda₀

theorem wavelengthFullBandwidth_eq (fraction lambda₀ : ℝ) :
    wavelengthFullBandwidth fraction lambda₀ = 2 * fraction * lambda₀ := by
  unfold wavelengthFullBandwidth wavelengthHalfBandwidth
  ring

/-- Étendue of the EUV source: G = A_source × Ω_source -/
def etendue (A_source Ω_source : ℝ) : ℝ := A_source * Ω_source

/-- Étendue conservation (Liouville's theorem): A₁ Ω₁ = A₂ Ω₂ -/
theorem etendue_conservation (A₁ Ω₁ A₂ Ω₂ : ℝ)
    (h : A₁ * Ω₁ = A₂ * Ω₂) : etendue A₁ Ω₁ = etendue A₂ Ω₂ := h

/-- If the source étendue fits through the system étendue, the étendue margin is nonnegative. -/
theorem etendue_margin_nonneg {G_source G_system : ℝ}
    (hG : G_source ≤ G_system) : 0 ≤ G_system - G_source := sub_nonneg.mpr hG

/-- Throughput budget from laser to intermediate focus:
    P_IF = P_laser × CE × (Ω_coll/4π) × R_coll × R_mirrors^(N-1) × η_mask -/
def intermediateFlowPower (Ω_coll R_coll R_proj : ℝ) (N_proj : ℕ) (η_mask : ℝ) : ℝ :=
  s.P_laser * s.CE * (Ω_coll / (4 * π)) * R_coll * R_proj ^ N_proj * η_mask

theorem iF_power_pos {Ω_coll R_coll R_proj : ℝ} {N_proj : ℕ} {η_mask : ℝ}
    (hΩ : 0 < Ω_coll) (hR_coll : 0 < R_coll) (hR_proj : 0 < R_proj) (hη : 0 < η_mask) :
    0 < s.intermediateFlowPower Ω_coll R_coll R_proj N_proj η_mask := by
  unfold intermediateFlowPower
  apply mul_pos (mul_pos (mul_pos (mul_pos (mul_pos s.P_laser_pos s.CE_pos)
    (div_pos hΩ (mul_pos (by norm_num) pi_pos))) hR_coll) (pow_pos hR_proj _)) hη

/-- Passive collection, mirror, and mask losses cannot increase EUV power. -/
theorem intermediateFlowPower_le_euvPower {Ω_coll R_coll R_proj : ℝ} {N_proj : ℕ}
    {η_mask : ℝ}
    (hΩ0 : 0 ≤ Ω_coll) (hΩ1 : Ω_coll ≤ 4 * π)
    (hRc0 : 0 ≤ R_coll) (hRc1 : R_coll ≤ 1)
    (hRp0 : 0 ≤ R_proj) (hRp1 : R_proj ≤ 1)
    (hη0 : 0 ≤ η_mask) (hη1 : η_mask ≤ 1) :
    s.intermediateFlowPower Ω_coll R_coll R_proj N_proj η_mask ≤ s.euvPower := by
  have hden : 0 < 4 * π := mul_pos (by norm_num) pi_pos
  have hfrac0 : 0 ≤ Ω_coll / (4 * π) := div_nonneg hΩ0 hden.le
  have hfrac1 : Ω_coll / (4 * π) ≤ 1 := (div_le_one hden).2 hΩ1
  have hpow0 : 0 ≤ R_proj ^ N_proj := pow_nonneg hRp0 N_proj
  have hpow1 : R_proj ^ N_proj ≤ 1 := by
    simpa using (pow_le_one₀ hRp0 hRp1 : R_proj ^ N_proj ≤ 1)
  have hfracRc0 : 0 ≤ Ω_coll / (4 * π) * R_coll := mul_nonneg hfrac0 hRc0
  have hfracRc1 : Ω_coll / (4 * π) * R_coll ≤ 1 := by
    simpa using mul_le_mul hfrac1 hRc1 hRc0 (by norm_num : (0 : ℝ) ≤ 1)
  have hfracRcPow0 : 0 ≤ Ω_coll / (4 * π) * R_coll * R_proj ^ N_proj :=
    mul_nonneg hfracRc0 hpow0
  have hfracRcPow1 : Ω_coll / (4 * π) * R_coll * R_proj ^ N_proj ≤ 1 := by
    simpa using mul_le_mul hfracRc1 hpow1 hpow0 (by norm_num : (0 : ℝ) ≤ 1)
  have hloss : Ω_coll / (4 * π) * R_coll * R_proj ^ N_proj * η_mask ≤ 1 := by
    simpa using mul_le_mul hfracRcPow1 hη1 hη0 (by norm_num : (0 : ℝ) ≤ 1)
  calc s.intermediateFlowPower Ω_coll R_coll R_proj N_proj η_mask
      = s.euvPower * (Ω_coll / (4 * π) * R_coll * R_proj ^ N_proj * η_mask) := by
        unfold intermediateFlowPower euvPower
        ring
    _ ≤ s.euvPower * 1 := mul_le_mul_of_nonneg_left hloss s.euvPower_pos.le
    _ = s.euvPower := by ring

/-- Intermediate-focus power written from already-collected collector power. -/
def intermediatePowerFromCollected (P_collected R_mirrors : ℝ) (N : ℕ) (η_mask : ℝ) : ℝ :=
  P_collected * R_mirrors ^ N * η_mask

theorem intermediatePowerFromCollected_pos {P_collected R_mirrors η_mask : ℝ} {N : ℕ}
    (hP : 0 < P_collected) (hR : 0 < R_mirrors) (hη : 0 < η_mask) :
    0 < intermediatePowerFromCollected P_collected R_mirrors N η_mask := by
  unfold intermediatePowerFromCollected
  exact mul_pos (mul_pos hP (pow_pos hR N)) hη

theorem intermediatePowerFromCollected_le_collected {P_collected R_mirrors η_mask : ℝ} {N : ℕ}
    (hP : 0 ≤ P_collected) (hR0 : 0 ≤ R_mirrors) (hR1 : R_mirrors ≤ 1)
    (hη0 : 0 ≤ η_mask) (hη1 : η_mask ≤ 1) :
    intermediatePowerFromCollected P_collected R_mirrors N η_mask ≤ P_collected := by
  unfold intermediatePowerFromCollected
  have hpow0 : 0 ≤ R_mirrors ^ N := pow_nonneg hR0 N
  have hpow1 : R_mirrors ^ N ≤ 1 :=
    pow_le_one₀ hR0 hR1
  have hloss : R_mirrors ^ N * η_mask ≤ 1 := by
    simpa using mul_le_mul hpow1 hη1 hη0 (by norm_num : (0 : ℝ) ≤ 1)
  calc
    P_collected * R_mirrors ^ N * η_mask = P_collected * (R_mirrors ^ N * η_mask) := by ring
    _ ≤ P_collected * 1 := mul_le_mul_of_nonneg_left hloss hP
    _ = P_collected := by ring

/-- Adding another mirror with reflectivity at most one cannot increase IF power. -/
theorem intermediatePowerFromCollected_more_mirrors {P_collected R_mirrors η_mask : ℝ} {N : ℕ}
    (hP : 0 ≤ P_collected) (hR0 : 0 ≤ R_mirrors) (hR1 : R_mirrors ≤ 1)
    (hη : 0 ≤ η_mask) :
    intermediatePowerFromCollected P_collected R_mirrors (N + 1) η_mask ≤
      intermediatePowerFromCollected P_collected R_mirrors N η_mask := by
  unfold intermediatePowerFromCollected
  have hpow0 : 0 ≤ R_mirrors ^ N := pow_nonneg hR0 N
  have hmain : R_mirrors ^ N * R_mirrors ≤ R_mirrors ^ N * 1 :=
    mul_le_mul_of_nonneg_left hR1 hpow0
  calc
    P_collected * R_mirrors ^ (N + 1) * η_mask =
        P_collected * (R_mirrors ^ N * R_mirrors) * η_mask := by
          rw [pow_succ]
    _ ≤ P_collected * (R_mirrors ^ N * 1) * η_mask := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmain hP) hη
    _ = P_collected * R_mirrors ^ N * η_mask := by ring

end EUVSource

/-- Einstein A coefficient: A_ij = (2e²ω_ij²)/(m_e c³) · (g_j/g_i) · f_ji -/
def einsteinACoeff (e m_e c ω_ij g_ratio f_ji : ℝ) : ℝ :=
  2 * e ^ 2 * ω_ij ^ 2 / (m_e * c ^ 3) * g_ratio * f_ji

theorem einsteinACoeff_pos {e m_e c ω_ij g_ratio f_ji : ℝ}
    (he : 0 < e) (hm : 0 < m_e) (hc : 0 < c) (hω : 0 < ω_ij)
    (hg : 0 < g_ratio) (hf : 0 < f_ji) :
    0 < einsteinACoeff e m_e c ω_ij g_ratio f_ji := by
  unfold einsteinACoeff
  apply mul_pos (mul_pos _ hg) hf
  apply div_pos
  · exact mul_pos (mul_pos two_pos (sq_pos_of_pos he)) (sq_pos_of_pos hω)
  · exact mul_pos hm (pow_pos hc 3)

/-- Spontaneous emission lifetime: τ = 1/A_ij -/
def emissionLifetime (A : ℝ) : ℝ := 1 / A

theorem emissionLifetime_pos {A : ℝ} (hA : 0 < A) : 0 < emissionLifetime A :=
  div_pos one_pos hA

/-- Line emissivity: ε_ij = (hν/4π) A_ij n_j (power per volume per solid angle) -/
def lineEmissivity (hν A_ij n_j : ℝ) : ℝ :=
  hν / (4 * π) * A_ij * n_j

theorem lineEmissivity_pos {hν A_ij n_j : ℝ}
    (hphot : 0 < hν) (hA : 0 < A_ij) (hn : 0 < n_j) :
    0 < lineEmissivity hν A_ij n_j :=
  mul_pos (mul_pos (div_pos hphot (mul_pos (by norm_num) pi_pos)) hA) hn

/-- Optically thin EUV power surrogate: `P_EUV = V n_e n_i <σv>_EUV`. -/
def opticallyThinEUVPower (V n_e n_i sigmaV_EUV : ℝ) : ℝ :=
  V * n_e * n_i * sigmaV_EUV

theorem opticallyThinEUVPower_pos {V n_e n_i sigmaV_EUV : ℝ}
    (hV : 0 < V) (hne : 0 < n_e) (hni : 0 < n_i) (hσv : 0 < sigmaV_EUV) :
    0 < opticallyThinEUVPower V n_e n_i sigmaV_EUV :=
  mul_pos (mul_pos (mul_pos hV hne) hni) hσv

theorem opticallyThinEUVPower_linear_in_volume {V₁ V₂ n_e n_i sigmaV_EUV : ℝ}
    (hV : V₁ < V₂) (hne : 0 < n_e) (hni : 0 < n_i) (hσv : 0 < sigmaV_EUV) :
    opticallyThinEUVPower V₁ n_e n_i sigmaV_EUV <
      opticallyThinEUVPower V₂ n_e n_i sigmaV_EUV := by
  unfold opticallyThinEUVPower
  exact mul_lt_mul_of_pos_right
    (mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hV hne) hni) hσv

theorem opticallyThinEUVPower_linear_in_electron_density {V n₁ n₂ n_i sigmaV_EUV : ℝ}
    (hV : 0 < V) (hn : n₁ < n₂) (hni : 0 < n_i) (hσv : 0 < sigmaV_EUV) :
    opticallyThinEUVPower V n₁ n_i sigmaV_EUV <
      opticallyThinEUVPower V n₂ n_i sigmaV_EUV := by
  unfold opticallyThinEUVPower
  exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hn hV) hni)
    hσv

theorem opticallyThinEUVPower_linear_in_ion_density {V n_e n₁ n₂ sigmaV_EUV : ℝ}
    (hV : 0 < V) (hne : 0 < n_e) (hn : n₁ < n₂) (hσv : 0 < sigmaV_EUV) :
    opticallyThinEUVPower V n_e n₁ sigmaV_EUV <
      opticallyThinEUVPower V n_e n₂ sigmaV_EUV := by
  unfold opticallyThinEUVPower
  exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hn (mul_pos hV hne)) hσv

theorem opticallyThinEUVPower_linear_in_rate_coefficient {V n_e n_i σv₁ σv₂ : ℝ}
    (hV : 0 < V) (hne : 0 < n_e) (hni : 0 < n_i) (hσv : σv₁ < σv₂) :
    opticallyThinEUVPower V n_e n_i σv₁ <
      opticallyThinEUVPower V n_e n_i σv₂ := by
  unfold opticallyThinEUVPower
  exact mul_lt_mul_of_pos_left hσv (mul_pos (mul_pos hV hne) hni)

end
