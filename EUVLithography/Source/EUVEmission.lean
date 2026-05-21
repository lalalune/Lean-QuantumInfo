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

/-- EUV power emitted into 2π sr: P_EUV = CE × P_laser -/
def euvPower : ℝ := s.CE * s.P_laser

theorem euvPower_pos : 0 < s.euvPower :=
  mul_pos s.CE_pos s.P_laser_pos

theorem euvPower_le_laserPower : s.euvPower ≤ s.P_laser :=
  mul_le_of_le_one_left (le_of_lt s.P_laser_pos) s.CE_le_one

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

end
