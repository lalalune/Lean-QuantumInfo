import EUVLithography.Source.EUVEmission
import EUVLithography.Contamination.MirrorPhysics
import EUVLithography.Optics.Etendue
import EUVLithography.ImageFormation.Mask
import EUVLithography.ImageFormation.ProjectionOptics
import EUVLithography.Resist.AcidDiffusion
import EUVLithography.Resist.DillModel
import EUVLithography.Plasma.InverseBremsstrahlung
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# EUV Lithography: Report Numeric Checks

Machine-checked arithmetic for selected numeric examples in the report.
-/

noncomputable section

open Real

theorem report_euv_power_30kW_6pct :
    (0.06 : ℝ) * 30000 = 1800 := by norm_num

theorem report_collected_power_17pct :
    (1800 : ℝ) * 0.17 = 306 := by norm_num

theorem report_collection_efficiency_with_mirror_numeric :
    (0.17 : ℝ) * 0.70 = 0.119 := by norm_num

theorem report_collector_fraction_solid_angle_identity :
    solidAngleFromFullSphereFraction 0.17 / (4 * π) = (0.17 : ℝ) :=
  collectionFraction_of_solidAngleFromFullSphereFraction

theorem report_mask_contrast_numeric :
    |maskContrast 0.65 0.005 - 0.9847328244274809| < (1e-12 : ℝ) := by
  norm_num [maskContrast]

theorem report_mask_shadow_numeric_using_tan6_approx :
    |65 * 0.105 / (4 : ℝ) - 1.7| < 0.01 := by
  norm_num

theorem report_tin_atomic_volume_numeric :
    |atomicVolume 118.7 6.022e23 7.29 - 2.71e-23| < 0.01e-23 := by
  norm_num [atomicVolume]

theorem report_tin_droplet_diameter_low_numeric :
    (1.89 : ℝ) * 15 = 28.35 := by
  norm_num

theorem report_tin_droplet_diameter_high_numeric :
    (1.89 : ℝ) * 20 = 37.8 := by
  norm_num

theorem report_photon_count_numeric :
    |photonCount 40 (100e-14) 91.8 - 2720| < 5 := by
  norm_num [photonCount]

theorem report_ponderomotive_numeric :
    |IBParams.ponderomotiveEnergyEV ((10 : ℝ) ^ 10) 10.6 - 0.10483188| < 0.00000001 := by
  norm_num [IBParams.ponderomotiveEnergyEV]

theorem report_co2_critical_density_rule_numeric :
    |(1.1e21 : ℝ) / (10.6 ^ 2) - 9.8e18| < 1e17 := by
  norm_num

theorem report_focused_waist_numeric :
    |(1.1 * 10.6e-6 * 0.2 / (π * 0.05) : ℝ) - 14.8e-6| < 0.1e-6 := by
  have hden : 0 < (π * 0.05 : ℝ) := mul_pos pi_pos (by norm_num)
  have hupper : (1.1 * 10.6e-6 * 0.2 / (π * 0.05) : ℝ) < 14.9e-6 := by
    rw [div_lt_iff₀ hden]
    nlinarith [Real.pi_gt_d2]
  have hlower : (14.7e-6 : ℝ) < 1.1 * 10.6e-6 * 0.2 / (π * 0.05) := by
    rw [lt_div_iff₀ hden]
    nlinarith [Real.pi_lt_d2]
  rw [abs_sub_lt_iff]
  constructor
  · linarith
  · linarith

theorem report_vacuum_pressure_requirement_numeric :
    (10 ^ 5 : ℝ) * (0.2 * 10 ^ (-3 : ℤ)) / 10 = 2 := by
  norm_num

theorem report_rayleigh_resolution_NA033_numeric :
    |0.3 * 13.5 / 0.33 - 12.3| < (0.1 : ℝ) := by
  norm_num

theorem report_rayleigh_resolution_NA055_numeric :
    |0.3 * 13.5 / 0.55 - 7.4| < (0.1 : ℝ) := by
  norm_num

theorem report_abbe_limit_NA055_numeric :
    |13.5 / (2 * 0.55 : ℝ) - 12.3| < 0.1 := by
  norm_num

theorem report_dof_NA033_numeric :
    |13.5 / (0.33 ^ 2) - 124| < (0.1 : ℝ) := by
  norm_num

theorem report_dof_NA055_numeric :
    |13.5 / (0.55 ^ 2) - 44.6| < (0.1 : ℝ) := by
  norm_num

theorem report_wavefront_lambda_over_60_numeric :
    13.5 / (60 : ℝ) = 0.225 := by
  norm_num

theorem report_acid_diffusion_numeric :
    |sqrt (2 * 5 * 60 : ℝ) - 24.5| < (0.01 : ℝ) := by
  have hupper : sqrt (2 * 5 * 60 : ℝ) < 24.51 := by
    rw [Real.sqrt_lt (by norm_num) (by norm_num)]
    norm_num
  have hlower : 24.49 < sqrt (2 * 5 * 60 : ℝ) := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  rw [abs_sub_lt_iff]
  constructor
  · linarith
  · linarith

end
