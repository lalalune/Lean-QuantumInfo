import EUVLithography.Constants
import EUVLithography.Source.EUVEmission
import EUVLithography.Source.TinDroplet
import EUVLithography.Contamination.MirrorPhysics
import EUVLithography.GasPhysics.BeerLambert
import EUVLithography.Optics.Etendue
import EUVLithography.Optics.BraggCondition
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
open EUVConstants

theorem report_euv_power_30kW_6pct :
    (0.06 : ℝ) * 30000 = 1800 := by norm_num

theorem report_planck_constant_table_rounding :
    |(planckConstantSI : ℝ) - 6.626e-34| < (0.001e-34 : ℝ) := by
  norm_num [planckConstantSI]

theorem report_reduced_planck_table_rounding :
    |(ReducedPlanckConstant.si : ℝ) - 1.055e-34| < (0.001e-34 : ℝ) := by
  norm_num [ReducedPlanckConstant.si]

theorem report_elementary_charge_table_rounding :
    |(elementaryChargeSI : ℝ) - 1.602e-19| < (0.001e-19 : ℝ) := by
  norm_num [elementaryChargeSI]

theorem report_electron_mass_table_rounding :
    |(electronMassSI : ℝ) - 9.109e-31| < (0.001e-31 : ℝ) := by
  norm_num [electronMassSI]

theorem report_tin118_mass_table_value :
    (tin118MassSI : ℝ) = (1.975e-25 : ℝ) := by
  norm_num [tin118MassSI]

theorem report_boltzmann_constant_table_rounding :
    |(BoltzmannConstant.si : ℝ) - 1.381e-23| < (0.001e-23 : ℝ) := by
  norm_num [BoltzmannConstant.si]

theorem report_vacuum_permittivity_table_rounding :
    |(vacuumPermittivitySI : ℝ) - 8.854e-12| < (0.001e-12 : ℝ) := by
  norm_num [vacuumPermittivitySI]

theorem report_vacuum_permeability_table_rounding :
    |(vacuumPermeabilitySI : ℝ) - 1.257e-6| < (0.001e-6 : ℝ) := by
  norm_num [vacuumPermeabilitySI]

theorem report_avogadro_table_rounding :
    |(avogadroNumberSI : ℝ) - 6.022e23| < (0.001e23 : ℝ) := by
  norm_num [avogadroNumberSI]

theorem report_ce_energy_ratio_numeric :
    EUVSource.conversionEfficiencyFromEnergies 1800 30000 = (0.06 : ℝ) := by
  norm_num [EUVSource.conversionEfficiencyFromEnergies]

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

theorem report_timing_jitter_displacement_low_numeric :
    timingJitterDisplacement 50 (1e-9) * 1e9 = (50 : ℝ) := by
  norm_num [timingJitterDisplacement]

theorem report_timing_jitter_displacement_high_numeric :
    timingJitterDisplacement 70 (1e-9) * 1e9 = (70 : ℝ) := by
  norm_num [timingJitterDisplacement]

theorem report_volume_conserving_disk_thickness_10x_30um :
    volumeConservingDiskThickness 10 30 = (0.2 : ℝ) := by
  norm_num [volumeConservingDiskThickness]

theorem report_10nm_square_area_cm2 :
    ((10 : ℝ) * 1e-7) ^ 2 = 1e-12 := by
  norm_num

theorem report_photon_count_numeric :
    |photonCount 40 (100e-14) 91.8 - 2720| < 5 := by
  norm_num [photonCount]

theorem report_euv_photon_energy_joule_from_eV :
    |eVToJoule ElectronVolt.si 91.8 - 1.470798150012e-17| < (1e-29 : ℝ) := by
  norm_num [eVToJoule, ElectronVolt.si]

theorem report_shot_noise_fraction_2700_between_1_9_and_2_percent :
    (0.019 : ℝ) < 1 / sqrt 2700 ∧ 1 / sqrt 2700 < (0.02 : ℝ) := by
  have hsqrt_pos : 0 < sqrt (2700 : ℝ) := sqrt_pos_of_pos (by norm_num)
  have hsqrt_sq : (sqrt (2700 : ℝ)) ^ 2 = 2700 := by
    rw [sq_sqrt (by norm_num)]
  constructor
  · rw [lt_div_iff₀ hsqrt_pos]
    have hprod_nonneg : 0 ≤ (0.019 : ℝ) * sqrt 2700 := by positivity
    have hsq : ((0.019 : ℝ) * sqrt 2700) ^ 2 < (1 : ℝ) ^ 2 := by
      nlinarith
    have habs := sq_lt_sq.mp hsq
    rwa [abs_of_nonneg hprod_nonneg, abs_of_pos one_pos] at habs
  · rw [div_lt_iff₀ hsqrt_pos]
    have hprod_pos : 0 < (0.02 : ℝ) * sqrt 2700 := by positivity
    have hsq : (1 : ℝ) ^ 2 < ((0.02 : ℝ) * sqrt 2700) ^ 2 := by
      nlinarith
    have habs := sq_lt_sq.mp hsq
    rwa [abs_of_pos one_pos, abs_of_pos hprod_pos] at habs

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

theorem report_focused_intensity_numeric :
    |(2 * 30000 / (π * (14.8e-6 : ℝ) ^ 2) / 1e4) - 8.7e9| < 0.1e9 := by
  have hden : 0 < (π * (14.8e-6 : ℝ) ^ 2) := mul_pos pi_pos (by norm_num)
  have hupper : (2 * 30000 / (π * (14.8e-6 : ℝ) ^ 2) / 1e4) < 8.8e9 := by
    rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 1e4)]
    rw [div_lt_iff₀ hden]
    nlinarith [Real.pi_gt_d2]
  have hlower : (8.6e9 : ℝ) < 2 * 30000 / (π * (14.8e-6 : ℝ) ^ 2) / 1e4 := by
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 1e4)]
    rw [lt_div_iff₀ hden]
    nlinarith [Real.pi_lt_d2]
  rw [abs_sub_lt_iff]
  constructor
  · linarith
  · linarith

theorem report_bragg_period_normal_numeric :
    (13.5 : ℝ) / 2 = 6.75 := by
  norm_num

theorem report_mo_si_nominal_period_numeric :
    (2.8 : ℝ) + 4.1 = 6.9 := by
  norm_num

theorem report_euv_bandwidth_one_percent_halfwidth :
    EUVSource.wavelengthHalfBandwidth 0.01 13.5 = (0.135 : ℝ) := by
  norm_num [EUVSource.wavelengthHalfBandwidth]

theorem report_euv_bandwidth_two_percent_fullwidth :
    EUVSource.wavelengthFullBandwidth 0.01 13.5 = (0.27 : ℝ) := by
  norm_num [EUVSource.wavelengthFullBandwidth, EUVSource.wavelengthHalfBandwidth]

theorem report_vacuum_pressure_requirement_numeric :
    (10 ^ 5 : ℝ) * (0.2 * 10 ^ (-3 : ℤ)) / 10 = 2 := by
  norm_num

theorem report_h2_absorption_length_stp_numeric :
    |h2At135nm.absorptionLength 101325 - 0.63| < (0.01 : ℝ) := by
  norm_num [GasAttenuation.absorptionLength, GasAttenuation.attenuationCoeff,
    GasAttenuation.massDensity, h2At135nm]

theorem report_h2_absorption_length_standard_atmosphere_numeric :
    |h2At135nm.absorptionLength (StandardAtmosphere.si : ℝ) - 0.63| < (0.01 : ℝ) := by
  norm_num [GasAttenuation.absorptionLength, GasAttenuation.attenuationCoeff,
    GasAttenuation.massDensity, h2At135nm, StandardAtmosphere.si]

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

theorem report_resist_absorption_depth_low_alpha_nm :
    absorptionDepthFromCoeff 4 * 1000 = (250 : ℝ) := by
  norm_num [absorptionDepthFromCoeff]

theorem report_resist_absorption_depth_high_alpha_nm :
    |absorptionDepthFromCoeff 6 * 1000 - 166.66666666666666| < (0.001 : ℝ) := by
  norm_num [absorptionDepthFromCoeff]

end
