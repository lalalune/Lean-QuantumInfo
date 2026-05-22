import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# EUV Lithography: Plasma Thermodynamics

Algebraic formalization of plasma pressure, electron-ion equilibration-time
positivity, and two-temperature source-term balances appearing in the EUV report.
-/

noncomputable section

open Real

/-- Plasma pressure written with ion density: `P = (Z + 1) n_i kT`. -/
def plasmaPressureIon (Z n_i kT : ℝ) : ℝ :=
  (Z + 1) * n_i * kT

/-- Plasma pressure written with electron density and charge neutrality `n_e = Z n_i`. -/
def plasmaPressureElectron (Z n_e kT : ℝ) : ℝ :=
  n_e * kT * (1 + 1 / Z)

theorem plasmaPressureIon_pos {Z n_i kT : ℝ}
    (hZ : 0 < Z) (hni : 0 < n_i) (hkT : 0 < kT) :
    0 < plasmaPressureIon Z n_i kT := by
  unfold plasmaPressureIon
  positivity

theorem plasmaPressure_forms_equal {Z n_i n_e kT : ℝ}
    (hZ : Z ≠ 0) (hne : n_e = Z * n_i) :
    plasmaPressureIon Z n_i kT = plasmaPressureElectron Z n_e kT := by
  unfold plasmaPressureIon plasmaPressureElectron
  rw [hne]
  field_simp [hZ]

/-- Plasma pressure increases with ion density at fixed charge state and temperature. -/
theorem plasmaPressureIon_increases_with_density {Z n₁ n₂ kT : ℝ}
    (hZ : 0 < Z) (hn : n₁ < n₂) (hkT : 0 < kT) :
    plasmaPressureIon Z n₁ kT < plasmaPressureIon Z n₂ kT := by
  unfold plasmaPressureIon
  exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left hn (by linarith)) hkT

/-- Plasma pressure increases with electron temperature at fixed charge state and density. -/
theorem plasmaPressureIon_increases_with_temperature {Z n_i kT₁ kT₂ : ℝ}
    (hZ : 0 < Z) (hni : 0 < n_i) (hkT : kT₁ < kT₂) :
    plasmaPressureIon Z n_i kT₁ < plasmaPressureIon Z n_i kT₂ := by
  unfold plasmaPressureIon
  exact mul_lt_mul_of_pos_left hkT (mul_pos (by linarith) hni)

/-- Plasma pressure increases with mean ion charge at fixed ion density and temperature. -/
theorem plasmaPressureIon_increases_with_charge {Z₁ Z₂ n_i kT : ℝ}
    (hZ : Z₁ < Z₂) (hni : 0 < n_i) (hkT : 0 < kT) :
    plasmaPressureIon Z₁ n_i kT < plasmaPressureIon Z₂ n_i kT := by
  unfold plasmaPressureIon
  have hZ' : Z₁ + 1 < Z₂ + 1 := by linarith
  exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hZ' hni) hkT

/-- Electron-ion equilibration-time scaling from the report. -/
def electronIonEquilibrationTime
    (m_e m_i n_e Z e lnΛ kT_e kT_i fourPiEps0Sq : ℝ) : ℝ :=
  (3 * m_e * m_i) / (8 * Real.sqrt (2 * π) * n_e * Z ^ 2 * e ^ 4 * lnΛ) *
    (kT_e / m_e + kT_i / m_i) ^ (3 / 2 : ℝ) * fourPiEps0Sq

theorem electronIonEquilibrationTime_pos
    {m_e m_i n_e Z e lnΛ kT_e kT_i fourPiEps0Sq : ℝ}
    (hme : 0 < m_e) (hmi : 0 < m_i) (hne : 0 < n_e) (hZ : 0 < Z)
    (he : 0 < e) (hln : 0 < lnΛ) (hkTe : 0 < kT_e) (hkTi : 0 < kT_i)
    (hfour : 0 < fourPiEps0Sq) :
    0 < electronIonEquilibrationTime m_e m_i n_e Z e lnΛ kT_e kT_i fourPiEps0Sq := by
  unfold electronIonEquilibrationTime
  have hpi2 : 0 < Real.sqrt (2 * π) :=
    Real.sqrt_pos.mpr (mul_pos two_pos pi_pos)
  have hbase : 0 < kT_e / m_e + kT_i / m_i :=
    add_pos (div_pos hkTe hme) (div_pos hkTi hmi)
  positivity

/-- Electron temperature equation right-hand side in the two-temperature model. -/
def electronTemperatureRHS
    (kappaIB I n_e cve T_e T_i tau_ei conduction : ℝ) : ℝ :=
  kappaIB * I - n_e * cve * (T_e - T_i) / tau_ei + conduction

/-- Ion temperature equation right-hand side in the two-temperature model. -/
def ionTemperatureRHS (n_e cve T_e T_i tau_ei : ℝ) : ℝ :=
  n_e * cve * (T_e - T_i) / tau_ei

theorem coupling_terms_cancel (kappaIB I n_e cve T_e T_i tau_ei conduction : ℝ) :
    electronTemperatureRHS kappaIB I n_e cve T_e T_i tau_ei conduction +
      ionTemperatureRHS n_e cve T_e T_i tau_ei =
    kappaIB * I + conduction := by
  unfold electronTemperatureRHS ionTemperatureRHS
  ring

/-- When electron and ion temperatures are equal, there is no ion heating from equilibration. -/
theorem ionTemperatureRHS_eq_zero_at_equal_temperature (n_e cve T tau_ei : ℝ) :
    ionTemperatureRHS n_e cve T T tau_ei = 0 := by
  unfold ionTemperatureRHS
  ring

/-- When electrons are hotter than ions, the coupling term heats ions. -/
theorem ionTemperatureRHS_pos_of_electron_hotter {n_e cve T_e T_i tau_ei : ℝ}
    (hne : 0 < n_e) (hcve : 0 < cve) (hT : T_i < T_e) (htau : 0 < tau_ei) :
    0 < ionTemperatureRHS n_e cve T_e T_i tau_ei := by
  unfold ionTemperatureRHS
  exact div_pos (mul_pos (mul_pos hne hcve) (sub_pos.mpr hT)) htau

/-- With equal electron and ion temperatures, electron RHS is just absorption plus conduction. -/
theorem electronTemperatureRHS_eq_absorption_plus_conduction_at_equal_temperature
    (kappaIB I n_e cve T tau_ei conduction : ℝ) :
    electronTemperatureRHS kappaIB I n_e cve T T tau_ei conduction =
      kappaIB * I + conduction := by
  unfold electronTemperatureRHS
  ring

/-- If electrons are hotter, equilibration lowers the electron RHS below absorption plus conduction. -/
theorem electronTemperatureRHS_lt_absorption_plus_conduction_of_electron_hotter
    {kappaIB I n_e cve T_e T_i tau_ei conduction : ℝ}
    (hne : 0 < n_e) (hcve : 0 < cve) (hT : T_i < T_e) (htau : 0 < tau_ei) :
    electronTemperatureRHS kappaIB I n_e cve T_e T_i tau_ei conduction <
      kappaIB * I + conduction := by
  unfold electronTemperatureRHS
  have hpos : 0 < n_e * cve * (T_e - T_i) / tau_ei :=
    div_pos (mul_pos (mul_pos hne hcve) (sub_pos.mpr hT)) htau
  linarith

end
