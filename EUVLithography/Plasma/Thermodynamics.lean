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

end
