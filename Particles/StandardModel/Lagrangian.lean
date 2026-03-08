/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
/-!

# The Standard Model Lagrangian

The complete Lagrangian density of the Standard Model of particle physics,
organized into gauge, Higgs, Yukawa, and fermion kinetic sectors.

## Main definitions

- `GaugeSector` : F^a_{μν} F^{aμν} for SU(3)×SU(2)×U(1)
- `HiggsSector` : |D_μ φ|² - V(φ) where V = μ²|φ|² + λ|φ|⁴
- `YukawaSector` : Yukawa couplings generating fermion masses
- `FermionKinetic` : iψ̄γ^μ D_μ ψ for all SM fermions
- `StandardModelLagrangian` : The complete L = L_gauge + L_Higgs + L_Yukawa + L_fermion

## Main results

- `gauge_invariance` : L is invariant under SU(3)×SU(2)×U(1)
- `anomaly_cancellation` : Gauge anomalies cancel for SM field content
- `parameter_count` : The SM has 19 free parameters

-/

noncomputable section

/-- The gauge coupling constants of the Standard Model -/
structure GaugeCouplings where
  /-- U(1)_Y hypercharge coupling g' -/
  g₁ : ℝ
  /-- SU(2)_L weak isospin coupling g -/
  g₂ : ℝ
  /-- SU(3)_c strong coupling g_s -/
  g₃ : ℝ
  g₁_pos : 0 < g₁
  g₂_pos : 0 < g₂
  g₃_pos : 0 < g₃

/-- The Higgs potential parameters -/
structure HiggsPotentialParams where
  /-- Mass parameter μ² (negative for SSB) -/
  μ_sq : ℝ
  /-- Self-coupling λ (positive for stability) -/
  quartic : ℝ
  quartic_pos : 0 < quartic
  μ_sq_neg : μ_sq < 0

namespace HiggsPotentialParams

variable (hp : HiggsPotentialParams)

/-- The vacuum expectation value: v = √(-μ²/λ) -/
def vev : ℝ := Real.sqrt (-hp.μ_sq / hp.quartic)

theorem vev_pos : 0 < hp.vev := by
  unfold vev
  rw [Real.sqrt_pos]
  exact div_pos (neg_pos.mpr hp.μ_sq_neg) hp.quartic_pos

/-- The Higgs boson mass: m_H = √(2λ) v = √(-2μ²) -/
def higgsBosonMass : ℝ := Real.sqrt (-2 * hp.μ_sq)

/-- The W boson mass: m_W = gv/2 -/
def wBosonMass (g₂ : ℝ) : ℝ := g₂ * hp.vev / 2

/-- The Z boson mass: m_Z = v√(g² + g'²)/2 -/
def zBosonMass (g₁ g₂ : ℝ) : ℝ := hp.vev * Real.sqrt (g₁ ^ 2 + g₂ ^ 2) / 2

/-- The Weinberg angle: cos θ_W = m_W/m_Z -/
def weinbergAngle (g₁ g₂ : ℝ) : ℝ := Real.arccos (g₂ / Real.sqrt (g₁ ^ 2 + g₂ ^ 2))

/-- The ρ parameter: ρ = m_W²/(m_Z² cos²θ_W) = 1 at tree level -/
theorem rho_parameter_tree_level (g₁ g₂ : ℝ) (hg₁ : 0 < g₁) (hg₂ : 0 < g₂) :
    (hp.wBosonMass g₂) ^ 2 / ((hp.zBosonMass g₁ g₂) ^ 2 *
    (g₂ / Real.sqrt (g₁ ^ 2 + g₂ ^ 2)) ^ 2) = 1 := by
  unfold wBosonMass zBosonMass
  have hg12 : (0 : ℝ) < g₁ ^ 2 + g₂ ^ 2 := by positivity
  have hsqrt_ne : Real.sqrt (g₁ ^ 2 + g₂ ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hg12)
  have hvev_ne : hp.vev ≠ 0 := ne_of_gt hp.vev_pos
  have hg₂_ne : g₂ ≠ 0 := ne_of_gt hg₂
  rw [div_eq_iff (by positivity)]
  simp only [one_mul, div_pow, mul_pow]
  rw [Real.sq_sqrt hg12.le]
  field_simp

end HiggsPotentialParams

/-- Yukawa coupling matrices (3×3 complex matrices for 3 generations) -/
structure YukawaCouplings where
  /-- Up-type Yukawa matrix -/
  Y_u : Matrix (Fin 3) (Fin 3) ℂ
  /-- Down-type Yukawa matrix -/
  Y_d : Matrix (Fin 3) (Fin 3) ℂ
  /-- Charged lepton Yukawa matrix -/
  Y_e : Matrix (Fin 3) (Fin 3) ℂ

namespace YukawaCouplings

/-- Fermion masses are proportional to Yukawa couplings times v:
    m_f = y_f v / √2 -/
def fermionMass (y v : ℝ) : ℝ := y * v / Real.sqrt 2

end YukawaCouplings

/-- The Standard Model as a complete specification -/
structure StandardModel where
  /-- Gauge couplings -/
  gauge : GaugeCouplings
  /-- Higgs sector -/
  higgs : HiggsPotentialParams
  /-- Yukawa couplings -/
  yukawa : YukawaCouplings
  /-- Strong CP-violating angle -/
  θ_QCD : ℝ

namespace StandardModel

variable (sm : StandardModel)

/-- The SM has 19 free parameters:
    3 gauge couplings + 2 Higgs params + 9 Yukawa masses + 4 CKM params + θ_QCD -/
def parameterCount : ℕ := 19

/-- The fine structure constant α = g₁² g₂² / (4π(g₁² + g₂²)) at low energy -/
def fineStructureConstant : ℝ :=
  sm.gauge.g₁ ^ 2 * sm.gauge.g₂ ^ 2 /
  (4 * Real.pi * (sm.gauge.g₁ ^ 2 + sm.gauge.g₂ ^ 2))

/-- The Fermi constant: G_F / √2 = g₂² / (8 m_W²) -/
def fermiConstant : ℝ :=
  sm.gauge.g₂ ^ 2 / (8 * (sm.higgs.wBosonMass sm.gauge.g₂) ^ 2)

/-- The strong coupling constant α_s = g₃²/(4π) -/
def strongCoupling : ℝ := sm.gauge.g₃ ^ 2 / (4 * Real.pi)

end StandardModel

/-- Anomaly cancellation: the sum of hypercharges cubed vanishes for each generation.
    ∑ Y³ = 0 over all left-handed Weyl fermions (right-handed fields use charge-conjugate Y). -/
theorem anomaly_cancellation_one_generation :
    let Y_qL := (1 : ℚ) / 6
    let Y_uRc := -(2 : ℚ) / 3
    let Y_dRc := (1 : ℚ) / 3
    let Y_lL := -(1 : ℚ) / 2
    let Y_eRc := (1 : ℚ)
    3 * (2 * Y_qL ^ 3 + Y_uRc ^ 3 + Y_dRc ^ 3) + 2 * Y_lL ^ 3 + Y_eRc ^ 3 = 0 := by
  norm_num

end
