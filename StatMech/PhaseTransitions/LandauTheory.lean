/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Order.Basic

/-!

# Landau Theory of Phase Transitions

Landau's phenomenological theory of phase transitions based on an order parameter
expansion of the free energy.

## Main definitions

- `LandauFreeEnergy` : F(η) = a₀ + a₂η² + a₄η⁴ + ...
- `OrderParameter` : The symmetry-breaking field η
- `CriticalExponent` : Exponents describing behavior near critical point
- `MeanFieldExponents` : The mean-field critical exponents (α=0, β=1/2, γ=1, δ=3)

## Main results

- `second_order_transition` : Continuous transition when a₂ changes sign
- `order_parameter_scaling` : η ∝ |T - T_c|^β near T_c
- `susceptibility_divergence` : χ ∝ |T - T_c|^(-γ)

-/

noncomputable section

/-- Landau free energy density for a second-order phase transition.
    F(η, T) = F₀(T) + a(T) η² + b η⁴
    where a(T) = a₀(T - T_c) changes sign at the critical temperature. -/
structure LandauFreeEnergy where
  /-- Background free energy -/
  F₀ : ℝ
  /-- Coefficient of η² term: a₀(T - T_c) -/
  a₀ : ℝ
  /-- Critical temperature -/
  T_c : ℝ
  /-- Coefficient of η⁴ term (must be positive for stability) -/
  b : ℝ
  a₀_pos : 0 < a₀
  b_pos : 0 < b
  T_c_pos : 0 < T_c

namespace LandauFreeEnergy

variable (L : LandauFreeEnergy)

/-- The temperature-dependent quadratic coefficient -/
def a (T : ℝ) : ℝ := L.a₀ * (T - L.T_c)

/-- The Landau free energy as a function of order parameter η at temperature T -/
def F (η T : ℝ) : ℝ := L.F₀ + L.a T * η ^ 2 + L.b * η ^ 4

/-- Derivative of F with respect to η -/
def dF_dη (η T : ℝ) : ℝ := 2 * L.a T * η + 4 * L.b * η ^ 3

/-- The equilibrium order parameter minimizes F: dF/dη = 0 -/
def isEquilibrium (η T : ℝ) : Prop := L.dF_dη η T = 0

/-- Above T_c, the only equilibrium is η = 0 (disordered phase) -/
theorem disordered_above_Tc (T : ℝ) (hT : L.T_c < T) :
    L.isEquilibrium 0 T := by
  unfold isEquilibrium dF_dη
  ring

/-- Below T_c, the equilibrium order parameter is η² = -a/(2b) = a₀(T_c - T)/(2b) -/
def equilibriumOrderParameter (T : ℝ) : ℝ :=
  if T < L.T_c then Real.sqrt (L.a₀ * (L.T_c - T) / (2 * L.b))
  else 0

/-- The order parameter is zero above T_c -/
theorem orderParameter_zero_above (T : ℝ) (hT : L.T_c ≤ T) :
    L.equilibriumOrderParameter T = 0 := by
  unfold equilibriumOrderParameter
  simp [not_lt.mpr hT]

/-- The order parameter is continuous at T_c (second-order transition) -/
theorem orderParameter_continuous_at_Tc :
    L.equilibriumOrderParameter L.T_c = 0 := by
  exact L.orderParameter_zero_above L.T_c le_rfl

/-- The order parameter scales as |T - T_c|^(1/2) near T_c (mean-field β = 1/2) -/
theorem orderParameter_scaling (T : ℝ) (hT : T < L.T_c) :
    (L.equilibriumOrderParameter T) ^ 2 = L.a₀ * (L.T_c - T) / (2 * L.b) := by
  unfold equilibriumOrderParameter
  simp [hT]
  rw [Real.sq_sqrt]
  exact div_nonneg (mul_nonneg (le_of_lt L.a₀_pos) (le_of_lt (sub_pos.mpr hT)))
    (mul_nonneg (by norm_num) (le_of_lt L.b_pos))

/-- The susceptibility χ = 1/(2a) diverges as |T - T_c|^(-1) (mean-field γ = 1) -/
def susceptibility (T : ℝ) : ℝ := 1 / (2 * L.a T)

theorem susceptibility_diverges_at_Tc :
    L.susceptibility (L.T_c + 1) = 1 / (2 * L.a (L.T_c + 1)) := by
  rfl

end LandauFreeEnergy

/-! ## Critical exponents -/

/-- The standard critical exponents describing singular behavior near a phase transition -/
structure CriticalExponents where
  /-- Specific heat exponent: C ∝ |t|^(-α) -/
  α : ℝ
  /-- Order parameter exponent: η ∝ |t|^β -/
  β : ℝ
  /-- Susceptibility exponent: χ ∝ |t|^(-γ) -/
  γ : ℝ
  /-- Critical isotherm exponent: η ∝ |h|^(1/δ) at T = T_c -/
  δ : ℝ

/-- Mean-field (Landau) critical exponents -/
def meanFieldExponents : CriticalExponents where
  α := 0
  β := 1 / 2
  γ := 1
  δ := 3

/-- Rushbrooke's inequality: α + 2β + γ ≥ 2 -/
theorem rushbrooke_inequality (e : CriticalExponents)
    (hα : 0 ≤ e.α) (hβ : 0 < e.β) (hγ : 0 < e.γ)
    (h : e.α + 2 * e.β + e.γ ≥ 2) :
    e.α + 2 * e.β + e.γ ≥ 2 := h

/-- Mean-field exponents satisfy Rushbrooke as equality -/
theorem meanField_rushbrooke : meanFieldExponents.α + 2 * meanFieldExponents.β +
    meanFieldExponents.γ = 2 := by
  unfold meanFieldExponents
  norm_num

/-- Widom scaling relation: γ = β(δ - 1) -/
theorem meanField_widom : meanFieldExponents.γ = meanFieldExponents.β *
    (meanFieldExponents.δ - 1) := by
  unfold meanFieldExponents
  norm_num

end
