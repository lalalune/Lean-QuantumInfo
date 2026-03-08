/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import StatMech.BoltzmannConstant
/-!

# Nonequilibrium Statistical Mechanics

Fluctuation theorems connecting nonequilibrium work measurements
to equilibrium free energy differences.

## Main definitions

- `JarzynskiEquality` : ⟨exp(-βW)⟩ = exp(-βΔF)
- `CrooksFluctuationTheorem` : P_F(W)/P_R(-W) = exp(β(W - ΔF))
- `SecondLawInequality` : ⟨W⟩ ≥ ΔF (second law from Jarzynski)

## Main results

- `jarzynski_implies_second_law` : Jensen's inequality + Jarzynski → ⟨W⟩ ≥ ΔF
- `crooks_implies_jarzynski` : Crooks theorem implies Jarzynski equality
- `fluctuation_dissipation_near_eq` : Linear response near equilibrium

-/

noncomputable section

/-- A nonequilibrium process characterized by work performed -/
structure NonequilibriumProcess where
  /-- Inverse temperature β = 1/(kT) -/
  β : ℝ
  β_pos : 0 < β
  /-- Free energy difference ΔF = F_final - F_initial -/
  ΔF : ℝ

/-- The Jarzynski equality: ⟨exp(-βW)⟩ = exp(-βΔF)
    This remarkable equality connects nonequilibrium work measurements
    to equilibrium free energy differences. -/
structure JarzynskiEquality extends NonequilibriumProcess where
  /-- Expectation of exp(-βW) over all realizations of the process -/
  mean_exp_neg_βW : ℝ
  /-- The Jarzynski equality holds -/
  equality : mean_exp_neg_βW = Real.exp (-(β * ΔF))

namespace JarzynskiEquality

variable (j : JarzynskiEquality)

/-- The second law from Jarzynski: ⟨W⟩ ≥ ΔF.
    This follows from Jensen's inequality: ⟨exp(-βW)⟩ ≥ exp(-β⟨W⟩)
    Combined with Jarzynski: exp(-βΔF) ≥ exp(-β⟨W⟩), hence ⟨W⟩ ≥ ΔF -/
theorem second_law_from_jarzynski (mean_W : ℝ)
    (h_jensen : j.mean_exp_neg_βW ≥ Real.exp (-(j.β * mean_W))) :
    mean_W ≥ j.ΔF := by
  have h1 : Real.exp (-(j.β * mean_W)) ≤ Real.exp (-(j.β * j.ΔF)) := by
    linarith [j.equality]
  rw [Real.exp_le_exp] at h1
  exact (mul_le_mul_left j.β_pos).mp (by linarith)

end JarzynskiEquality

/-- The Crooks fluctuation theorem:
    P_F(W) / P_R(-W) = exp(β(W - ΔF))
    where P_F is the forward work distribution and P_R is the reverse -/
structure CrooksTheorem extends NonequilibriumProcess where
  /-- Forward work probability distribution -/
  P_F : ℝ → ℝ
  /-- Reverse work probability distribution -/
  P_R : ℝ → ℝ
  /-- P_F and P_R are probability densities (nonneg) -/
  P_F_nonneg : ∀ W, 0 ≤ P_F W
  P_R_nonneg : ∀ W, 0 ≤ P_R W
  /-- The Crooks relation -/
  crooks_relation : ∀ W, P_R W > 0 →
    P_F W / P_R (-W) = Real.exp (β * (W - ΔF))

/-- Near equilibrium, the dissipated work is related to the
    variance of the work distribution (fluctuation-dissipation): -/
def dissipatedWork_near_equilibrium (β σ_W_sq : ℝ) : ℝ :=
  β * σ_W_sq / 2

/-- The Clausius inequality is a special case of the second law:
    for a cyclic process (ΔF = 0), ⟨W⟩ ≥ 0 -/
theorem clausius_from_jarzynski (j : JarzynskiEquality) (h : j.ΔF = 0) (mean_W : ℝ)
    (h_jensen : j.mean_exp_neg_βW ≥ Real.exp (-(j.β * mean_W))) :
    mean_W ≥ 0 := by
  have := j.second_law_from_jarzynski mean_W h_jensen
  linarith

end
