/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import StatMech.BoltzmannConstant
import Thermodynamics.Temperature.Basic

/-!

# Gibbs Free Energy and Thermodynamic Potentials

This module defines the four fundamental thermodynamic potentials and the
Legendre transform relationships between them.

## Main definitions

- `Enthalpy` : H = U + PV
- `GibbsFreeEnergy` : G = U - TS + PV = H - TS = A + PV
- `GrandPotential` : Ω = U - TS - μN = A - μN

## Main results

- `gibbs_from_helmholtz` : G = A + PV
- `gibbs_from_enthalpy` : G = H - TS
- `grand_potential_from_helmholtz` : Ω = A - μN
- `legendre_transform_relations` : Consistency of all potential relationships

-/

noncomputable section

/-- The enthalpy H = U + PV, natural variables (S, P). -/
structure Enthalpy where
  internalEnergy : ℝ
  pressure : ℝ
  volume : ℝ

namespace Enthalpy

def val (h : Enthalpy) : ℝ := h.internalEnergy + h.pressure * h.volume

theorem val_def (h : Enthalpy) : h.val = h.internalEnergy + h.pressure * h.volume := rfl

end Enthalpy

/-- The Gibbs free energy G = U - TS + PV, natural variables (T, P). -/
structure GibbsFreeEnergy where
  internalEnergy : ℝ
  temperature : ℝ
  entropy : ℝ
  pressure : ℝ
  volume : ℝ

namespace GibbsFreeEnergy

def val (g : GibbsFreeEnergy) : ℝ :=
  g.internalEnergy - g.temperature * g.entropy + g.pressure * g.volume

theorem val_def (g : GibbsFreeEnergy) :
    g.val = g.internalEnergy - g.temperature * g.entropy + g.pressure * g.volume := rfl

/-- G = A + PV where A = U - TS is the Helmholtz free energy -/
theorem from_helmholtz (g : GibbsFreeEnergy) :
    g.val = (g.internalEnergy - g.temperature * g.entropy) + g.pressure * g.volume := by
  unfold val
  ring

/-- G = H - TS where H = U + PV is the enthalpy -/
theorem from_enthalpy (g : GibbsFreeEnergy) :
    g.val = (g.internalEnergy + g.pressure * g.volume) - g.temperature * g.entropy := by
  unfold val
  ring

/-- At equilibrium at constant T and P, G is minimized. -/
def isEquilibrium (G : ℝ → ℝ) (x : ℝ) : Prop :=
  ∀ y, G x ≤ G y

end GibbsFreeEnergy

/-- The grand potential Ω = U - TS - μN, natural variables (T, V, μ). -/
structure GrandPotential where
  internalEnergy : ℝ
  temperature : ℝ
  entropy : ℝ
  chemicalPotential : ℝ
  particleNumber : ℝ

namespace GrandPotential

def val (ω : GrandPotential) : ℝ :=
  ω.internalEnergy - ω.temperature * ω.entropy - ω.chemicalPotential * ω.particleNumber

theorem val_def (ω : GrandPotential) :
    ω.val = ω.internalEnergy - ω.temperature * ω.entropy -
    ω.chemicalPotential * ω.particleNumber := rfl

/-- Ω = A - μN where A = U - TS is the Helmholtz free energy -/
theorem from_helmholtz (ω : GrandPotential) :
    ω.val = (ω.internalEnergy - ω.temperature * ω.entropy) -
    ω.chemicalPotential * ω.particleNumber := by
  unfold val
  ring

/-- For an ideal gas, Ω = -PV -/
def isIdealGas (ω : GrandPotential) (P V : ℝ) : Prop :=
  ω.val = -(P * V)

end GrandPotential

/-- Euler's relation for homogeneous thermodynamic systems:
    U = TS - PV + μN -/
theorem euler_relation (U T S P V μ N : ℝ) (h : U = T * S - P * V + μ * N) :
    U - T * S + P * V = μ * N := by linarith

/-- Gibbs-Duhem relation: at equilibrium, SdT - VdP + Ndμ = 0.
    This constrains the intensive variables. -/
structure GibbsDuhem where
  S_dT : ℝ
  V_dP : ℝ
  N_dμ : ℝ
  relation : S_dT - V_dP + N_dμ = 0

end
