/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import Relativity.LorentzBoost.TTime

/-!
# Thermal Time: A Second Derivation of Special Relativity

This file provides the documented interface for thermal time theory.
**All proofs live in `TTime.lean`**; this module re-exports them with the `ThermalTime`
namespace for documentation and historical context (Connes-Rovelli 1994).

## Historical Context

**Einstein (1905)**: Postulated the constancy of light speed → derived time dilation

**Connes-Rovelli (1994)**: Proposed t = (ℏ/2πk_B) · τ/T as the thermal time hypothesis

**This file (2026)**: Proves t = c·τ/T is the UNIQUE covariant form, and derives
time dilation from it combined with Ott (see `TTime.lean`)

We now have two independent derivations of special relativistic time dilation:
1. Kinematic (Einstein): constancy of c
2. Thermodynamic (this file via TTime): Ott + thermal time uniqueness

## Main Results (from `ThermalTimeBasic` and `ThermalTimeConsequences`)

- `thermalTime_unique` — the form f(T,τ) = c·τ/T is forced by Lorentz covariance
- `thermal_time_gives_time_dilation` — time dilation emerges from Ott + thermal time
- `modular_hamiltonian_invariant` — K = H/T is a Lorentz scalar
- `unruh_from_modular_period` — the 2π in T_U = a/(2π) is modular periodicity
- `rindler_thermodynamics_covariant` — Clausius relation δQ = TdS is Lorentz covariant
- `thermal_to_ground_state_limit` — quantum mechanics emerges as T → 0

## References

* Connes, Rovelli, *Von Neumann algebra automorphisms and time-thermodynamics relation*, Class. Quantum Grav. 11 (1994)
* Jacobson, *Thermodynamics of Spacetime*, PRL 75 (1995)
* Takesaki, *Tomita's Theory of Modular Hilbert Algebras* (1970)
-/

namespace ThermalTime
-- Re-export core thermal time from TTime for the documented `ThermalTime` namespace
export ThermalTimeBasic (
  thermalTime thermal_time_gives_time_dilation lorentzGamma_surjective_ge_one
  satisfiesCovariance functional_equation_solution thermalTime_unique thermalTime_inverse_unique
  modular_parameter_recovery thermal_time_scale_invariant thermal_time_homogeneous
  thermal_time_determines_modular_structure modular_period one_cycle_thermal_time
  thermal_time_physical_units
)

export ThermalTimeBasic.ThermalTimeConsequences (
  inverse_temperature modularHamiltonian modular_hamiltonian_invariant unruhTemperature
  unruh_from_modular_period unruh_temperature_pos boosted_unruh_temperature
  LocalRindlerThermodynamics rindler_thermodynamics_covariant wheeler_dewitt_constraint
  thermalDensityMatrix thermal_to_ground_state_limit thermal_time_consistency
)

end ThermalTime
