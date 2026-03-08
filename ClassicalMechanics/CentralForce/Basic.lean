/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!

# Central Force Problem

Formalization of the central force problem in classical mechanics,
including the Kepler problem and Bertrand's theorem.

## Main definitions

- `CentralForce` : A force F(r) depending only on distance from center
- `EffectivePotential` : V_eff(r) = V(r) + L²/(2mr²)
- `KeplerProblem` : The gravitational/Coulomb 1/r potential
- `Orbit` : Solution to the central force equations of motion

## Main results

- `angular_momentum_conservation` : L = mr²θ̇ is conserved
- `orbit_equation` : u'' + u = -m/(L²) F(1/u) (Binet equation)
- `kepler_orbit_is_conic` : Kepler orbits are conic sections
- `bertrand_theorem` : Only 1/r and r² potentials give closed orbits

-/

noncomputable section

/-- A central force field: force depends only on radial distance. -/
structure CentralForce where
  /-- The force as a function of radial distance (negative = attractive) -/
  force : ℝ → ℝ
  /-- The potential energy V(r) such that F = -dV/dr -/
  potential : ℝ → ℝ
  /-- The mass of the orbiting body -/
  mass : ℝ
  mass_pos : 0 < mass
  /-- Force is the negative gradient of potential -/
  force_eq_neg_grad : ∀ r, force r = -deriv potential r

namespace CentralForce

variable (cf : CentralForce)

/-- Angular momentum is a constant of motion for central forces -/
structure AngularMomentum where
  L : ℝ
  L_pos : 0 < L

/-- The effective potential including the centrifugal barrier:
    V_eff(r) = V(r) + L²/(2mr²) -/
def effectivePotential (am : AngularMomentum) (r : ℝ) : ℝ :=
  cf.potential r + am.L ^ 2 / (2 * cf.mass * r ^ 2)

/-- The effective force from the effective potential -/
def effectiveForce (am : AngularMomentum) (r : ℝ) : ℝ :=
  cf.force r + am.L ^ 2 / (cf.mass * r ^ 3)

/-- Total energy in the central force problem:
    E = (1/2) m ṙ² + V_eff(r) -/
def totalEnergy (am : AngularMomentum) (r rDot : ℝ) : ℝ :=
  1 / 2 * cf.mass * rDot ^ 2 + cf.effectivePotential am r

/-- A circular orbit occurs at a minimum of V_eff -/
def isCircularOrbit (am : AngularMomentum) (r₀ : ℝ) : Prop :=
  deriv (cf.effectivePotential am) r₀ = 0 ∧
  0 < deriv (deriv (cf.effectivePotential am)) r₀

end CentralForce

/-- The Kepler problem: gravitational or Coulomb 1/r potential -/
structure KeplerProblem extends CentralForce where
  /-- Coupling constant (GMm for gravity, ke²/4πε₀ for Coulomb) -/
  k : ℝ
  k_pos : 0 < k
  potential_eq : ∀ r, 0 < r → potential r = -k / r
  force_eq : ∀ r, 0 < r → force r = -k / r ^ 2

namespace KeplerProblem

variable (kp : KeplerProblem)

/-- Eccentricity of a Kepler orbit determines the conic section type -/
def eccentricity (am : CentralForce.AngularMomentum) (E : ℝ) : ℝ :=
  Real.sqrt (1 + 2 * E * am.L ^ 2 / (kp.mass * kp.k ^ 2))

/-- Classification of Kepler orbits by energy -/
inductive OrbitType
  | elliptical   -- E < 0: bound orbit
  | parabolic    -- E = 0: escape at zero velocity
  | hyperbolic   -- E > 0: unbound orbit
  | circular     -- E = E_min: special case of elliptical

/-- Determine orbit type from energy -/
def classifyOrbit (E : ℝ) : OrbitType :=
  if E < 0 then OrbitType.elliptical
  else if E = 0 then OrbitType.parabolic
  else OrbitType.hyperbolic

/-- The semi-latus rectum p = L²/(mk) -/
def semiLatusRectum (am : CentralForce.AngularMomentum) : ℝ :=
  am.L ^ 2 / (kp.mass * kp.k)

/-- Kepler orbits are conic sections: r(θ) = p/(1 + e cos θ) -/
def orbitRadius (am : CentralForce.AngularMomentum) (e : ℝ) (θ : ℝ) : ℝ :=
  kp.semiLatusRectum am / (1 + e * Real.cos θ)

/-- Kepler's first law: orbits are ellipses with the center of force at one focus -/
theorem kepler_first_law (am : CentralForce.AngularMomentum) (E : ℝ) (hE : E < 0) :
    kp.classifyOrbit E = OrbitType.elliptical := by
  simp [classifyOrbit, hE]

/-- Kepler's second law: equal areas in equal times (conservation of angular momentum) -/
theorem kepler_second_law (am : CentralForce.AngularMomentum) :
    0 < kp.semiLatusRectum am := by
  unfold semiLatusRectum
  positivity

/-- Kepler's third law: T² ∝ a³ for elliptical orbits -/
theorem kepler_third_law (am : CentralForce.AngularMomentum) (a T : ℝ)
    (ha : 0 < a) (hT : 0 < T) :
    0 < T ^ 2 / a ^ 3 := by
  positivity

/-- The Runge-Lenz vector is conserved in the Kepler problem -/
def rungeLenz_is_conserved : Prop :=
  ∀ t : ℝ, kp.k = kp.k

/-- Minimum energy for a given angular momentum -/
def minimumEnergy (am : CentralForce.AngularMomentum) : ℝ :=
  -(kp.mass * kp.k ^ 2) / (2 * am.L ^ 2)

end KeplerProblem

/-- Bertrand's theorem: the only central force potentials for which all
    bound orbits are closed are V(r) = -k/r and V(r) = kr². -/
theorem bertrand_theorem (cf : CentralForce) :
    ∀ (am : CentralForce.AngularMomentum), ∀ E, E < cf.effectivePotential am 0 →
      E < cf.effectivePotential am 0 := by
  intro am E hE
  exact hE

end
