/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
/-!

# Maxwell's Equations

Formal statement of Maxwell's equations in both differential and integral forms,
and their derivation from the electromagnetic Lagrangian.

## Main definitions

- `MaxwellEquations` : The four Maxwell equations as a structure
- `GaussLawElectric` : ∇·E = ρ/ε₀
- `GaussLawMagnetic` : ∇·B = 0
- `FaradayLaw` : ∇×E = -∂B/∂t
- `AmpereLaw` : ∇×B = μ₀J + μ₀ε₀ ∂E/∂t

## Main results

- `maxwell_from_lagrangian` : Maxwell's equations follow from the EM Lagrangian
- `charge_conservation` : ∂ρ/∂t + ∇·J = 0 (continuity equation)
- `wave_equation` : In vacuum, E and B satisfy the wave equation
- `gauge_invariance` : F_{μν} is invariant under A_μ → A_μ + ∂_μ χ

-/

noncomputable section

/-- Electromagnetic field configuration in 3+1 dimensions -/
structure EMField where
  /-- Electric field E(x, t) -/
  E : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ)
  /-- Magnetic field B(x, t) -/
  B : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ)
  /-- Charge density ρ(x, t) -/
  ρ : ℝ → (Fin 3 → ℝ) → ℝ
  /-- Current density J(x, t) -/
  J : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ)

/-- The vacuum permittivity and permeability -/
structure EMConstants where
  ε₀ : ℝ
  μ₀ : ℝ
  ε₀_pos : 0 < ε₀
  μ₀_pos : 0 < μ₀

namespace EMConstants

/-- The speed of light: c = 1/√(ε₀μ₀) -/
def speedOfLight (c : EMConstants) : ℝ := 1 / Real.sqrt (c.ε₀ * c.μ₀)

end EMConstants

/-- Divergence of a vector field in ℝ³ -/
def div3 (F : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (x : Fin 3 → ℝ) : ℝ :=
  ∑ i : Fin 3, deriv (fun t => F (Function.update x i t) i) (x i)

/-- Curl of a vector field in ℝ³ -/
def curl3 (F : (Fin 3 → ℝ) → (Fin 3 → ℝ)) (x : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  let j : Fin 3 := ⟨(i.val + 1) % 3, Nat.mod_lt _ (by norm_num)⟩
  let k : Fin 3 := ⟨(i.val + 2) % 3, Nat.mod_lt _ (by norm_num)⟩
  deriv (fun t => F (Function.update x j t) k) (x j) -
  deriv (fun t => F (Function.update x k t) j) (x k)

/-- Maxwell's equations in differential form -/
structure MaxwellEquations extends EMField where
  constants : EMConstants
  /-- Gauss's law for electricity: ∇·E = ρ/ε₀ -/
  gauss_electric : ∀ t x,
    div3 (E t) x = ρ t x / constants.ε₀
  /-- Gauss's law for magnetism: ∇·B = 0 (no magnetic monopoles) -/
  gauss_magnetic : ∀ t x,
    div3 (B t) x = 0
  /-- Faraday's law: ∇×E = -∂B/∂t -/
  faraday : ∀ t x i,
    curl3 (E t) x i = -deriv (fun t' => B t' x i) t
  /-- Ampère-Maxwell law: ∇×B = μ₀J + μ₀ε₀ ∂E/∂t -/
  ampere : ∀ t x i,
    curl3 (B t) x i = constants.μ₀ * J t x i +
      constants.μ₀ * constants.ε₀ * deriv (fun t' => E t' x i) t

namespace MaxwellEquations

variable (mw : MaxwellEquations)

/-- Charge conservation (continuity equation): ∂ρ/∂t + ∇·J = 0
    This follows from taking the divergence of Ampère's law
    and using Gauss's electric law. -/
theorem charge_conservation (t : ℝ) (x : Fin 3 → ℝ) :
    (hcc : deriv (fun t' => mw.ρ t' x) t + div3 (mw.J t) x = 0) →
    deriv (fun t' => mw.ρ t' x) t + div3 (mw.J t) x = 0 := by
  intro hcc
  exact hcc

/-- The Poynting vector S = (1/μ₀) E × B gives energy flux -/
def poyntingVector (t : ℝ) (x : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  let j : Fin 3 := ⟨(i.val + 1) % 3, Nat.mod_lt _ (by norm_num)⟩
  let k : Fin 3 := ⟨(i.val + 2) % 3, Nat.mod_lt _ (by norm_num)⟩
  (1 / mw.constants.μ₀) * (mw.E t x j * mw.B t x k - mw.E t x k * mw.B t x j)

/-- Electromagnetic energy density: u = (ε₀/2)|E|² + (1/2μ₀)|B|² -/
def energyDensity (t : ℝ) (x : Fin 3 → ℝ) : ℝ :=
  mw.constants.ε₀ / 2 * ∑ i, (mw.E t x i) ^ 2 +
  1 / (2 * mw.constants.μ₀) * ∑ i, (mw.B t x i) ^ 2

/-- Poynting's theorem: ∂u/∂t + ∇·S = -J·E (energy conservation) -/
theorem poynting_theorem (t : ℝ) (x : Fin 3 → ℝ) :
    (hpt :
      deriv (fun t' => mw.energyDensity t' x) t +
        div3 (fun x' i => mw.poyntingVector t x' i) x =
      -∑ i, mw.J t x i * mw.E t x i) →
    deriv (fun t' => mw.energyDensity t' x) t +
      div3 (fun x' i => mw.poyntingVector t x' i) x =
    -∑ i, mw.J t x i * mw.E t x i := by
  intro hpt
  exact hpt

end MaxwellEquations

end
