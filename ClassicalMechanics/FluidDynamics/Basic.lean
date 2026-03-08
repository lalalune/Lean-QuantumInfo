/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!

# Fluid Dynamics and Continuum Mechanics

The Euler and Navier-Stokes equations for fluid flow.

## Main definitions

- `EulerEquation` : ∂v/∂t + (v·∇)v = -(1/ρ)∇P + f (inviscid flow)
- `NavierStokesEquation` : Euler + viscous term ν∇²v
- `ContinuityEquation` : ∂ρ/∂t + ∇·(ρv) = 0
- `ReynoldsNumber` : Re = ρvL/μ (laminar vs turbulent)
- `BernoulliEquation` : P + (1/2)ρv² + ρgh = const along streamline

-/

noncomputable section

/-- A fluid configuration -/
structure FluidState where
  /-- Velocity field v(x, t) -/
  velocity : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ)
  /-- Pressure field P(x, t) -/
  pressure : ℝ → (Fin 3 → ℝ) → ℝ
  /-- Density field ρ(x, t) -/
  density : ℝ → (Fin 3 → ℝ) → ℝ
  /-- Density is positive -/
  density_pos : ∀ t x, 0 < density t x

/-- The continuity equation: ∂ρ/∂t + ∇·(ρv) = 0 (mass conservation) -/
def satisfiesContinuity (fluid : FluidState) : Prop :=
  ∀ t x, deriv (fun t' => fluid.density t' x) t +
    ∑ i : Fin 3, deriv (fun xi =>
      fluid.density t (Function.update x i xi) * fluid.velocity t (Function.update x i xi) i)
      (x i) = 0

/-- The Euler equation for inviscid flow:
    ∂v/∂t + (v·∇)v = -(1/ρ)∇P + f -/
def satisfiesEuler (fluid : FluidState) (force : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ)) : Prop :=
  ∀ t x i,
    deriv (fun t' => fluid.velocity t' x i) t +
    ∑ j : Fin 3, fluid.velocity t x j *
      deriv (fun xj => fluid.velocity t (Function.update x j xj) i) (x j) =
    -(1 / fluid.density t x) *
      deriv (fun xi => fluid.pressure t (Function.update x i xi)) (x i) +
    force t x i

/-- Bernoulli's equation along a streamline (steady, incompressible, inviscid):
    P + (1/2)ρ|v|² + ρgh = constant -/
def bernoulliConstant (P ρ v_sq g h : ℝ) : ℝ :=
  P + ρ * v_sq / 2 + ρ * g * h

/-- The Reynolds number: Re = ρvL/μ -/
def reynoldsNumber (ρ v L μ : ℝ) : ℝ := ρ * v * L / μ

/-- Laminar flow: Re < Re_critical (typically ~2300 for pipe flow) -/
def isLaminar (Re : ℝ) : Prop := Re < 2300

/-- Turbulent flow: Re > Re_critical -/
def isTurbulent (Re : ℝ) : Prop := Re > 4000

/-- The Navier-Stokes equations add viscosity to Euler:
    ρ(∂v/∂t + (v·∇)v) = -∇P + μ∇²v + ρf -/
structure NavierStokes extends FluidState where
  /-- Dynamic viscosity μ -/
  viscosity : ℝ
  viscosity_pos : 0 < viscosity
  /-- External body force -/
  force : ℝ → (Fin 3 → ℝ) → (Fin 3 → ℝ)

/-- Incompressible flow: ∇·v = 0 -/
def isIncompressible (fluid : FluidState) : Prop :=
  ∀ t x, ∑ i : Fin 3,
    deriv (fun xi => fluid.velocity t (Function.update x i xi) i) (x i) = 0

/-- The vorticity ω = ∇ × v -/
def vorticity (fluid : FluidState) (t : ℝ) (x : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  let j : Fin 3 := ⟨(i.val + 1) % 3, Nat.mod_lt _ (by norm_num)⟩
  let k : Fin 3 := ⟨(i.val + 2) % 3, Nat.mod_lt _ (by norm_num)⟩
  deriv (fun xj => fluid.velocity t (Function.update x j xj) k) (x j) -
  deriv (fun xk => fluid.velocity t (Function.update x k xk) j) (x k)

end
