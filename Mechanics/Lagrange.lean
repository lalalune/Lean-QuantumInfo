import Mechanics.Hamilton
import Mathlib.Data.Real.Basic

/-!
# Lagrangian Mechanics

Concrete definitions for Lagrangian mechanics on finite-dimensional configuration spaces.
A Lagrangian system consists of a configuration space ℝⁿ, a Lagrangian L(q, q̇),
and the Euler-Lagrange equations.

## Main Definitions
- `ConfigVelocity`: a point (q, q̇) in configuration-velocity space
- `ClassicalLagrangian`: a function L(q, q̇) → ℝ
- `LagrangianSystem`: bundles Lagrangian with its partial derivatives
- `SatisfiesEulerLagrange`: trajectory satisfies d/dt(∂L/∂q̇) = ∂L/∂q
- `ActionFunctional`: the action integral S[q] = ∫ L dt
- `LegendreData`: the Legendre transform p = ∂L/∂q̇

## References
- V.I. Arnold, *Mathematical Methods of Classical Mechanics*, Ch. 3-4
- L.D. Landau, E.M. Lifshitz, *Mechanics*, Ch. 1-2
-/

noncomputable section

open Matrix Finset BigOperators

namespace Mechanics

/-- A point in configuration-velocity space: q and q̇. -/
structure ConfigVelocity (n : ℕ) where
  /-- Generalized coordinates qᵢ. -/
  q : Fin n → ℝ
  /-- Generalized velocities q̇ᵢ. -/
  q_dot : Fin n → ℝ

/-- A classical Lagrangian is a function from (q, q̇) to energy. -/
abbrev ClassicalLagrangian (n : ℕ) := ConfigVelocity n → ℝ

/-- A Lagrangian system bundles the Lagrangian with its partial derivatives. -/
structure LagrangianSystem (n : ℕ) where
  /-- The Lagrangian function L(q, q̇). -/
  L : ClassicalLagrangian n
  /-- ∂L/∂qᵢ at each configuration-velocity point. -/
  dL_dq : ConfigVelocity n → (Fin n → ℝ)
  /-- ∂L/∂q̇ᵢ at each configuration-velocity point (the conjugate momentum). -/
  dL_dqdot : ConfigVelocity n → (Fin n → ℝ)

/-- A trajectory in configuration space: q(t). -/
abbrev ConfigTrajectory (n : ℕ) := ℝ → (Fin n → ℝ)

/-- A trajectory satisfies the Euler-Lagrange equations if
    d/dt (∂L/∂q̇ᵢ) = ∂L/∂qᵢ for all i.

    Given:
    - `q`: the trajectory q(t)
    - `q_dot`: the velocity q̇(t)
    - `p_dot`: the time derivative of the conjugate momentum ṗ(t)
    all as externally provided data. -/
def SatisfiesEulerLagrange {n : ℕ} (sys : LagrangianSystem n)
    (q : ConfigTrajectory n) (q_dot : ConfigTrajectory n)
    (p_dot : ConfigTrajectory n) : Prop :=
  ∀ t : ℝ, ∀ i : Fin n,
    let cv := ConfigVelocity.mk (q t) (q_dot t)
    p_dot t i = sys.dL_dq cv i

/-- The conjugate momentum defined by the Lagrangian: pᵢ = ∂L/∂q̇ᵢ. -/
def conjugateMomentum {n : ℕ} (sys : LagrangianSystem n) (cv : ConfigVelocity n) : Fin n → ℝ :=
  sys.dL_dqdot cv

/-- The Legendre transform produces a Hamiltonian from a Lagrangian:
    H(q, p) = Σᵢ pᵢ q̇ᵢ - L(q, q̇)
    where q̇ is expressed in terms of (q, p) by inverting p = ∂L/∂q̇. -/
structure LegendreData (n : ℕ) where
  /-- The original Lagrangian system. -/
  lagrangian : LagrangianSystem n
  /-- Inversion: given (q, p), recover q̇. Assumes the Hessian ∂²L/∂q̇² is non-degenerate. -/
  invert_momentum : (Fin n → ℝ) → (Fin n → ℝ) → (Fin n → ℝ)

/-- Apply the Legendre transform to obtain a Hamiltonian. -/
def legendreTransform {n : ℕ} (ld : LegendreData n) : ClassicalHamiltonian n :=
  fun z =>
    let q := PhasePoint.q z
    let p := PhasePoint.p z
    let q_dot := ld.invert_momentum q p
    (∑ i : Fin n, p i * q_dot i) - ld.lagrangian.L ⟨q, q_dot⟩

/-- The action functional: S[q] = ∫₀ᵀ L(q(t), q̇(t)) dt.
    Since we don't have Lebesgue integration over trajectories directly,
    we represent the action as a structure. -/
structure ActionFunctional (n : ℕ) where
  /-- The Lagrangian system. -/
  sys : LagrangianSystem n
  /-- The trajectory q(t). -/
  q : ConfigTrajectory n
  /-- The velocity q̇(t). -/
  q_dot : ConfigTrajectory n
  /-- Start time. -/
  t₀ : ℝ
  /-- End time. -/
  t₁ : ℝ

/-- Standard kinetic-minus-potential Lagrangian: L = T - V = ½ m|q̇|² - V(q). -/
def kineticMinusPotential (n : ℕ) (m : ℝ)
    (V : (Fin n → ℝ) → ℝ) (dV : (Fin n → ℝ) → (Fin n → ℝ)) : LagrangianSystem n where
  L := fun cv => (m / 2) * ∑ i, (cv.q_dot i)^2 - V cv.q
  dL_dq := fun cv i => -(dV cv.q i)
  dL_dqdot := fun cv i => m * cv.q_dot i

/-- For a standard L = T - V Lagrangian, the conjugate momentum is p = m q̇. -/
theorem conjugateMomentum_kinetic_minus_potential (n : ℕ) (m : ℝ)
    (V : (Fin n → ℝ) → ℝ) (dV : (Fin n → ℝ) → (Fin n → ℝ))
    (cv : ConfigVelocity n) (i : Fin n) :
    conjugateMomentum (kineticMinusPotential n m V dV) cv i = m * cv.q_dot i := by
  simp [conjugateMomentum, kineticMinusPotential]

end Mechanics
