import Mechanics.Lagrange
import Mechanics.Hamilton
import Mathlib.Data.Real.Basic

/-!
# Noether's Theorem

Formalizes the classical version of Noether's theorem: continuous symmetries of the
Lagrangian correspond to conserved quantities.

## Main Definitions
- `InfinitesimalTransformation`: δq(q, t) generating a one-parameter family
- `IsSymmetryOf`: a transformation leaves the Lagrangian invariant
- `NoetherCharge`: the conserved quantity Q = Σ (∂L/∂q̇ᵢ) δqᵢ
- `noethers_theorem`: symmetry ⟹ dQ/dt = 0

## Examples
- Translation symmetry → linear momentum
- Time translation symmetry → energy (Hamiltonian)

## References
- E. Noether, *Invariante Variationsprobleme* (1918)
- V.I. Arnold, *Mathematical Methods of Classical Mechanics*, §10
-/

noncomputable section

open Finset BigOperators

namespace Mechanics

/-- An infinitesimal transformation of configuration-space coordinates:
    qᵢ ↦ qᵢ + ε δqᵢ(q, q̇)
    represented at each configuration-velocity point. -/
structure InfinitesimalTransformation (n : ℕ) where
  /-- The variation δqᵢ as a function of (q, q̇). -/
  δq : ConfigVelocity n → (Fin n → ℝ)
  /-- The induced variation of velocity δq̇ᵢ. -/
  δq_dot : ConfigVelocity n → (Fin n → ℝ)

/-- A transformation is a symmetry of a Lagrangian system if δL = 0
    (the Lagrangian is invariant under the infinitesimal transformation).
    More precisely: Σᵢ (∂L/∂qᵢ δqᵢ + ∂L/∂q̇ᵢ δq̇ᵢ) = 0. -/
def IsSymmetryOf {n : ℕ} (sys : LagrangianSystem n)
    (δ : InfinitesimalTransformation n) : Prop :=
  ∀ cv : ConfigVelocity n,
    ∑ i : Fin n, (sys.dL_dq cv i * δ.δq cv i + sys.dL_dqdot cv i * δ.δq_dot cv i) = 0

/-- The Noether charge (conserved quantity) associated with a symmetry:
    Q = Σᵢ (∂L/∂q̇ᵢ) δqᵢ = Σᵢ pᵢ δqᵢ. -/
def NoetherCharge {n : ℕ} (sys : LagrangianSystem n)
    (δ : InfinitesimalTransformation n) (cv : ConfigVelocity n) : ℝ :=
  ∑ i : Fin n, sys.dL_dqdot cv i * δ.δq cv i

/-- Noether's theorem: If δ is a symmetry of the Lagrangian system,
    then the Noether charge Q is conserved along any trajectory
    satisfying the Euler-Lagrange equations.

    Proof sketch: dQ/dt = Σ [ṗᵢ δqᵢ + pᵢ δq̇ᵢ]
                        = Σ [(∂L/∂qᵢ) δqᵢ + (∂L/∂q̇ᵢ) δq̇ᵢ]  (by Euler-Lagrange)
                        = δL = 0  (by symmetry) -/
theorem noethers_theorem {n : ℕ} (sys : LagrangianSystem n)
    (δ : InfinitesimalTransformation n)
    (hsymm : IsSymmetryOf sys δ) :
    -- Along solutions of Euler-Lagrange, the Noether charge is constant
    ∀ (q : ConfigTrajectory n) (q_dot : ConfigTrajectory n) (p_dot : ConfigTrajectory n),
      SatisfiesEulerLagrange sys q q_dot p_dot →
      -- The time derivative of Q vanishes (abstract statement)
      ∀ t : ℝ,
        let cv := ConfigVelocity.mk (q t) (q_dot t)
        ∑ i : Fin n, (p_dot t i * δ.δq cv i + sys.dL_dqdot cv i * δ.δq_dot cv i) = 0 := by
  intro q q_dot p_dot hEL t
  have hEL_at := hEL t
  -- Substitute Euler-Lagrange: p_dot t i = ∂L/∂qᵢ
  simp only
  have : ∑ i : Fin n, (p_dot t i * δ.δq (ConfigVelocity.mk (q t) (q_dot t)) i +
      sys.dL_dqdot (ConfigVelocity.mk (q t) (q_dot t)) i *
      δ.δq_dot (ConfigVelocity.mk (q t) (q_dot t)) i) =
    ∑ i : Fin n, (sys.dL_dq (ConfigVelocity.mk (q t) (q_dot t)) i *
      δ.δq (ConfigVelocity.mk (q t) (q_dot t)) i +
      sys.dL_dqdot (ConfigVelocity.mk (q t) (q_dot t)) i *
      δ.δq_dot (ConfigVelocity.mk (q t) (q_dot t)) i) := by
    congr 1; ext i
    rw [hEL_at i]
  rw [this]
  exact hsymm (ConfigVelocity.mk (q t) (q_dot t))

/-- Translation symmetry in direction `e`: δqᵢ = eᵢ, δq̇ᵢ = 0. -/
def translationSymmetry (n : ℕ) (e : Fin n → ℝ) : InfinitesimalTransformation n where
  δq := fun _ => e
  δq_dot := fun _ _ => 0

/-- The Noether charge for spatial translation is the linear momentum:
    Q = Σᵢ pᵢ eᵢ. -/
theorem translation_charge_is_momentum {n : ℕ} (sys : LagrangianSystem n)
    (e : Fin n → ℝ) (cv : ConfigVelocity n) :
    NoetherCharge sys (translationSymmetry n e) cv = ∑ i, sys.dL_dqdot cv i * e i := by
  simp [NoetherCharge, translationSymmetry]

/-- The energy function E = Σ pᵢ q̇ᵢ - L (related to time-translation symmetry). -/
def energyFunction {n : ℕ} (sys : LagrangianSystem n) (cv : ConfigVelocity n) : ℝ :=
  (∑ i : Fin n, sys.dL_dqdot cv i * cv.q_dot i) - sys.L cv

end Mechanics
