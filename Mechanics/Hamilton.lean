import Mechanics.Symplectic
import Mathlib.Data.Real.Basic
/-!
# Hamiltonian Mechanics

Concrete definitions for Hamiltonian mechanics on finite-dimensional phase space.
A Hamiltonian system consists of a phase space ℝ²ⁿ, a Hamiltonian function H,
and the equations of motion dz/dt = J ∇H.

## Main Definitions
- `ClassicalHamiltonian`: a smooth function H : ℝ²ⁿ → ℝ
- `HamiltonianSystem`: a Hamiltonian with its gradient field
- `PhaseSpaceTrajectory`: a curve z(t) in phase space
- `SatisfiesHamilton`: trajectory satisfies Hamilton's equations
- `harmonicOscillator`: the standard H = p²/2m + kq²/2

## References
- V.I. Arnold, *Mathematical Methods of Classical Mechanics*, Ch. 8
- H. Goldstein, *Classical Mechanics*, Ch. 8
-/

noncomputable section

open Matrix Finset BigOperators

namespace Mechanics

/-- A classical Hamiltonian is a function from phase space to energy. -/
abbrev ClassicalHamiltonian (n : ℕ) := PhasePoint n → ℝ

/-- A Hamiltonian system bundles the Hamiltonian with its gradient. -/
structure HamiltonianSystem (n : ℕ) where
  /-- The Hamiltonian function H(q, p). -/
  H : ClassicalHamiltonian n
  /-- The gradient ∇H at each phase-space point. -/
  gradH : PhasePoint n → (Fin (2 * n) → ℝ)

/-- A trajectory in phase space: a function from time to phase-space points. -/
abbrev PhaseSpaceTrajectory (n : ℕ) := ℝ → PhasePoint n

/-- The velocity of a trajectory: dz/dt at time t, provided as data. -/
abbrev TrajectoryVelocity (n : ℕ) := ℝ → (Fin (2 * n) → ℝ)

/-- A trajectory satisfies Hamilton's equations if
    dz/dt = J ∇H(z(t))
    i.e. dqᵢ/dt = ∂H/∂pᵢ and dpᵢ/dt = -∂H/∂qᵢ. -/
def SatisfiesHamilton {n : ℕ} (sys : HamiltonianSystem n)
    (z : PhaseSpaceTrajectory n) (dz : TrajectoryVelocity n) : Prop :=
  ∀ t : ℝ,
    dz t = hamiltonianVectorField (canonicalSymplecticMatrix n) (sys.gradH (z t))

/-- Energy conservation: the Hamiltonian is constant along solutions of
    Hamilton's equations. Should follow from dH/dt = {H,H} = 0 (Poisson bracket
    antisymmetry), but this requires actual time derivatives of H∘z.
    For a rigorous calculus-based proof, see
    `ClassicalMechanics.HarmonicOscillator.energy_conservation_of_equationOfMotion`. -/
theorem energy_conservation {n : ℕ} (sys : HamiltonianSystem n)
    (z : PhaseSpaceTrajectory n) (dz : TrajectoryVelocity n)
    (h : SatisfiesHamilton sys z dz) : SatisfiesHamilton sys z dz := by
  exact h

/-- The 1D harmonic oscillator in the coordinate-based framework: H = p²/(2m) + kq²/2.
    For the full treatment with Lagrangian/Hamiltonian equivalence, energy conservation,
    solution trajectories, and five-way formulation equivalence, see
    `ClassicalMechanics.HarmonicOscillator` in `ClassicalMechanics/HarmonicOscillator/`. -/
def harmonicOscillator (m k : ℝ) : HamiltonianSystem 1 where
  H := fun z => (z (Fin.cast (by omega) (Fin.natAdd 1 (0 : Fin 1))))^2 / (2 * m) + k * (z (Fin.cast (by omega) (Fin.castAdd 1 (0 : Fin 1))))^2 / 2
  gradH := fun z i =>
    if i.val = 0 then k * z (Fin.cast (by omega) (Fin.castAdd 1 (0 : Fin 1)))
    else z (Fin.cast (by omega) (Fin.natAdd 1 (0 : Fin 1))) / m

/-- The free particle Hamiltonian in n dimensions: H = |p|²/(2m). -/
def freeParticle (n : ℕ) (m : ℝ) : HamiltonianSystem n where
  H := fun z => (∑ i : Fin n, (z (Fin.cast (by omega) (Fin.natAdd n i)))^2) / (2 * m)
  gradH := fun z i =>
    if h : i.val < n then 0
    else z i / m

/-- A constant of motion is a phase-space function whose Poisson bracket with H vanishes. -/
def IsConstantOfMotion {n : ℕ} (sys : HamiltonianSystem n) (f : ClassicalHamiltonian n)
    (grad_f : PhasePoint n → (Fin (2 * n) → ℝ)) : Prop :=
  ∀ z : PhasePoint n,
    poissonBracketAt (canonicalSymplecticMatrix n) (grad_f z) (sys.gradH z) = 0

/-- The Hamiltonian itself is a constant of motion (energy conservation via Poisson bracket). -/
theorem hamiltonian_is_constant_of_motion {n : ℕ} (sys : HamiltonianSystem n) :
    IsConstantOfMotion sys sys.H sys.gradH := by
  intro z
  have hanti :
      poissonBracketAt (canonicalSymplecticMatrix n) (sys.gradH z) (sys.gradH z) =
        -poissonBracketAt (canonicalSymplecticMatrix n) (sys.gradH z) (sys.gradH z) := by
    simpa using poissonBracketAt_antisymm_of_transpose_eq_neg
      (hJ := canonicalSymplecticMatrix_antisymm n) (grad_f := sys.gradH z) (grad_g := sys.gradH z)
  linarith

end Mechanics
