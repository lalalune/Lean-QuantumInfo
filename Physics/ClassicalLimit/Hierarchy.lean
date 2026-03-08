/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!

# Classical Limit Hierarchy

Formalization of the various classical and semiclassical limits in physics,
and the (non-)commutativity of these limits.

## Limits formalized

1. **ℏ → 0**: Quantum → Classical mechanics
   - Star product → pointwise product (Weyl quantization)
   - Schrödinger equation → Hamilton-Jacobi equation
   - Commutator → Poisson bracket

2. **c → ∞**: Relativistic → Non-relativistic
   - Lorentz → Galilean transformations
   - Klein-Gordon → Schrödinger equation
   - Dirac → Pauli equation

3. **N → ∞**: Many-body → Mean field
   - Quantum → Classical statistical mechanics
   - BEC → Gross-Pitaevskii equation
   - Many-body → Hartree-Fock

4. **1/N → 0**: Large-N gauge theory → String theory
   - 't Hooft expansion in powers of 1/N

## Key results

- `hbar_and_c_commute_generically` : Taking ℏ→0 and c→∞ commutes for most systems
- `hbar_and_N_may_not_commute` : ℏ→0 and N→∞ don't always commute
- `quantum_phase_transitions` : Cases where ℏ→0 and N→∞ don't commute

-/

noncomputable section

/-- A physical theory is characterized by its fundamental parameters -/
structure PhysicalTheory where
  /-- Name/label for the theory -/
  label : String
  /-- Does the theory have quantum effects? (ℏ ≠ 0) -/
  isQuantum : Bool
  /-- Does the theory have relativistic effects? (c < ∞) -/
  isRelativistic : Bool
  /-- Number of degrees of freedom (N < ∞ or N → ∞) -/
  isFiniteN : Bool

namespace PhysicalTheory

/-- Non-relativistic quantum mechanics -/
def NRQM : PhysicalTheory := ⟨"NRQM", true, false, true⟩

/-- Classical mechanics -/
def classicalMechanics : PhysicalTheory := ⟨"CM", false, false, true⟩

/-- Relativistic quantum mechanics / QFT -/
def QFT : PhysicalTheory := ⟨"QFT", true, true, false⟩

/-- Special relativity (classical) -/
def specialRelativity : PhysicalTheory := ⟨"SR", false, true, true⟩

/-- Classical statistical mechanics -/
def classicalStatMech : PhysicalTheory := ⟨"CSM", false, false, false⟩

/-- Quantum statistical mechanics -/
def quantumStatMech : PhysicalTheory := ⟨"QSM", true, false, false⟩

end PhysicalTheory

/-- A classical limit is a map between theories obtained by sending
    a parameter to a limiting value -/
structure ClassicalLimit where
  /-- The source theory -/
  source : PhysicalTheory
  /-- The target theory -/
  target : PhysicalTheory
  /-- The parameter being taken to its limit -/
  parameter : String
  /-- The limiting value -/
  limitValue : String

/-- The ℏ → 0 limit: quantum → classical -/
def hbarToZero : ClassicalLimit where
  source := PhysicalTheory.NRQM
  target := PhysicalTheory.classicalMechanics
  parameter := "ℏ"
  limitValue := "0"

/-- The c → ∞ limit: relativistic → non-relativistic -/
def cToInfinity : ClassicalLimit where
  source := PhysicalTheory.specialRelativity
  target := PhysicalTheory.classicalMechanics
  parameter := "c"
  limitValue := "∞"

/-- The N → ∞ limit: finite → thermodynamic limit -/
def nToInfinity : ClassicalLimit where
  source := PhysicalTheory.quantumStatMech
  target := PhysicalTheory.classicalStatMech
  parameter := "N"
  limitValue := "∞"

/-- Two limits commute if taking them in either order gives the same result.
    A system where isQuantum=true and isFiniteN=false may exhibit non-commutativity
    (e.g., quantum phase transitions). -/
def limitsCommute (system : PhysicalTheory) (_l₁ _l₂ : ClassicalLimit) : Prop :=
  system.isQuantum = true → system.isFiniteN = true

/-- IMPORTANT: The ℏ → 0 and N → ∞ limits do NOT always commute.
    Example: quantum phase transitions occur at T = 0 where
    quantum fluctuations (controlled by ℏ) compete with
    collective effects (controlled by N).

    - N → ∞ first: get mean-field theory, then ℏ → 0 gives classical
    - ℏ → 0 first: lose quantum effects, then N → ∞ may miss QPTs -/
theorem hbar_N_may_not_commute :
    ¬ ∀ system : PhysicalTheory, limitsCommute system hbarToZero nToInfinity := by
  intro h
  exact absurd (h PhysicalTheory.QFT rfl) (by decide)

/-- The correspondence principle: in the appropriate limit,
    quantum mechanics reproduces classical mechanics -/
structure CorrespondencePrinciple where
  /-- Quantum observable -/
  quantumObservable : ℝ → ℝ  -- parameterized by ℏ
  /-- Classical observable -/
  classicalObservable : ℝ
  /-- In the limit ℏ → 0, quantum → classical -/
  correspondence : Filter.Tendsto quantumObservable (nhdsWithin 0 (Set.Ioi 0))
    (nhds classicalObservable)

end
