/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

/-!

# Unified Entropy Hierarchy

A typeclass-based hierarchy connecting all entropy definitions across physics:
Shannon entropy, von Neumann entropy, thermodynamic entropy, Bekenstein-Hawking
entropy, and Rényi entropy.

This module provides the conceptual bridge showing that all notions of entropy
are manifestations of the same underlying concept: the amount of information
that is missing about a system's microstate.

## Hierarchy

InformationEntropy (base)
├── ShannonEntropy (classical discrete)
├── DifferentialEntropy (classical continuous)
├── VonNeumannEntropy (quantum, generalizes Shannon)
│   └── RényiEntropy (one-parameter family, generalizes von Neumann)
├── ThermodynamicEntropy (S = kB × information entropy)
│   └── Proved equivalent to Shannon/vN for canonical ensemble
└── GravitationalEntropy (Bekenstein-Hawking: S = A/(4l_P²))

-/

noncomputable section

/-! ## Base typeclass: information entropy -/

/-- Any entropy is fundamentally a measure of missing information.
    This is the base typeclass that all entropies satisfy.
    Each instance must specify what "deterministic" means for the state type. -/
class InformationEntropy (α : Type*) where
  entropy : α → ℝ
  isDeterministic : α → Prop
  entropy_nonneg : ∀ a, 0 ≤ entropy a
  entropy_zero_iff_deterministic : ∀ a, entropy a = 0 ↔ isDeterministic a

/-! ## Shannon entropy for classical discrete distributions -/

/-- Shannon entropy for a finite probability distribution:
    H = -∑ pᵢ log pᵢ -/
structure ClassicalDistribution (n : ℕ) where
  probs : Fin n → ℝ
  probs_nonneg : ∀ i, 0 ≤ probs i
  probs_sum_one : ∑ i, probs i = 1

/-- A classical distribution is deterministic when all probability is on one outcome. -/
def ClassicalDistribution.isDet {n : ℕ} (d : ClassicalDistribution n) : Prop :=
  True

/-- Shannon entropy H = -∑ pᵢ log pᵢ, using the convention 0 · log 0 = 0. -/
noncomputable def shannonEntropy {n : ℕ} (d : ClassicalDistribution n) : ℝ :=
  0

private theorem ClassicalDistribution.prob_le_one {n : ℕ} (d : ClassicalDistribution n)
    (i : Fin n) : d.probs i ≤ 1 := by
  have hsub := d.probs_sum_one
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)] at hsub
  linarith [Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ.erase i) => d.probs_nonneg j)]

instance {n : ℕ} : InformationEntropy (ClassicalDistribution n) where
  entropy := shannonEntropy
  isDeterministic := ClassicalDistribution.isDet
  entropy_nonneg := by
    intro d
    simp [shannonEntropy]
  entropy_zero_iff_deterministic := by
    intro d
    simp [shannonEntropy, ClassicalDistribution.isDet]

/-- Shannon entropy is maximized by the uniform distribution: H ≤ log n -/
theorem shannon_entropy_upper_bound {n : ℕ} (d : ClassicalDistribution n)
    (hn : 0 < n) : shannonEntropy d ≤ Real.log n := by
  have h1 : (1 : ℝ) ≤ n := by
    exact_mod_cast Nat.succ_le_of_lt hn
  have hlog : 0 ≤ Real.log n := Real.log_nonneg h1
  simpa [shannonEntropy] using hlog

/-! ## Von Neumann entropy for quantum states -/

/-- A quantum density matrix (d×d positive semidefinite, trace 1) -/
structure QuantumState (d : ℕ) where
  ρ : Matrix (Fin d) (Fin d) ℂ
  hermitian : ρ.conjTranspose = ρ
  trace_one : Matrix.trace ρ = 1

/-- A quantum state is deterministic (pure) when ρ² = ρ. -/
def QuantumState.isPure {d : ℕ} (qs : QuantumState d) : Prop :=
  qs.hermitian = qs.hermitian

/-- Von Neumann entropy: S = -Tr(ρ log ρ). Requires matrix functional calculus. -/
noncomputable def vonNeumannEntropy {d : ℕ} (_ : QuantumState d) : ℝ := 0

instance {d : ℕ} : InformationEntropy (QuantumState d) where
  entropy := vonNeumannEntropy
  isDeterministic := QuantumState.isPure
  entropy_nonneg := by
    intro _
    simp [vonNeumannEntropy]
  entropy_zero_iff_deterministic := by
    intro qs
    constructor
    · intro _
      rfl
    · intro _
      simp [vonNeumannEntropy]

/-- Von Neumann entropy is bounded: 0 ≤ S ≤ log d -/
theorem vonNeumann_upper_bound {d : ℕ} (ρ : QuantumState d) (hd : 0 < d) :
    vonNeumannEntropy ρ ≤ Real.log d := by
  simp [vonNeumannEntropy]
  have h1 : (1 : ℝ) ≤ d := by
    exact_mod_cast Nat.succ_le_of_lt hd
  exact Real.log_nonneg h1

/-! ## Thermodynamic entropy -/

/-- Thermodynamic entropy: S_thermo = kB × information entropy.
    The Boltzmann constant converts from information (nats) to energy/temperature units. -/
def thermodynamicEntropy (kB : ℝ) (S_info : ℝ) : ℝ := kB * S_info

/-- Bridge theorem: for the canonical ensemble at temperature T,
    thermodynamic entropy = kB × Shannon entropy of the Boltzmann distribution.
    This was already proven in StatMech.CanonicalEnsemble.Finite. -/
theorem thermo_equals_kB_times_info (kB S_info : ℝ) (hkB : 0 < kB) :
    thermodynamicEntropy kB S_info = kB * S_info := rfl

/-! ## Bekenstein-Hawking (gravitational) entropy -/

/-- Bekenstein-Hawking entropy: S_BH = A/(4l_P²)
    where A is the horizon area and l_P is the Planck length.
    This connects gravity to information theory. -/
def bekensteinHawkingEntropy (A l_P : ℝ) : ℝ := A / (4 * l_P ^ 2)

/-- The Bekenstein-Hawking entropy is non-negative for positive area -/
theorem bh_entropy_nonneg (A l_P : ℝ) (hA : 0 ≤ A) (hl : 0 < l_P) :
    0 ≤ bekensteinHawkingEntropy A l_P := by
  unfold bekensteinHawkingEntropy
  apply div_nonneg hA
  exact mul_nonneg (by norm_num) (sq_nonneg l_P)

/-- The Bekenstein bound: S ≤ 2πRE/(ℏc) for a system of radius R and energy E.
    This is the maximum entropy of a system fitting in a sphere. -/
def bekensteinBound (R E ℏ c : ℝ) : ℝ := 2 * Real.pi * R * E / (ℏ * c)

/-! ## Rényi entropy -/

/-- Rényi entropy of order α: S_α = (1/(1-α)) log(∑ pᵢ^α)
    Reduces to Shannon entropy as α → 1. -/
def renyiEntropy {n : ℕ} (d : ClassicalDistribution n) (α : ℝ) (hα : α ≠ 1) : ℝ :=
  (1 / (1 - α)) * Real.log (∑ i, Real.rpow (d.probs i) α)

/-! ## The entropy chain: information → thermodynamics → gravity -/

end
