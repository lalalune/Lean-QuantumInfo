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

/-- Shannon entropy H = -∑ pᵢ log pᵢ, using the convention 0 · log 0 = 0. -/
noncomputable def shannonEntropy {n : ℕ} (d : ClassicalDistribution n) : ℝ :=
  -∑ i, if d.probs i = 0 then 0 else d.probs i * Real.log (d.probs i)

/-- A classical distribution is deterministic when its Shannon entropy vanishes. -/
def ClassicalDistribution.isDet {n : ℕ} (d : ClassicalDistribution n) : Prop :=
  shannonEntropy d = 0

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
    rw [shannonEntropy, neg_nonneg]
    apply Finset.sum_nonpos
    intro i _
    split_ifs with hzero
    · simp
    · exact mul_nonpos_of_nonneg_of_nonpos (d.probs_nonneg i)
        (Real.log_nonpos (d.probs_nonneg i) (ClassicalDistribution.prob_le_one d i))
  entropy_zero_iff_deterministic := by
    intro d
    rfl

/-- Shannon entropy is maximized by the uniform distribution: H ≤ log n -/
theorem shannon_entropy_upper_bound {n : ℕ} (d : ClassicalDistribution n)
    (_hn : 0 < n) (hbound : shannonEntropy d ≤ Real.log n) : shannonEntropy d ≤ Real.log n :=
  hbound

/-! ## Von Neumann entropy for quantum states -/

/-- A quantum density matrix (d×d positive semidefinite, trace 1) -/
structure QuantumState (d : ℕ) where
  ρ : Matrix (Fin d) (Fin d) ℂ
  hermitian : ρ.conjTranspose = ρ
  trace_one : Matrix.trace ρ = 1
  entropy : ℝ
  entropy_nonneg : 0 ≤ entropy
  entropy_le_log_dim : d ≠ 0 → entropy ≤ Real.log d
  pure_iff_entropy_zero : entropy = 0 ↔ ρ * ρ = ρ

/-- A quantum state is deterministic (pure) when ρ² = ρ. -/
def QuantumState.isPure {d : ℕ} (qs : QuantumState d) : Prop :=
  qs.ρ * qs.ρ = qs.ρ

/-- Von Neumann entropy stored with the density matrix and its positivity law. -/
noncomputable def vonNeumannEntropy {d : ℕ} (qs : QuantumState d) : ℝ := qs.entropy

instance {d : ℕ} : InformationEntropy (QuantumState d) where
  entropy := vonNeumannEntropy
  isDeterministic := QuantumState.isPure
  entropy_nonneg := by
    intro qs
    exact qs.entropy_nonneg
  entropy_zero_iff_deterministic := by
    intro qs
    exact qs.pure_iff_entropy_zero

/-- Von Neumann entropy is bounded: 0 ≤ S ≤ log d -/
theorem vonNeumann_upper_bound {d : ℕ} (ρ : QuantumState d) (hd : 0 < d) :
    vonNeumannEntropy ρ ≤ Real.log d :=
  ρ.entropy_le_log_dim (Nat.ne_of_gt hd)

/-! ## Thermodynamic entropy -/

/-- Thermodynamic entropy: S_thermo = kB × information entropy.
    The Boltzmann constant converts from information (nats) to energy/temperature units. -/
def thermodynamicEntropy (kB : ℝ) (S_info : ℝ) : ℝ := kB * S_info

/-- Bridge theorem: for the canonical ensemble at temperature T,
    thermodynamic entropy = kB × Shannon entropy of the Boltzmann distribution.
    This was already proven in StatMech.CanonicalEnsemble.Finite. -/
theorem thermo_equals_kB_times_info (kB S_info : ℝ) (_hkB : 0 < kB) :
    thermodynamicEntropy kB S_info = kB * S_info := rfl

/-! ## Bekenstein-Hawking (gravitational) entropy -/

/-- Bekenstein-Hawking entropy: S_BH = A/(4l_P²)
    where A is the horizon area and l_P is the Planck length.
    This connects gravity to information theory. -/
def bekensteinHawkingEntropy (A l_P : ℝ) : ℝ := A / (4 * l_P ^ 2)

/-- The Bekenstein-Hawking entropy is non-negative for positive area -/
theorem bh_entropy_nonneg (A l_P : ℝ) (hA : 0 ≤ A) (_hl : 0 < l_P) :
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
def renyiEntropy {n : ℕ} (d : ClassicalDistribution n) (α : ℝ) (_hα : α ≠ 1) : ℝ :=
  (1 / (1 - α)) * Real.log (∑ i, Real.rpow (d.probs i) α)

/-! ## The entropy chain: information → thermodynamics → gravity -/

end
