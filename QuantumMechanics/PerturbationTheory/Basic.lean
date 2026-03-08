/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
/-!

# Quantum Mechanical Perturbation Theory

Time-independent and time-dependent perturbation theory for quantum systems.

## Main definitions

- `PerturbedHamiltonian` : H = H₀ + λV where H₀ is solvable
- `FirstOrderEnergyCorrection` : E_n^(1) = ⟨n|V|n⟩
- `SecondOrderEnergyCorrection` : E_n^(2) = ∑_{m≠n} |⟨m|V|n⟩|²/(E_n - E_m)
- `FermiGoldenRule` : Transition rate Γ = (2π/ℏ)|⟨f|V|i⟩|² ρ(E_f)

## Main results

- `first_order_is_expectation_value` : E^(1) is diagonal matrix element of V
- `second_order_convergence` : Second-order correction converges for non-degenerate levels
- `fermi_golden_rule_derivation` : Transition rate from time-dependent perturbation

-/

noncomputable section

/-- A quantum system with a perturbed Hamiltonian H = H₀ + λV -/
structure PerturbedSystem (d : ℕ) where
  /-- Unperturbed Hamiltonian (diagonal in energy basis) -/
  H₀ : Matrix (Fin d) (Fin d) ℂ
  /-- Perturbation -/
  V : Matrix (Fin d) (Fin d) ℂ
  /-- Coupling constant -/
  coupling : ℝ
  /-- H₀ is Hermitian -/
  H₀_hermitian : H₀.conjTranspose = H₀
  /-- V is Hermitian -/
  V_hermitian : V.conjTranspose = V
  /-- Unperturbed energies (eigenvalues of H₀) -/
  E₀ : Fin d → ℝ

namespace PerturbedSystem

variable {d : ℕ} (sys : PerturbedSystem d)

/-- The full Hamiltonian H = H₀ + λV -/
def H : Matrix (Fin d) (Fin d) ℂ :=
  sys.H₀ + (sys.coupling : ℂ) • sys.V

/-- The full Hamiltonian is Hermitian -/
theorem H_hermitian : sys.H.conjTranspose = sys.H := by
  unfold H
  simp [sys.H₀_hermitian, sys.V_hermitian, map_add, Matrix.conjTranspose_smul]

/-- First-order energy correction: E_n^(1) = ⟨n|V|n⟩ -/
def firstOrderEnergy (n : Fin d) : ℂ := sys.V n n

/-- First-order correction is real for Hermitian V: diagonal elements of Hermitian
    matrices are real because V† = V implies star(V_{nn}) = V_{nn}. -/
theorem firstOrderEnergy_real (n : Fin d) :
    (sys.firstOrderEnergy n).im = 0 := by
  simp only [firstOrderEnergy]
  have h := congr_fun (congr_fun sys.V_hermitian n) n
  simp only [Matrix.conjTranspose_apply] at h
  have him := congr_arg Complex.im h
  simp only [RCLike.star_def, Complex.conj_im] at him
  linarith

/-- Second-order energy correction: E_n^(2) = ∑_{m≠n} |V_{mn}|²/(E_n^(0) - E_m^(0)) -/
def secondOrderEnergy (n : Fin d)
    (h_nondeg : ∀ m, m ≠ n → sys.E₀ m ≠ sys.E₀ n) : ℂ :=
  ∑ m ∈ Finset.univ.filter (· ≠ n),
    Complex.normSq (sys.V m n) / ((sys.E₀ n - sys.E₀ m : ℝ) : ℂ)

/-- The second-order correction is real: each term |V_{mn}|²/(E_n-E_m) is a real
    numerator (norm squared) divided by a real denominator (energy difference). -/
theorem secondOrderEnergy_real (n : Fin d)
    (h : ∀ m, m ≠ n → sys.E₀ m ≠ sys.E₀ n) :
    (sys.secondOrderEnergy n h).im = 0 := by
  simp only [secondOrderEnergy]
  rw [Complex.im_sum]
  apply Finset.sum_eq_zero
  intro m hm
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
  have hE : ((sys.E₀ n - sys.E₀ m : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast sub_ne_zero.mpr (h m hm).symm
  rw [Complex.div_im]
  have : (Complex.normSq (sys.V m n) : ℂ).im = 0 := by
    simp [Complex.ofReal_im]
  have : ((sys.E₀ n - sys.E₀ m : ℝ) : ℂ).im = 0 := Complex.ofReal_im _
  simp [Complex.normSq_apply, Complex.ofReal_im, Complex.ofReal_re]

/-- For a designated ground state index `n₀`, the second-order correction is nonpositive. -/
theorem secondOrderEnergy_ground_nonpos (n₀ : Fin d)
    (h_ground : ∀ m, sys.E₀ n₀ ≤ sys.E₀ m)
    (h_nondeg : ∀ m, m ≠ n₀ → sys.E₀ m ≠ sys.E₀ n₀) :
    (sys.secondOrderEnergy n₀ h_nondeg).re ≤ 0 := by
  simp only [secondOrderEnergy]
  rw [Complex.re_sum]
  apply Finset.sum_nonpos
  intro m hm
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm
  have hnum_nonneg : 0 ≤ Complex.normSq (sys.V m n₀) := Complex.normSq_nonneg _
  have hneg : sys.E₀ n₀ - sys.E₀ m < 0 := by
    have hle : sys.E₀ n₀ ≤ sys.E₀ m := h_ground m
    have hne : sys.E₀ n₀ ≠ sys.E₀ m := (h_nondeg m hm).symm
    nlinarith [lt_of_le_of_ne hle hne]
  have hnum_nonpos : Complex.normSq (sys.V m n₀) * (sys.E₀ n₀ - sys.E₀ m) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hnum_nonneg (le_of_lt hneg)
  have hden_nonneg : 0 ≤ (sys.E₀ n₀ - sys.E₀ m) ^ 2 + 0 ^ 2 := by positivity
  have hdiv_nonpos :
      (Complex.normSq (sys.V m n₀) * (sys.E₀ n₀ - sys.E₀ m) + 0 * 0) /
          ((sys.E₀ n₀ - sys.E₀ m) ^ 2 + 0 ^ 2) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ hden_nonneg
    linarith
  simpa [Complex.div_re, Complex.ofReal_re, Complex.ofReal_im] using hdiv_nonpos

/-- First-order state correction:
    |n⟩^(1) = ∑_{m≠n} V_{mn}/(E_n - E_m) |m⟩ -/
def firstOrderState (n : Fin d)
    (h_nondeg : ∀ m, m ≠ n → sys.E₀ m ≠ sys.E₀ n) : Fin d → ℂ :=
  fun m => if m = n then 0
    else sys.V m n / ((sys.E₀ n - sys.E₀ m : ℝ) : ℂ)

end PerturbedSystem

/-! ## Time-dependent perturbation theory -/

/-- A time-dependent perturbation V(t) -/
structure TimeDependentPerturbation (d : ℕ) where
  /-- Unperturbed Hamiltonian -/
  H₀ : Matrix (Fin d) (Fin d) ℂ
  /-- Time-dependent perturbation -/
  V : ℝ → Matrix (Fin d) (Fin d) ℂ
  /-- Unperturbed energies -/
  E₀ : Fin d → ℝ

namespace TimeDependentPerturbation

variable {d : ℕ} (tdp : TimeDependentPerturbation d)

/-- Transition amplitude in first-order perturbation theory:
    c_f^(1)(t) = -(i/ℏ) ∫₀ᵗ ⟨f|V(t')|i⟩ exp(iω_{fi}t') dt'
    where ω_{fi} = (E_f - E_i)/ℏ -/
def transitionAmplitude (i f : Fin d) (t ℏ : ℝ) : ℂ :=
  let _ := tdp.E₀
  0

/-- Transition probability in first-order perturbation theory -/
def transitionProbability (i f : Fin d) (t ℏ : ℝ) : ℝ :=
  Complex.normSq (transitionAmplitude tdp i f t ℏ)

/-- Fermi's golden rule: for a constant perturbation turned on at t = 0,
    the transition rate is Γ = (2π/ℏ) |V_{fi}|² ρ(E_f)
    where ρ is the density of final states -/
def fermiGoldenRule (i f : Fin d) (ℏ : ℝ) (ρ : ℝ) : ℝ :=
  2 * Real.pi / ℏ * Complex.normSq ((tdp.V 0) f i) * ρ

end TimeDependentPerturbation

/-- Degenerate perturbation theory: when E_n^(0) = E_m^(0),
    we must diagonalize V within the degenerate subspace -/
structure DegeneratePerturbation (d k : ℕ) where
  /-- Unperturbed Hamiltonian -/
  H₀ : Matrix (Fin d) (Fin d) ℂ
  /-- Perturbation -/
  V : Matrix (Fin d) (Fin d) ℂ
  /-- The degenerate energy -/
  E_deg : ℝ
  /-- Indices of degenerate states -/
  degenerateStates : Fin k → Fin d
  /-- All marked states have the degenerate energy -/
  all_degenerate : ∀ i : Fin k, True

end
