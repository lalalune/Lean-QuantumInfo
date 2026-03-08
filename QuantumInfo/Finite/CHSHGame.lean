import QuantumMechanics.BellsTheorem.Basic
import QuantumMechanics.BellsTheorem.CHSH_bounds

/-!
# CHSH Game Bounds (Finite-Core Integration)

Finite-dimensional CHSH game upper-bound interfaces for the `QuantumInfo` core,
bridging the integrated Bell/CHSH development into a reusable finite module.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Matrix Complex

namespace QuantumInfo
namespace CHSHGame

/-- Convert an absolute CHSH value upper bound into a CHSH game winning-probability
upper bound via `p_win ≤ (4 + |S|)/8`. -/
def winProbUpperFromAbs (sabs : ℝ) : ℝ := (4 + sabs) / 8

@[simp] theorem winProbUpperFromAbs_two : winProbUpperFromAbs 2 = (3 / 4 : ℝ) := by
  norm_num [winProbUpperFromAbs]

/-- LHV CHSH game winning-probability upper bound associated to a hidden-variable model. -/
def lhvWinProbUpper {Λ : Type*} [MeasurableSpace Λ] (M : LocalHiddenVariableModel Λ) : ℝ :=
  winProbUpperFromAbs |LHV_CHSH_value M|

/-- Under local hidden variables, CHSH game winning probability is at most `3/4`. -/
theorem lhvWinProbUpper_le_three_quarters {Λ : Type*} [MeasurableSpace Λ]
    (M : LocalHiddenVariableModel Λ) :
    lhvWinProbUpper M ≤ (3 / 4 : ℝ) := by
  unfold lhvWinProbUpper winProbUpperFromAbs
  have hchsh : |LHV_CHSH_value M| ≤ 2 := CHSH_lhv_bound M
  have hadd : 4 + |LHV_CHSH_value M| ≤ 4 + 2 := add_le_add_left hchsh 4
  have hdiv : (4 + |LHV_CHSH_value M|) / 8 ≤ (4 + 2) / 8 :=
    div_le_div_of_nonneg_right hadd (by norm_num : (0 : ℝ) ≤ 8)
  norm_num at hdiv
  simpa using hdiv

/-- Quantum CHSH game winning-probability upper bound extracted from
`|CHSH_expect|`. -/
def quantumWinProbUpper {n : ℕ} [NeZero n]
    (A₀ A₁ B₀ B₁ : Matrix (Fin n) (Fin n) ℂ)
    (ρ : DensityMatrix n) : ℝ :=
  winProbUpperFromAbs ‖CHSH_expect A₀ A₁ B₀ B₁ ρ.toMatrix‖

/-- Tsirelson-based CHSH game upper bound in direct `(4 + 2√2)/8` form. -/
theorem quantumWinProbUpper_le_tsirelson {n : ℕ} [NeZero n]
    (A₀ A₁ B₀ B₁ : Matrix (Fin n) (Fin n) ℂ)
    (hT : IsCHSHTuple A₀ A₁ B₀ B₁)
    (ρ : DensityMatrix n) :
    quantumWinProbUpper A₀ A₁ B₀ B₁ ρ ≤ (4 + 2 * Real.sqrt 2) / 8 := by
  unfold quantumWinProbUpper winProbUpperFromAbs
  have hchsh : ‖CHSH_expect A₀ A₁ B₀ B₁ ρ.toMatrix‖ ≤ 2 * Real.sqrt 2 :=
    tsirelson_bound A₀ A₁ B₀ B₁ hT ρ
  have hadd : 4 + ‖CHSH_expect A₀ A₁ B₀ B₁ ρ.toMatrix‖ ≤ 4 + 2 * Real.sqrt 2 :=
    add_le_add_left hchsh 4
  exact div_le_div_of_nonneg_right hadd (by norm_num : (0 : ℝ) ≤ 8)

/-- Tsirelson CHSH game bound in standard closed form `1/2 + √2/4`. -/
theorem quantumWinProbUpper_le_tsirelson_closedForm {n : ℕ} [NeZero n]
    (A₀ A₁ B₀ B₁ : Matrix (Fin n) (Fin n) ℂ)
    (hT : IsCHSHTuple A₀ A₁ B₀ B₁)
    (ρ : DensityMatrix n) :
    quantumWinProbUpper A₀ A₁ B₀ B₁ ρ ≤ (1 / 2 : ℝ) + Real.sqrt 2 / 4 := by
  have h := quantumWinProbUpper_le_tsirelson A₀ A₁ B₀ B₁ hT ρ
  have hrewrite : (4 + 2 * Real.sqrt 2) / 8 = (1 / 2 : ℝ) + Real.sqrt 2 / 4 := by
    ring
  simpa [hrewrite] using h

/-- If Alice-side or Bob-side CHSH observables commute, the CHSH game winning
probability is at most `3/4` (classical limit). -/
theorem quantumWinProbUpper_le_three_quarters_of_commuting {n : ℕ} [NeZero n]
    (A₀ A₁ B₀ B₁ : Matrix (Fin n) (Fin n) ℂ)
    (hT : IsCHSHTuple A₀ A₁ B₀ B₁)
    (hcomm : (A₀ * A₁ = A₁ * A₀) ∨ (B₀ * B₁ = B₁ * B₀))
    (ρ : DensityMatrix n) :
    quantumWinProbUpper A₀ A₁ B₀ B₁ ρ ≤ (3 / 4 : ℝ) := by
  unfold quantumWinProbUpper winProbUpperFromAbs
  have hchsh : ‖CHSH_expect A₀ A₁ B₀ B₁ ρ.toMatrix‖ ≤ 2 :=
    CHSH_commuting_bound A₀ A₁ B₀ B₁ hT hcomm ρ
  have hadd : 4 + ‖CHSH_expect A₀ A₁ B₀ B₁ ρ.toMatrix‖ ≤ 4 + 2 := add_le_add_left hchsh 4
  have hdiv : (4 + ‖CHSH_expect A₀ A₁ B₀ B₁ ρ.toMatrix‖) / 8 ≤ (4 + 2) / 8 :=
    div_le_div_of_nonneg_right hadd (by norm_num : (0 : ℝ) ≤ 8)
  norm_num at hdiv
  simpa using hdiv

end CHSHGame
end QuantumInfo
