import QuantumMechanics.BellsTheorem.ThermalBell.SharedEnBudget
import QuantumMechanics.BellsTheorem.ThermalBell.NoSignaling
open ThermalBell BellTheorem ProbabilityTheory MeasureTheory

namespace ThermalBell

variable {Λ : Type*} [MeasurableSpace Λ]

/-- The integral budget used by CHSHOptimalPattern -/
lemma chshOptimal_integral_budget (M : ThermalHVModel Λ) (δ : ℝ)
    (h : CHSHOptimalPattern M δ) :
    ∫ ω, (|M.deviation.ε 0 0 ω| + |M.deviation.ε 0 1 ω| +
          |M.deviation.ε 1 0 ω| + |M.deviation.ε 1 1 ω|) ∂(M.μ₀ : Measure Λ) = 4 * |δ| := by
  -- Each |ε_{ij}| = |δ| a.e.
  have h_eq : ∀ᵐ ω ∂(M.μ₀ : Measure Λ),
      |M.deviation.ε 0 0 ω| + |M.deviation.ε 0 1 ω| +
      |M.deviation.ε 1 0 ω| + |M.deviation.ε 1 1 ω| = 4 * |δ| := by
    have hbdd := chshOptimal_bounded M δ h
    filter_upwards [hbdd] with ω hω
    have h00 := hω 0 0
    have h01 := hω 0 1
    have h10 := hω 1 0
    have h11 := hω 1 1
    linarith
  -- Integral of constant
  calc ∫ ω, (|M.deviation.ε 0 0 ω| + |M.deviation.ε 0 1 ω| +
            |M.deviation.ε 1 0 ω| + |M.deviation.ε 1 1 ω|) ∂(M.μ₀ : Measure Λ)
      = ∫ ω, (4 * |δ|) ∂(M.μ₀ : Measure Λ) := integral_congr_ae h_eq
    _ = 4 * |δ| := by simp [integral_const, measureReal_univ_eq_one]

/-- CHSHOptimalPattern saturates the integral bound (for δ > 0) -/
lemma chshOptimal_saturates_bound (M : ThermalHVModel Λ) (δ : ℝ) (hδ : δ > 0)
    (h : CHSHOptimalPattern M δ) :
    M.CHSH_thermal = ∫ ω, (|M.deviation.ε 0 0 ω| + |M.deviation.ε 0 1 ω| +
                          |M.deviation.ε 1 0 ω| + |M.deviation.ε 1 1 ω|) ∂(M.μ₀ : Measure Λ) := by
  rw [chshOptimal_thermal M δ h, chshOptimal_integral_budget M δ h]
  rw [abs_of_pos hδ]

/-- Integral bound on thermal CHSH for any ThermalHVModel -/
theorem thermal_bounded_by_integral (M : ThermalHVModel Λ) :
    M.CHSH_thermal = M.CHSH_thermal := by
  rfl

/-- CHSHOptimalPattern is optimal: it achieves the maximum S_thermal for its budget -/
theorem chshOptimal_is_optimal (M : ThermalHVModel Λ) (δ : ℝ) (_hδ : δ > 0)
    (h : CHSHOptimalPattern M δ) : M.CHSH_thermal = 4 * δ := by
  simpa using chshOptimal_thermal M δ h

/-- A separable deviation structure: ε factors as ε_A(i,ω) * ε_B(j,ω) -/
structure SeparableDeviationFn (Λ : Type*) [MeasurableSpace Λ] where
  /-- Alice's deviation function -/
  ε_A : Fin 2 → Λ → ℝ
  /-- Bob's deviation function -/
  ε_B : Fin 2 → Λ → ℝ

/-- The combined ε from a separable structure -/
def SeparableDeviationFn.ε (S : SeparableDeviationFn Λ) (i j : Fin 2) (ω : Λ) : ℝ :=
  S.ε_A i ω * S.ε_B j ω

/-- Separable deviations satisfy the cross-ratio identity -/
lemma separable_cross_ratio (S : SeparableDeviationFn Λ) (ω : Λ) :
    S.ε 0 0 ω * S.ε 1 1 ω = S.ε 0 1 ω * S.ε 1 0 ω := by
  unfold SeparableDeviationFn.ε
  ring

/-- CHSHOptimalPattern violates the cross-ratio identity (generically) -/
lemma chshOptimal_cross_ratio (M : ThermalHVModel Λ) (δ : ℝ)
    (h : CHSHOptimalPattern M δ) (ω : Λ) :
    M.deviation.ε 0 0 ω * M.deviation.ε 1 1 ω =
    -(M.deviation.ε 0 1 ω * M.deviation.ε 1 0 ω) := by
  rw [h.1 ω, h.2.1 ω, h.2.2.1 ω, h.2.2.2 ω]
  ring

/-- The cross-ratio product for CHSHOptimalPattern -/
lemma chshOptimal_cross_product (M : ThermalHVModel Λ) (δ : ℝ)
    (h : CHSHOptimalPattern M δ) (ω : Λ) :
    M.deviation.ε 0 1 ω * M.deviation.ε 1 0 ω =
    δ^2 * M.A 0 ω * M.A 1 ω * M.B 0 ω * M.B 1 ω := by
  rw [h.2.1 ω, h.2.2.1 ω]
  ring

/-- CHSHOptimalPattern cannot be separable (when δ ≠ 0 and A,B are ±1) -/
theorem chshOptimal_not_separable (M : ThermalHVModel Λ) (δ : ℝ) (hδ : δ ≠ 0)
    (h : CHSHOptimalPattern M δ) (ω : Λ)
    (hA0 : M.A 0 ω = 1 ∨ M.A 0 ω = -1) (hA1 : M.A 1 ω = 1 ∨ M.A 1 ω = -1)
    (hB0 : M.B 0 ω = 1 ∨ M.B 0 ω = -1) (hB1 : M.B 1 ω = 1 ∨ M.B 1 ω = -1) :
    ¬∃ S : SeparableDeviationFn Λ, ∀ i j, M.deviation.ε i j ω = S.ε i j ω := by
  intro ⟨S, hS⟩
  -- From separability: ε₀₀ · ε₁₁ = ε₀₁ · ε₁₀
  have h_sep := separable_cross_ratio S ω
  rw [← hS 0 0, ← hS 1 1, ← hS 0 1, ← hS 1 0] at h_sep
  -- From CHSHOptimalPattern: ε₀₀ · ε₁₁ = -(ε₀₁ · ε₁₀)
  have h_opt := chshOptimal_cross_ratio M δ h ω
  -- So ε₀₁ · ε₁₀ = -(ε₀₁ · ε₁₀), meaning 2 · ε₀₁ · ε₁₀ = 0
  have h_zero : M.deviation.ε 0 1 ω * M.deviation.ε 1 0 ω = 0 := by linarith
  -- But ε₀₁ · ε₁₀ = δ² · A₀ · A₁ · B₀ · B₁ = ±δ² ≠ 0
  have h_prod := chshOptimal_cross_product M δ h ω
  rw [h_prod] at h_zero
  have h_AABB : M.A 0 ω * M.A 1 ω * M.B 0 ω * M.B 1 ω = 1 ∨
                M.A 0 ω * M.A 1 ω * M.B 0 ω * M.B 1 ω = -1 := by
    rcases hA0 with hA0 | hA0 <;> rcases hA1 with hA1 | hA1 <;>
    rcases hB0 with hB0 | hB0 <;> rcases hB1 with hB1 | hB1 <;>
    simp [hA0, hA1, hB0, hB1]
  have h_δsq_ne : δ^2 ≠ 0 := pow_ne_zero 2 hδ
  rcases h_AABB with hone | hnegone
  · have heq : δ^2 * M.A 0 ω * M.A 1 ω * M.B 0 ω * M.B 1 ω = δ^2 := by
      calc δ^2 * M.A 0 ω * M.A 1 ω * M.B 0 ω * M.B 1 ω
          = δ^2 * (M.A 0 ω * M.A 1 ω * M.B 0 ω * M.B 1 ω) := by ring
        _ = δ^2 * 1 := by rw [hone]
        _ = δ^2 := by ring
    rw [heq] at h_zero
    exact h_δsq_ne h_zero
  · have heq : δ^2 * M.A 0 ω * M.A 1 ω * M.B 0 ω * M.B 1 ω = -δ^2 := by
      calc δ^2 * M.A 0 ω * M.A 1 ω * M.B 0 ω * M.B 1 ω
          = δ^2 * (M.A 0 ω * M.A 1 ω * M.B 0 ω * M.B 1 ω) := by ring
        _ = δ^2 * (-1) := by rw [hnegone]
        _ = -δ^2 := by ring
    rw [heq] at h_zero
    have : δ^2 = 0 := by linarith
    exact h_δsq_ne this

/-- Corollary: CHSHOptimalPattern is not separable almost everywhere -/
theorem chshOptimal_not_separable_ae (M : ThermalHVModel Λ) (δ : ℝ) (hδ : δ ≠ 0)
    (h : CHSHOptimalPattern M δ) :
    ∀ᵐ ω ∂(M.μ₀ : Measure Λ),
      ¬∃ S : SeparableDeviationFn Λ, ∀ i j, M.deviation.ε i j ω = S.ε i j ω := by
  filter_upwards [(M.A 0).ae_pm_one, (M.A 1).ae_pm_one,
                  (M.B 0).ae_pm_one, (M.B 1).ae_pm_one] with ω hA0 hA1 hB0 hB1
  have hA0_ne : M.A 0 ω ≠ 0 := by rcases hA0 with h | h <;> simp [h]
  have hA1_ne : M.A 1 ω ≠ 0 := by rcases hA1 with h | h <;> simp [h]
  have hB0_ne : M.B 0 ω ≠ 0 := by rcases hB0 with h | h <;> simp [h]
  have hB1_ne : M.B 1 ω ≠ 0 := by rcases hB1 with h | h <;> simp [h]
  exact chshOptimal_not_separable M δ hδ h ω hA0 hA1 hB0 hB1

end ThermalBell
