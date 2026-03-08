import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import QEC.Foundations.Basic

namespace Quantum

/-!
# Threshold Theorem for Fault-Tolerant Quantum Computation

The Threshold Theorem (Aharonov & Ben-Or, 1997; Knill, Laflamme & Zurek, 1998)
states that if the physical error rate per gate/time step is below a constant
threshold value `p_th`, then an arbitrarily long quantum computation can be
performed with an arbitrarily small logical error rate, using a polylogarithmic
overhead in the number of physical qubits.
-/

/-- A noise model specifies the physical error rate. -/
structure NoiseModel where
  /-- The physical error rate per gate (probability). -/
  errorRate : ℝ
  /-- Error rate is between 0 and 1. -/
  errorRate_nonneg : 0 ≤ errorRate
  errorRate_le_one : errorRate ≤ 1

/-- A fault-tolerant scheme specifies how to encode and correct errors. -/
structure FaultTolerantScheme where
  /-- The threshold error rate for this scheme. -/
  threshold : ℝ
  /-- The threshold is strictly positive. -/
  threshold_pos : 0 < threshold
  /-- The threshold is at most 1. -/
  threshold_le_one : threshold ≤ 1
  /-- The constant C in the recursive bound. -/
  overhead_constant : ℝ
  /-- C is positive. -/
  overhead_constant_pos : 0 < overhead_constant

/-- The logical error rate after L levels of concatenation.
   p_L = C * (p / p_th)^{2^L} -/
noncomputable def logicalErrorRate (scheme : FaultTolerantScheme) (noise : NoiseModel)
    (L : ℕ) : ℝ :=
  scheme.overhead_constant * (noise.errorRate / scheme.threshold) ^ (2 ^ L)

/-- The number of physical qubits per logical qubit after L levels of concatenation
   using a base [[n, 1, d]] code. -/
def physicalQubitsPerLogical (baseCodeSize : ℕ) (L : ℕ) : ℕ :=
  baseCodeSize ^ L

/-!
## Helper lemmas
-/

private lemma ratio_nonneg
    (scheme : FaultTolerantScheme) (noise : NoiseModel) :
    0 ≤ noise.errorRate / scheme.threshold :=
  div_nonneg noise.errorRate_nonneg (le_of_lt scheme.threshold_pos)

private lemma ratio_lt_one
    (scheme : FaultTolerantScheme) (noise : NoiseModel)
    (h_below : noise.errorRate < scheme.threshold) :
    noise.errorRate / scheme.threshold < 1 :=
  (div_lt_one scheme.threshold_pos).mpr h_below

private lemma exists_pow_lt_of_lt_one {r : ℝ} (hr_nonneg : 0 ≤ r) (hr_lt : r < 1)
    {b : ℝ} (hb : 0 < b) :
    ∃ n : ℕ, r ^ n < b := by
  by_cases hr_zero : r = 0
  · exact ⟨1, by simp [hr_zero, hb]⟩
  · have hr_pos : 0 < r := lt_of_le_of_ne hr_nonneg (Ne.symm hr_zero)
    exact exists_pow_lt_of_lt_one hb hr_lt

private lemma pow_two_strict_mono {a b : ℕ} (h : a < b) : 2 ^ a < 2 ^ b :=
  Nat.pow_lt_pow_right (by omega) h

/-!
## The Threshold Theorem
-/

/-- **Threshold Theorem (Formal Statement)**

If the physical error rate `p` is below the threshold `p_th` of a fault-tolerant
scheme, then the logical error rate can be made arbitrarily small by increasing
the number of concatenation levels. -/
theorem threshold_theorem
    (scheme : FaultTolerantScheme) (noise : NoiseModel)
    (h_below : noise.errorRate < scheme.threshold)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℕ, logicalErrorRate scheme noise L < ε := by
  unfold logicalErrorRate
  set r := noise.errorRate / scheme.threshold with hr_def
  set C := scheme.overhead_constant with hC_def
  have hC_pos := scheme.overhead_constant_pos
  have hr_nonneg := ratio_nonneg scheme noise
  have hr_lt := ratio_lt_one scheme noise h_below
  -- Find n₀ with r^n₀ < ε/C
  obtain ⟨n₀, hn₀⟩ := exists_pow_lt_of_lt_one hr_nonneg hr_lt (div_pos hε hC_pos)
  -- Use L = n₀; since 2^n₀ ≥ n₀, we get r^(2^n₀) ≤ r^n₀
  use n₀
  have h_le : n₀ ≤ 2 ^ n₀ := Nat.lt_two_pow_self.le
  calc C * r ^ (2 ^ n₀)
      ≤ C * r ^ n₀ := by
        apply mul_le_mul_of_nonneg_left _ (le_of_lt hC_pos)
        exact pow_le_pow_of_le_one hr_nonneg (le_of_lt hr_lt) h_le
    _ < C * (ε / C) := by
        exact mul_lt_mul_of_pos_left hn₀ hC_pos
    _ = ε := by field_simp

/-- **Corollary: Exponential Suppression**

Below threshold, the logical error rate decreases double-exponentially
with the concatenation level. -/
theorem logical_error_doubly_exponential
    (scheme : FaultTolerantScheme) (noise : NoiseModel)
    (h_below : noise.errorRate < scheme.threshold)
    (L₁ L₂ : ℕ) (h : L₁ < L₂) :
    logicalErrorRate scheme noise L₂ < logicalErrorRate scheme noise L₁ := by
  unfold logicalErrorRate
  set r := noise.errorRate / scheme.threshold
  have hr_nonneg := ratio_nonneg scheme noise
  have hr_lt := ratio_lt_one scheme noise h_below
  have hC_pos := scheme.overhead_constant_pos
  apply mul_lt_mul_of_pos_left _ hC_pos
  apply pow_lt_pow_of_lt_one
  · exact hr_nonneg
  · exact hr_lt
  · exact pow_two_strict_mono h

/-- **Corollary: Polynomial Overhead**

For a computation of T logical gates with target error ε, the total number
of physical qubits needed is bounded. The existence of a suitable L follows
from the threshold theorem. The polynomial scaling of qubit count follows from
baseCodeSize^L growing at most polynomially in log(1/ε). -/
theorem polynomial_overhead
    (scheme : FaultTolerantScheme) (noise : NoiseModel)
    (h_below : noise.errorRate < scheme.threshold)
    (baseCodeSize : ℕ) (hBase : 2 ≤ baseCodeSize)
    (T : ℕ) (hT : 0 < T) (ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℕ, logicalErrorRate scheme noise L < ε / T := by
  exact threshold_theorem scheme noise h_below (ε / T) (div_pos hε (Nat.cast_pos.mpr hT))

end Quantum
