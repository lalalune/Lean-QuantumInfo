import QuantumInfo.Finite.Entropy.Relative
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.MeanValue

open scoped RealInnerProductSpace ComplexOrder

variable {d : Type*} [Fintype d] [DecidableEq d]

theorem jensen_log_sum {ι : Type*} [Fintype ι] (p b : ι → ℝ)
    (hp_nonneg : ∀ i, 0 ≤ p i) (hp_sum : ∑ i, p i = 1)
    (hb_pos : ∀ i, p i > 0 → 0 < b i) :
    let B := ∑ i, p i * b i
    (∑ i, p i * Real.log (b i)) ≤ Real.log B := by
  change (∑ i, p i * Real.log (b i)) ≤ Real.log (∑ i, p i * b i)
  set B := ∑ i, p i * b i
  have h_pj_bj_nonneg : ∀ j, 0 ≤ p j * b j := by
    intro j
    by_cases hpj : p j = 0
    · simp [hpj]
    · exact mul_nonneg (hp_nonneg j) (hb_pos j ((hp_nonneg j).lt_of_ne' hpj)).le
  have hB_pos_of_pi : ∀ i, 0 < p i → 0 < B := by
    intro i hpi_pos
    apply Finset.sum_pos'
    · intro j _
      exact h_pj_bj_nonneg j
    · use i, Finset.mem_univ i
      exact mul_pos hpi_pos (hb_pos i hpi_pos)
  have key : ∀ i, p i * Real.log (b i / B) ≤ p i * (b i / B - 1) := by
    intro i
    by_cases hpi : p i = 0
    · simp [hpi]
    · have hpi_pos : 0 < p i := (hp_nonneg i).lt_of_ne' hpi
      have hb_i_pos : 0 < b i := hb_pos i hpi_pos
      have hB_pos : 0 < B := hB_pos_of_pi i hpi_pos
      have h_div_pos : 0 < b i / B := div_pos hb_i_pos hB_pos
      exact mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos h_div_pos) hpi_pos.le
  have sum_bound : ∑ i, p i * Real.log (b i / B) ≤ 0 := by
    calc ∑ i, p i * Real.log (b i / B)
        ≤ ∑ i, p i * (b i / B - 1) := Finset.sum_le_sum (fun i _ => key i)
      _ = ∑ i, (p i * b i / B - p i) := by apply Finset.sum_congr rfl; intro i _; ring
      _ = (∑ i, p i * b i) / B - ∑ i, p i := by rw [Finset.sum_sub_distrib, ← Finset.sum_div]
      _ = B / B - 1 := by rw [hp_sum]
      _ = 1 - 1 := by
        have hB_pos : 0 < B := by
          obtain ⟨j, hj⟩ : ∃ j, p j > 0 := by
            by_contra! hcontra
            have h_all_zero : ∀ j, p j = 0 := fun j => le_antisymm (hcontra j) (hp_nonneg j)
            have h_sum_zero : ∑ j, p j = 0 := by simp [h_all_zero]
            linarith [hp_sum, h_sum_zero]
          exact hB_pos_of_pi j hj
        rw [div_self hB_pos.ne']
      _ = 0 := by ring
  -- Now expand log(b i / B)
  have log_expand : ∑ i, p i * Real.log (b i / B) = ∑ i, p i * Real.log (b i) - ∑ i, p i * Real.log B := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hpi : p i = 0
    · simp [hpi]
    · have hpi_pos : 0 < p i := (hp_nonneg i).lt_of_ne' hpi
      have hb_i_pos : 0 < b i := hb_pos i hpi_pos
      have hB_pos : 0 < B := hB_pos_of_pi i hpi_pos
      rw [Real.log_div hb_i_pos.ne' hB_pos.ne']
      ring
  rw [log_expand] at sum_bound
  have h_sub : ∑ i, p i * Real.log B = Real.log B := by
    calc ∑ i, p i * Real.log B = (∑ i, p i) * Real.log B := by rw [← Finset.sum_mul]
      _ = 1 * Real.log B := by rw [hp_sum]
      _ = Real.log B := by ring
  linarith [h_sub, sum_bound]

