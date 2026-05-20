import Mathlib

/-!
# Fixed-width binary expansions

This file contains a small proof-complete binary representation API for natural
numbers.  The digits are returned most-significant first and padded to a fixed
width.
-/

namespace Nat

/-- Auxiliary fixed-width binary representation with `n + 1` digits, most-significant first. -/
def binRepAux : Nat → Nat → List Nat
  | 0, m => [m % 2]
  | n + 1, m => (m / 2 ^ (n + 1)) % 2 :: binRepAux n m

/-- Fixed-width binary representation with `n` digits, most-significant first. -/
def binRep (n m : Nat) : List Nat :=
  (binRepAux n m).tail

@[simp]
theorem binRepAux_length (n m : Nat) : (binRepAux n m).length = n + 1 := by
  induction n generalizing m with
  | zero => simp [binRepAux]
  | succ n ih => simp [binRepAux, ih]

theorem binRepAux_ne_nil (n m : Nat) : binRepAux n m ≠ [] := by
  cases n <;> simp [binRepAux]

@[simp]
theorem binRep_length (n m : Nat) : (binRep n m).length = n := by
  simp [binRep, List.length_tail, binRepAux_length]

@[simp]
theorem binRepAux_getLast (n m : Nat) :
    (binRepAux n m).getLast (binRepAux_ne_nil n m) = m % 2 := by
  induction n with
  | zero => simp [binRepAux]
  | succ n ih =>
      simp only [binRepAux]
      rw [List.getLast_cons (binRepAux_ne_nil n m)]
      exact ih

private theorem binRepAux_getD_eq (n m j : Nat) (hj : j ≤ n) :
    (binRepAux n m).getD j 0 = (m / 2 ^ (n - j)) % 2 := by
  induction n generalizing m j with
  | zero =>
      have : j = 0 := Nat.le_zero.mp hj
      subst this
      simp [binRepAux]
  | succ n ih =>
      rcases j with _ | j
      · simp [binRepAux]
      · simp only [binRepAux, List.getD_cons_succ]
        rw [ih m j (by omega)]
        have : n + 1 - (j + 1) = n - j := by omega
        rw [this]

theorem binRepAux_getD_eq_zero_or_one (n m i : Nat) (hi : i ≤ n) :
    (binRepAux n m).getD i 0 = 0 ∨ (binRepAux n m).getD i 0 = 1 := by
  rw [binRepAux_getD_eq n m i hi]
  exact Nat.mod_two_eq_zero_or_one _

private theorem binRep_getD_eq_aux_succ (n m i : Nat) :
    (binRep n m).getD i 0 = (binRepAux n m).getD (i + 1) 0 := by
  simp only [binRep]
  rcases h : binRepAux n m with _ | ⟨a, l⟩
  · exact absurd h (binRepAux_ne_nil n m)
  · simp

theorem binRep_getD_eq_zero_or_one (n m i : Nat) (hi : i < n) :
    (binRep n m).getD i 0 = 0 ∨ (binRep n m).getD i 0 = 1 := by
  rw [binRep_getD_eq_aux_succ]
  exact binRepAux_getD_eq_zero_or_one n m (i + 1) (by omega)

theorem binRep_getD_eq (n m i : Nat) (hn : 1 ≤ n) (_hm : m < 2 ^ n) (hi : i < n) :
    (binRep n m).getD i 0 = (m / 2 ^ (n - 1 - i)) % 2 := by
  rcases n with _ | n
  · omega
  · simp only [binRep_getD_eq_aux_succ, binRepAux, List.getD_cons_succ]
    rw [binRepAux_getD_eq n m i (by omega)]
    have : n - i = n + 1 - 1 - i := by omega
    rw [this]

private lemma div_pow_mod_two_eq_mod_div_pow_mod_two {m j k : Nat} (hj : j < k) :
    m / 2 ^ j % 2 = (m % 2 ^ k) / 2 ^ j % 2 := by
  have heq : m.testBit j = (m % 2 ^ k).testBit j := by
    rw [Nat.testBit_mod_two_pow]
    simp [hj]
  simp only [Nat.testBit, Nat.shiftRight_eq_div_pow] at heq
  rcases Nat.mod_two_eq_zero_or_one (m / 2 ^ j) with h1 | h1 <;>
    rcases Nat.mod_two_eq_zero_or_one ((m % 2 ^ k) / 2 ^ j) with h2 | h2 <;>
      simp_all

theorem bit_sum_mod_two_pow (k m : Nat) :
    ∑ j ∈ Finset.range k, (m / 2 ^ j % 2) * 2 ^ j = m % 2 ^ k := by
  induction k with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      have hmod : m % 2 ^ k.succ / 2 ^ k = m / 2 ^ k % 2 := by
        have hlt : m % 2 ^ k.succ / 2 ^ k < 2 := by
          apply Nat.div_lt_iff_lt_mul (by positivity) |>.mpr
          simpa [pow_succ, mul_comm] using Nat.mod_lt m (show 0 < 2 ^ k.succ by positivity)
        have hmod2 := (div_pow_mod_two_eq_mod_div_pow_mod_two
          (show k < k.succ by omega) (m := m)).symm
        exact (Nat.mod_eq_of_lt hlt).symm.trans hmod2
      have hmod3 := Nat.mod_mod_of_dvd m (Nat.pow_dvd_pow 2 (show k ≤ k.succ by omega))
      have key := Nat.div_add_mod (m % 2 ^ k.succ) (2 ^ k)
      rw [hmod, hmod3] at key
      linarith

theorem binRep_reconstruction (n m : Nat) (hn : 1 ≤ n) (hm : m < 2 ^ n) :
    m = ∑ i ∈ Finset.range n, (binRep n m).getD i 0 * 2 ^ (n - 1 - i) := by
  have hsum : ∑ i ∈ Finset.range n, (binRep n m).getD i 0 * 2 ^ (n - 1 - i) =
      ∑ i ∈ Finset.range n, (m / 2 ^ (n - 1 - i)) % 2 * 2 ^ (n - 1 - i) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [binRep_getD_eq n m i hn hm (Finset.mem_range.mp hi)]
  rw [hsum]
  have hflip := Finset.sum_flip (n := n - 1) (fun j => (m / 2 ^ j % 2) * 2 ^ j)
  simp only [show n - 1 + 1 = n from by omega] at hflip
  rw [hflip]
  exact ((bit_sum_mod_two_pow n m).trans (Nat.mod_eq_of_lt hm)).symm

theorem binRep_leading_zero (n m k : Nat) (hm : m < 2 ^ n) (hk : n < k) :
    (binRep k m).getD 0 0 = 0 := by
  have hk1 : 1 ≤ k := by omega
  have hm_k : m < 2 ^ k :=
    Nat.lt_of_lt_of_le hm (pow_le_pow_right₀ (by norm_num : (1 : Nat) ≤ 2) (by omega : n ≤ k))
  rw [binRep_getD_eq k m 0 hk1 hm_k (by omega)]
  simp only [show k - 1 - 0 = k - 1 from by omega]
  have hkn : n ≤ k - 1 := by omega
  have hlt : m < 2 ^ (k - 1) :=
    Nat.lt_of_lt_of_le hm (pow_le_pow_right₀ (by norm_num : (1 : Nat) ≤ 2) hkn)
  have hmzero : m / 2 ^ (k - 1) = 0 := by
    rw [Nat.div_eq_zero_iff]
    right
    exact hlt
  simp [hmzero]

theorem binRep_msb_one (n m : Nat) (hlo : 2 ^ n ≤ m) (hhi : m < 2 ^ (n + 1)) :
    (binRep (n + 1) m).getD 0 0 = 1 := by
  rw [binRep_getD_eq (n + 1) m 0 (by omega) hhi (by omega)]
  simp only [show n + 1 - 1 - 0 = n from by omega]
  have hd : m / 2 ^ n = 1 := by
    apply Nat.div_eq_of_lt_le
    · simpa using hlo
    · simpa [pow_succ, mul_comm] using hhi
  simp [hd]

end Nat
