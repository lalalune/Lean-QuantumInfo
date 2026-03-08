/-
Copyright (c) 2025 Bell Theorem / Tsirelson Bound
Released under Apache 2.0 license.

# Tsirelson's Bound Constant

Single source of truth for the critical ε value (√2 - 1)/2 that relates
thermal CHSH corrections to the quantum Tsirelson bound 2√2.

Used by: TLHV (thermal Bell), ThermMerm (Mermin), SharedEnBudget, TLHV_P.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt

open Real

/-- The critical ε value: (√2 - 1)/2 ≈ 0.207. Equals (1 - √2/2)/√2.
    When thermal correction ε = ε_tsirelson, CHSH bound reaches 2√2 (Tsirelson). -/
noncomputable def ε_tsirelson : ℝ := (Real.sqrt 2 - 1) / 2

lemma ε_tsirelson_value : 2 + 4 * ε_tsirelson = 2 * Real.sqrt 2 := by
  simp only [ε_tsirelson]
  ring

lemma ε_tsirelson_alt : ε_tsirelson = (1 - Real.sqrt 2 / 2) / Real.sqrt 2 := by
  unfold ε_tsirelson
  have h : Real.sqrt 2 > 0 := Real.sqrt_pos.mpr (by norm_num)
  field_simp [h.ne']
  ring_nf
  nlinarith [sq_sqrt (by positivity : 0 ≤ (2 : ℝ))]
