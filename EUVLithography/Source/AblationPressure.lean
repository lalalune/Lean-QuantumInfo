import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# EUV Lithography: Ablation Pressure Scaling

Formal algebra for the Fabbro-Mora-style ablation-pressure scaling used in the
EUV report.
-/

noncomputable section

/-- Ablation pressure scaling:
`P = K I^(3/4) lambda^(-1/4) A^(1/16) Z^(1/16)`. -/
def ablationPressure (K I lambda A Z : ℝ) : ℝ :=
  K * I ^ (3 / 4 : ℝ) * lambda ^ (-(1 / 4 : ℝ)) * A ^ (1 / 16 : ℝ) * Z ^ (1 / 16 : ℝ)

theorem ablationPressure_pos {K I lambda A Z : ℝ}
    (hK : 0 < K) (hI : 0 < I) (hlambda : 0 < lambda) (hA : 0 < A) (hZ : 0 < Z) :
    0 < ablationPressure K I lambda A Z := by
  unfold ablationPressure
  positivity

theorem ablationPressure_increases_with_intensity {K I₁ I₂ lambda A Z : ℝ}
    (hK : 0 < K) (hI₁ : 0 < I₁) (hI : I₁ < I₂)
    (hlambda : 0 < lambda) (hA : 0 < A) (hZ : 0 < Z) :
    ablationPressure K I₁ lambda A Z < ablationPressure K I₂ lambda A Z := by
  unfold ablationPressure
  have hI₂ : 0 < I₂ := lt_trans hI₁ hI
  have hpow : I₁ ^ (3 / 4 : ℝ) < I₂ ^ (3 / 4 : ℝ) :=
    Real.rpow_lt_rpow (le_of_lt hI₁) hI (by norm_num)
  have hleft : 0 < K * I₁ ^ (3 / 4 : ℝ) := mul_pos hK (Real.rpow_pos_of_pos hI₁ _)
  have htail : 0 < lambda ^ (-(1 / 4 : ℝ)) * A ^ (1 / 16 : ℝ) * Z ^ (1 / 16 : ℝ) := by
    positivity
  have hmain : K * I₁ ^ (3 / 4 : ℝ) < K * I₂ ^ (3 / 4 : ℝ) :=
    mul_lt_mul_of_pos_left hpow hK
  nlinarith [mul_lt_mul_of_pos_right hmain htail]

theorem ablationPressure_scales_K {K₁ K₂ I lambda A Z : ℝ}
    (_hK₁ : 0 < K₁) (hK : K₁ < K₂) (hI : 0 < I)
    (hlambda : 0 < lambda) (hA : 0 < A) (hZ : 0 < Z) :
    ablationPressure K₁ I lambda A Z < ablationPressure K₂ I lambda A Z := by
  unfold ablationPressure
  have hfactor : 0 < I ^ (3 / 4 : ℝ) * lambda ^ (-(1 / 4 : ℝ)) *
      A ^ (1 / 16 : ℝ) * Z ^ (1 / 16 : ℝ) := by
    positivity
  nlinarith [mul_lt_mul_of_pos_right hK hfactor]

end
