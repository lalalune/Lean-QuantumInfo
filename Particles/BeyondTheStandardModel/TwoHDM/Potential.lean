/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Particles.BeyondTheStandardModel.TwoHDM.GramMatrix
/-!

# The potential of the Two Higgs doublet model

## i. Overview

In this module we give the define the parameters of the 2HDM potential, and
give stability properties of the potential.

## ii. Key results

- `PotentialParameters` : The parameters of the 2HDM potential.
- `massTerm` : The mass term of the 2HDM potential.
- `quarticTerm` : The quartic term of the 2HDM potential.
- `potential` : The full potential of the 2HDM.
- `PotentialIsStable` : The condition that the potential is stable.

## iii. Table of contents

- A. The parameters of the potential
  - A.1. The potential parameters corresponding to zero
  - A.2. Gram parameters
  - A.3. Specific cases
- B. The mass term
- C. The quartic term
- D. The full potential
- E. Stability of the potential
  - E.1. The stability condition
  - E.2. Instability of the stabilityCounterExample potential
  - E.3. The reduced mass term
  - E.4. The reduced quartic term
  - E.5. Stability in terms of the gram vectors
  - E.6. Strong stability implies stability
  - E.7. Showing step in hep-ph/0605184 is invalid

## iv. References

For the parameterization of the potential we follow the convention of
- https://arxiv.org/pdf/1605.03237

Stability arguments of the potential follow, in part, those from
- https://arxiv.org/abs/hep-ph/0605184
Although we note that we explicitly prove that one of the steps in this paper is not valid.

-/
namespace TwoHiggsDoublet
open InnerProductSpace
open StandardModel

/-!

## A. The parameters of the potential

We define a type for the parameters of the Higgs potential in the 2HDM.

We follow the convention of `1605.03237`, which is highlighted in the explicit construction
of the potential itself.

We relate these parameters to the `ξ` and `η` parameters used in the gram vector formalism
given in arXiv:hep-ph/0605184.

-/

/-- The parameters of the Two Higgs doublet model potential.
  Following the convention of https://arxiv.org/pdf/1605.03237. -/
structure PotentialParameters where
  /-- The parameter corresponding to `m₁₁²` in the 2HDM potential. -/
  m₁₁2 : ℝ
  /-- The parameter corresponding to `m₂₂²` in the 2HDM potential. -/
  m₂₂2 : ℝ
  /-- The parameter corresponding to `m₁₂²` in the 2HDM potential. -/
  m₁₂2 : ℂ
  /-- The parameter corresponding to `λ₁` in the 2HDM potential. -/
  𝓵₁ : ℝ
  /-- The parameter corresponding to `λ₂` in the 2HDM potential. -/
  𝓵₂ : ℝ
  /-- The parameter corresponding to `λ₃` in the 2HDM potential. -/
  𝓵₃ : ℝ
  /-- The parameter corresponding to `λ₄` in the 2HDM potential. -/
  𝓵₄ : ℝ
  /-- The parameter corresponding to `λ₅` in the 2HDM potential. -/
  𝓵₅ : ℂ
  /-- The parameter corresponding to `λ₆` in the 2HDM potential. -/
  𝓵₆ : ℂ
  /-- The parameter corresponding to `λ₇` in the 2HDM potential. -/
  𝓵₇ : ℂ

namespace PotentialParameters

/-!

### A.1. The potential parameters corresponding to zero

We define an instance of `Zero` for the potential parameters, corresponding to all
parameters being zero, and therefore the potential itself being zero.

-/

instance : Zero PotentialParameters where
  zero :=
    { m₁₁2 := 0
      m₂₂2 := 0
      m₁₂2 := 0
      𝓵₁ := 0
      𝓵₂ := 0
      𝓵₃ := 0
      𝓵₄ := 0
      𝓵₅ := 0
      𝓵₆ := 0
      𝓵₇ := 0 }

@[simp] lemma zero_m₁₁2 : (0 : PotentialParameters).m₁₁2 = 0 := rfl

@[simp] lemma zero_m₂₂2 : (0 : PotentialParameters).m₂₂2 = 0 := rfl

@[simp] lemma zero_m₁₂2 : (0 : PotentialParameters).m₁₂2 = 0 := rfl

@[simp] lemma zero_𝓵₁ : (0 : PotentialParameters).𝓵₁ = 0 := rfl

@[simp] lemma zero_𝓵₂ : (0 : PotentialParameters).𝓵₂ = 0 := rfl

@[simp] lemma zero_𝓵₃ : (0 : PotentialParameters).𝓵₃ = 0 := rfl

@[simp] lemma zero_𝓵₄ : (0 : PotentialParameters).𝓵₄ = 0 := rfl

@[simp] lemma zero_𝓵₅ : (0 : PotentialParameters).𝓵₅ = 0 := rfl

@[simp] lemma zero_𝓵₆ : (0 : PotentialParameters).𝓵₆ = 0 := rfl

@[simp] lemma zero_𝓵₇ : (0 : PotentialParameters).𝓵₇ = 0 := rfl

/-!

### A.2. Gram parameters

A reparameterization of the potential parameters corresponding to `ξ` and `η` in
arXiv:hep-ph/0605184.

-/

/-- A reparameterization of the parameters of the quadratic terms of the
  potential for use with the gramVector. -/
noncomputable def ξ (P : PotentialParameters) (μ : Fin 1 ⊕ Fin 3) : ℝ :=
  match μ with
  | .inl 0 => (P.m₁₁2 + P.m₂₂2) / 2
  | .inr 0 => -Complex.re P.m₁₂2
  | .inr 1 => Complex.im P.m₁₂2
  | .inr 2 => (P.m₁₁2 - P.m₂₂2) / 2

@[simp]
lemma ξ_zero : (0 : PotentialParameters).ξ = 0 := by
  ext μ
  fin_cases μ <;> simp [ξ]

/-- A reparameterization of the parameters of the quartic terms of the
  potential for use with the gramVector. -/
noncomputable def η (P : PotentialParameters) : Fin 1 ⊕ Fin 3 → Fin 1 ⊕ Fin 3 → ℝ
  | .inl 0, .inl 0 => (P.𝓵₁ + P.𝓵₂ + 2 * P.𝓵₃) / 8
  | .inl 0, .inr 0 => (P.𝓵₆.re + P.𝓵₇.re) / 4
  | .inl 0, .inr 1 => - (P.𝓵₆.im + P.𝓵₇.im) / 4
  | .inl 0, .inr 2 => (P.𝓵₁ - P.𝓵₂) / 8
  | .inr 0, .inl 0 => (P.𝓵₆.re + P.𝓵₇.re) / 4
  | .inr 1, .inl 0 => -(P.𝓵₆.im + P.𝓵₇.im) / 4
  | .inr 2, .inl 0 => (P.𝓵₁ - P.𝓵₂) / 8
  | .inr 0, .inr 0 => (P.𝓵₅.re + P.𝓵₄) / 4
  | .inr 1, .inr 1 => (P.𝓵₄ - P.𝓵₅.re) / 4
  | .inr 2, .inr 2 => (P.𝓵₁ + P.𝓵₂ - 2 * P.𝓵₃) / 8
  | .inr 0, .inr 1 => - P.𝓵₅.im / 4
  | .inr 2, .inr 0 => (P.𝓵₆.re - P.𝓵₇.re) / 4
  | .inr 2, .inr 1 => (P.𝓵₇.im - P.𝓵₆.im) / 4
  | .inr 1, .inr 0 => - P.𝓵₅.im / 4
  | .inr 0, .inr 2 => (P.𝓵₆.re - P.𝓵₇.re) / 4
  | .inr 1, .inr 2 => (P.𝓵₇.im - P.𝓵₆.im) / 4

lemma η_symm (P : PotentialParameters) (μ ν : Fin 1 ⊕ Fin 3) :
    P.η μ ν = P.η ν μ := by
  fin_cases μ <;> fin_cases ν <;> simp [η]

@[simp]
lemma η_zero : (0 : PotentialParameters).η = 0 := by
  ext μ ν
  fin_cases μ <;> fin_cases ν <;> simp [η]

/-!

### A.3. Specific cases

-/

/-- An example of potential parameters that serve as a counterexample to the stability
  condition given in arXiv:hep-ph/0605184.
  This corresponds to the potential:
  `2 * (⟪H.Φ1, H.Φ2⟫_ℂ).im + ‖H.Φ1 - H.Φ2‖ ^ 4`
  which has the property that the quartic term is non-negative and only zero if
  the mass term is also zero, but the potential is not stable.
  In the proof that `stabilityCounterExample_not_potentialIsStable`, we give
  explicit vectors `H.Φ1` and `H.Φ2` that show this potential is not stable.

  This is the first occurrence of such a counterexample in the literature to the best of
  the author's knowledge.
-/
def stabilityCounterExample : PotentialParameters := {(0 : PotentialParameters) with
    m₁₂2 := Complex.I
    𝓵₁ := 2
    𝓵₂ := 2
    𝓵₃ := 2
    𝓵₄ := 2
    𝓵₅ := 2
    𝓵₆ := -2
    𝓵₇ := -2}

lemma stabilityCounterExample_ξ :
    stabilityCounterExample.ξ = fun
      | .inl 0 => 0
      | .inr 0 => 0
      | .inr 1 => 1
      | .inr 2 => 0 := by
  funext μ
  simp [stabilityCounterExample, ξ]

lemma stabilityCounterExample_η :
    stabilityCounterExample.η = fun μ => fun ν =>
    match μ, ν with
    | .inl 0, .inl 0 => 1
    | .inl 0, .inr 0 => -1
    | .inl 0, .inr 1 => 0
    | .inl 0, .inr 2 => 0
    | .inr 0, .inl 0 => -1
    | .inr 1, .inl 0 => 0
    | .inr 2, .inl 0 => 0
    | .inr 0, .inr 0 => 1
    | .inr 1, .inr 1 => 0
    | .inr 2, .inr 2 => 0
    | .inr 0, .inr 1 => 0
    | .inr 2, .inr 0 => 0
    | .inr 2, .inr 1 => 0
    | .inr 1, .inr 0 => 0
    | .inr 0, .inr 2 => 0
    | .inr 1, .inr 2 => 0 := by
  funext μ ν
  simp [stabilityCounterExample, η]
  ring_nf

end PotentialParameters

open ComplexConjugate

/-!

## B. The mass term

We define the mass term of the potential, write it in terms of the gram vector,
and prove that it is gauge invariant.

-/

/-- The mass term of the two Higgs doublet model potential. -/
noncomputable def massTerm (P : PotentialParameters) (H : TwoHiggsDoublet) : ℝ :=
  P.m₁₁2 * ‖H.Φ1‖ ^ 2 + P.m₂₂2 * ‖H.Φ2‖ ^ 2 -
  (P.m₁₂2 * ⟪H.Φ1, H.Φ2⟫_ℂ + conj P.m₁₂2 * ⟪H.Φ2, H.Φ1⟫_ℂ).re

lemma massTerm_eq_gramVector (P : PotentialParameters) (H : TwoHiggsDoublet) :
    massTerm P H = ∑ μ, P.ξ μ * H.gramVector μ := by
  simp [massTerm, Fin.sum_univ_three, PotentialParameters.ξ, normSq_Φ1_eq_gramVector,
    normSq_Φ2_eq_gramVector, Φ1_inner_Φ2_eq_gramVector, Φ2_inner_Φ1_eq_gramVector]
  ring

@[simp]
lemma gaugeGroupI_smul_massTerm (g : StandardModel.GaugeGroupI) (P : PotentialParameters)
    (H : TwoHiggsDoublet) :
    massTerm P (g • H) = massTerm P H := by
  rw [massTerm_eq_gramVector, massTerm_eq_gramVector]
  simp

@[simp]
lemma massTerm_zero : massTerm 0 = 0 := by
  ext H
  simp [massTerm]

lemma massTerm_stabilityCounterExample (H : TwoHiggsDoublet) :
    massTerm PotentialParameters.stabilityCounterExample H =
    2 * (⟪H.Φ1, H.Φ2⟫_ℂ).im := by
  simp [massTerm, PotentialParameters.stabilityCounterExample]
  rw [show ⟪H.Φ2, H.Φ1⟫_ℂ = conj ⟪H.Φ1, H.Φ2⟫_ℂ from Eq.symm (conj_inner_symm H.Φ2 H.Φ1)]
  rw [Complex.conj_im]
  ring_nf

/-!

## C. The quartic term

We define the quartic term of the potential, write it in terms of the gram vector,
and prove that it is gauge invariant.

-/

/-- The quartic term of the two Higgs doublet model potential. -/
noncomputable def quarticTerm (P : PotentialParameters) (H : TwoHiggsDoublet) : ℝ :=
  1/2 * P.𝓵₁ * ‖H.Φ1‖ ^ 2 * ‖H.Φ1‖ ^ 2 + 1/2 * P.𝓵₂ * ‖H.Φ2‖ ^ 2 * ‖H.Φ2‖ ^ 2
  + P.𝓵₃ * ‖H.Φ1‖ ^ 2 * ‖H.Φ2‖ ^ 2
  + P.𝓵₄ * ‖⟪H.Φ1, H.Φ2⟫_ℂ‖ ^ 2
  + (1/2 * P.𝓵₅ * ⟪H.Φ1, H.Φ2⟫_ℂ ^ 2 + 1/2 * conj P.𝓵₅ * ⟪H.Φ2, H.Φ1⟫_ℂ ^ 2).re
  + (P.𝓵₆ * ‖H.Φ1‖ ^ 2 * ⟪H.Φ1, H.Φ2⟫_ℂ + conj P.𝓵₆ * ‖H.Φ1‖ ^ 2 * ⟪H.Φ2, H.Φ1⟫_ℂ).re
  + (P.𝓵₇ * ‖H.Φ2‖ ^ 2 * ⟪H.Φ1, H.Φ2⟫_ℂ + conj P.𝓵₇ * ‖H.Φ2‖ ^ 2 * ⟪H.Φ2, H.Φ1⟫_ℂ).re

lemma quarticTerm_𝓵₄_expand (P : PotentialParameters) (H : TwoHiggsDoublet) :
    H.quarticTerm P =
    1/2 * P.𝓵₁ * ‖H.Φ1‖ ^ 2 * ‖H.Φ1‖ ^ 2 + 1/2 * P.𝓵₂ * ‖H.Φ2‖ ^ 2 * ‖H.Φ2‖ ^ 2
    + P.𝓵₃ * ‖H.Φ1‖ ^ 2 * ‖H.Φ2‖ ^ 2
    + P.𝓵₄ * (⟪H.Φ1, H.Φ2⟫_ℂ * ⟪H.Φ2, H.Φ1⟫_ℂ).re
    + (1/2 * P.𝓵₅ * ⟪H.Φ1, H.Φ2⟫_ℂ ^ 2 + 1/2 * conj P.𝓵₅ * ⟪H.Φ2, H.Φ1⟫_ℂ ^ 2).re
    + (P.𝓵₆ * ‖H.Φ1‖ ^ 2 * ⟪H.Φ1, H.Φ2⟫_ℂ + conj P.𝓵₆ * ‖H.Φ1‖ ^ 2 * ⟪H.Φ2, H.Φ1⟫_ℂ).re
    + (P.𝓵₇ * ‖H.Φ2‖ ^ 2 * ⟪H.Φ1, H.Φ2⟫_ℂ + conj P.𝓵₇ * ‖H.Φ2‖ ^ 2 * ⟪H.Φ2, H.Φ1⟫_ℂ).re := by
  simp [quarticTerm]
  left
  rw [Complex.sq_norm]
  rw [← Complex.mul_re]
  rw [← inner_conj_symm, ← Complex.normSq_eq_conj_mul_self]
  simp only [inner_conj_symm, Complex.ofReal_re]
  rw [← inner_conj_symm]
  exact Complex.normSq_conj ⟪H.Φ2, H.Φ1⟫_ℂ

lemma quarticTerm_eq_gramVector (P : PotentialParameters) (H : TwoHiggsDoublet) :
    quarticTerm P H = ∑ a, ∑ b, H.gramVector a * H.gramVector b * P.η a b := by
  simp [quarticTerm_𝓵₄_expand, Fin.sum_univ_three, PotentialParameters.η, normSq_Φ1_eq_gramVector,
    normSq_Φ2_eq_gramVector, Φ1_inner_Φ2_eq_gramVector, Φ2_inner_Φ1_eq_gramVector]
  ring_nf
  simp [← Complex.ofReal_pow, Complex.ofReal_re, normSq_Φ1_eq_gramVector,
    normSq_Φ2_eq_gramVector]
  ring

@[simp]
lemma gaugeGroupI_smul_quarticTerm (g : StandardModel.GaugeGroupI) (P : PotentialParameters)
    (H : TwoHiggsDoublet) :
    quarticTerm P (g • H) = quarticTerm P H := by
  rw [quarticTerm_eq_gramVector, quarticTerm_eq_gramVector]
  simp

@[simp]
lemma quarticTerm_zero : quarticTerm 0 = 0 := by
  ext H
  simp [quarticTerm]

lemma quarticTerm_stabilityCounterExample (H : TwoHiggsDoublet) :
    quarticTerm .stabilityCounterExample H =
    (‖H.Φ1‖ ^ 2 + ‖H.Φ2‖ ^ 2 - 2 * (⟪H.Φ1, H.Φ2⟫_ℂ).re) ^ 2:= by
  /- Proof by calculation. -/
  calc _ = (‖H.Φ1‖ ^ 2 + ‖H.Φ2‖ ^ 2) ^ 2
    + 2 * ‖⟪H.Φ1, H.Φ2⟫_ℂ‖ ^ 2
    + (⟪H.Φ1, H.Φ2⟫_ℂ ^ 2 + ⟪H.Φ2, H.Φ1⟫_ℂ ^ 2).re
    - 2 * (‖H.Φ1‖ ^ 2 + ‖H.Φ2‖ ^ 2) * ((⟪H.Φ1, H.Φ2⟫_ℂ).re + (⟪H.Φ2, H.Φ1⟫_ℂ).re) := by
        simp [quarticTerm, PotentialParameters.stabilityCounterExample, Complex.add_re,
          ← Complex.ofReal_pow]
        ring
      _ = (‖H.Φ1‖ ^ 2 + ‖H.Φ2‖ ^ 2) ^ 2
      + 4 * (⟪H.Φ1, H.Φ2⟫_ℂ).re ^ 2
      - 2 * (‖H.Φ1‖ ^ 2 + ‖H.Φ2‖ ^ 2) * ((⟪H.Φ1, H.Φ2⟫_ℂ).re + (⟪H.Φ2, H.Φ1⟫_ℂ).re) := by
        have h1 : 2 * ‖⟪H.Φ1, H.Φ2⟫_ℂ‖ ^ 2
            + (⟪H.Φ1, H.Φ2⟫_ℂ ^ 2 + ⟪H.Φ2, H.Φ1⟫_ℂ ^ 2).re = 4 * (⟪H.Φ1, H.Φ2⟫_ℂ).re ^ 2 := by
          rw [show ⟪H.Φ2, H.Φ1⟫_ℂ = conj ⟪H.Φ1, H.Φ2⟫_ℂ from Eq.symm (conj_inner_symm H.Φ2 H.Φ1)]
          generalize ⟪H.Φ1, H.Φ2⟫_ℂ = z
          have hz : z = z.re + z.im * Complex.I := by exact Eq.symm (Complex.re_add_im z)
          generalize z.re = x at hz
          generalize z.im = y at hz
          subst hz
          have h0 : ‖↑x + ↑y * Complex.I‖ ^ 2 = x ^ 2 + y ^ 2 := by
            rw [Complex.norm_add_mul_I, Real.sq_sqrt]
            positivity
          rw [h0]
          simp [Complex.add_re, sq]
          ring
        rw [← h1]
        ring
      _ = (‖H.Φ1‖ ^ 2 + ‖H.Φ2‖ ^ 2 - 2 * (⟪H.Φ1, H.Φ2⟫_ℂ).re) ^ 2 := by
        rw [show ⟪H.Φ2, H.Φ1⟫_ℂ = conj ⟪H.Φ1, H.Φ2⟫_ℂ from Eq.symm (conj_inner_symm H.Φ2 H.Φ1)]
        rw [Complex.conj_re]
        ring

lemma quarticTerm_stabilityCounterExample_eq_norm_pow_four (H : TwoHiggsDoublet) :
    quarticTerm .stabilityCounterExample H = ‖H.Φ1 - H.Φ2‖ ^ 4 := by
  /- Proof by calculation. -/
  calc _
      _ = (‖H.Φ1‖ ^ 2 + ‖H.Φ2‖ ^ 2 - 2 * (⟪H.Φ1, H.Φ2⟫_ℂ).re) ^ 2 := by
        rw [quarticTerm_stabilityCounterExample]
      _ = (‖H.Φ1 - H.Φ2‖ ^ 2) ^ 2 := by
        congr
        have h1 (v : HiggsVec) : ‖v‖ ^ 2 = (⟪v, v⟫_ℂ).re := by
          rw [inner_self_eq_norm_sq_to_K]
          simp [← Complex.ofReal_pow]
        rw [h1, h1, h1]
        simp only [inner_sub_right, inner_sub_left, Complex.sub_re]
        rw [show ⟪H.Φ2, H.Φ1⟫_ℂ = conj ⟪H.Φ1, H.Φ2⟫_ℂ from Eq.symm (conj_inner_symm H.Φ2 H.Φ1)]
        rw [Complex.conj_re]
        ring
      _ = ‖H.Φ1 - H.Φ2‖ ^ 4 := by ring

lemma quarticTerm_stabilityCounterExample_nonneg (H : TwoHiggsDoublet) :
    0 ≤ quarticTerm .stabilityCounterExample H := by
  rw [quarticTerm_stabilityCounterExample_eq_norm_pow_four]
  positivity

lemma massTerm_zero_of_quarticTerm_zero_stabilityCounterExample (H : TwoHiggsDoublet)
    (h : quarticTerm .stabilityCounterExample H = 0) :
    massTerm .stabilityCounterExample H = 0 := by
  rw [quarticTerm_stabilityCounterExample_eq_norm_pow_four] at h
  have h1 : ‖H.Φ1 - H.Φ2‖ = 0 := by
    exact pow_eq_zero h
  have h2 : H.Φ1 = H.Φ2 := by rwa [norm_eq_zero, sub_eq_zero] at h1
  rw [massTerm_stabilityCounterExample, h2]
  have him : (⟪H.Φ2, H.Φ2⟫_ℂ).im = 0 := by
    simpa [inner_self_eq_norm_sq_to_K]
  rw [him]
  ring

/-!

## D. The full potential

We define the full potential as the sum of the mass and quartic terms,
and prove that it is gauge invariant.

-/

/-- The potential of the two Higgs doublet model. -/
noncomputable def potential (P : PotentialParameters) (H : TwoHiggsDoublet) : ℝ :=
  massTerm P H + quarticTerm P H

@[simp]
lemma gaugeGroupI_smul_potential (g : StandardModel.GaugeGroupI)
    (P : PotentialParameters) (H : TwoHiggsDoublet) :
    potential P (g • H) = potential P H := by
  rw [potential, potential]
  simp

@[simp]
lemma potential_zero : potential 0 = 0 := by
  ext H
  simp [potential]

lemma potential_stabilityCounterExample (H : TwoHiggsDoublet) :
    potential .stabilityCounterExample H = 2 * (⟪H.Φ1, H.Φ2⟫_ℂ).im + ‖H.Φ1 - H.Φ2‖ ^ 4 := by
  simp [potential, massTerm_stabilityCounterExample,
    quarticTerm_stabilityCounterExample_eq_norm_pow_four]

lemma potential_eq_gramVector (P : PotentialParameters) (H : TwoHiggsDoublet) :
    potential P H = ∑ μ, P.ξ μ * H.gramVector μ +
    ∑ a, ∑ b, H.gramVector a * H.gramVector b * P.η a b := by
  rw [potential, massTerm_eq_gramVector, quarticTerm_eq_gramVector]

/-!

## E. Stability of the potential

-/

/-!

### E.1. The stability condition

We define the condition that the potential is stable, that is, bounded from below.

-/

/-- The condition that the potential is stable. -/
def PotentialIsStable (P : PotentialParameters) : Prop :=
  ∃ c : ℝ, ∀ H : TwoHiggsDoublet, c ≤ potential P H

/-!

### E.2. Instability of the stabilityCounterExample potential

-/

open Real

/-- The potential `stabilityCounterExample` is not stable. -/
lemma stabilityCounterExample_not_potentialIsStable :
    ¬ PotentialIsStable .stabilityCounterExample := by
  simp [PotentialIsStable]
  intro c
  /- The angle t and properties thereof. -/
  let t := Real.arctan (2 * Real.sqrt (|c| + 1))⁻¹
  have t_pos : 0 < t := by
    dsimp [t]
    apply Real.arctan_pos.2
    positivity
  have t_le_pi_div_2 : t ≤ Real.pi / 2 := by
    simpa [t] using le_of_lt <| arctan_lt_pi_div_two ((√(|c| + 1))⁻¹ * 2⁻¹)
  have t_ne_zero : t ≠ 0 := by
    exact ne_of_gt t_pos
  have sin_t_pos : 0 < sin t := by
    apply Real.sin_pos_of_pos_of_lt_pi t_pos
    linarith [t_le_pi_div_2, Real.pi_pos]
  have cos_t_pos : 0 < cos t := by
    simp [t]
    exact cos_arctan_pos ((√(|c| + 1))⁻¹ * 2⁻¹)
  have t_mul_sin_t_nonneg : 0 ≤ 2 * t * sin t - t ^ 2 := by
    rw [sub_nonneg]
    trans 2 * t * (2 / Real.pi * t)
    · ring_nf
      rw [mul_assoc]
      apply le_mul_of_one_le_right
      · positivity
      · field_simp
        exact Real.pi_le_four
    · have := Real.mul_le_sin (le_of_lt t_pos) t_le_pi_div_2
      nlinarith
  /- The Two Higgs doublet violating stability.
    The two Higgs doublet is constructed so that for the gram vector
    `v` we have:
    - `v₀ = cos t/(2 * t * (sin t)^2)`
    - `v₁/v₀ = (1 - t * sin t)`
    - `v₂/v₀ = - t * cos t`
    - `v₃ = 0` -/
  let H : TwoHiggsDoublet := {
    Φ1 := !₂[√(cos t/(4 * t * (sin t)^2)), 0]
    Φ2 := √(cos t/(4 * t * (sin t)^2)) • !₂[1 - t * sin t - Complex.I * t * cos t,
      √(2 * t * sin t - t ^ 2)] }
  have Φ1_norm_sq : ‖H.Φ1‖ ^ 2 = cos t/(4 * t * (sin t)^2) := by
    simp [H, PiLp.norm_sq_eq_of_L2]
    rw [sq_sqrt]
    positivity
  have Φ2_norm_sq : ‖H.Φ2‖ ^ 2 = cos t/(4 * t * (sin t)^2) := by
    simp [H, norm_smul, mul_pow]
    rw [sq_sqrt (by positivity)]
    simp [PiLp.norm_sq_eq_of_L2]
    rw [sq_sqrt (by positivity)]
    have h0 : ‖1 - ↑t * Complex.sin ↑t - Complex.I * ↑t * Complex.cos ↑t‖ ^ 2 =
        1 + t ^ 2 - 2 * t * sin t := by
      rw [← Complex.normSq_eq_norm_sq]
      trans Complex.normSq (Complex.ofReal (1 - t * sin t) +
        Complex.ofReal (-t * cos t) * Complex.I)
      · simp
        ring_nf
      rw [Complex.normSq_add_mul_I]
      trans 1 + t ^2 * (sin t ^2 + cos t ^2) - 2 *(t * sin t)
      · ring
      rw [sin_sq_add_cos_sq]
      ring
    rw [h0]
    field_simp
    ring
  have Φ1_inner_Φ2 : ⟪H.Φ1, H.Φ2⟫_ℂ = Complex.ofReal (cos t/(4 * t * (sin t)^2) *
      (1 - t * sin t)) + Complex.I *
      Complex.ofReal (cos t/(4 * t * (sin t)^2) * (- t * cos t)) := by
    simp [H, PiLp.inner_apply]
    trans Complex.ofReal ((√(cos t / (4 * t * sin t ^ 2))) ^ 2) *
        (1 - ↑t * Complex.sin ↑t - Complex.I * ↑t * Complex.cos ↑t)
    · simp
      ring
    rw [sq_sqrt (by positivity)]
    simp only [Complex.ofReal_div, Complex.ofReal_cos, Complex.ofReal_mul, Complex.ofReal_ofNat,
      Complex.ofReal_pow, Complex.ofReal_sin]
    ring
  have Φ1_inner_Φ2_re : (⟪H.Φ1, H.Φ2⟫_ℂ).re = cos t/(4 * t * (sin t)^2) * (1 - t * sin t) := by
    rw [Φ1_inner_Φ2, Complex.add_re, Complex.ofReal_re, Complex.re_mul_ofReal]
    simp
  have Φ1_inner_Φ2_im : (⟪H.Φ1, H.Φ2⟫_ℂ).im = cos t/(4 * t * (sin t)^2) * (- t * cos t) := by
    rw [Φ1_inner_Φ2, Complex.add_im, Complex.im_mul_ofReal, Complex.ofReal_im]
    simp
  have potential_H_cos_sin : potential .stabilityCounterExample H =
      - (cos t) ^ 2/ (4 * (sin t)^2) := by
    rw [potential, massTerm_stabilityCounterExample, quarticTerm_stabilityCounterExample]
    rw [Φ1_norm_sq, Φ2_norm_sq, Φ1_inner_Φ2_re, Φ1_inner_Φ2_im]
    field
  have potential_H_tan : potential .stabilityCounterExample H =
      - 1/(4 * tan t ^ 2) := by
    rw [potential_H_cos_sin, tan_eq_sin_div_cos]
    field
  have potential_eq_c : potential .stabilityCounterExample H = - (|c| + 1) := by
    rw [potential_H_tan, tan_arctan]
    field_simp
    rw [sq_sqrt (by positivity)]
    ring
  /- Proving potential is unbounded. -/
  use H
  rw [potential_eq_c]
  have hlt : -(|c| + 1) < c := by
    have habs : -|c| ≤ c := by
      exact neg_abs_le c
    linarith
  exact hlt

/-!

### E.3. The reduced mass term

The reduced mass term is a function that helps express the stability condition.
It is the function `J2` in https://arxiv.org/abs/hep-ph/0605184.

-/

/-- A function related to the mass term of the potential, used in the stableness
  condition and equivalent to the term `J2` in
  https://arxiv.org/abs/hep-ph/0605184. -/
noncomputable def massTermReduced (P : PotentialParameters) (k : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  P.ξ (Sum.inl 0) + ∑ μ, P.ξ (Sum.inr μ) * k μ

lemma massTermReduced_lower_bound (P : PotentialParameters) (k : EuclideanSpace ℝ (Fin 3))
    (hk : ‖k‖ ^ 2 ≤ 1) : P.ξ (Sum.inl 0) - √(∑ a, |P.ξ (Sum.inr a)| ^ 2) ≤ massTermReduced P k := by
  simp only [Fin.isValue, massTermReduced]
  have h1 (a b c : ℝ) (h : - b ≤ c) : a - b ≤ a + c := by
    linarith
  apply h1
  let ξEuclid : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 (fun a => P.ξ (Sum.inr a))
  trans - ‖ξEuclid‖
  · simp [PiLp.norm_eq_of_L2, ξEuclid]
  trans - (‖k‖ * ‖ξEuclid‖)
  · simp
    simp at hk
    have ha (a b : ℝ) (h : a ≤ 1) (ha : 0 ≤ a) (hb : 0 ≤ b) : a * b ≤ b := by nlinarith
    apply ha
    · exact hk
    · exact norm_nonneg k
    · exact norm_nonneg ξEuclid
  trans - ‖⟪k, ξEuclid⟫_ℝ‖
  · simp
    exact abs_real_inner_le_norm k ξEuclid
  trans ⟪k, ξEuclid⟫_ℝ
  · simp
    exact neg_abs_le _ 
  simp [PiLp.inner_apply, ξEuclid]

@[simp]
lemma massTermReduced_zero : massTermReduced 0 = 0 := by
  ext k
  simp [massTermReduced]

lemma massTermReduced_stabilityCounterExample (k : EuclideanSpace ℝ (Fin 3)) :
    massTermReduced .stabilityCounterExample k = k 1 := by
  simp [massTermReduced, PotentialParameters.ξ, Fin.isValue,
    PotentialParameters.stabilityCounterExample, Fin.sum_univ_three]

/-!

### E.4. The reduced quartic term

The reduced quartic term is a function that helps express the stability condition.
It is the function `J4` in https://arxiv.org/abs/hep-ph/0605184.

-/

/-- A function related to the quartic term of the potential, used in the stableness
  condition and equivalent to the term `J4` in
  https://arxiv.org/abs/hep-ph/0605184. -/
noncomputable def quarticTermReduced (P : PotentialParameters) (k : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  P.η (Sum.inl 0) (Sum.inl 0) + 2 * ∑ b, k b * P.η (Sum.inl 0) (Sum.inr b) +
  ∑ a, ∑ b, k a * k b * P.η (Sum.inr a) (Sum.inr b)

@[simp]
lemma quarticTermReduced_zero : quarticTermReduced 0 = 0 := by
  ext k
  simp [quarticTermReduced]

lemma quarticTermReduced_stabilityCounterExample (k : EuclideanSpace ℝ (Fin 3)) :
    quarticTermReduced .stabilityCounterExample k = (1 - k 0) ^ 2 := by
  simp [quarticTermReduced, PotentialParameters.η, Fin.isValue,
    PotentialParameters.stabilityCounterExample, Fin.sum_univ_three]
  ring

lemma quarticTermReduced_stabilityCounterExample_nonneg (k : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ quarticTermReduced .stabilityCounterExample k := by
  rw [quarticTermReduced_stabilityCounterExample]
  apply sq_nonneg

/-!

### E.5. Stability in terms of the gram vectors

We give some necessary and sufficient conditions for the potential to be stable
in terms of the gram vectors.

This follows the analysis in https://arxiv.org/abs/hep-ph/0605184.

We also give some necessary conditions.

-/

lemma potentialIsStable_iff_forall_gramVector (P : PotentialParameters) :
    PotentialIsStable P ↔ ∃ c : ℝ, ∀ K : Fin 1 ⊕ Fin 3 → ℝ, 0 ≤ K (Sum.inl 0) →
      ∑ μ : Fin 3, K (Sum.inr μ) ^ 2 ≤ K (Sum.inl 0) ^ 2 →
      c ≤ ∑ μ, P.ξ μ * K μ + ∑ a, ∑ b, K a * K b * P.η a b := by
  apply Iff.intro
  · intro h
    obtain ⟨c, hc⟩ := h
    use c
    intro v hv₀ hv_sum
    obtain ⟨H, hH⟩ := gramVector_surjective v hv₀ hv_sum
    apply (hc H).trans
    apply le_of_eq
    rw [potential, massTerm_eq_gramVector, quarticTerm_eq_gramVector]
    simp [hH]
  · intro h
    obtain ⟨c, hc⟩ := h
    use c
    intro H
    apply (hc H.gramVector (gramVector_inl_nonneg H) (gramVector_inr_sum_sq_le_inl H)).trans
    apply le_of_eq
    rw [potential, massTerm_eq_gramVector, quarticTerm_eq_gramVector]

lemma potentialIsStable_iff_forall_euclid (P : PotentialParameters) :
    PotentialIsStable P ↔ ∃ c, ∀ K0 : ℝ, ∀ K : EuclideanSpace ℝ (Fin 3), 0 ≤ K0 →
      ‖K‖ ^ 2 ≤ K0 ^ 2 → c ≤ P.ξ (Sum.inl 0) * K0 + ∑ μ, P.ξ (Sum.inr μ) * K μ
      + K0 ^ 2 * P.η (Sum.inl 0) (Sum.inl 0)
      + 2 * K0 * ∑ b, K b * P.η (Sum.inl 0) (Sum.inr b) +
      ∑ a, ∑ b, K a * K b * P.η (Sum.inr a) (Sum.inr b) := by
  rw [potentialIsStable_iff_forall_gramVector]
  refine exists_congr (fun c => ?_)
  rw [Equiv.forall_congr_left (Equiv.sumArrowEquivProdArrow (Fin 1) (Fin 3) ℝ)]
  simp only [Fin.isValue, Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero,
    Finset.sum_singleton, Prod.forall, Equiv.sumArrowEquivProdArrow_symm_apply_inl,
    Equiv.sumArrowEquivProdArrow_symm_apply_inr]
  rw [Equiv.forall_congr_left <| Equiv.funUnique (Fin 1) ℝ]
  apply forall_congr'
  intro K0
  rw [Equiv.forall_congr_left <| (WithLp.equiv 2 ((i : Fin 3) → (fun x => ℝ) i)).symm]
  apply forall_congr'
  intro K
  simp only [Fin.isValue, Equiv.funUnique_symm_apply, uniqueElim_const, Equiv.symm_symm,
    WithLp.equiv_apply]
  refine imp_congr_right ?_
  intro hle
  simp only [PiLp.norm_sq_eq_of_L2]
  simp only [Fin.isValue, Real.norm_eq_abs, sq_abs]
  refine imp_congr_right ?_
  intro hle'
  apply le_iff_le_of_cmp_eq_cmp
  congr 1
  simp [add_assoc, sq, Finset.sum_add_distrib]
  ring_nf
  simp [mul_assoc, ← Finset.mul_sum]
  conv_lhs =>
    enter [2, 2, 2, i]
    rw [PotentialParameters.η_symm]
  ring

lemma potentialIsStable_iff_forall_euclid_lt (P : PotentialParameters) :
    PotentialIsStable P ↔ ∃ c ≤ 0, ∀ K0 : ℝ, ∀ K : EuclideanSpace ℝ (Fin 3), 0 < K0 →
      ‖K‖ ^ 2 ≤ K0 ^ 2 → c ≤ P.ξ (Sum.inl 0) * K0 + ∑ μ, P.ξ (Sum.inr μ) * K μ
      + K0 ^ 2 * P.η (Sum.inl 0) (Sum.inl 0)
      + 2 * K0 * ∑ b, K b * P.η (Sum.inl 0) (Sum.inr b) +
      ∑ a, ∑ b, K a * K b * P.η (Sum.inr a) (Sum.inr b) := by
  rw [potentialIsStable_iff_forall_euclid]
  apply Iff.intro
  · intro h
    obtain ⟨c, hc⟩ := h
    use c
    apply And.intro
    · simpa using hc 0 0 (by simp) (by simp)
    · intro K0 K hk0 hle
      exact hc K0 K hk0.le hle
  · intro h
    obtain ⟨c, hc₀, hc⟩ := h
    use c
    intro K0 K hK0 hle
    by_cases hK0' : K0 = 0
    · subst hK0'
      simp_all
    · refine hc K0 K ?_ hle
      grind

lemma potentialIsStable_iff_exists_forall_forall_reduced (P : PotentialParameters) :
    PotentialIsStable P ↔ ∃ c ≤ 0, ∀ K0 : ℝ, ∀ k : EuclideanSpace ℝ (Fin 3), 0 < K0 →
      ‖k‖ ^ 2 ≤ 1 → c ≤ K0 * massTermReduced P k + K0 ^ 2 * quarticTermReduced P k := by
  rw [potentialIsStable_iff_forall_euclid_lt]
  refine exists_congr <| fun c => and_congr_right <| fun hc => forall_congr' <| fun K0 => ?_
  apply Iff.intro
  · refine fun h k hK0 k_le_one => (h (K0 • k) hK0 ?_).trans (le_of_eq ?_)
    · simp [norm_smul]
      rw [abs_of_nonneg (by positivity), mul_pow]
      nlinarith
    · simp [add_assoc, massTermReduced, quarticTermReduced]
      ring_nf
      simp [add_assoc, mul_assoc, ← Finset.mul_sum, sq]
      ring
  · intro h K hK0 hle
    refine (h ((1 / K0) • K) hK0 ?_).trans (le_of_eq ?_)
    · simp [norm_smul]
      field_simp
      rw [sq_le_sq] at hle
      simpa using hle
    · simp [add_assoc, massTermReduced, quarticTermReduced]
      ring_nf
      simp [add_assoc, mul_assoc, ← Finset.mul_sum, sq]
      field_simp
      ring_nf
      simp only [← Finset.sum_mul, Fin.isValue]
      field_simp
      ring

lemma quarticTermReduced_nonneg_of_potentialIsStable (P : PotentialParameters)
    (hP : PotentialIsStable P) (k : EuclideanSpace ℝ (Fin 3))
    (hk : ‖k‖ ^ 2 ≤ 1) : 0 ≤ quarticTermReduced P k := by
  rw [potentialIsStable_iff_exists_forall_forall_reduced] at hP
  obtain ⟨c, _, hc⟩ := hP
  by_contra h
  push_neg at h
  -- For large K0, the K0^2 * quarticTermReduced term dominates, giving arbitrarily negative values
  have : ∀ M : ℝ, ∃ K0 : ℝ, 0 < K0 ∧
    K0 * massTermReduced P k + K0 ^ 2 * quarticTermReduced P k < M := by
    intro M
    -- Pick K0 large enough that the negative quadratic term dominates.
    set K0 : ℝ := max 1 ((|massTermReduced P k| + |M| + 1) / |quarticTermReduced P k|)
    use K0
    constructor
    · positivity
    · have hq_neg : quarticTermReduced P k < 0 := h
      have hq_abs_pos : 0 < |quarticTermReduced P k| := by
        exact abs_pos.mpr (ne_of_lt hq_neg)
      have hbound_q :
          |massTermReduced P k| + |M| + 1 ≤ K0 * |quarticTermReduced P k| := by
        have hratio :
            (|massTermReduced P k| + |M| + 1) / |quarticTermReduced P k| ≤ K0 := by
          simpa [K0] using le_max_right 1
            ((|massTermReduced P k| + |M| + 1) / |quarticTermReduced P k|)
        exact (div_le_iff hq_abs_pos).1 hratio
      have hK0_nonneg : 0 ≤ K0 := le_of_lt (by positivity : 0 < K0)
      have h1 : K0 * massTermReduced P k ≤ K0 * |massTermReduced P k| := by
        exact mul_le_mul_of_nonneg_left (le_abs_self (massTermReduced P k)) hK0_nonneg
      have h2 : K0 ^ 2 * quarticTermReduced P k = -(K0 ^ 2 * |quarticTermReduced P k|) := by
        rw [abs_of_neg hq_neg]
        ring
      calc
        K0 * massTermReduced P k + K0 ^ 2 * quarticTermReduced P k
            ≤ K0 * |massTermReduced P k| + K0 ^ 2 * quarticTermReduced P k := by linarith
        _ = K0 * |massTermReduced P k| - K0 ^ 2 * |quarticTermReduced P k| := by
          rw [h2]
          ring
        _ = K0 * (|massTermReduced P k| - K0 * |quarticTermReduced P k|) := by ring
        _ ≤ K0 * (|massTermReduced P k| - (|massTermReduced P k| + |M| + 1)) := by
          have hinner :
              |massTermReduced P k| - K0 * |quarticTermReduced P k|
                ≤ |massTermReduced P k| - (|massTermReduced P k| + |M| + 1) := by
            linarith
          exact mul_le_mul_of_nonneg_left hinner hK0_nonneg
        _ = -K0 * (|M| + 1) := by ring
        _ ≤ -(|M| + 1) := by
          have hK0_ge : 1 ≤ K0 := by
            simpa [K0] using le_max_left 1
              ((|massTermReduced P k| + |M| + 1) / |quarticTermReduced P k|)
          nlinarith
        _ < M := by
          nlinarith [neg_abs_le M]
  obtain ⟨K0, hK0, hlt⟩ := this c
  linarith [hc K0 k hK0 hk]

lemma massTermReduced_pos_of_quarticTermReduced_zero_potentialIsStable (P : PotentialParameters)
    (hP : PotentialIsStable P) (k : EuclideanSpace ℝ (Fin 3))
    (hk : ‖k‖ ^ 2 ≤ 1) (hq : quarticTermReduced P k = 0) : 0 ≤ massTermReduced P k := by
  rw [potentialIsStable_iff_exists_forall_forall_reduced] at hP
  obtain ⟨c, _, hc⟩ := hP
  by_contra h
  push_neg at h
  set K0 : ℝ := max 1 ((|c| + 1) / |massTermReduced P k|)
  have hK0_pos : 0 < K0 := by positivity
  have hbound : c ≤ K0 * massTermReduced P k := by
    have hcK := hc K0 k hK0_pos hk
    simpa [hq] using hcK
  have hm_abs : |massTermReduced P k| = -(massTermReduced P k) := abs_of_neg h
  have hratio :
      (|c| + 1) / |massTermReduced P k| ≤ K0 := by
    simpa [K0] using le_max_right 1 ((|c| + 1) / |massTermReduced P k|)
  have hm_abs_pos : 0 < |massTermReduced P k| := by
    exact abs_pos.mpr (ne_of_lt h)
  have hmul :
      K0 * massTermReduced P k ≤ -(|c| + 1) := by
    have hmul_abs : |c| + 1 ≤ K0 * |massTermReduced P k| := by
      exact (div_le_iff hm_abs_pos).1 hratio
    have : K0 * massTermReduced P k = -(K0 * |massTermReduced P k|) := by
      rw [hm_abs]
      ring
    rw [this]
    linarith
  have hlt : K0 * massTermReduced P k < c := by
    have haux : -(|c| + 1) < c := by
      nlinarith [neg_abs_le c]
    linarith
  linarith

lemma potentialIsStable_iff_massTermReduced_sq_le_quarticTermReduced (P : PotentialParameters) :
    PotentialIsStable P ↔ ∃ c, 0 ≤ c ∧ ∀ k : EuclideanSpace ℝ (Fin 3), ‖k‖ ^ 2 ≤ 1 →
      0 ≤ quarticTermReduced P k ∧
      (massTermReduced P k < 0 →
      massTermReduced P k ^ 2 ≤ 4 * quarticTermReduced P k * c) := by
  rw [potentialIsStable_iff_exists_forall_forall_reduced]
  constructor
  · intro ⟨c, hc_le, hc⟩
    use -c
    constructor
    · linarith
    · intro k hk
      have hP : PotentialIsStable P := (potentialIsStable_iff_exists_forall_forall_reduced P).mpr ⟨c, hc_le, hc⟩
      have hq := quarticTermReduced_nonneg_of_potentialIsStable P hP k hk
      refine ⟨hq, fun hm => ?_⟩
      have hq_ne : quarticTermReduced P k ≠ 0 := by
        intro hq0; linarith [massTermReduced_pos_of_quarticTermReduced_zero_potentialIsStable P hP k hk hq0]
      have hq_pos : 0 < quarticTermReduced P k := lt_of_le_of_ne hq (Ne.symm hq_ne)
      -- At K0 = -m/(2q), the quadratic K0*m + K0²*q attains minimum -m²/(4q)
      have K0_min := -massTermReduced P k / (2 * quarticTermReduced P k)
      have hK0_pos : 0 < K0_min := div_pos (neg_pos.mpr hm) (by positivity)
      have hmin : K0_min * massTermReduced P k + K0_min ^ 2 * quarticTermReduced P k = -(massTermReduced P k) ^ 2 / (4 * quarticTermReduced P k) := by
        field_simp [ne_of_gt hq_pos]
        ring
      have := hc K0_min k hK0_pos hk
      rw [hmin] at this
      have : c ≤ -(massTermReduced P k) ^ 2 / (4 * quarticTermReduced P k) := this
      have h4q_pos : 0 < 4 * quarticTermReduced P k := by positivity
      exact (div_le_iff₀ (by positivity)).mpr (by linarith)
  · intro ⟨c, hc_nonneg, hc⟩
    use -c
    constructor
    · linarith
    · intro K0 k hK0 hk
      obtain ⟨hq, _⟩ := hc k hk
      -- The quadratic f(K0) = K0*m + K0²*q in K0 has derivative 2*K0*q + m, zero at K0 = -m/(2q)
      by_cases hm : massTermReduced P k < 0
      · obtain ⟨_, hm_sq⟩ := hc k hk
        specialize hm_sq hm
        have hq_ne : quarticTermReduced P k ≠ 0 := by
          intro hq0
          rw [hq0] at hm_sq
          have hm_sq_nonpos : massTermReduced P k ^ 2 ≤ 0 := by simpa using hm_sq
          have hm_zero : massTermReduced P k = 0 := by
            nlinarith [sq_nonneg (massTermReduced P k), hm_sq_nonpos]
          linarith
        have hq_pos : 0 < quarticTermReduced P k := lt_of_le_of_ne hq (Ne.symm hq_ne)
        -- Minimum of quadratic is -m²/(4q), and we need -c ≤ that minimum
        have hmin : ∀ K0 > 0, K0 * massTermReduced P k + K0 ^ 2 * quarticTermReduced P k ≥ -(massTermReduced P k) ^ 2 / (4 * quarticTermReduced P k) := by
          intro K0 hK0
          -- Completing the square: q*K0² + m*K0 = q*(K0 + m/(2q))² - m²/(4q) ≥ -m²/(4q)
          have h_complete : K0 * massTermReduced P k + K0 ^ 2 * quarticTermReduced P k - (-(massTermReduced P k) ^ 2 / (4 * quarticTermReduced P k)) =
              quarticTermReduced P k * (K0 + massTermReduced P k / (2 * quarticTermReduced P k)) ^ 2 := by
            field_simp [ne_of_gt hq_pos]
            ring
          suffices K0 * massTermReduced P k + K0 ^ 2 * quarticTermReduced P k - (-(massTermReduced P k) ^ 2 / (4 * quarticTermReduced P k)) ≥ 0 by linarith
          rw [h_complete]
          positivity
        have hbound' : massTermReduced P k ^ 2 / (4 * quarticTermReduced P k) ≤ c := by
          refine (div_le_iff (by positivity)).2 ?_
          simpa [mul_assoc, mul_left_comm, mul_comm] using hm_sq
        have hbound : -c ≤ -(massTermReduced P k) ^ 2 / (4 * quarticTermReduced P k) := by
          linarith [hbound']
        exact le_trans hbound (hmin K0 hK0)
      · push_neg at hm
        -- When m ≥ 0, f(K0) = K0*m + K0²*q ≥ 0 for K0 > 0, q ≥ 0, so -c ≤ f(K0) since -c ≤ 0
        nlinarith [sq_nonneg (massTermReduced P k), hm, hq]

/-!

### E.6. Strong stability implies stability

Stability in terms of the positivity of the quartic term, implies that the whole
potential is stable.

-/

/-- The potential is stable if it is strongly stable, i.e. its quartic term is always positive.
    The proof of this result relies on the compactness of the closed unit ball in
    `EuclideanSpace ℝ (Fin 3)`, and the `extreme value theorem`. -/
lemma potentialIsStable_of_strong (P : PotentialParameters)
    (h : ∀ k, ‖k‖ ^ 2 ≤ 1 → 0 < quarticTermReduced P k) :
    PotentialIsStable P := by
  rw [potentialIsStable_iff_massTermReduced_sq_le_quarticTermReduced]
  let S := Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1
  have S_isCompact : IsCompact S := isCompact_closedBall 0 1
  have S_nonEmpty : S.Nonempty := ⟨0, by simp [S]⟩
  obtain ⟨kmax, kmax_S, kmax_isMax⟩ := IsCompact.exists_isMaxOn
    (isCompact_closedBall 0 1) S_nonEmpty
    (f := fun k => (massTermReduced P k ^ 2) / (4 * quarticTermReduced P k)) <| by
    apply ContinuousOn.div₀
    · apply Continuous.continuousOn
      simp only [massTermReduced, Fin.isValue]
      fun_prop
    · apply Continuous.continuousOn
      simp only [quarticTermReduced, Fin.isValue]
      fun_prop
    · intro x hx
      specialize h x (by simpa using hx)
      linarith
  use (massTermReduced P kmax) ^ 2 / (4 * quarticTermReduced P kmax)
  apply And.intro
  · refine (le_div_iff₀ ?_).mpr ?_
    · specialize h kmax (by simpa using kmax_S)
      linarith
    · simp only [zero_mul]
      exact sq_nonneg (massTermReduced P kmax)
  · intro k hk
    apply And.intro
    · specialize h k hk
      linarith
    · intro hq
      rw [isMaxOn_iff] at kmax_isMax
      refine (div_le_iff₀' ?_).mp (kmax_isMax k (by simpa using hk))
      grind

/-!

### E.7. Showing step in hep-ph/0605184 is invalid

-/

/-- A lemma invalidating the step in https://arxiv.org/pdf/hep-ph/0605184 leading to
  equation (4.4). -/
lemma forall_reduced_exists_not_potentialIsStable :
    ∃ P, ¬ PotentialIsStable P ∧ (∀ k : EuclideanSpace ℝ (Fin 3), ‖k‖ ^ 2 ≤ 1 →
    0 ≤ quarticTermReduced P k ∧ (quarticTermReduced P k = 0 → 0 ≤ massTermReduced P k)) := by
  /- Construction of the explicit counter example.
    The reason that this counter example works is that:
    - There is a zero of the quartic term `z` on the boundary.
    - The quartic term is equal to `((k - z) · z)²`, as `k - z` approaches orthogonal to `z`,
      this becomes small on two accounts: the abs of `k - z` has to become small as `z` is on
      the boundary, and the angle between `k - z` and `z` also becomes small.
    - The mass term is of the form `-(k - z) · w` for some `w` orthogonal to `z`, so as `k - z`
      approaches orthogonal to `z`, the mass term becomes small only on the account that the abs of
      `k - z` becomes small. -/
  use .stabilityCounterExample
  apply And.intro
  /- The condition that P is not stable. -/
  · exact stabilityCounterExample_not_potentialIsStable
  /- The condition on the reduced terms. -/
  · refine fun k hk => And.intro (quarticTermReduced_stabilityCounterExample_nonneg k)
      (fun hq => ?_)
    simp [quarticTermReduced_stabilityCounterExample] at hq
    simp only [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs, Fin.sum_univ_three,
      Fin.isValue] at hk
    have hk1 : k 1 = 0 := by nlinarith
    rw [massTermReduced_stabilityCounterExample, hk1]

end TwoHiggsDoublet
