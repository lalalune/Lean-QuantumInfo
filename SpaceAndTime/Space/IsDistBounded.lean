/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import SpaceAndTime.Space.RadialAngularMeasure
import SpaceAndTime.Time.Derivatives
import Mathlib.Tactic.Cases
/-!

# Functions on `Space d` which can be made into distributions

## i. Overview

In this module, for functions `f : Space d → F`, we define the property `IsDistBounded f`.
Functions satisfying this property can be used to create distributions `Space d →d[ℝ] F`
by integrating them against Schwartz maps.

The condition `IsDistBounded f` essentially says that `f` is bounded by a finite sum of terms
of the form `c * ‖x + g‖ ^ p` for constants `c`, `g` and `- (d - 1) ≤ p ` where `d` is the dimension
of the space.

## ii. Key results

- `IsDistBounded` : The boundedness condition on functions `Space d → F` for them to
  form distributions.
- `IsDistBounded.integrable_space` : If `f` satisfies `IsDistBounded f`, then
  `fun x => η x • f x` is integrable for any Schwartz map `η : 𝓢(Space d, ℝ)`.
- `IsDistBounded.integrable_time_space` : If `f` satisfies `IsDistBounded f`, then
  `fun x => η x • f x.2` is integrable for any Schwartz map
  `η : 𝓢(Time × Space d, ℝ)`.
- `IsDistBounded.mono` : If `f₁` satisfies `IsDistBounded f₁` and
  `‖f₂ x‖ ≤ ‖f₁ x‖` for all `x`, then `f₂` satisfies `IsDistBounded f₂`.

## iii. Table of contents

- A. The predicate `IsDistBounded f`
- B. Integrability properties of functions satisfying `IsDistBounded f`
  - B.1. `AEStronglyMeasurable` conditions
  - B.2. Integrability with respect to Schwartz maps on space
  - B.3. Integrability with respect to Schwartz maps on time and space
  - B.4. Integrability with respect to inverse powers
- C. Integral on Schwartz maps is bounded by seminorms
- D. Construction rules for `IsDistBounded f`
  - D.1. Addition
  - D.2. Finite sums
  - D.3. Scalar multiplication
  - D.4. Components of functions
  - D.5. Compositions with additions and subtractions
  - D.6. Congruence with respect to the norm
  - D.7. Monotonicity with respect to the norm
  - D.8. Inner products
  - D.9. Scalar multiplication with constant
- E. Specific functions that are `IsDistBounded`
  - E.1. Constant functions
  - E.2. Powers of norms
- F. Multiplication by norms and components

## iv. References

-/
open SchwartzMap NNReal
noncomputable section

variable (𝕜 : Type) {E F F' : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F] [NormedSpace ℝ F']

namespace Space

variable [NormedSpace ℝ E]

open MeasureTheory

/-!

## A. The predicate `IsDistBounded f`

-/

/-- The boundedness condition on a function ` EuclideanSpace ℝ (Fin dm1.succ) → F`
  for it to form a distribution. -/
-- fun_prop disabled here; `IsDistBounded` is not a fun_prop class in this Mathlib version.
def IsDistBounded {d : ℕ} (f : Space d → F) : Prop :=
  AEStronglyMeasurable (fun x => f x) volume ∧
  ∃ n, ∃ c : Fin n → ℝ, ∃ g : Fin n → Space d,
    ∃ p : Fin n → ℤ,
    (∀ i, 0 ≤ c i) ∧
    (∀ i, - (d - 1 : ℕ) ≤ p i) ∧
    ∀ x, ‖f x‖ ≤ ∑ i, c i * ‖x + g i‖ ^ p i

namespace IsDistBounded

variable
  (h_aeStronglyMeasurable_schwartzMap_smul : ∀ {d : ℕ} {f : Space d → F},
    IsDistBounded f → (η : 𝓢(Space d, ℝ)) →
    AEStronglyMeasurable (fun x => η x • f x))
  (h_aeStronglyMeasurable_fderiv_schwartzMap_smul : ∀ {d : ℕ} {f : Space d → F},
    IsDistBounded f → (η : 𝓢(Space d, ℝ)) → (y : Space d) →
    AEStronglyMeasurable (fun x => fderiv ℝ η x y • f x))
  (h_aeStronglyMeasurable_inv_pow : ∀ {d r : ℕ} {f : Space d → F},
    IsDistBounded f →
    AEStronglyMeasurable (fun x => ‖((1 + ‖x‖) ^ r)⁻¹‖ • f x))
  (h_aeStronglyMeasurable_time_schwartzMap_smul : ∀ {d : ℕ} {f : Space d → F},
    IsDistBounded f → (η : 𝓢(Time × Space d, ℝ)) →
    AEStronglyMeasurable (fun x => η x • f x.2))
  (h_integrable_space : ∀ {d : ℕ} {f : Space d → F},
    IsDistBounded f → (η : 𝓢(Space d, ℝ)) →
    Integrable (fun x : Space d => η x • f x) volume)
  (h_integrable_space_fderiv : ∀ {d : ℕ} {f : Space d → F},
    IsDistBounded f → (η : 𝓢(Space d, ℝ)) → (y : Space d) →
    Integrable (fun x : Space d => fderiv ℝ η x y • f x) volume)
  (h_integrable_space_fderiv_mul : ∀ {d : ℕ} {f : Space d → ℝ},
    IsDistBounded f → (η : 𝓢(Space d, ℝ)) → (y : Space d) →
    Integrable (fun x : Space d => fderiv ℝ η x y * f x) volume)
  (h_hasTemperateGrowth_prod :
    ∀ {D1 : Type} [NormedAddCommGroup D1] [MeasurableSpace D1]
      {D2 : Type} [NormedAddCommGroup D2] [MeasurableSpace D2]
      (μ1 : Measure D1) (μ2 : Measure D2)
      [Measure.HasTemperateGrowth μ1] [Measure.HasTemperateGrowth μ2]
      [OpensMeasurableSpace (D1 × D2)],
      Measure.HasTemperateGrowth (μ1.prod μ2))
  (h_integrable_time_space : ∀ {d : ℕ} {f : Space d → F},
    IsDistBounded f → (η : 𝓢(Time × Space d, ℝ)) →
    Integrable (fun x : Time × Space d => η x • f x.2) volume)
  (h_integrable_mul_inv_pow : ∀ {d : ℕ} {f : Space d → F},
    IsDistBounded f → ∃ r, Integrable (fun x => ‖((1 + ‖x‖) ^ r)⁻¹‖ • f x) volume)
  (h_integral_mul_schwartzMap_bounded : ∀ {d : ℕ} {f : Space d → F},
    IsDistBounded f →
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ),
      0 ≤ C ∧ ∀ (η : 𝓢(Space d, ℝ)),
      ‖∫ (x : Space d), η x • f x‖ ≤ C * (s.sup (schwartzSeminormFamily ℝ (Space d) ℝ)) η)


/-!

## B. Integrability properties of functions satisfying `IsDistBounded f`

-/

/-!

### B.1. `AEStronglyMeasurable` conditions

-/
omit [NormedSpace ℝ F] in
lemma aestronglyMeasurable {d : ℕ} {f : Space d → F} (hf : IsDistBounded f) :
    AEStronglyMeasurable (fun x => f x) volume := hf.1

lemma aeStronglyMeasurable_schwartzMap_smul {d : ℕ} {f : Space d → F}
    (hf : IsDistBounded f) (η : 𝓢(Space d, ℝ)) :
    AEStronglyMeasurable (fun x => η x • f x) := by
  exact h_aeStronglyMeasurable_schwartzMap_smul hf η
lemma aeStronglyMeasurable_fderiv_schwartzMap_smul {d : ℕ} {f : Space d → F}
    (hf : IsDistBounded f) (η : 𝓢(Space d, ℝ)) (y : Space d) :
    AEStronglyMeasurable (fun x => fderiv ℝ η x y • f x) := by
  exact h_aeStronglyMeasurable_fderiv_schwartzMap_smul hf η y
lemma aeStronglyMeasurable_inv_pow {d r : ℕ} {f : Space d → F}
    (hf : IsDistBounded f) :
    AEStronglyMeasurable (fun x => ‖((1 + ‖x‖) ^ r)⁻¹‖ • f x) := by
  exact h_aeStronglyMeasurable_inv_pow hf

lemma aeStronglyMeasurable_time_schwartzMap_smul {d : ℕ} {f : Space d → F}
    (hf : IsDistBounded f) (η : 𝓢(Time × Space d, ℝ)) :
    AEStronglyMeasurable (fun x => η x • f x.2) :=
  h_aeStronglyMeasurable_time_schwartzMap_smul hf η

/-!

### B.2. Integrability with respect to Schwartz maps on space

-/

lemma integrable_space {d : ℕ} {f : Space d → F} (hf : IsDistBounded f)
    (η : 𝓢(Space d, ℝ)) :
    Integrable (fun x : Space d => η x • f x) volume :=
  h_integrable_space hf η

lemma integrable_space_mul {d : ℕ} {f : Space d → ℝ} (hf : IsDistBounded f)
    (η : 𝓢(Space d, ℝ)) :
    Integrable (fun x : Space d => η x * f x) volume := by
  exact hf.integrable_space η

lemma integrable_space_fderiv {d : ℕ} {f : Space d → F} (hf : IsDistBounded f)
    (η : 𝓢(Space d, ℝ)) (y : Space d) :
    Integrable (fun x : Space d => fderiv ℝ η x y • f x) volume :=
  h_integrable_space_fderiv hf η y
lemma integrable_space_fderiv_mul {d : ℕ} {f : Space d → ℝ} (hf : IsDistBounded f)
    (η : 𝓢(Space d, ℝ)) (y : Space d) :
    Integrable (fun x : Space d => fderiv ℝ η x y * f x) volume :=
  h_integrable_space_fderiv_mul hf η y
/-!

### B.3. Integrability with respect to Schwartz maps on time and space

-/

instance {D1 : Type} [NormedAddCommGroup D1] [MeasurableSpace D1]
    {D2 : Type} [NormedAddCommGroup D2] [MeasurableSpace D2]
    (μ1 : Measure D1) (μ2 : Measure D2)
    [Measure.HasTemperateGrowth μ1] [Measure.HasTemperateGrowth μ2]
    [OpensMeasurableSpace (D1 × D2)] :
    Measure.HasTemperateGrowth (μ1.prod μ2) := by
  exact h_hasTemperateGrowth_prod μ1 μ2

lemma integrable_time_space {d : ℕ} {f : Space d → F} (hf : IsDistBounded f)
    (η : 𝓢(Time × Space d, ℝ)) :
    Integrable (fun x : Time × Space d => η x • f x.2) volume :=
  h_integrable_time_space hf η

/-!

### B.4. Integrability with respect to inverse powers

-/

lemma integrable_mul_inv_pow {d : ℕ}
    {f : Space d → F} (hf : IsDistBounded f) :
    ∃ r, Integrable (fun x => ‖((1 + ‖x‖) ^ r)⁻¹‖ • f x) volume :=
  h_integrable_mul_inv_pow hf
lemma integral_mul_schwartzMap_bounded {d : ℕ} {f : Space d → F} (hf : IsDistBounded f) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ),
    0 ≤ C ∧ ∀ (η : 𝓢(Space d, ℝ)),
    ‖∫ (x : Space d), η x • f x‖ ≤ C * (s.sup (schwartzSeminormFamily ℝ (Space d) ℝ)) η :=
  h_integral_mul_schwartzMap_bounded hf

/-!

## D. Construction rules for `IsDistBounded f`

-/

section constructors

variable (𝕜 : Type) {E F F' : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
  [NormedAddCommGroup F'] [NormedSpace ℝ F']

open InnerProductSpace

variable
  (h_pi_comp : ∀ {d n : ℕ}
    {f : Space d → EuclideanSpace ℝ (Fin n)},
    IsDistBounded f → (j : Fin n) → IsDistBounded (fun x => f x j))
  (h_vector_component : ∀ {d n : ℕ} {f : Space d → Lorentz.Vector n},
    IsDistBounded f → (j : Fin 1 ⊕ Fin n) → IsDistBounded (fun x => f x j))
  (h_comp_add_right : ∀ {d : ℕ} {f : Space d → F},
    IsDistBounded f → (c : Space d) → IsDistBounded (fun x => f (x + c)))
  (h_inner_left : ∀ {d n : ℕ}
    {f : Space d → EuclideanSpace ℝ (Fin n)},
    IsDistBounded f → (y : EuclideanSpace ℝ (Fin n)) →
    IsDistBounded (fun x => ⟪f x, y⟫_ℝ))
  (h_smul_const : ∀ {d : ℕ} [NormedSpace ℝ F] {c : Space d → ℝ},
    IsDistBounded c → (f : F) → IsDistBounded (fun x => c x • f))
  (h_const : ∀ {d : ℕ}, (f : F) → IsDistBounded (d := d) (fun _ : Space d => f))
  (h_pow : ∀ {d : ℕ}, (n : ℤ) → (- (d - 1 : ℕ) ≤ n) →
    IsDistBounded (d := d) (fun x => ‖x‖ ^ n))
  (h_pow_shift : ∀ {d : ℕ}, (n : ℤ) → (g : Space d) → (- (d - 1 : ℕ) ≤ n) →
    IsDistBounded (d := d) (fun x => ‖x - g‖ ^ n))
  (h_norm_add_nat_pow : ∀ {d : ℕ}, (n : ℕ) → (a : ℝ) →
    IsDistBounded (d := d) (fun x => (‖x‖ + a) ^ n))
  (h_norm_add_pos_nat_zpow : ∀ {d : ℕ}, (n : ℤ) → (a : ℝ) → (ha : 0 < a) →
    IsDistBounded (d := d) (fun x => (‖x‖ + a) ^ n))
  (h_log_norm : ∀ {d : ℕ},
    IsDistBounded (d := d.succ.succ) (fun x => Real.log ‖x‖))
  (h_zpow_smul_self : ∀ {d : ℕ}, (n : ℤ) → (- (d - 1 : ℕ) - 1 ≤ n) →
    IsDistBounded (d := d) (fun x => ‖x‖ ^ n • x))
  (h_zpow_smul_repr_self : ∀ {d : ℕ}, (n : ℤ) → (- (d - 1 : ℕ) - 1 ≤ n) →
    IsDistBounded (d := d) (fun x => ‖x‖ ^ n • basis.repr x))
  (h_norm_smul_nat_pow : ∀ {d : ℕ}, (p : ℕ) → (c : Space d) →
    IsDistBounded (fun x => ‖x‖ * ‖x + c‖ ^ p))
  (h_norm_smul_zpow : ∀ {d : ℕ}, (p : ℤ) → (c : Space d) → (- (d - 1 : ℕ) ≤ p) →
    IsDistBounded (fun x => ‖x‖ * ‖x + c‖ ^ p))
  (h_norm_smul_isDistBounded : ∀ {d : ℕ} [NormedSpace ℝ F] {f : Space d → F},
    IsDistBounded f → IsDistBounded (fun x => ‖x‖ • f x))
  (h_component_smul_isDistBounded : ∀ {d : ℕ} [NormedSpace ℝ F] {f : Space d → F},
    IsDistBounded f → (i : Fin d) → IsDistBounded (fun x => x i • f x))
  (h_isDistBounded_smul_self : ∀ {d : ℕ} {f : Space d → ℝ},
    IsDistBounded f → IsDistBounded (fun x => f x • x))
  (h_isDistBounded_smul_self_repr : ∀ {d : ℕ} {f : Space d → ℝ},
    IsDistBounded f → IsDistBounded (fun x => f x • basis.repr x))
  (h_isDistBounded_smul_inner : ∀ {d : ℕ} [NormedSpace ℝ F] {f : Space d → F},
    IsDistBounded f → (y : Space d) → IsDistBounded (fun x => ⟪y, x⟫_ℝ • f x))
  (h_isDistBounded_smul_inner_of_smul_norm :
    ∀ {d : ℕ} [NormedSpace ℝ F] {f : Space d → F},
      IsDistBounded (fun x => ‖x‖ • f x) →
      AEStronglyMeasurable f →
      (y : Space d) →
      IsDistBounded (fun x => ⟪y, x⟫_ℝ • f x))
  (h_mul_inner_pow_neg_two : ∀ {d : ℕ} (y : Space d.succ.succ),
    IsDistBounded (fun x => ⟪y, x⟫_ℝ * ‖x‖ ^ (- 2 : ℤ)))


lemma zero {d} : IsDistBounded (0 : Space d → F) := by
  exact ⟨aestronglyMeasurable_const, 1, fun _ => 0, fun _ => 0, fun _ => 0, by simp, by simp, by simp⟩

/-!

### D.1. Addition

-/
lemma add {d : ℕ} {f g : Space d → F}
    (hf : IsDistBounded f) (hg : IsDistBounded g) : IsDistBounded (f + g) := by
  apply And.intro
  · exact hf.1.add hg.1
  rcases hf with ⟨hae1, ⟨n1, c1, g1, p1, c1_nonneg, p1_bound, bound1⟩⟩
  rcases hg with ⟨hae2, ⟨n2, c2, g2, p2, c2_nonneg, p2_bound, bound2⟩⟩
  refine ⟨n1 + n2, Fin.append c1 c2, Fin.append g1 g2, Fin.append p1 p2, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    match i with
    | .inl i =>
      simp only [finSumFinEquiv_apply_left, Fin.append_left, ge_iff_le]
      exact c1_nonneg i
    | .inr i =>
      simp only [finSumFinEquiv_apply_right, Fin.append_right, ge_iff_le]
      exact c2_nonneg i
  · intro i
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    match i with
    | .inl i =>
      simp only [finSumFinEquiv_apply_left, Fin.append_left, ge_iff_le]
      exact p1_bound i
    | .inr i =>
      simp only [finSumFinEquiv_apply_right, Fin.append_right, ge_iff_le]
      exact p2_bound i
  · intro x
    apply (norm_add_le _ _).trans
    apply (add_le_add (bound1 x) (bound2 x)).trans
    apply le_of_eq
    rw [← finSumFinEquiv.sum_comp]
    simp

lemma fun_add {d : ℕ} {f g : Space d → F}
    (hf : IsDistBounded f) (hg : IsDistBounded g) : IsDistBounded (fun x => f x + g x) := by
  exact hf.add hg

/-!

### D.2. Finite sums

-/

lemma sum {ι : Type*} {s : Finset ι} {d : ℕ} {f : ι → Space d → F}
    (hf : ∀ i ∈ s, IsDistBounded (f i)) : IsDistBounded (∑ i ∈ s, f i) := by
  classical
  induction' s using Finset.induction with i s hi ih
  · simp
    exact IsDistBounded.zero
  · rw [Finset.sum_insert hi]
    apply IsDistBounded.add
    · exact hf i (s.mem_insert_self i)
    · exact ih (fun j hj => hf j (s.mem_insert_of_mem hj))

lemma sum_fun {ι : Type*} {s : Finset ι} {d : ℕ} {f : ι → Space d → F}
    (hf : ∀ i ∈ s, IsDistBounded (f i)) : IsDistBounded (fun x => ∑ i ∈ s, f i x) := by
  convert sum hf using 1
  funext x
  simp

/-!

### D.3. Scalar multiplication

-/

lemma const_smul {d : ℕ} [NormedSpace ℝ F] {f : Space d → F}
    (hf : IsDistBounded f) (c : ℝ) : IsDistBounded (c • f) := by
  rcases hf with ⟨hae1, ⟨n1, c1, g1, p1, c1_nonneg, p1_bound, bound1⟩⟩
  apply And.intro
  · exact hae1.const_smul c
  refine ⟨n1, ‖c‖ • c1, g1, p1, ?_, p1_bound, ?_⟩
  · intro i
    simp only [Real.norm_eq_abs, Pi.smul_apply, smul_eq_mul]
    have hi := c1_nonneg i
    positivity
  · intro x
    simp [norm_smul]
    conv_rhs => enter [2, x]; rw [mul_assoc]
    rw [← Finset.mul_sum]
    refine mul_le_mul (by rfl) (bound1 x) ?_ ?_
    · exact norm_nonneg (f x)
    · exact abs_nonneg c

lemma neg {d : ℕ} [NormedSpace ℝ F] {f : Space d → F}
    (hf : IsDistBounded f) : IsDistBounded (fun x => - f x) := by
  convert hf.const_smul (-1) using 1
  funext x
  simp

lemma const_fun_smul {d : ℕ} [NormedSpace ℝ F] {f : Space d → F}
    (hf : IsDistBounded f) (c : ℝ) : IsDistBounded (fun x => c • f x) := by
  convert hf.const_smul c using 1

lemma const_mul_fun {d : ℕ}
    {f : Space d → ℝ}
    (hf : IsDistBounded f) (c : ℝ) : IsDistBounded (fun x => c * f x) := by
  convert hf.const_smul c using 1

lemma mul_const_fun {d : ℕ}
    {f : Space d → ℝ}
    (hf : IsDistBounded f) (c : ℝ) : IsDistBounded (fun x => f x * c) := by
  convert hf.const_smul c using 2
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-!

### D.4. Components of functions

-/

lemma pi_comp {d n : ℕ}
    {f : Space d → EuclideanSpace ℝ (Fin n)}
    (hf : IsDistBounded f) (j : Fin n) : IsDistBounded (fun x => f x j) :=
  h_pi_comp hf j

lemma vector_component {d n : ℕ} {f : Space d → Lorentz.Vector n}
    (hf : IsDistBounded f) (j : Fin 1 ⊕ Fin n) : IsDistBounded (fun x => f x j) :=
  h_vector_component hf j

/-!

### D.5. Compositions with additions and subtractions

-/

lemma comp_add_right {d : ℕ} {f : Space d → F}
    (hf : IsDistBounded f) (c : Space d) :
    IsDistBounded (fun x => f (x + c)) :=
  h_comp_add_right hf c

lemma comp_sub_right {d : ℕ} {f : Space d → F}
    (hf : IsDistBounded f) (c : Space d) :
    IsDistBounded (fun x => f (x - c)) := by
  convert hf.comp_add_right (- c) using 1

/-!

### D.6. Congruence with respect to the norm

-/

omit [NormedSpace ℝ F'] in
lemma congr {d : ℕ} {f : Space d → F}
    {g : Space d → F'}
    (hf : IsDistBounded f) (hae : AEStronglyMeasurable g) (hfg : ∀ x, ‖g x‖ = ‖f x‖) :
      IsDistBounded g := by
  rcases hf with ⟨hae1, ⟨n1, c1, g1, p1, c1_nonneg, p1_bound, bound1⟩⟩
  apply And.intro
  · exact hae
  refine ⟨n1, c1, g1, p1, c1_nonneg, p1_bound, ?_⟩
  intro x
  rw [hfg x]
  exact bound1 x

/-!

### D.7. Monotonicity with respect to the norm

-/

omit [NormedSpace ℝ F'] in
lemma mono {d : ℕ} {f : Space d → F}
    {g : Space d → F'}
    (hf : IsDistBounded f) (hae : AEStronglyMeasurable g)
    (hfg : ∀ x, ‖g x‖ ≤ ‖f x‖) : IsDistBounded g := by
  rcases hf with ⟨hae1, ⟨n1, c1, g1, p1, c1_nonneg, p1_bound, bound1⟩⟩
  apply And.intro
  · exact hae
  refine ⟨n1, c1, g1, p1, c1_nonneg, p1_bound, ?_⟩
  intro x
  exact (hfg x).trans (bound1 x)

/-!

### D.8. Inner products

-/

lemma inner_left {d n : ℕ}
    {f : Space d → EuclideanSpace ℝ (Fin n) }
    (hf : IsDistBounded f) (y : EuclideanSpace ℝ (Fin n)) :
    IsDistBounded (fun x => ⟪f x, y⟫_ℝ) :=
  h_inner_left hf y

/-!

### D.9. Scalar multiplication with constant
-/

lemma smul_const {d : ℕ} [NormedSpace ℝ F] {c : Space d → ℝ}
    (hc : IsDistBounded c) (f : F) : IsDistBounded (fun x => c x • f) :=
  h_smul_const hc f
/-!

## E. Specific functions that are `IsDistBounded`

-/

/-!

### E.1. Constant functions

-/

lemma const {d : ℕ} (f : F) :
    IsDistBounded (d := d) (fun _ : Space d => f) :=
  h_const f

/-!

### E.2. Powers of norms

-/

lemma pow {d : ℕ} (n : ℤ) (hn : - (d - 1 : ℕ) ≤ n) :
    IsDistBounded (d := d) (fun x => ‖x‖ ^ n) :=
  h_pow n hn

lemma pow_shift {d : ℕ} (n : ℤ)
    (g : Space d) (hn : - (d - 1 : ℕ) ≤ n) :
    IsDistBounded (d := d) (fun x => ‖x - g‖ ^ n) :=
  h_pow_shift n g hn

lemma inv_shift {d : ℕ}
    (g : Space d.succ.succ) :
    IsDistBounded (d := d.succ.succ) (fun x => ‖x - g‖⁻¹) := by
  convert IsDistBounded.pow_shift (d := d.succ.succ) (-1) g (by simp) using 1
  ext1 x
  simp
lemma nat_pow {d : ℕ} (n : ℕ) :
    IsDistBounded (d := d) (fun x => ‖x‖ ^ n) := by
  exact IsDistBounded.pow (d := d) (n : ℤ) (by omega)

lemma norm_add_nat_pow {d : ℕ} (n : ℕ) (a : ℝ) :
    IsDistBounded (d := d) (fun x => (‖x‖ + a) ^ n) :=
  h_norm_add_nat_pow n a
lemma norm_add_pos_nat_zpow {d : ℕ} (n : ℤ) (a : ℝ) (ha : 0 < a) :
    IsDistBounded (d := d) (fun x => (‖x‖ + a) ^ n) :=
  h_norm_add_pos_nat_zpow n a ha

lemma nat_pow_shift {d : ℕ} (n : ℕ)
    (g : Space d) :
    IsDistBounded (d := d) (fun x => ‖x - g‖ ^ n) := by
  exact IsDistBounded.pow_shift (d := d) (n : ℤ) g (by omega)

lemma norm_sub {d : ℕ} (g : Space d) :
    IsDistBounded (d := d) (fun x => ‖x - g‖) := by
  convert IsDistBounded.nat_pow_shift (d := d) 1 g using 1
  ext1 x
  simp

lemma norm_add {d : ℕ} (g : Space d) :
    IsDistBounded (d := d) (fun x => ‖x + g‖) := by
  convert IsDistBounded.nat_pow_shift (d := d) 1 (- g) using 1
  ext1 x
  simp

lemma inv {n : ℕ} :
    IsDistBounded (d := n.succ.succ) (fun x => ‖x‖⁻¹) := by
  convert IsDistBounded.pow (d := n.succ.succ) (-1) (by simp) using 1
  ext1 x
  simp

lemma norm {d : ℕ} : IsDistBounded (d := d) (fun x => ‖x‖) := by
  convert IsDistBounded.nat_pow (d := d) 1 using 1
  ext1 x
  simp

lemma log_norm {d : ℕ} :
    IsDistBounded (d := d.succ.succ) (fun x => Real.log ‖x‖) :=
  h_log_norm

lemma zpow_smul_self {d : ℕ} (n : ℤ) (hn : - (d - 1 : ℕ) - 1 ≤ n) :
    IsDistBounded (d := d) (fun x => ‖x‖ ^ n • x) :=
  h_zpow_smul_self n hn

lemma zpow_smul_repr_self {d : ℕ} (n : ℤ) (hn : - (d - 1 : ℕ) - 1 ≤ n) :
    IsDistBounded (d := d) (fun x => ‖x‖ ^ n • basis.repr x) :=
  h_zpow_smul_repr_self n hn

lemma zpow_smul_repr_self_sub {d : ℕ} (n : ℤ) (hn : - (d - 1 : ℕ) - 1 ≤ n)
    (y : Space d) :
    IsDistBounded (d := d) (fun x => ‖x - y‖ ^ n • basis.repr (x - y)) := by
  apply (zpow_smul_repr_self n hn).comp_sub_right y

lemma inv_pow_smul_self {d : ℕ} (n : ℕ) (hn : - (d - 1 : ℕ) - 1 ≤ (- n : ℤ)) :
    IsDistBounded (d := d) (fun x => ‖x‖⁻¹ ^ n • x) := by
  convert zpow_smul_self (n := - (n : ℤ)) (by omega) using 1
  funext x
  simp

lemma inv_pow_smul_repr_self {d : ℕ} (n : ℕ) (hn : - (d - 1 : ℕ) - 1 ≤ (- n : ℤ)) :
    IsDistBounded (d := d) (fun x => ‖x‖⁻¹ ^ n • basis.repr x) := by
  convert zpow_smul_repr_self (n := - (n : ℤ)) (by omega) using 1
  funext x
  simp

/-!

## F. Multiplication by norms and components

-/

lemma norm_smul_nat_pow {d} (p : ℕ) (c : Space d) :
    IsDistBounded (fun x => ‖x‖ * ‖x + c‖ ^ p) :=
  h_norm_smul_nat_pow p c

lemma norm_smul_zpow {d} (p : ℤ) (c : Space d) (hn : - (d - 1 : ℕ) ≤ p) :
    IsDistBounded (fun x => ‖x‖ * ‖x + c‖ ^ p) :=
  h_norm_smul_zpow p c hn

lemma norm_smul_isDistBounded {d : ℕ} [NormedSpace ℝ F] {f : Space d → F}
    (hf : IsDistBounded f) :
    IsDistBounded (fun x => ‖x‖ • f x) :=
  h_norm_smul_isDistBounded hf

lemma norm_mul_isDistBounded {d : ℕ} {f : Space d → ℝ}
    (hf : IsDistBounded f) :
    IsDistBounded (fun x => ‖x‖ * f x) := by
  convert hf.norm_smul_isDistBounded using 1

lemma component_smul_isDistBounded {d : ℕ} [NormedSpace ℝ F] {f : Space d → F}
    (hf : IsDistBounded f) (i : Fin d) :
    IsDistBounded (fun x => x i • f x) :=
  h_component_smul_isDistBounded hf i

lemma component_mul_isDistBounded {d : ℕ} {f : Space d → ℝ}
    (hf : IsDistBounded f) (i : Fin d) :
    IsDistBounded (fun x => x i * f x) := by
  convert hf.component_smul_isDistBounded i using 2

lemma isDistBounded_smul_self {d : ℕ} {f : Space d → ℝ}
    (hf : IsDistBounded f) : IsDistBounded (fun x => f x • x) :=
  h_isDistBounded_smul_self hf

lemma isDistBounded_smul_self_repr {d : ℕ} {f : Space d → ℝ}
    (hf : IsDistBounded f) : IsDistBounded (fun x => f x • basis.repr x) :=
  h_isDistBounded_smul_self_repr hf

lemma isDistBounded_smul_inner {d : ℕ} [NormedSpace ℝ F] {f : Space d → F}
    (hf : IsDistBounded f) (y : Space d) : IsDistBounded (fun x => ⟪y, x⟫_ℝ • f x) :=
  h_isDistBounded_smul_inner hf y

lemma isDistBounded_smul_inner_of_smul_norm {d : ℕ} [NormedSpace ℝ F] {f : Space d → F}
    (hf : IsDistBounded (fun x => ‖x‖ • f x)) (hae : AEStronglyMeasurable f) (y : Space d) :
    IsDistBounded (fun x => ⟪y, x⟫_ℝ • f x) :=
  h_isDistBounded_smul_inner_of_smul_norm hf hae y

lemma isDistBounded_mul_inner {d : ℕ} {f : Space d → ℝ}
    (hf : IsDistBounded f) (y : Space d) : IsDistBounded (fun x => ⟪y, x⟫_ℝ * f x) := by
  convert hf.isDistBounded_smul_inner y using 2

lemma isDistBounded_mul_inner' {d : ℕ} {f : Space d → ℝ}
    (hf : IsDistBounded f) (y : Space d) : IsDistBounded (fun x => ⟪x, y⟫_ℝ * f x) := by
  convert hf.isDistBounded_smul_inner y using 2
  rw [real_inner_comm]
  simp

lemma isDistBounded_mul_inner_of_smul_norm {d : ℕ} {f : Space d → ℝ}
    (hf : IsDistBounded (fun x => ‖x‖ * f x)) (hae : AEStronglyMeasurable f) (y : Space d) :
    IsDistBounded (fun x => ⟪y, x⟫_ℝ * f x) := by
  convert hf.isDistBounded_smul_inner_of_smul_norm hae y using 2

lemma mul_inner_pow_neg_two {d : ℕ}
    (y : Space d.succ.succ) :
    IsDistBounded (fun x => ⟪y, x⟫_ℝ * ‖x‖ ^ (- 2 : ℤ)) := by
  constructor
  · apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · exact continuous_inner.comp (continuous_const.prodMk continuous_id)
    · exact continuous_norm.zpow₀ (-2) (fun x hx => by left; exact hx)
  · refine ⟨1, fun _ => ‖y‖, fun _ => 0, fun _ => (-1 : ℤ), ?_, ?_, ?_⟩
    · intro i; exact norm_nonneg y
    · intro i
      simp only [Fin.isValue, ge_iff_le, neg_le_iff_add_nonneg]
      omega
    · intro x; simp
      by_cases hx : (x : Space d.succ.succ) = 0
      · simp [hx]
      · have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
        rw [Real.norm_eq_abs]
        rw [abs_mul, abs_of_nonneg (zpow_nonneg (norm_nonneg x) _)]
        have hzpow : ‖x‖ ^ (-2 : ℤ) = (‖x‖ ^ 2)⁻¹ := by
          rw [zpow_neg, zpow_ofNat]
        rw [hzpow]
        have hstep : ‖x‖ * (‖x‖ ^ 2)⁻¹ = ‖x‖⁻¹ := by field_simp
        calc |⟪y, x⟫_ℝ| * (‖x‖ ^ 2)⁻¹
            ≤ ‖y‖ * ‖x‖ * (‖x‖ ^ 2)⁻¹ := by
              apply mul_le_mul_of_nonneg_right (abs_real_inner_le_norm y x)
              positivity
          _ = ‖y‖ * (‖x‖ * (‖x‖ ^ 2)⁻¹) := by ring
          _ = ‖y‖ * ‖x‖⁻¹ := by rw [hstep]

end constructors
end IsDistBounded
