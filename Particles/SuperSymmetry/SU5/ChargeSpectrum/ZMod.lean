/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.ZMod.Defs
import Particles.SuperSymmetry.SU5.ChargeSpectrum.Yukawa
import Particles.SuperSymmetry.SU5.ChargeSpectrum.Completions
import Particles.SuperSymmetry.SU5.ChargeSpectrum.PhenoClosed
import Meta.Linters.Sorry
/-!

# Charge spectra with values in `ZMod n`

## i. Overview

The way that we have defined `ChargeSpectrum` means we can consider values
of charges which are not only elements of `ℤ`, but also elements of other types.

In this file we will consider `ChargeSpectrum` which have values in `ZMod n` for various
natural numbers `n`, as well as charge spectra with values in `ZMod n × ZMod m`.

In this file we focus on 4-insertions of singlets to be phenomenologically viable.
In other files we usually just consider one.

## ii. Key results

- `ZModCharges n` : The finite set of `ZMod n` valued charges which are complete,
  not pheno-constrained and don't regenerate dangerous couplings
  with the Yukawa term up-to 4-inserstions of singlets.
- `ZModZModCharges m n` : The finite set of `ZMod n × ZMod m` valued charges which are complete,
  not pheno-constrained and don't regenerate dangerous couplings
  with the Yukawa term up-to 4-inserstions of singlets.

## iii. Table of contents

- A. The finite set of viable `ZMod n` charge spectra
  - A.1. General construction
  - A.2. Finite set of viable `ZMod 1` charge spectra is empty
  - A.3. Finite set of viable `ZMod 2` charge spectra is empty
  - A.4. Finite set of viable `ZMod 3` charge spectra is empty
  - A.5. Finite set of viable `ZMod 4` has four elements
  - A.6. Finite set of viable `ZMod 5` charge spectra is empty
  - A.7. Finite set of viable `ZMod 6` charge spectra is non-empty
- B. The finite set of viable `ZMod n × ZMod m` charge spectra
  - B.1. General construction

## iv. References

There are no known references for the material in this module.

-/

namespace SuperSymmetry

namespace SU5
namespace ChargeSpectrum

/-!

## A. The finite set of viable `ZMod n` charge spectra

-/

/-!

### A.1. General construction

-/

/-- The finite set of `ZMod n` valued charges which are complete,
  not pheno-constrained and don't regenerate dangerous couplings
  with the Yukawa term up-to 4-inserstions of singlets. -/
def ZModCharges (n : ℕ) [NeZero n] : Finset (ChargeSpectrum (ZMod n)) :=
  let S : Finset (ChargeSpectrum (ZMod n)) := ofFinset Finset.univ Finset.univ
  S.filter (fun x => IsComplete x ∧ ¬ x.IsPhenoConstrained ∧ ¬ x.YukawaGeneratesDangerousAtLevel 4)

/-!

### A.2. Finite set of viable `ZMod 1` charge spectra is empty

-/

/-- This lemma corresponds to the statement that there are no choices of `ℤ₁` representations
  which give a phenomenologically viable theory. -/
lemma ZModCharges_one_eq : ZModCharges 1 = ∅:= by decide

/-!

### A.3. Finite set of viable `ZMod 2` charge spectra is empty

-/

set_option maxRecDepth 2000 in
/-- This lemma corresponds to the statement that there are no choices of `ℤ₂` representations
  which give a phenomenologically viable theory. -/
lemma ZModCharges_two_eq : ZModCharges 2 = ∅ := by decide

/-!

### A.4. Finite set of viable `ZMod 3` charge spectra is empty

-/

/-- This lemma corresponds to the statement that there are no choices of `ℤ₃` representations
  which give a phenomenologically viable theory. -/
lemma ZModCharges_three_eq : ZModCharges 3 = ∅ := by decide +kernel

/-!

### A.5. Finite set of viable `ZMod 4` has four elements

-/

lemma ZModCharges_four_eq : ZModCharges 4 = {⟨some 0, some 2, {1}, {3}⟩,
    ⟨some 0, some 2, {3}, {1}⟩, ⟨some 1, some 2, {0}, {3}⟩, ⟨some 3, some 2, {0}, {1}⟩} := by
  decide +kernel

/-!

### A.6. Finite set of viable `ZMod 5` charge spectra is empty

-/

/-- This lemma corresponds to the statement that there are no choices of `ℤ₅` representations
  which give a phenomenologically viable theory. -/
lemma ZModCharges_five_eq : ZModCharges 5 = ∅ := by decide +kernel

/-!

### A.7. Finite set of viable `ZMod 6` charge spectra is non-empty

-/

private def zmod6SingletonEmbedding :
    ((ZMod 6 × ZMod 6) × (ZMod 6 × ZMod 6)) ↪ ChargeSpectrum (ZMod 6) where
  toFun x := ⟨some x.1.1, some x.1.2, {x.2.1}, {x.2.2}⟩
  inj' := by
    rintro ⟨⟨qHd, qHu⟩, ⟨q5, q10⟩⟩ ⟨⟨qHd', qHu'⟩, ⟨q5', q10'⟩⟩ h
    simp [ChargeSpectrum.eq_iff] at h
    simp [h]

private def zmod6SingletonCharges : Finset (ChargeSpectrum (ZMod 6)) :=
  (Finset.univ : Finset ((ZMod 6 × ZMod 6) × (ZMod 6 × ZMod 6))).map
    zmod6SingletonEmbedding

private lemma zmod6_singleton_topYukawa_of_good :
    ∀ x ∈ zmod6SingletonCharges,
      ¬ x.IsPhenoConstrained → ¬ x.YukawaGeneratesDangerousAtLevel 4 →
        x.AllowsTerm .topYukawa := by
  decide +kernel

private lemma zmod6_topYukawa_of_good {x : ChargeSpectrum (ZMod 6)}
    (hComplete : x.IsComplete) (hPheno : ¬ x.IsPhenoConstrained)
    (hYukawa : ¬ x.YukawaGeneratesDangerousAtLevel 4) :
    x.AllowsTerm .topYukawa := by
  obtain ⟨qHd, hqHd⟩ := Option.isSome_iff_exists.mp hComplete.1
  obtain ⟨qHu, hqHu⟩ := Option.isSome_iff_exists.mp hComplete.2.1
  obtain ⟨q5, hq5⟩ := Finset.nonempty_iff_ne_empty.mpr hComplete.2.2.1
  obtain ⟨q10, hq10⟩ := Finset.nonempty_iff_ne_empty.mpr hComplete.2.2.2
  let y : ChargeSpectrum (ZMod 6) := ⟨some qHd, some qHu, {q5}, {q10}⟩
  have hyMem : y ∈ zmod6SingletonCharges := by
    simp [zmod6SingletonCharges, zmod6SingletonEmbedding, y]
  have hySubset : y ⊆ x := by
    simp [subset_def, y, hqHd, hqHu, hq5, hq10]
  have hyPheno : ¬ y.IsPhenoConstrained := fun hy =>
    hPheno (isPhenoConstrained_mono hySubset hy)
  have hyYukawa : ¬ y.YukawaGeneratesDangerousAtLevel 4 := fun hy =>
    hYukawa (yukawaGeneratesDangerousAtLevel_of_subset hySubset hy)
  exact allowsTerm_mono hySubset (zmod6_singleton_topYukawa_of_good y hyMem hyPheno hyYukawa)

private def zmod6TopYukawaLevelOneCharges : Finset (ChargeSpectrum (ZMod 6)) :=
  {⟨some 0, some 2, {1}, {1}⟩,
    ⟨some 0, some 2, {5}, {1}⟩,
    ⟨some 0, some 4, {1}, {5}⟩,
    ⟨some 0, some 4, {5}, {5}⟩,
    ⟨some 1, some 0, {2}, {3}⟩,
    ⟨some 1, some 0, {4}, {3}⟩,
    ⟨some 1, some 2, {0}, {1}⟩,
    ⟨some 1, some 2, {4}, {1}⟩,
    ⟨some 1, some 2, {5}, {1}⟩,
    ⟨some 1, some 2, {5}, {4}⟩,
    ⟨some 1, some 4, {0}, {5}⟩,
    ⟨some 1, some 4, {2}, {5}⟩,
    ⟨some 1, some 4, {3}, {2}⟩,
    ⟨some 1, some 4, {5}, {5}⟩,
    ⟨some 2, some 0, {1}, {3}⟩,
    ⟨some 2, some 0, {5}, {3}⟩,
    ⟨some 2, some 4, {1}, {2}⟩,
    ⟨some 2, some 4, {1}, {5}⟩,
    ⟨some 2, some 4, {3}, {2}⟩,
    ⟨some 2, some 4, {5}, {5}⟩,
    ⟨some 3, some 2, {5}, {4}⟩,
    ⟨some 3, some 4, {1}, {2}⟩,
    ⟨some 4, some 0, {1}, {3}⟩,
    ⟨some 4, some 0, {5}, {3}⟩,
    ⟨some 4, some 2, {1}, {1}⟩,
    ⟨some 4, some 2, {3}, {4}⟩,
    ⟨some 4, some 2, {5}, {1}⟩,
    ⟨some 4, some 2, {5}, {4}⟩,
    ⟨some 5, some 0, {2}, {3}⟩,
    ⟨some 5, some 0, {4}, {3}⟩,
    ⟨some 5, some 2, {0}, {1}⟩,
    ⟨some 5, some 2, {1}, {1}⟩,
    ⟨some 5, some 2, {3}, {4}⟩,
    ⟨some 5, some 2, {4}, {1}⟩,
    ⟨some 5, some 4, {0}, {5}⟩,
    ⟨some 5, some 4, {1}, {2}⟩,
    ⟨some 5, some 4, {1}, {5}⟩,
    ⟨some 5, some 4, {2}, {5}⟩}

private lemma zmod6_level1_topYukawa :
    ∀ x ∈ zmod6TopYukawaLevelOneCharges.val, x.AllowsTerm .topYukawa := by
  decide +kernel

private lemma zmod6_level1_not_pheno :
    ∀ x ∈ zmod6TopYukawaLevelOneCharges.val, ¬ x.IsPhenoConstrained := by
  decide +kernel

private lemma zmod6_level1_not_yukawa1 :
    ∀ x ∈ zmod6TopYukawaLevelOneCharges.val, ¬ x.YukawaGeneratesDangerousAtLevel 1 := by
  decide +kernel

private lemma zmod6_level1_complete :
    ∀ x ∈ zmod6TopYukawaLevelOneCharges.val, x.IsComplete := by
  decide +kernel

private lemma zmod6_level1_closed_Q5 :
    IsPhenoClosedQ5 (Finset.univ : Finset (ZMod 6)) zmod6TopYukawaLevelOneCharges.val := by
  apply isPhenClosedQ5_of_isPhenoConstrainedQ5
  decide +kernel

private lemma zmod6_level1_closed_Q10 :
    IsPhenoClosedQ10 (Finset.univ : Finset (ZMod 6)) zmod6TopYukawaLevelOneCharges.val := by
  apply isPhenClosedQ10_of_isPhenoConstrainedQ10
  decide +kernel

private lemma zmod6_level1_contains :
    ContainsPhenoCompletionsOfMinimallyAllows
      (Finset.univ : Finset (ZMod 6)) (Finset.univ : Finset (ZMod 6))
      zmod6TopYukawaLevelOneCharges.val := by
  rw [← completeMinSubset_subset_iff_containsPhenoCompletionsOfMinimallyAllows]
  decide +kernel

private lemma mem_zmod6TopYukawaLevelOneCharges_iff {x : ChargeSpectrum (ZMod 6)} :
    x ∈ zmod6TopYukawaLevelOneCharges ↔
      x.AllowsTerm .topYukawa ∧ x.IsComplete ∧
        ¬ x.IsPhenoConstrained ∧ ¬ x.YukawaGeneratesDangerousAtLevel 1 := by
  have h := completeness_of_isPhenoClosedQ5_isPhenoClosedQ10
    (S5 := (Finset.univ : Finset (ZMod 6)))
    (S10 := (Finset.univ : Finset (ZMod 6)))
    (charges := zmod6TopYukawaLevelOneCharges.val)
    zmod6_level1_topYukawa
    zmod6_level1_not_pheno
    zmod6_level1_not_yukawa1
    zmod6_level1_complete
    zmod6_level1_closed_Q5
    zmod6_level1_closed_Q10
    zmod6_level1_contains
    (x := x)
    (ofFinset_univ x)
  constructor
  · intro hx
    have hx' : x ∈ zmod6TopYukawaLevelOneCharges.val := hx
    rcases h.mp hx' with ⟨hTop, hNoPheno, hNoYukawa1, hComplete⟩
    exact ⟨hTop, hComplete, hNoPheno, hNoYukawa1⟩
  · intro hx
    exact h.mpr ⟨hx.1, hx.2.2.1, hx.2.2.2, hx.2.1⟩

private def zmod6ChargesSixExpected : Finset (ChargeSpectrum (ZMod 6)) :=
  {⟨some 0, some 2, {5}, {1}⟩,
    ⟨some 0, some 4, {1}, {5}⟩, ⟨some 1, some 0, {2}, {3}⟩, ⟨some 1, some 2, {4}, {1}⟩,
    ⟨some 1, some 4, {0}, {5}⟩, ⟨some 1, some 4, {3}, {2}⟩, ⟨some 2, some 0, {1}, {3}⟩,
    ⟨some 2, some 4, {5}, {5}⟩, ⟨some 3, some 2, {5}, {4}⟩, ⟨some 3, some 4, {1}, {2}⟩,
    ⟨some 4, some 0, {5}, {3}⟩, ⟨some 4, some 2, {1}, {1}⟩, ⟨some 5, some 0, {4}, {3}⟩,
    ⟨some 5, some 2, {0}, {1}⟩, ⟨some 5, some 2, {3}, {4}⟩, ⟨some 5, some 4, {2}, {5}⟩}

private lemma zmod6_topYukawaLevelOne_filter_eq :
    zmod6TopYukawaLevelOneCharges.filter (fun x => ¬ x.YukawaGeneratesDangerousAtLevel 4) =
    zmod6ChargesSixExpected := by
  decide +kernel

lemma ZModCharges_six_eq : ZModCharges 6 = {⟨some 0, some 2, {5}, {1}⟩,
    ⟨some 0, some 4, {1}, {5}⟩, ⟨some 1, some 0, {2}, {3}⟩, ⟨some 1, some 2, {4}, {1}⟩,
    ⟨some 1, some 4, {0}, {5}⟩, ⟨some 1, some 4, {3}, {2}⟩, ⟨some 2, some 0, {1}, {3}⟩,
    ⟨some 2, some 4, {5}, {5}⟩, ⟨some 3, some 2, {5}, {4}⟩, ⟨some 3, some 4, {1}, {2}⟩,
    ⟨some 4, some 0, {5}, {3}⟩, ⟨some 4, some 2, {1}, {1}⟩, ⟨some 5, some 0, {4}, {3}⟩,
    ⟨some 5, some 2, {0}, {1}⟩, ⟨some 5, some 2, {3}, {4}⟩, ⟨some 5, some 4, {2}, {5}⟩} := by
  change ZModCharges 6 = zmod6ChargesSixExpected
  ext x
  constructor
  · intro hx
    rw [ZModCharges] at hx
    have hxFilter := Finset.mem_filter.mp hx
    have hxComplete : IsComplete x := hxFilter.2.1
    have hxPheno : ¬ x.IsPhenoConstrained := hxFilter.2.2.1
    have hxYukawa4 : ¬ x.YukawaGeneratesDangerousAtLevel 4 := hxFilter.2.2.2
    have hxTop : x.AllowsTerm .topYukawa :=
      zmod6_topYukawa_of_good hxComplete hxPheno hxYukawa4
    have hxYukawa1 : ¬ x.YukawaGeneratesDangerousAtLevel 1 := fun h1 =>
      hxYukawa4 (yukawaGeneratesDangerousAtLevel_of_le (by decide : 1 ≤ 4) h1)
    have hxLevelOne : x ∈ zmod6TopYukawaLevelOneCharges :=
      mem_zmod6TopYukawaLevelOneCharges_iff.mpr
        ⟨hxTop, hxComplete, hxPheno, hxYukawa1⟩
    have hxFiltered :
        x ∈ zmod6TopYukawaLevelOneCharges.filter
          (fun x => ¬ x.YukawaGeneratesDangerousAtLevel 4) := by
      exact Finset.mem_filter.mpr ⟨hxLevelOne, hxYukawa4⟩
    rw [zmod6_topYukawaLevelOne_filter_eq] at hxFiltered
    exact hxFiltered
  · intro hx
    have hxFiltered :
        x ∈ zmod6TopYukawaLevelOneCharges.filter
          (fun x => ¬ x.YukawaGeneratesDangerousAtLevel 4) := by
      rw [zmod6_topYukawaLevelOne_filter_eq]
      exact hx
    have hxLevelOne : x ∈ zmod6TopYukawaLevelOneCharges :=
      (Finset.mem_filter.mp hxFiltered).1
    have hxYukawa4 : ¬ x.YukawaGeneratesDangerousAtLevel 4 :=
      (Finset.mem_filter.mp hxFiltered).2
    have hxProps := mem_zmod6TopYukawaLevelOneCharges_iff.mp hxLevelOne
    rw [ZModCharges]
    exact Finset.mem_filter.mpr
      ⟨ofFinset_univ x, hxProps.2.1, hxProps.2.2.1, hxYukawa4⟩

/-!

## B. The finite set of viable `ZMod n × ZMod m` charge spectra

-/

/-!

### B.1. General construction

-/

/-- The finite set of `ZMod n × ZMod m` valued charges which are complete,
  not pheno-constrained and don't regenerate dangerous couplings
  with the Yukawa term up-to 4-inserstions of singlets. -/
def ZModZModCharges (n m : ℕ) [NeZero n] [NeZero m] : Finset (ChargeSpectrum (ZMod n × ZMod m)) :=
  let S : Finset (ChargeSpectrum (ZMod n × ZMod m)) := ofFinset (Finset.univ) Finset.univ
  S.filter (fun x => IsComplete x ∧
  ¬ x.IsPhenoConstrained ∧ ¬ x.YukawaGeneratesDangerousAtLevel 4)

end ChargeSpectrum
end SU5

end SuperSymmetry
