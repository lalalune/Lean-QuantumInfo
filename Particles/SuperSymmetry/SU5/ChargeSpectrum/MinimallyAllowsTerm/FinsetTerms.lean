/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Particles.SuperSymmetry.SU5.ChargeSpectrum.PhenoConstrained
import Particles.SuperSymmetry.SU5.ChargeSpectrum.MinimallyAllowsTerm.Basic
/-!

# Minimally allows a set of terms

## i. Overview

In this module we consider those charge spectra which minimally allow a
finite set of potential terms.
That is, they those charge spectra which allow each term in the set, but no proper subset of the
charge spectra allows each term in that set.

We have special focus on those charge spectra which minimally allow a top and bottom Yukawa term.

## ii. Key results

- `MinimallyAllowsFinsetTerms`: the proposition that a charge spectrum
  minimally allows a given finite set of potential terms.
- `minTopBottom`: a finite set of charge spectra which contains every
  charge spectrum which minimally allows a top and bottom Yukawa term, given
  finite sets of possible `5`-bar and `10` charges.

## iii. Table of contents

- A. Charge spectra which minimally allow a finite set of potential terms
  - A.1. `MinimallyAllowsFinsetTerms`: Prop of minimally allowing a finset of potential terms
  - A.2. The prop `MinimallyAllowsFinsetTerms` is decidable
  - A.3. Every element of `MinimallyAllowsFinsetTerms` allows each term in the finset
  - A.4. `MinimallyAllowsFinsetTerms` for the singleton set is equivalent to `MinimallyAllowsTerm`
- B. Minimally allowing the top and bottom Yukawa
  - B.1. Finset of charge spectra containing those which minimally allow top and bottom Yukawa
  - B.2. Every element of `minTopBottom` allows a top Yukawa
  - B.3. Every element of `minTopBottom` allows a bottom Yukawa
  - B.4. Every charge spectrum minimally allowing a top and bottom Yukawa in `minTopBottom`

## iv. References

There are no references for this module.

-/

namespace SuperSymmetry
namespace SU5

namespace ChargeSpectrum

variable {𝓩 : Type} [AddCommGroup 𝓩] [DecidableEq 𝓩]
open SuperSymmetry.SU5
open PotentialTerm
/-!

## A. Charge spectra which minimally allow a finite set of potential terms

We start by defining the proposition that a charge spectrum minimally allows a
finite set of potential terms, and prove some basic properties there of.

-/

/-!

### A.1. `MinimallyAllowsFinsetTerms`: Prop of minimally allowing a finset of potential terms

-/
/-- A collection of charge spectra is said to minimally allow
  a finite set of potential terms `Ts` if it allows
  all terms in `Ts` and no strict subset of it allows all terms in `Ts`. -/
def MinimallyAllowsFinsetTerms (x : ChargeSpectrum 𝓩) (Ts : Finset PotentialTerm) : Prop :=
  ∀ y ∈ x.powerset, y = x ↔ ∀ T ∈ Ts, y.AllowsTerm T

/-!

### A.2. The prop `MinimallyAllowsFinsetTerms` is decidable

-/

instance (x : ChargeSpectrum 𝓩) (Ts : Finset PotentialTerm) :
    Decidable (x.MinimallyAllowsFinsetTerms Ts) :=
  inferInstanceAs (Decidable (∀ y ∈ powerset x, y = x ↔ ∀ T ∈ Ts, y.AllowsTerm T))

/-!

### A.3. Every element of `MinimallyAllowsFinsetTerms` allows each term in the finset

-/

variable {Ts : Finset PotentialTerm} {x : ChargeSpectrum 𝓩}

lemma allowsTerm_of_minimallyAllowsFinsetTerms {T : PotentialTerm}
    (h : x.MinimallyAllowsFinsetTerms Ts) (hT : T ∈ Ts) : x.AllowsTerm T :=
  (h x (self_mem_powerset x)).mp rfl T hT

/-!

### A.4. `MinimallyAllowsFinsetTerms` for the singleton set is equivalent to `MinimallyAllowsTerm`

-/

@[simp]
lemma minimallyAllowsFinsetTerms_singleton {T : PotentialTerm} :
    x.MinimallyAllowsFinsetTerms {T} ↔ x.MinimallyAllowsTerm T := by
  simp [MinimallyAllowsFinsetTerms, MinimallyAllowsTerm]

/-!

## B. Minimally allowing the top and bottom Yukawa

We now consider the special case of those charge spectra which minimally allow
a top and bottom Yukawa term.

We construct a finite set of such charge spectra given finite sets of
possible `5`-bar and `10` charges which contains every charge
spectrum which minimally allows a top and bottom Yukawa term.

-/

/-!

### B.1. Finset of charge spectra containing those which minimally allow top and bottom Yukawa

Here we define `minTopBottom` in a way which is computationally efficient.

-/

/-- The set of charges of the form `(qHd, qHu, {q5}, {-qHd-q5, q10, qHu - q10})`
  This includes every charge which minimally allows for the top and bottom Yukawas. -/
def minTopBottom (S5 S10 : Finset 𝓩) : Multiset (ChargeSpectrum 𝓩) := Multiset.dedup <|
  (S5.val ×ˢ S5.val ×ˢ S5.val ×ˢ S10.val).map
    (fun x => ⟨x.1, x.2.1, {x.2.2.1}, {- x.1 - x.2.2.1, x.2.2.2, x.2.1 - x.2.2.2}⟩)

/-!

### B.2. Every element of `minTopBottom` allows a top Yukawa

-/

lemma allowsTerm_topYukawa_of_mem_minTopBottom {S5 S10 : Finset 𝓩}
    {x : ChargeSpectrum 𝓩} (h : x ∈ minTopBottom S5 S10) :
    x.AllowsTerm topYukawa := by
  have h' : x ∈ (S5.val ×ˢ S5.val ×ˢ S5.val ×ˢ S10.val).map
      (fun x => ⟨x.1, x.2.1, {x.2.2.1}, {- x.1 - x.2.2.1, x.2.2.2, x.2.1 - x.2.2.2}⟩) := by
    simpa [minTopBottom] using (Multiset.mem_dedup.mp h)
  rcases Multiset.mem_map.mp h' with ⟨y, hy, rfl⟩
  rw [allowsTerm_iff_zero_mem_ofPotentialTerm']
  simp [ofPotentialTerm']
  refine ⟨y.2.2.2, y.2.1 - y.2.2.2, ?_, ?_⟩
  · exact Multiset.mem_product.mpr
      ⟨Multiset.mem_ndinsert.mpr (Or.inr (Multiset.mem_ndinsert.mpr (Or.inl rfl))),
       Multiset.mem_ndinsert.mpr (Or.inr (Multiset.mem_ndinsert.mpr (Or.inr
        (Multiset.mem_singleton.mpr (by abel)))))⟩
  · abel
/-!

### B.3. Every element of `minTopBottom` allows a bottom Yukawa

-/

lemma allowsTerm_bottomYukawa_of_mem_minTopBottom {S5 S10 : Finset 𝓩}
    {x : ChargeSpectrum 𝓩} (h : x ∈ minTopBottom S5 S10) :
    x.AllowsTerm bottomYukawa := by
  have h' : x ∈ (S5.val ×ˢ S5.val ×ˢ S5.val ×ˢ S10.val).map
      (fun x => ⟨x.1, x.2.1, {x.2.2.1}, {- x.1 - x.2.2.1, x.2.2.2, x.2.1 - x.2.2.2}⟩) := by
    simpa [minTopBottom] using (Multiset.mem_dedup.mp h)
  rcases Multiset.mem_map.mp h' with ⟨y, hy, rfl⟩
  rw [allowsTerm_iff_zero_mem_ofPotentialTerm']
  simp [ofPotentialTerm']
/-!

### B.4. Every charge spectrum minimally allowing a top and bottom Yukawa in `minTopBottom`

-/

lemma mem_minTopBottom_of_minimallyAllowsFinsetTerms
    {x : ChargeSpectrum 𝓩} {S5 S10 : Finset 𝓩}
    (h : x.MinimallyAllowsFinsetTerms {topYukawa, bottomYukawa})
    (hx : x ∈ ofFinset S5 S10) :
    x ∈ minTopBottom S5 S10 := by
  have hTop : x.AllowsTerm topYukawa := allowsTerm_of_minimallyAllowsFinsetTerms h (by simp)
  have hBottom : x.AllowsTerm bottomYukawa := allowsTerm_of_minimallyAllowsFinsetTerms h (by simp)
  obtain ⟨aT, bT, cT, hTopSub, hTopAllows⟩ := allowsTermForm_subset_allowsTerm_of_allowsTerm hTop
  obtain ⟨aB, bB, cB, hBottomSub, hBottomAllows⟩ :=
    allowsTermForm_subset_allowsTerm_of_allowsTerm hBottom
  have hx' := hx
  rw [mem_ofFinset_iff] at hx'
  have hTopHuSub : ({-aT} : Finset 𝓩) ⊆ x.qHu.toFinset := by
    simpa [allowsTermForm, subset_def] using hTopSub.2.1
  have hTopQ10Sub : ({bT, -aT - bT} : Finset 𝓩) ⊆ x.Q10 := by
    simpa [allowsTermForm, subset_def] using hTopSub.2.2.2
  have hBottomHdSub : ({aB} : Finset 𝓩) ⊆ x.qHd.toFinset := by
    simpa [allowsTermForm, subset_def] using hBottomSub.1
  have hBottomQ5Sub : ({bB} : Finset 𝓩) ⊆ x.Q5 := by
    simpa [allowsTermForm, subset_def] using hBottomSub.2.2.1
  have hBottomQ10Sub : ({-aB - bB} : Finset 𝓩) ⊆ x.Q10 := by
    simpa [allowsTermForm, subset_def] using hBottomSub.2.2.2
  have haB_qHd : aB ∈ x.qHd.toFinset := hBottomHdSub (by simp)
  have hnegAT_qHu : -aT ∈ x.qHu.toFinset := hTopHuSub (by simp)
  have hbB_Q5 : bB ∈ x.Q5 := hBottomQ5Sub (by simp)
  have hbT_Q10 : bT ∈ x.Q10 := hTopQ10Sub (by simp)
  have hnegATbT_Q10 : -aT - bT ∈ x.Q10 := hTopQ10Sub (by simp)
  have hnegABbB_Q10 : -aB - bB ∈ x.Q10 := hBottomQ10Sub (by simp)
  have haB_S5 : aB ∈ S5 := hx'.1 haB_qHd
  have hnegAT_S5 : -aT ∈ S5 := hx'.2.1 hnegAT_qHu
  have hbB_S5 : bB ∈ S5 := hx'.2.2.1 hbB_Q5
  have hbT_S10 : bT ∈ S10 := hx'.2.2.2 hbT_Q10
  let y : ChargeSpectrum 𝓩 := ⟨some aB, some (-aT), {bB}, {-aB - bB, bT, -aT - bT}⟩
  have hyTop : y.AllowsTerm topYukawa := by
    rw [allowsTerm_iff_zero_mem_ofPotentialTerm']
    simp [y, ofPotentialTerm']
    refine ⟨bT, -aT - bT, ?_, ?_⟩
    · exact Multiset.mem_product.mpr
        ⟨Multiset.mem_ndinsert.mpr (Or.inr (Multiset.mem_ndinsert.mpr (Or.inl rfl))),
         Multiset.mem_ndinsert.mpr (Or.inr (Multiset.mem_ndinsert.mpr (Or.inr
          (Multiset.mem_singleton.mpr (by abel)))))⟩
    · abel
  have hyBottom : y.AllowsTerm bottomYukawa := by
    rw [allowsTerm_iff_zero_mem_ofPotentialTerm']
    simp [y, ofPotentialTerm']
  have hyQ10Sub : ({-aB - bB, bT, -aT - bT} : Finset 𝓩) ⊆ x.Q10 := by
    intro q hq
    rcases (Finset.mem_insert.mp hq) with hq1 | hqRest
    · subst hq1
      exact hnegABbB_Q10
    rcases (Finset.mem_insert.mp hqRest) with hq2 | hq3
    · subst hq2
      exact hbT_Q10
    simp only [Finset.mem_singleton] at hq3; subst hq3; exact hnegATbT_Q10
  have hySub : y ⊆ x := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [y] using hBottomHdSub
    · simpa [y] using hTopHuSub
    · simpa [y] using hBottomQ5Sub
    · simpa [y] using hyQ10Sub
  have hyPow : y ∈ x.powerset := by
    simpa [mem_powerset_iff_subset]
  have hyEq : y = x := (h y hyPow).2 (by simpa [hyTop, hyBottom])
  rw [← hyEq]
  apply Multiset.mem_dedup.mpr
  apply Multiset.mem_map.mpr
  refine ⟨(aB, (-aT, (bB, bT))), ?_, rfl⟩
  exact Multiset.mem_product.mpr ⟨Finset.mem_val.mpr haB_S5,
    Multiset.mem_product.mpr ⟨Finset.mem_val.mpr hnegAT_S5,
    Multiset.mem_product.mpr ⟨Finset.mem_val.mpr hbB_S5, Finset.mem_val.mpr hbT_S10⟩⟩⟩
end ChargeSpectrum

end SU5
end SuperSymmetry
