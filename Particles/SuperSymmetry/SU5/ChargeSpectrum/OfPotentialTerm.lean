/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Particles.SuperSymmetry.SU5.ChargeSpectrum.OfFieldLabel
import Mathlib.Tactic.Abel

/-!

# Charges associated with a potential term

## i. Overview

In this module we give the multiset of charges associated with a given type of potential term,
given a charge spectrum.

We will define two versions of this, one based on the underlying fields on the
potentials, and the charges that they carry, and one more explicit version which
is faster to compute with. The former is `ofPotentialTerm`, and the latter is
`ofPotentialTerm'`.

We will show that these two multisets have the same elements.

## ii. Key results

- `ofPotentialTerm` : The multiset of charges associated with a potential term,
  defined in terms of the fields making up that potential term, given a charge spectrum.
- `ofPotentialTerm'` : The multiset of charges associated with a potential term,
  defined explicitly, given a charge spectrum.

## iii. Table of contents

- A. Charges of a potential term from field labels
  - A.1. Monotonicity of `ofPotentialTerm`
  - A.2. Charges of potential terms for the empty charge spectrum
- B. Explicit construction of charges of a potential term
  - B.1. Explicit multisets for `ofPotentialTerm'`
  - B.2. `ofPotentialTerm'` on the empty charge spectrum
- C. Relation between two constructions of charges of potential terms
  - C.1. Showing that `ofPotentialTerm` is a subset of `ofPotentialTerm'`
  - C.2. Showing that `ofPotentialTerm'` is a subset of `ofPotentialTerm`
  - C.3. Equivalence of elements of `ofPotentialTerm` and `ofPotentialTerm'`
  - C.4. Induced monotonicity of `ofPotentialTerm'`

## iv. References

There are no known references for this material.

-/

namespace SuperSymmetry
namespace SU5

namespace ChargeSpectrum
open PotentialTerm

variable {𝓩 : Type} [AddCommGroup 𝓩]

private theorem multiset_mem_sprod {α β : Type*} {s : Multiset α} {t : Multiset β}
    {p : α × β} : p ∈ s ×ˢ t ↔ p.1 ∈ s ∧ p.2 ∈ t :=
  Multiset.mem_product

private lemma exists_perm_Q5Q5Q10 {Q5 Q10 : Finset 𝓩} {u v w : 𝓩}
    (hu : u ∈ Q10) (hv : v ∈ Q5) (hw : w ∈ Q5) :
    ∃ a a' b, (a ∈ Q5 ∧ a' ∈ Q5 ∧ b ∈ Q10) ∧ a + (a' + b) = u + (v + w) := by
  refine ⟨v, w, u, ?_, ?_⟩
  · exact ⟨hv, hw, hu⟩
  · abel

private lemma exists_perm_Q5Q10 {Q5 Q10 : Finset 𝓩} {u v : 𝓩}
    (hu : u ∈ Q10) (hv : v ∈ Q5) :
    ∃ a b, (a ∈ Q5 ∧ b ∈ Q10) ∧ a + b = u + v := by
  refine ⟨v, u, ?_, ?_⟩
  · exact ⟨hv, hu⟩
  · abel

private lemma exists_perm_Q10Q5Q5 {Q5 Q10 : Finset 𝓩} {u v w : 𝓩}
    (hu : u ∈ Q5) (hv : v ∈ Q5) (hw : w ∈ Q10) :
    ∃ b a b', ((a ∈ Q5 ∧ b' ∈ Q5) ∧ b ∈ Q10) ∧ b + (a + b') = u + (v + w) := by
  refine ⟨w, u, v, ?_, ?_⟩
  · exact ⟨⟨hu, hv⟩, hw⟩
  · abel

private lemma exists_perm_Q10Q10Q5 {Q5 Q10 : Finset 𝓩} {u v w : 𝓩}
    (hu : u ∈ Q5) (hv : v ∈ Q10) (hw : w ∈ Q10) :
    ∃ a a' b, (a ∈ Q5 ∧ a' ∈ Q10 ∧ b ∈ Q10) ∧ a' + (b + -a) = v + (w + -u) := by
  refine ⟨u, v, w, ?_, ?_⟩
  · exact ⟨hu, hv, hw⟩
  · abel

private lemma exists_perm_Q10Q10Q5_assoc {Q5 Q10 : Finset 𝓩} {u v w : 𝓩}
    (hu : u ∈ Q5) (hv : v ∈ Q10) (hw : w ∈ Q10) :
    ∃ a a' b, (a ∈ Q5 ∧ a' ∈ Q10 ∧ b ∈ Q10) ∧ a' + (b + -a) = v + w + -u := by
  obtain ⟨a, a', b, hmem, hsum⟩ := exists_perm_Q10Q10Q5 hu hv hw
  refine ⟨a, a', b, hmem, ?_⟩
  simpa [add_assoc] using hsum

private lemma exists_perm_Q10Q10Q5' {Q5 Q10 : Finset 𝓩} {u v w : 𝓩}
    (hu : u ∈ Q5) (hv : v ∈ Q10) (hw : w ∈ Q10) :
    ∃ a a' b, ((a' ∈ Q10 ∧ b ∈ Q10) ∧ a ∈ Q5) ∧ a' + b + -a = v + (w + -u) := by
  refine ⟨u, v, w, ?_, ?_⟩
  · exact ⟨⟨hv, hw⟩, hu⟩
  · abel

private lemma exists_perm_Q10Q5 {Q5 Q10 : Finset 𝓩} {u v : 𝓩}
    (hu : u ∈ Q5) (hv : v ∈ Q10) :
    ∃ a b, (a ∈ Q10 ∧ b ∈ Q5) ∧ a + b = u + v := by
  refine ⟨v, u, ?_, ?_⟩
  · exact ⟨hv, hu⟩
  · abel

private lemma exists_perm_two_add_right {Q : Finset 𝓩} {u v c : 𝓩}
    (hu : u ∈ Q) (hv : v ∈ Q) :
    ∃ a b, (a ∈ Q ∧ b ∈ Q) ∧ a + (b + c) = u + v + c := by
  refine ⟨u, v, ⟨hu, hv⟩, ?_⟩
  abel

private lemma exists_perm_two_add_right' {Q : Finset 𝓩} {u v c : 𝓩}
    (hu : u ∈ Q) (hv : v ∈ Q) :
    ∃ a b, (a ∈ Q ∧ b ∈ Q) ∧ a + b + c = u + (v + c) := by
  refine ⟨u, v, ⟨hu, hv⟩, ?_⟩
  abel

private lemma exists_perm_one_add_right {Q : Finset 𝓩} {u v c : 𝓩}
    (hu : u ∈ Q) :
    ∃ a ∈ Q, v + (a + c) = v + u + c := by
  refine ⟨u, hu, ?_⟩
  abel

private lemma exists_perm_one_add_right' {Q : Finset 𝓩} {u v c : 𝓩}
    (hu : u ∈ Q) :
    ∃ a ∈ Q, v + a + c = v + (u + c) := by
  refine ⟨u, hu, ?_⟩
  abel

/-!

## A. Charges of a potential term from field labels

We first define `ofPotentialTerm`, and prover properties of it.
This is slow to compute in practice.

-/

/-- Given a charges `x : Charges` associated to the representations, and a potential
  term `T`, the charges associated with instances of that potential term. -/
def ofPotentialTerm (x : ChargeSpectrum 𝓩) (T : PotentialTerm) : Multiset 𝓩 :=
  let add : Multiset 𝓩 → Multiset 𝓩 → Multiset 𝓩 := fun a b => (a ×ˢ b).map
      fun (x, y) => x + y
  (T.toFieldLabel.map fun F => (ofFieldLabel x F).val).foldl add {0}

/-!

### A.1. Monotonicity of `ofPotentialTerm`

We show that `ofPotentialTerm` is monotone in its charge spectrum argument.
That is if `x ⊆ y` then `ofPotentialTerm x T ⊆ ofPotentialTerm y T`.

-/
lemma ofPotentialTerm_mono {x y : ChargeSpectrum 𝓩} (h : x ⊆ y) (T : PotentialTerm) :
    x.ofPotentialTerm T ⊆ y.ofPotentialTerm T := by
  simp only [ofPotentialTerm]
  have hFL : ∀ F : FieldLabel, ∀ z ∈ (ofFieldLabel x F).val, z ∈ (ofFieldLabel y F).val :=
    fun F z hz => Finset.mem_val.mpr (ofFieldLabel_mono h F (Finset.mem_val.mp hz))
  let add : Multiset 𝓩 → Multiset 𝓩 → Multiset 𝓩 := fun a b => (a ×ˢ b).map fun (x, y) => x + y
  suffices ∀ (l : List FieldLabel) (i₁ i₂ : Multiset 𝓩), i₁ ⊆ i₂ →
      (l.map fun F => (ofFieldLabel x F).val).foldl add i₁ ⊆
      (l.map fun F => (ofFieldLabel y F).val).foldl add i₂ by
    exact this T.toFieldLabel {0} {0} (Multiset.Subset.refl _)
  intro l
  induction l with
  | nil => intro _ _ h; exact h
  | cons F Fs ih =>
    intro i₁ i₂ hi
    simp only [List.map_cons, List.foldl_cons]
    apply ih
    intro z hz
    have hadd : ∀ (a b : Multiset 𝓩), add a b = (a ×ˢ b).map fun (x, y) => x + y :=
      fun _ _ => rfl
    simp only [hadd, Multiset.mem_map] at hz ⊢
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := hz
    exact ⟨⟨a, b⟩, Multiset.mem_product.mpr ⟨hi (Multiset.mem_product.mp hab).1,
      hFL F b (Multiset.mem_product.mp hab).2⟩, rfl⟩
/-!

### A.2. Charges of potential terms for the empty charge spectrum

For the empty charge spectrum, the charges associated with any potential term is empty.

-/

@[simp]
lemma ofPotentialTerm_empty (T : PotentialTerm) :
    ofPotentialTerm (∅ : ChargeSpectrum 𝓩) T = ∅ := by
  cases T
  all_goals
    rfl

/-!

## B. Explicit construction of charges of a potential term

We now turn to a more explicit construction of the charges associated with a potential term.
This is faster to compute with, but less obviously connected to the underlying
fields.

-/

/-- Given a charges `x : ChargeSpectrum` associated to the representations, and a potential
  term `T`, the charges associated with instances of that potential term.

  This is a more explicit form of `PotentialTerm`, which has the benefit that
  it is quick with `decide`, but it is not defined based on more fundamental
  concepts, like `ofPotentialTerm` is. -/
def ofPotentialTerm' (y : ChargeSpectrum 𝓩) (T : PotentialTerm) : Multiset 𝓩 :=
  let qHd := y.qHd
  let qHu := y.qHu
  let Q5 := y.Q5
  let Q10 := y.Q10
  match T with
  | μ =>
    match qHd, qHu with
    | none, _ => ∅
    | _, none => ∅
    | some qHd, some qHu => {qHd - qHu}
  | β =>
    match qHu with
    | none => ∅
    | some qHu => Q5.val.map (fun x => - qHu + x)
  | Λ => (Q5.product <| Q5.product <| Q10).val.map (fun x => x.1 + x.2.1 + x.2.2)
  | W1 => (Q5.product <| Q10.product <| Q10.product <| Q10).val.map
    (fun x => x.1 + x.2.1 + x.2.2.1 + x.2.2.2)
  | W2 =>
    match qHd with
    | none => ∅
    | some qHd =>
      (Q10.product <| Q10.product <| Q10).val.map (fun x => qHd + x.1 + x.2.1 + x.2.2)
  | W3 =>
    match qHu with
    | none => ∅
    | some qHu => (Q5.product <| Q5).val.map (fun x => -qHu - qHu + x.1 + x.2)
  | W4 =>
    match qHd, qHu with
    | none, _ => ∅
    | _, none => ∅
    | some qHd, some qHu => Q5.val.map (fun x => qHd - qHu - qHu + x)
  | K1 => (Q5.product <| Q10.product <| Q10).val.map
    (fun x => - x.1 + x.2.1 + x.2.2)
  | K2 =>
    match qHd, qHu with
    | none, _ => ∅
    | _, none => ∅
    | some qHd, some qHu => Q10.val.map (fun x => qHd + qHu + x)
  | topYukawa =>
    match qHu with
    | none => ∅
    | some qHu => (Q10.product <| Q10).val.map (fun x => - qHu + x.1 + x.2)
  | bottomYukawa =>
    match qHd with
    | none => ∅
    | some qHd => (Q5.product <| Q10).val.map (fun x => qHd + x.1 + x.2)

/-!

### B.1. Explicit multisets for `ofPotentialTerm'`

For each potential term, we give an explicit form of the multiset `ofPotentialTerm'`.

-/
lemma ofPotentialTerm'_μ_finset {x : ChargeSpectrum 𝓩} :
    x.ofPotentialTerm' μ =
    (x.qHd.toFinset.product <| x.qHu.toFinset).val.map (fun x => x.1 - x.2) := by
  match x with
  | ⟨none, qHu, Q5, Q10⟩ =>
    simp [ofPotentialTerm']
  | ⟨some qHd, none, Q5, Q10⟩ =>
    simp [ofPotentialTerm']
  | ⟨some qHd, some qHu, Q5, Q10⟩ =>
    simp [ofPotentialTerm']

lemma ofPotentialTerm'_β_finset {x : ChargeSpectrum 𝓩} :
    x.ofPotentialTerm' β =
    (x.qHu.toFinset.product <| x.Q5).val.map (fun x => - x.1 + x.2) := by
  match x with
  | ⟨qHd, none, Q5, Q10⟩ =>
    simp [ofPotentialTerm']
  | ⟨qHd, some qHu, Q5, Q10⟩ =>
    simp [ofPotentialTerm']

lemma ofPotentialTerm'_W2_finset {x : ChargeSpectrum 𝓩} :
    x.ofPotentialTerm' W2 = (x.qHd.toFinset.product <|
      x.Q10.product <| x.Q10.product <| x.Q10).val.map
    (fun x => x.1 + x.2.1 + x.2.2.1 + x.2.2.2) := by
  match x with
  | ⟨none, qHu, Q5, Q10⟩ =>
    simp [ofPotentialTerm']
  | ⟨some qHd, qHu, Q5, Q10⟩ =>
    simp [ofPotentialTerm']

lemma ofPotentialTerm'_W3_finset {x : ChargeSpectrum 𝓩} :
    x.ofPotentialTerm' W3 = (x.qHu.toFinset.product <| x.Q5.product <| x.Q5).val.map
    (fun x => -x.1 - x.1 + x.2.1 + x.2.2) := by
  match x with
  | ⟨qHd, none, Q5, Q10⟩ =>
    simp [ofPotentialTerm']
  | ⟨qHd, some qHu, Q5, Q10⟩ =>
    simp [ofPotentialTerm']

lemma ofPotentialTerm'_W4_finset {x : ChargeSpectrum 𝓩} :
    x.ofPotentialTerm' W4 = (x.qHd.toFinset.product <|
      x.qHu.toFinset.product <| x.Q5).val.map
    (fun x => x.1 - x.2.1 - x.2.1 + x.2.2) := by
  match x with
  | ⟨none, qHu, Q5, Q10⟩ =>
    simp [ofPotentialTerm']
  | ⟨some qHd, none, Q5, Q10⟩ =>
    simp [ofPotentialTerm']
  | ⟨some qHd, some qHu, Q5, Q10⟩ =>
    simp [ofPotentialTerm']

lemma ofPotentialTerm'_K2_finset {x : ChargeSpectrum 𝓩} :
    x.ofPotentialTerm' K2 = (x.qHd.toFinset.product <|
      x.qHu.toFinset.product <| x.Q10).val.map
    (fun x => x.1 + x.2.1 + x.2.2) := by
  match x with
  | ⟨none, qHu, Q5, Q10⟩ =>
    simp [ofPotentialTerm']
  | ⟨some qHd, none, Q5, Q10⟩ =>
    simp [ofPotentialTerm']
  | ⟨some qHd, some qHu, Q5, Q10⟩ =>
    simp [ofPotentialTerm']

lemma ofPotentialTerm'_topYukawa_finset {x : ChargeSpectrum 𝓩} :
    x.ofPotentialTerm' topYukawa = (x.qHu.toFinset.product <|
      x.Q10.product <| x.Q10).val.map
    (fun x => -x.1 + x.2.1 + x.2.2) := by
  match x with
  | ⟨qHd, none, Q5, Q10⟩ =>
    simp [ofPotentialTerm']
  | ⟨qHd, some qHu, Q5, Q10⟩ =>
    simp [ofPotentialTerm']

lemma ofPotentialTerm'_bottomYukawa_finset {x : ChargeSpectrum 𝓩} :
    x.ofPotentialTerm' bottomYukawa = (x.1.toFinset.product <|
      x.Q5.product <| x.Q10).val.map
    (fun x => x.1 + x.2.1 + x.2.2) := by
  match x with
  | ⟨none, qHu, Q5, Q10⟩ =>
    simp [ofPotentialTerm']
  | ⟨some qHd, qHu, Q5, Q10⟩ =>
    simp [ofPotentialTerm']

/-!

### B.2. `ofPotentialTerm'` on the empty charge spectrum

We show that for the empty charge spectrum, the charges associated with any potential term is empty,
as defined through `ofPotentialTerm'`.

-/

@[simp]
lemma ofPotentialTerm'_empty (T : PotentialTerm) :
    ofPotentialTerm' (∅ : ChargeSpectrum 𝓩) T = ∅ := by
  cases T
  all_goals
    simp [ofPotentialTerm']
/-!

## C. Relation between two constructions of charges of potential terms

We now give the relation between `ofPotentialTerm` and `ofPotentialTerm'`.
We show that they have the same elements, by showing that they are subsets of each other.

The prove of some of these results are rather long since they involve explicit
case analysis for each potential term, due to the nature of the definition
of `ofPotentialTerm'`.

-/

/-!

### C.1. Showing that `ofPotentialTerm` is a subset of `ofPotentialTerm'`

We first show that `ofPotentialTerm` is a subset of `ofPotentialTerm'`.

-/

set_option maxHeartbeats 12800000 in
lemma ofPotentialTerm_subset_ofPotentialTerm' {x : ChargeSpectrum 𝓩} (T : PotentialTerm) :
    x.ofPotentialTerm T ⊆ x.ofPotentialTerm' T := by
  intro a ha
  cases x with
  | mk qHd qHu Q5 Q10 =>
    cases T <;> cases qHd <;> cases qHu
    all_goals (try simp_all [ofPotentialTerm, ofPotentialTerm', PotentialTerm.toFieldLabel,
      List.foldl, ofFieldLabel, Multiset.mem_map, Multiset.mem_product, Prod.exists,
      sub_eq_add_neg, multiset_mem_sprod, Finset.mem_val])
    all_goals (try aesop (add norm simp [add_comm, add_left_comm]))
    all_goals (try solve_by_elim [exists_perm_Q5Q5Q10, exists_perm_Q10Q10Q5_assoc,
      exists_perm_Q5Q10, exists_perm_two_add_right, exists_perm_two_add_right',
      exists_perm_one_add_right, exists_perm_one_add_right'])
/-!

### C.2. Showing that `ofPotentialTerm'` is a subset of `ofPotentialTerm`

We now show the other direction of the subset relation, that
`ofPotentialTerm'` is a subset of `ofPotentialTerm`.

-/

set_option maxHeartbeats 12800000 in
lemma ofPotentialTerm'_subset_ofPotentialTerm [DecidableEq 𝓩]
    {x : ChargeSpectrum 𝓩} (T : PotentialTerm) :
    x.ofPotentialTerm' T ⊆ x.ofPotentialTerm T := by
  intro a ha
  cases x with
  | mk qHd qHu Q5 Q10 =>
    cases T <;> cases qHd <;> cases qHu
    all_goals (try simp_all [ofPotentialTerm, ofPotentialTerm', PotentialTerm.toFieldLabel,
      List.foldl, ofFieldLabel, Multiset.mem_map, Multiset.mem_product, Prod.exists,
      sub_eq_add_neg, multiset_mem_sprod, Finset.mem_val])
    all_goals (try aesop (add norm simp [add_comm, add_left_comm]))
    all_goals (try solve_by_elim [exists_perm_Q10Q5Q5, exists_perm_Q10Q10Q5',
      exists_perm_Q10Q5, exists_perm_two_add_right, exists_perm_two_add_right',
      exists_perm_one_add_right, exists_perm_one_add_right'])
/-!

### C.3. Equivalence of elements of `ofPotentialTerm` and `ofPotentialTerm'`

We now show that a charge is in `ofPotentialTerm` if and only if it is in
`ofPotentialTerm'`. I.e. their underlying finite sets are equal.
We do not say anything about the multiplicity of elements within the multisets,
which is not important for us.

-/
lemma mem_ofPotentialTerm_iff_mem_ofPotentialTerm [DecidableEq 𝓩]
    {T : PotentialTerm} {n : 𝓩} {y : ChargeSpectrum 𝓩} :
    n ∈ y.ofPotentialTerm T ↔ n ∈ y.ofPotentialTerm' T := by
  constructor
  · exact fun h => ofPotentialTerm_subset_ofPotentialTerm' T h
  · exact fun h => ofPotentialTerm'_subset_ofPotentialTerm T h

/-!

### C.4. Induced monotonicity of `ofPotentialTerm'`

Due to the equivalence of elements of `ofPotentialTerm` and `ofPotentialTerm'`,
we can now also show that `ofPotentialTerm'` is monotone in its charge spectrum argument.

-/

lemma ofPotentialTerm'_mono [DecidableEq 𝓩] {x y : ChargeSpectrum 𝓩}
    (h : x ⊆ y) (T : PotentialTerm) :
    x.ofPotentialTerm' T ⊆ y.ofPotentialTerm' T := by
  intro i
  rw [← mem_ofPotentialTerm_iff_mem_ofPotentialTerm,
      ← mem_ofPotentialTerm_iff_mem_ofPotentialTerm]
  exact fun a => ofPotentialTerm_mono h T a

end ChargeSpectrum

end SU5
end SuperSymmetry
