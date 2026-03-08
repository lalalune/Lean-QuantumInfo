/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Particles.BeyondTheStandardModel.RHN.AnomalyCancellation.Basic
import Particles.AnomalyCancellation.FamilyMapsCore
/-!
# Family maps for the Standard Model for RHN ACCs

We define the a series of maps between the charges for different numbers of families.
-/

namespace SMRHN
open SMνCharges
open SMνACCs
open BigOperators

private abbrev coreChargesMap {n m : ℕ}
    (f : (SMνSpecies n).Charges →ₗ[ℚ] (SMνSpecies m).Charges) :
    (SMνCharges n).Charges →ₗ[ℚ] (SMνCharges m).Charges :=
  ACCSystemCharges.FamilyMaps.chargesMapOfSpeciesMap
    (k := 6) (ChargeSystem := SMνCharges)
    (toSpeciesEquiv := fun {n} => (toSpeciesEquiv (n := n)))
    (toSpecies := fun {n} => (toSpecies (n := n)))
    (charges_eq_toSpecies_eq := fun {n} => (charges_eq_toSpecies_eq (n := n)))
    (toSpeciesEquiv_symm_apply := fun {n} => (toSMSpecies_toSpecies_inv (n := n)))
    f

private abbrev coreSpeciesProj {m n : ℕ} (h : n ≤ m) :
    (SMνSpecies m).Charges →ₗ[ℚ] (SMνSpecies n).Charges :=
  ACCSystemCharges.FamilyMaps.speciesFamilyProj h

private abbrev coreSpeciesEmbed (m n : ℕ) :
    (SMνSpecies m).Charges →ₗ[ℚ] (SMνSpecies n).Charges :=
  ACCSystemCharges.FamilyMaps.speciesEmbed m n

private abbrev coreSpeciesUniversal (n : ℕ) :
    (SMνSpecies 1).Charges →ₗ[ℚ] (SMνSpecies n).Charges :=
  ACCSystemCharges.FamilyMaps.speciesFamilyUniversial n

/-- Given a map for a generic species, the corresponding map for charges. -/
@[simps!]
abbrev chargesMapOfSpeciesMap {n m : ℕ}
    (f : (SMνSpecies n).Charges →ₗ[ℚ] (SMνSpecies m).Charges) :
    (SMνCharges n).Charges →ₗ[ℚ] (SMνCharges m).Charges :=
  coreChargesMap f

lemma chargesMapOfSpeciesMap_toSpecies {n m : ℕ}
    (f : (SMνSpecies n).Charges →ₗ[ℚ] (SMνSpecies m).Charges)
    (S : (SMνCharges n).Charges) (j : Fin 6) :
    toSpecies j (chargesMapOfSpeciesMap f S) = (LinearMap.comp f (toSpecies j)) S := by
  simpa [chargesMapOfSpeciesMap, coreChargesMap] using
    (ACCSystemCharges.FamilyMaps.chargesMapOfSpeciesMap_toSpecies
      (k := 6) (ChargeSystem := SMνCharges)
      (toSpeciesEquiv := fun {n} => (toSpeciesEquiv (n := n)))
      (toSpecies := fun {n} => (toSpecies (n := n)))
      (charges_eq_toSpecies_eq := fun {n} => (charges_eq_toSpecies_eq (n := n)))
      (toSpeciesEquiv_symm_apply := fun {n} => (toSMSpecies_toSpecies_inv (n := n)))
      f S j)

/-- The projection of the `m`-family charges onto the first `n`-family charges for species. -/
@[simps!]
abbrev speciesFamilyProj {m n : ℕ} (h : n ≤ m) :
    (SMνSpecies m).Charges →ₗ[ℚ] (SMνSpecies n).Charges :=
  coreSpeciesProj h

/-- The projection of the `m`-family charges onto the first `n`-family charges. -/
abbrev familyProjection {m n : ℕ} (h : n ≤ m) :
    (SMνCharges m).Charges →ₗ[ℚ] (SMνCharges n).Charges :=
  ACCSystemCharges.FamilyMaps.familyProjection
    (k := 6) (ChargeSystem := SMνCharges)
    (toSpeciesEquiv := fun {n} => (toSpeciesEquiv (n := n)))
    (toSpecies := fun {n} => (toSpecies (n := n)))
    (charges_eq_toSpecies_eq := fun {n} => (charges_eq_toSpecies_eq (n := n)))
    (toSpeciesEquiv_symm_apply := fun {n} => (toSMSpecies_toSpecies_inv (n := n)))
    h

/-- For species, the embedding of the `m`-family charges onto the `n`-family charges, with all
other charges zero. -/
@[simps!]
abbrev speciesEmbed (m n : ℕ) :
    (SMνSpecies m).Charges →ₗ[ℚ] (SMνSpecies n).Charges :=
  coreSpeciesEmbed m n

/-- The embedding of the `m`-family charges onto the `n`-family charges, with all
other charges zero. -/
abbrev familyEmbedding (m n : ℕ) :
    (SMνCharges m).Charges →ₗ[ℚ] (SMνCharges n).Charges :=
  ACCSystemCharges.FamilyMaps.familyEmbedding
    (k := 6) (ChargeSystem := SMνCharges)
    (toSpeciesEquiv := fun {n} => (toSpeciesEquiv (n := n)))
    (toSpecies := fun {n} => (toSpecies (n := n)))
    (charges_eq_toSpecies_eq := fun {n} => (charges_eq_toSpecies_eq (n := n)))
    (toSpeciesEquiv_symm_apply := fun {n} => (toSMSpecies_toSpecies_inv (n := n)))
    m n

/-- For species, the embedding of the `1`-family charges into the `n`-family charges in
a universal manner. -/
@[simps!]
abbrev speciesFamilyUniversial (n : ℕ) :
    (SMνSpecies 1).Charges →ₗ[ℚ] (SMνSpecies n).Charges :=
  coreSpeciesUniversal n

/-- The embedding of the `1`-family charges into the `n`-family charges in
a universal manner. -/
abbrev familyUniversal (n : ℕ) :
    (SMνCharges 1).Charges →ₗ[ℚ] (SMνCharges n).Charges :=
  ACCSystemCharges.FamilyMaps.familyUniversal
    (k := 6) (ChargeSystem := SMνCharges)
    (toSpeciesEquiv := fun {n} => (toSpeciesEquiv (n := n)))
    (toSpecies := fun {n} => (toSpecies (n := n)))
    (charges_eq_toSpecies_eq := fun {n} => (charges_eq_toSpecies_eq (n := n)))
    (toSpeciesEquiv_symm_apply := fun {n} => (toSMSpecies_toSpecies_inv (n := n)))
    n

lemma toSpecies_familyUniversal {n : ℕ} (j : Fin 6) (S : (SMνCharges 1).Charges)
    (i : Fin n) : toSpecies j (familyUniversal n S) i = toSpecies j S ⟨0, by simp⟩ := by
  erw [chargesMapOfSpeciesMap_toSpecies]
  rfl

lemma sum_familyUniversal {n : ℕ} (m : ℕ) (S : (SMνCharges 1).Charges) (j : Fin 6) :
    ∑ i, ((fun a => a ^ m) ∘ toSpecies j (familyUniversal n S)) i =
    n * (toSpecies j S ⟨0, by simp⟩) ^ m := by
  simp only [SMνSpecies_numberCharges, Function.comp_apply, toSpecies_apply, Fin.zero_eta,
    Fin.isValue]
  have h1 : (n : ℚ) * (toSpecies j S ⟨0, by simp⟩) ^ m =
      ∑ _i : Fin n, (toSpecies j S ⟨0, by simp⟩) ^ m := by
    rw [Fin.sum_const]
    simp
  erw [h1]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  erw [toSpecies_familyUniversal]

lemma sum_familyUniversal_one {n : ℕ} (S : (SMνCharges 1).Charges) (j : Fin 6) :
    ∑ i, toSpecies j (familyUniversal n S) i = n * (toSpecies j S ⟨0, by simp⟩) := by
  simpa using @sum_familyUniversal n 1 S j

lemma sum_familyUniversal_two {n : ℕ} (S : (SMνCharges 1).Charges)
    (T : (SMνCharges n).Charges) (j : Fin 6) :
    ∑ i, (toSpecies j (familyUniversal n S) i * toSpecies j T i) =
    (toSpecies j S ⟨0, by simp⟩) * ∑ i, toSpecies j T i := by
  simp only [SMνSpecies_numberCharges, toSpecies_apply, Fin.zero_eta, Fin.isValue]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  erw [toSpecies_familyUniversal]
  rfl

lemma sum_familyUniversal_three {n : ℕ} (S : (SMνCharges 1).Charges)
    (T L : (SMνCharges n).Charges) (j : Fin 6) :
    ∑ i, (toSpecies j (familyUniversal n S) i * toSpecies j T i * toSpecies j L i) =
    (toSpecies j S ⟨0, by simp⟩) * ∑ i, toSpecies j T i * toSpecies j L i := by
  simp only [SMνSpecies_numberCharges, toSpecies_apply, Fin.zero_eta, Fin.isValue]
  rw [Finset.mul_sum]
  apply Finset.sum_congr
  · rfl
  · intro i _
    erw [toSpecies_familyUniversal]
    simp only [SMνSpecies_numberCharges, Fin.zero_eta, Fin.isValue, toSpecies_apply]
    ring

lemma familyUniversal_accGrav (S : (SMνCharges 1).Charges) :
    accGrav (familyUniversal n S) = n * (accGrav S) := by
  rw [accGrav_decomp, accGrav_decomp]
  repeat rw [sum_familyUniversal_one]
  simp only [Fin.isValue, SMνSpecies_numberCharges, Fin.zero_eta, toSpecies_apply,
    Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
  ring

lemma familyUniversal_accSU2 (S : (SMνCharges 1).Charges) :
    accSU2 (familyUniversal n S) = n * (accSU2 S) := by
  rw [accSU2_decomp, accSU2_decomp]
  repeat rw [sum_familyUniversal_one]
  simp only [Fin.isValue, SMνSpecies_numberCharges, Fin.zero_eta, toSpecies_apply,
    Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
  ring

lemma familyUniversal_accSU3 (S : (SMνCharges 1).Charges) :
    accSU3 (familyUniversal n S) = n * (accSU3 S) := by
  rw [accSU3_decomp, accSU3_decomp]
  repeat rw [sum_familyUniversal_one]
  simp only [Fin.isValue, SMνSpecies_numberCharges, Fin.zero_eta, toSpecies_apply,
    Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
  ring

lemma familyUniversal_accYY (S : (SMνCharges 1).Charges) :
    accYY (familyUniversal n S) = n * (accYY S) := by
  rw [accYY_decomp, accYY_decomp]
  repeat rw [sum_familyUniversal_one]
  simp only [Fin.isValue, SMνSpecies_numberCharges, Fin.zero_eta, toSpecies_apply,
    Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
  ring

lemma familyUniversal_quadBiLin (S : (SMνCharges 1).Charges) (T : (SMνCharges n).Charges) :
    quadBiLin (familyUniversal n S) T =
    S (0 : Fin 6) * ∑ i, Q T i - 2 * S (1 : Fin 6) * ∑ i, U T i + S (2 : Fin 6) *∑ i, D T i -
    S (3 : Fin 6) * ∑ i, L T i + S (4 : Fin 6) * ∑ i, E T i := by
  rw [quadBiLin_decomp]
  repeat rw [sum_familyUniversal_two]
  repeat rw [toSpecies_one]
  simp only [Fin.isValue, SMνSpecies_numberCharges, toSpecies_apply, add_left_inj, sub_left_inj,
    sub_right_inj]
  ring

lemma familyUniversal_accQuad (S : (SMνCharges 1).Charges) :
    accQuad (familyUniversal n S) = n * (accQuad S) := by
  rw [accQuad_decomp]
  repeat erw [sum_familyUniversal]
  rw [accQuad_decomp]
  simp only [Fin.isValue, SMνSpecies_numberCharges, Fin.zero_eta, toSpecies_apply,
    Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
  ring

lemma familyUniversal_cubeTriLin (S : (SMνCharges 1).Charges) (T R : (SMνCharges n).Charges) :
    cubeTriLin (familyUniversal n S) T R = 6 * S (0 : Fin 6) * ∑ i, (Q T i * Q R i) +
      3 * S (1 : Fin 6) * ∑ i, (U T i * U R i) + 3 * S (2 : Fin 6) * ∑ i, (D T i * D R i)
      + 2 * S (3 : Fin 6) * ∑ i, (L T i * L R i) +
      S (4 : Fin 6) * ∑ i, (E T i * E R i) + S (5 : Fin 6) * ∑ i, (N T i * N R i) := by
  rw [cubeTriLin_decomp]
  repeat rw [sum_familyUniversal_three]
  repeat rw [toSpecies_one]
  simp only [Fin.isValue, SMνSpecies_numberCharges, toSpecies_apply, add_left_inj]
  ring

lemma familyUniversal_cubeTriLin' (S T : (SMνCharges 1).Charges) (R : (SMνCharges n).Charges) :
    cubeTriLin (familyUniversal n S) (familyUniversal n T) R =
      6 * S (0 : Fin 6) * T (0 : Fin 6) * ∑ i, Q R i +
      3 * S (1 : Fin 6) * T (1 : Fin 6) * ∑ i, U R i
      + 3 * S (2 : Fin 6) * T (2 : Fin 6) * ∑ i, D R i +
      2 * S (3 : Fin 6) * T (3 : Fin 6) * ∑ i, L R i +
      S (4 : Fin 6) * T (4 : Fin 6) * ∑ i, E R i + S (5 : Fin 6) * T (5 : Fin 6) * ∑ i, N R i := by
  rw [familyUniversal_cubeTriLin]
  repeat rw [sum_familyUniversal_two]
  repeat rw [toSpecies_one]
  simp only [Fin.isValue, SMνSpecies_numberCharges, toSpecies_apply]
  ring

lemma familyUniversal_accCube (S : (SMνCharges 1).Charges) :
    accCube (familyUniversal n S) = n * (accCube S) := by
  rw [accCube_decomp]
  repeat erw [sum_familyUniversal]
  rw [accCube_decomp]
  simp only [Fin.isValue, SMνSpecies_numberCharges, Fin.zero_eta, toSpecies_apply,
    Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
  ring

end SMRHN
