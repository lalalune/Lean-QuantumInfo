import QFT.AnomalyCancellation.Basic

/-!
Core family-map constructions shared by anomaly-cancellation charge systems.

These are parameterized by:
- a charge system `ChargeSystem n`,
- a species splitting `toSpeciesEquiv`,
- the corresponding species projection maps `toSpecies`.

The species space is canonically `ACCSystemChargesMk n` (i.e. `Fin n → ℚ`), which
matches the Standard Model and RHN anomaly-cancellation setups.
-/

namespace ACCSystemCharges
namespace FamilyMaps

variable {k : ℕ}
variable (ChargeSystem : ℕ → ACCSystemCharges)
variable (toSpeciesEquiv :
    ∀ {n : ℕ}, (ChargeSystem n).Charges ≃ (Fin k → Fin n → ℚ))
variable (toSpecies :
    ∀ {n : ℕ}, Fin k → (ChargeSystem n).Charges →ₗ[ℚ] (ACCSystemChargesMk n).Charges)
variable (charges_eq_toSpecies_eq :
    ∀ {n : ℕ} (S T : (ChargeSystem n).Charges),
      S = T ↔ ∀ i, toSpecies (n := n) i S = toSpecies (n := n) i T)
variable (toSpeciesEquiv_symm_apply :
    ∀ {n : ℕ} (i : Fin k) (f : Fin k → Fin n → ℚ),
      toSpecies (n := n) i ((toSpeciesEquiv (n := n)).symm f) = f i)

/-- Given a map for a generic species, the corresponding map for full charges. -/
@[simps!]
def chargesMapOfSpeciesMap {n m : ℕ}
    (f : (ACCSystemChargesMk n).Charges →ₗ[ℚ] (ACCSystemChargesMk m).Charges) :
    (ChargeSystem n).Charges →ₗ[ℚ] (ChargeSystem m).Charges where
  toFun S := (toSpeciesEquiv (n := m)).symm (fun i => (LinearMap.comp f (toSpecies (n := n) i)) S)
  map_add' S T := by
    refine (charges_eq_toSpecies_eq (n := m) _ _).2 ?_
    intro i
    have hST :
        (toSpecies (n := m) i)
            ((toSpeciesEquiv (n := m)).symm
              (fun j => (LinearMap.comp f (toSpecies (n := n) j)) (S + T))) =
          (LinearMap.comp f (toSpecies (n := n) i)) (S + T) := by
      simpa using
        (toSpeciesEquiv_symm_apply (n := m) i
          (fun j => (LinearMap.comp f (toSpecies (n := n) j)) (S + T)))
    have hS :
        (toSpecies (n := m) i)
            ((toSpeciesEquiv (n := m)).symm
              (fun j => (LinearMap.comp f (toSpecies (n := n) j)) S)) =
          (LinearMap.comp f (toSpecies (n := n) i)) S := by
      simpa using
        (toSpeciesEquiv_symm_apply (n := m) i
          (fun j => (LinearMap.comp f (toSpecies (n := n) j)) S))
    have hT :
        (toSpecies (n := m) i)
            ((toSpeciesEquiv (n := m)).symm
              (fun j => (LinearMap.comp f (toSpecies (n := n) j)) T)) =
          (LinearMap.comp f (toSpecies (n := n) i)) T := by
      simpa using
        (toSpeciesEquiv_symm_apply (n := m) i
          (fun j => (LinearMap.comp f (toSpecies (n := n) j)) T))
    rw [(toSpecies (n := m) i).map_add, hST, hS, hT]
    exact (LinearMap.comp f (toSpecies (n := n) i)).map_add S T
  map_smul' a S := by
    refine (charges_eq_toSpecies_eq (n := m) _ _).2 ?_
    intro i
    have hAS :
        (toSpecies (n := m) i)
            ((toSpeciesEquiv (n := m)).symm
              (fun j => (LinearMap.comp f (toSpecies (n := n) j)) (a • S))) =
          (LinearMap.comp f (toSpecies (n := n) i)) (a • S) := by
      simpa using
        (toSpeciesEquiv_symm_apply (n := m) i
          (fun j => (LinearMap.comp f (toSpecies (n := n) j)) (a • S)))
    have hS :
        (toSpecies (n := m) i)
            ((toSpeciesEquiv (n := m)).symm
              (fun j => (LinearMap.comp f (toSpecies (n := n) j)) S)) =
          (LinearMap.comp f (toSpecies (n := n) i)) S := by
      simpa using
        (toSpeciesEquiv_symm_apply (n := m) i
          (fun j => (LinearMap.comp f (toSpecies (n := n) j)) S))
    rw [(toSpecies (n := m) i).map_smul, hAS, hS]
    exact (LinearMap.comp f (toSpecies (n := n) i)).map_smul a S

lemma chargesMapOfSpeciesMap_toSpecies {n m : ℕ}
    (f : (ACCSystemChargesMk n).Charges →ₗ[ℚ] (ACCSystemChargesMk m).Charges)
    (S : (ChargeSystem n).Charges) (j : Fin k) :
    toSpecies (n := m) j
      (chargesMapOfSpeciesMap (k := k) (ChargeSystem := ChargeSystem)
        toSpeciesEquiv toSpecies charges_eq_toSpecies_eq
        toSpeciesEquiv_symm_apply f S) =
      (LinearMap.comp f (toSpecies (n := n) j)) S := by
  simpa using
    (toSpeciesEquiv_symm_apply (n := m) j
      (fun i => (LinearMap.comp f (toSpecies (n := n) i)) S))

/-- The projection of `m`-family species-charges onto the first `n` families. -/
@[simps!]
def speciesFamilyProj {m n : ℕ} (h : n ≤ m) :
    (ACCSystemChargesMk m).Charges →ₗ[ℚ] (ACCSystemChargesMk n).Charges where
  toFun S := S ∘ Fin.castLE h
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The projection of `m`-family charges onto the first `n` families. -/
def familyProjection {m n : ℕ} (h : n ≤ m) :
    (ChargeSystem m).Charges →ₗ[ℚ] (ChargeSystem n).Charges :=
  chargesMapOfSpeciesMap (k := k) (ChargeSystem := ChargeSystem)
    toSpeciesEquiv toSpecies charges_eq_toSpecies_eq toSpeciesEquiv_symm_apply
    (speciesFamilyProj h)

/-- Embed `m`-family species-charges into `n` families, padding extra slots with zero. -/
@[simps!]
def speciesEmbed (m n : ℕ) :
    (ACCSystemChargesMk m).Charges →ₗ[ℚ] (ACCSystemChargesMk n).Charges where
  toFun S := fun i =>
    if hi : i.1 < m then
      S ⟨i, hi⟩
    else
      0
  map_add' S T := by
    funext i
    by_cases hi : i.1 < m
    · simp [hi]
    · simp [hi]
  map_smul' a S := by
    funext i
    rcases i with ⟨i, hi⟩
    by_cases him : i < m
    · simp [HSMul.hSMul, SMul.smul, him]
    · simp [HSMul.hSMul, SMul.smul, him]

/-- Embed `m`-family charges into `n` families, padding extra slots with zero. -/
def familyEmbedding (m n : ℕ) :
    (ChargeSystem m).Charges →ₗ[ℚ] (ChargeSystem n).Charges :=
  chargesMapOfSpeciesMap (k := k) (ChargeSystem := ChargeSystem)
    toSpeciesEquiv toSpecies charges_eq_toSpecies_eq toSpeciesEquiv_symm_apply
    (speciesEmbed m n)

/-- Universal species embedding from one family to `n` families (constant in family index). -/
@[simps!]
def speciesFamilyUniversial (n : ℕ) :
    (ACCSystemChargesMk 1).Charges →ₗ[ℚ] (ACCSystemChargesMk n).Charges where
  toFun S _ := S ⟨0, Nat.zero_lt_succ 0⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Universal embedding from one-family charges to `n`-family charges. -/
def familyUniversal (n : ℕ) :
    (ChargeSystem 1).Charges →ₗ[ℚ] (ChargeSystem n).Charges :=
  chargesMapOfSpeciesMap (k := k) (ChargeSystem := ChargeSystem)
    toSpeciesEquiv toSpecies charges_eq_toSpecies_eq toSpeciesEquiv_symm_apply
    (speciesFamilyUniversial n)

end FamilyMaps
end ACCSystemCharges
