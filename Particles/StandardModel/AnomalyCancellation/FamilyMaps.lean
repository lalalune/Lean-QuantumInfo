/- 
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Particles.StandardModel.AnomalyCancellation.Basic
import Particles.AnomalyCancellation.FamilyMapsCore
/-!
# Family maps for the Standard Model ACCs

We define a series of maps between charges for different numbers of families.
-/

namespace SM
open SMCharges
open SMACCs

private abbrev coreChargesMap {n m : ℕ}
    (f : (SMSpecies n).Charges →ₗ[ℚ] (SMSpecies m).Charges) :
    (SMCharges n).Charges →ₗ[ℚ] (SMCharges m).Charges :=
  ACCSystemCharges.FamilyMaps.chargesMapOfSpeciesMap
    (k := 5) (ChargeSystem := SMCharges)
    (toSpeciesEquiv := fun {n} => (toSpeciesEquiv (n := n)))
    (toSpecies := fun {n} => (toSpecies (n := n)))
    (charges_eq_toSpecies_eq := fun {n} => (charges_eq_toSpecies_eq (n := n)))
    (toSpeciesEquiv_symm_apply := fun {n} => (toSMSpecies_toSpecies_inv (n := n)))
    f

private abbrev coreSpeciesProj {m n : ℕ} (h : n ≤ m) :
    (SMSpecies m).Charges →ₗ[ℚ] (SMSpecies n).Charges :=
  ACCSystemCharges.FamilyMaps.speciesFamilyProj h

private abbrev coreSpeciesEmbed (m n : ℕ) :
    (SMSpecies m).Charges →ₗ[ℚ] (SMSpecies n).Charges :=
  ACCSystemCharges.FamilyMaps.speciesEmbed m n

private abbrev coreSpeciesUniversal (n : ℕ) :
    (SMSpecies 1).Charges →ₗ[ℚ] (SMSpecies n).Charges :=
  ACCSystemCharges.FamilyMaps.speciesFamilyUniversial n

/-- Given a map for a generic species, the corresponding map for charges. -/
@[simps!]
abbrev chargesMapOfSpeciesMap {n m : ℕ}
    (f : (SMSpecies n).Charges →ₗ[ℚ] (SMSpecies m).Charges) :
    (SMCharges n).Charges →ₗ[ℚ] (SMCharges m).Charges :=
  coreChargesMap f

/-- The projection of `m`-family charges onto the first `n`-family species charges. -/
@[simps!]
abbrev speciesFamilyProj {m n : ℕ} (h : n ≤ m) :
    (SMSpecies m).Charges →ₗ[ℚ] (SMSpecies n).Charges :=
  coreSpeciesProj h

/-- The projection of `m`-family charges onto the first `n`-family charges. -/
abbrev familyProjection {m n : ℕ} (h : n ≤ m) :
    (SMCharges m).Charges →ₗ[ℚ] (SMCharges n).Charges :=
  ACCSystemCharges.FamilyMaps.familyProjection
    (k := 5) (ChargeSystem := SMCharges)
    (toSpeciesEquiv := fun {n} => (toSpeciesEquiv (n := n)))
    (toSpecies := fun {n} => (toSpecies (n := n)))
    (charges_eq_toSpecies_eq := fun {n} => (charges_eq_toSpecies_eq (n := n)))
    (toSpeciesEquiv_symm_apply := fun {n} => (toSMSpecies_toSpecies_inv (n := n)))
    h

/-- Embed `m`-family species charges into `n` families, padding with zero. -/
@[simps!]
abbrev speciesEmbed (m n : ℕ) :
    (SMSpecies m).Charges →ₗ[ℚ] (SMSpecies n).Charges :=
  coreSpeciesEmbed m n

/-- Embed `m`-family charges into `n` families, padding with zero. -/
abbrev familyEmbedding (m n : ℕ) :
    (SMCharges m).Charges →ₗ[ℚ] (SMCharges n).Charges :=
  ACCSystemCharges.FamilyMaps.familyEmbedding
    (k := 5) (ChargeSystem := SMCharges)
    (toSpeciesEquiv := fun {n} => (toSpeciesEquiv (n := n)))
    (toSpecies := fun {n} => (toSpecies (n := n)))
    (charges_eq_toSpecies_eq := fun {n} => (charges_eq_toSpecies_eq (n := n)))
    (toSpeciesEquiv_symm_apply := fun {n} => (toSMSpecies_toSpecies_inv (n := n)))
    m n

/-- Universal species embedding from one family into `n` families. -/
@[simps!]
abbrev speciesFamilyUniversial (n : ℕ) :
    (SMSpecies 1).Charges →ₗ[ℚ] (SMSpecies n).Charges :=
  coreSpeciesUniversal n

/-- Universal embedding from one-family charges into `n`-family charges. -/
abbrev familyUniversal (n : ℕ) :
    (SMCharges 1).Charges →ₗ[ℚ] (SMCharges n).Charges :=
  ACCSystemCharges.FamilyMaps.familyUniversal
    (k := 5) (ChargeSystem := SMCharges)
    (toSpeciesEquiv := fun {n} => (toSpeciesEquiv (n := n)))
    (toSpecies := fun {n} => (toSpecies (n := n)))
    (charges_eq_toSpecies_eq := fun {n} => (charges_eq_toSpecies_eq (n := n)))
    (toSpeciesEquiv_symm_apply := fun {n} => (toSMSpecies_toSpecies_inv (n := n)))
    n

end SM
