/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import SpaceAndTime.Space.Derivatives.Basic
set_option maxHeartbeats 800000
/-!

# Lorentz group actions related to SpaceTime

## i. Overview

We already have a Lorentz group action on `SpaceTime d`, in this module
we define the induced action on Schwartz functions and distributions.

## ii. Key results

- `schwartzAction` : Defines the action of the Lorentz group on Schwartz functions.
- An instance of `DistribMulAction` for the Lorentz group acting on distributions.

## iii. Table of contents

- A. Lorentz group action on Schwartz functions
  - A.1. The definition of the action
  - A.2. Basic properties of the action
  - A.3. Injectivity of the action
  - A.4. Surjectivity of the action
- B. Lorentz group action on distributions
  - B.1. The SMul instance
  - B.2. The DistribMulAction instance
  - B.3. The SMulCommClass instance
  - B.4. Action as a linear map

## iv. References

-/
noncomputable section

namespace SpaceTime

open Manifold
open Matrix
open Complex
open ComplexConjugate
open TensorSpecies
open SchwartzMap
attribute [-simp] Fintype.sum_sum_type

/-!

## A. Lorentz group action on Schwartz functions

-/

/-!

### A.1. The definition of the action

-/

/-- The Lorentz group action on Schwartz functions taking the Lorentz group to
  continuous linear maps. -/
noncomputable def lorentzActionCLE {d} (Λ : LorentzGroup d) : SpaceTime d ≃L[ℝ] SpaceTime d :=
  LinearEquiv.toContinuousLinearEquiv <|
    LinearEquiv.ofBijective (Lorentz.Vector.actionCLM Λ).toLinearMap
      ⟨Lorentz.Vector.actionCLM_injective Λ, Lorentz.Vector.actionCLM_surjective Λ⟩

@[simp]
lemma lorentzActionCLE_apply {d} (Λ : LorentzGroup d) (x : SpaceTime d) :
    lorentzActionCLE Λ x = Λ • x := rfl

/-- The Lorentz group action on Schwartz functions taking the Lorentz group to
  continuous linear maps. -/
noncomputable def schwartzAction {d} : LorentzGroup d →* 𝓢(SpaceTime d, ℝ) →L[ℝ] 𝓢(SpaceTime d, ℝ) where
  toFun Λ := SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (lorentzActionCLE Λ⁻¹)
  map_one' := by
    ext η x
    simp [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, lorentzActionCLE,
      Lorentz.Vector.actionCLM_apply]
  map_mul' Λ₁ Λ₂ := by
    ext η x
    simp [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, lorentzActionCLE,
      Lorentz.Vector.actionCLM_apply, Function.comp, MulAction.mul_smul]

/-!

### A.2. Basic properties of the action

-/

lemma schwartzAction_mul_apply {d} (Λ₁ Λ₂ : LorentzGroup d)
    (η : 𝓢(SpaceTime d, ℝ)) :
    schwartzAction Λ₂ (schwartzAction (Λ₁) η) =
    schwartzAction (Λ₂ * Λ₁) η := by
  simpa [map_mul] using congrArg (fun f => f η) (schwartzAction.map_mul Λ₂ Λ₁)

theorem schwartzAction_apply {d} (Λ : LorentzGroup d)
    (η : 𝓢(SpaceTime d, ℝ)) (x : SpaceTime d) :
    (schwartzAction Λ η) x = η (Λ⁻¹ • x) := by
  simp [schwartzAction, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]

/-!

### A.3. Injectivity of the action

-/

theorem schwartzAction_injective {d} (Λ : LorentzGroup d) :
    Function.Injective (schwartzAction Λ) := by
  intro η1 η2 hη
  have hη' := congrArg (schwartzAction Λ⁻¹) hη
  simpa [schwartzAction_mul_apply] using hη'

/-!

### A.4. Surjectivity of the action

-/

theorem schwartzAction_surjective {d} (Λ : LorentzGroup d) :
    Function.Surjective (schwartzAction Λ) := by
  intro η
  refine ⟨schwartzAction Λ⁻¹ η, ?_⟩
  simpa [schwartzAction_mul_apply] using
    (schwartzAction_mul_apply (Λ₁ := Λ⁻¹) (Λ₂ := Λ) (η := η))

/-!

## B. Lorentz group action on distributions

-/
section Distribution

/-!

### B.1. The SMul instance

-/
variable
    {c : Fin n → realLorentzTensor.Color} {M : Type} [NormedAddCommGroup M]
      [NormedSpace ℝ M] [Tensorial (realLorentzTensor d) c M] [T2Space M]

open Distribution
instance : SMul (LorentzGroup d) ((SpaceTime d) →d[ℝ] M) where
  smul Λ f := (Tensorial.actionCLM (realLorentzTensor d) Λ) ∘L f ∘L (schwartzAction Λ⁻¹)

lemma lorentzGroup_smul_dist_apply (Λ : LorentzGroup d) (f : (SpaceTime d) →d[ℝ] M)
    (η : 𝓢(SpaceTime d, ℝ)) : (Λ • f) η = Λ • (f (schwartzAction Λ⁻¹ η)) := rfl

/-!

### B.2. The DistribMulAction instance

-/

noncomputable instance instDistribMulAction :
    DistribMulAction (LorentzGroup d) ((SpaceTime d) →d[ℝ] M) := by
  letI : MulAction (LorentzGroup d) ((SpaceTime d) →d[ℝ] M) := {
    one_smul := by
      intro f
      ext η
      simp [lorentzGroup_smul_dist_apply]
    mul_smul := by
      intro Λ₁ Λ₂ f
      ext η
      rw [lorentzGroup_smul_dist_apply, lorentzGroup_smul_dist_apply, lorentzGroup_smul_dist_apply]
      rw [smul_smul]
      have harg :
          schwartzAction ((Λ₁ * Λ₂)⁻¹) η =
            schwartzAction (Λ₂⁻¹) (schwartzAction (Λ₁⁻¹) η) := by
        calc
          schwartzAction ((Λ₁ * Λ₂)⁻¹) η = schwartzAction (Λ₂⁻¹ * Λ₁⁻¹) η := by simp
          _ = schwartzAction (Λ₂⁻¹) (schwartzAction (Λ₁⁻¹) η) := by
            symm
            simpa using schwartzAction_mul_apply (Λ₁ := Λ₁⁻¹) (Λ₂ := Λ₂⁻¹) (η := η)
      simpa using congrArg f harg
  }
  refine
    { smul_zero := ?_
      smul_add := ?_ }
  · intro Λ
    ext η
    simp [lorentzGroup_smul_dist_apply]
  · intro Λ f₁ f₂
    ext η
    simp [lorentzGroup_smul_dist_apply, smul_add]

instance instSMulCommClassDist :
    SMulCommClass ℝ (LorentzGroup d) ((SpaceTime d) →d[ℝ] M) where
  smul_comm a Λ f := by
    ext η
    simp [lorentzGroup_smul_dist_apply, smul_comm]

attribute [instance] instSMulCommClassDist

/-!

### B.4. Action as a linear map

-/

/-- The Lorentz action on distributions as a linear map. -/
def distActionLinearMap {d} {M : Type} [NormedAddCommGroup M]
    [NormedSpace ℝ M] [Tensorial (realLorentzTensor d) c M] [T2Space M](Λ : LorentzGroup d) :
    ((SpaceTime d) →d[ℝ] M) →ₗ[ℝ] ((SpaceTime d) →d[ℝ] M) where
  toFun f := Λ • f
  map_add' f1 f2 := by
    ext η
    simp [lorentzGroup_smul_dist_apply, smul_add]
  map_smul' a f := by
    ext η
    change
      (Tensorial.actionCLM (realLorentzTensor d) Λ) (a • f (schwartzAction Λ⁻¹ η)) =
        a • (Tensorial.actionCLM (realLorentzTensor d) Λ) (f (schwartzAction Λ⁻¹ η))
    simpa using
      (Tensorial.actionCLM (realLorentzTensor d) Λ).map_smul a (f (schwartzAction Λ⁻¹ η))
end Distribution
end SpaceTime

end
