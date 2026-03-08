/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Inspired by PhysLean's QFT/PerturbationTheory/FieldSpecification.
-/
import QFT.PerturbationTheory.CreateAnnihilate

/-!
# Field Specification for Perturbation Theory

Defines the algebraic structure of quantum fields needed for perturbation theory.
A field specification classifies field operators into creation/annihilation parts
and assigns them a statistics type (bosonic or fermionic).

## Main definitions

* `FieldStatistics` : bosonic or fermionic classification
* `FieldSpec` : specification of a quantum field theory's operator algebra
* `FieldSpec.FieldOp` : a field operator labeled by field type and create/annihilate

## References

* PhysLean (lean-phys-community), QFT/PerturbationTheory
* Peskin & Schroeder, *An Introduction to Quantum Field Theory*
-/

/-! ## Field Statistics -/

/-- Classification of quantum fields by their statistics. -/
inductive FieldStatistics
  | bosonic : FieldStatistics
  | fermionic : FieldStatistics
  deriving DecidableEq, Repr

namespace FieldStatistics

/-- The exchange sign: +1 for bosons, -1 for fermions. -/
def exchangeSign : FieldStatistics → ℤ
  | bosonic => 1
  | fermionic => -1

/-- Combining statistics follows ℤ/2ℤ addition: same → bosonic, different → fermionic. -/
def combine : FieldStatistics → FieldStatistics → FieldStatistics
  | bosonic, bosonic => bosonic
  | fermionic, fermionic => bosonic
  | _, _ => fermionic

@[simp] theorem exchangeSign_bosonic : bosonic.exchangeSign = 1 := rfl
@[simp] theorem exchangeSign_fermionic : fermionic.exchangeSign = -1 := rfl
@[simp] theorem combine_fermionic_fermionic : combine fermionic fermionic = bosonic := rfl
@[simp] theorem combine_bosonic_bosonic : combine bosonic bosonic = bosonic := rfl

theorem exchangeSign_combine (s₁ s₂ : FieldStatistics) :
    (combine s₁ s₂).exchangeSign = s₁.exchangeSign * s₂.exchangeSign := by
  cases s₁ <;> cases s₂ <;> simp [combine, exchangeSign]

/-- The Koszul sign accumulated by moving the operator at position `i` past all predecessors. -/
def koszulSign (stats : List FieldStatistics) (i : ℕ) : ℤ :=
  (stats.take i).foldl (fun acc s => acc * s.exchangeSign) 1

end FieldStatistics

/-! ## Field Specification -/

/-- A field specification describes the types of fields in the theory and their properties. -/
structure FieldSpec where
  FieldType : Type
  statistics : FieldType → FieldStatistics
  isComplex : FieldType → Bool

namespace FieldSpec

variable (spec : FieldSpec)

/-- A field operator: a field type paired with a creation/annihilation label. -/
structure FieldOp where
  fieldType : spec.FieldType
  ca : CreateAnnihilate

def fieldOpStatistics (op : spec.FieldOp) : FieldStatistics :=
  spec.statistics op.fieldType

/-- A monomial of field operators (an ordered product). -/
abbrev FieldMonomial := List spec.FieldOp

/-- The combined statistics of a monomial, folded left from bosonic identity. -/
def monomialStatistics (ops : spec.FieldMonomial) : FieldStatistics :=
  ops.foldl (fun acc op => FieldStatistics.combine acc (spec.fieldOpStatistics op))
    FieldStatistics.bosonic

/-- Normal-order a monomial by moving creation operators to the left. -/
def normalOrderMonomial (ops : spec.FieldMonomial) : spec.FieldMonomial :=
  ops.mergeSort (fun a b => CreateAnnihilate.normalOrder a.ca b.ca)

end FieldSpec

/-! ## Standard Examples -/

/-- A scalar field theory has a single real bosonic field. -/
def scalarFieldSpec : FieldSpec where
  FieldType := Unit
  statistics := fun _ => .bosonic
  isComplex := fun _ => false

/-- QED field types. -/
inductive QEDField
  | electron | photon
  deriving DecidableEq

def qedFieldSpec : FieldSpec where
  FieldType := QEDField
  statistics := fun | .electron => .fermionic | .photon => .bosonic
  isComplex := fun | .electron => true | .photon => false

/-! ## Verification Tests -/

section Tests

/-- `combine` is commutative. -/
theorem FieldStatistics.combine_comm (s₁ s₂ : FieldStatistics) :
    combine s₁ s₂ = combine s₂ s₁ := by
  cases s₁ <;> cases s₂ <;> rfl

/-- `combine` is associative. -/
theorem FieldStatistics.combine_assoc (s₁ s₂ s₃ : FieldStatistics) :
    combine (combine s₁ s₂) s₃ = combine s₁ (combine s₂ s₃) := by
  cases s₁ <;> cases s₂ <;> cases s₃ <;> rfl

/-- Bosonic is the identity for `combine`. -/
theorem FieldStatistics.combine_bosonic_left (s : FieldStatistics) :
    combine bosonic s = s := by cases s <;> rfl

theorem FieldStatistics.combine_bosonic_right (s : FieldStatistics) :
    combine s bosonic = s := by cases s <;> rfl

/-- Every element is its own inverse under `combine`. -/
theorem FieldStatistics.combine_self (s : FieldStatistics) :
    combine s s = bosonic := by cases s <;> rfl

/-- The exchange sign squared is always 1. -/
theorem FieldStatistics.exchangeSign_sq (s : FieldStatistics) :
    s.exchangeSign ^ 2 = 1 := by cases s <;> simp [exchangeSign]

/-- Exchange sign is never zero. -/
theorem FieldStatistics.exchangeSign_ne_zero (s : FieldStatistics) :
    s.exchangeSign ≠ 0 := by cases s <;> simp [exchangeSign]

/-- Koszul sign of an empty list is 1. -/
theorem FieldStatistics.koszulSign_nil (i : ℕ) :
    koszulSign [] i = 1 := by simp [koszulSign]

/-- Koszul sign at position 0 is always 1 (no predecessors). -/
theorem FieldStatistics.koszulSign_zero (stats : List FieldStatistics) :
    koszulSign stats 0 = 1 := by simp [koszulSign]

/-- Scalar field is bosonic. -/
example : scalarFieldSpec.statistics () = .bosonic := rfl

/-- Electron is fermionic. -/
example : qedFieldSpec.statistics .electron = .fermionic := rfl

/-- Photon is bosonic. -/
example : qedFieldSpec.statistics .photon = .bosonic := rfl

/-- Scalar field is real. -/
example : scalarFieldSpec.isComplex () = false := rfl

/-- Electron is complex. -/
example : qedFieldSpec.isComplex .electron = true := rfl

/-- Empty monomial has bosonic statistics. -/
example : scalarFieldSpec.monomialStatistics [] = .bosonic := rfl

end Tests
