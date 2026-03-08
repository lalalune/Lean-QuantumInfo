import Mathlib.Tactic
import QEC.Stabilizer.Core.StabilizerCode
import QEC.Stabilizer.Core.CSS
import QEC.Stabilizer.Core.CSSNoNegI

namespace Quantum
namespace StabilizerGroup

/--
A CSS Code is a specific type of stabilizer code where the stabilizer group
is generated purely by a set of X-type operators and a set of Z-type operators.
-/
structure CSSCode (n k : ℕ) extends StabilizerCode n k where
  /-- The set of Z-type generators. -/
  ZGens : Finset (NQubitPauliGroupElement n)
  /-- The set of X-type generators. -/
  XGens : Finset (NQubitPauliGroupElement n)

  /-- Every generator in the code's generator list comes from either the Z or X set. -/
  generators_partition :
    ∀ g ∈ generatorsList, g ∈ ZGens ∨ g ∈ XGens

  /-- The union of Z and X generators covers the code's generators. -/
  generators_cover :
    ∀ g, g ∈ ZGens ∨ g ∈ XGens → g ∈ generatorsList

  /-- Every element in the Z generator set is a Z-type element. -/
  z_gen_are_z_type : ∀ g ∈ ZGens, NQubitPauliGroupElement.IsZTypeElement g

  /-- Every element in the X generator set is an X-type element. -/
  x_gen_are_x_type : ∀ g ∈ XGens, NQubitPauliGroupElement.IsXTypeElement g

namespace CSSCode

variable {n k : ℕ}

/-- In a CSS code, all Z generators commute with all X generators.
This follows from the fact that the generators all commute (stabilizer property)
and is the algebraic equivalent of H_X · H_Z^T = 0. -/
theorem z_commutes_x (C : CSSCode n k) :
    ∀ z ∈ C.ZGens, ∀ x ∈ C.XGens, z * x = x * z := by
  intro z hz x hx
  have hz_gen := C.generators_cover z (Or.inl hz)
  have hx_gen := C.generators_cover x (Or.inr hx)
  exact C.generators_commute z hz_gen x hx_gen

/-- In a CSS code, all Z generators commute with each other (since they are all Z-type). -/
theorem z_commutes_z (C : CSSCode n k) :
    ∀ z₁ ∈ C.ZGens, ∀ z₂ ∈ C.ZGens, z₁ * z₂ = z₂ * z₁ := by
  intro z₁ hz₁ z₂ hz₂
  have hz₁_gen := C.generators_cover z₁ (Or.inl hz₁)
  have hz₂_gen := C.generators_cover z₂ (Or.inl hz₂)
  exact C.generators_commute z₁ hz₁_gen z₂ hz₂_gen

/-- In a CSS code, all X generators commute with each other (since they are all X-type). -/
theorem x_commutes_x (C : CSSCode n k) :
    ∀ x₁ ∈ C.XGens, ∀ x₂ ∈ C.XGens, x₁ * x₂ = x₂ * x₁ := by
  intro x₁ hx₁ x₂ hx₂
  have hx₁_gen := C.generators_cover x₁ (Or.inr hx₁)
  have hx₂_gen := C.generators_cover x₂ (Or.inr hx₂)
  exact C.generators_commute x₁ hx₁_gen x₂ hx₂_gen

/-- A CSS code automatically has the no -I property because Z-type
and X-type closures don't produce -I. This follows from the existing
`CSS.negIdentity_not_mem_closure_union` lemma. -/
theorem css_no_negI (C : CSSCode n k) :
    negIdentity n ∉ C.toStabilizerCode.toStabilizerGroup.toSubgroup := by
  exact C.closure_no_neg_identity

end CSSCode

end StabilizerGroup
end Quantum
