import Mathlib
import QFT.Spacetime

/-!
# Algebraic quantum field theory

This file adds the reusable Haag-Kastler net layer from `physicslib4`, adapted
to the local `QFT.Spacetime` definitions instead of duplicating Minkowski
space.  Regions are bounded open subsets of four-dimensional spacetime, and a
net assigns a C*-algebra of observables to every region functorially with
respect to inclusion.
-/

namespace QFT

noncomputable section

open Set

/-- A bounded open region of four-dimensional Minkowski spacetime. -/
structure Region where
  carrier : Set (Fin 4 → ℝ)
  isOpen : IsOpen carrier
  compact_closure : IsCompact (closure carrier)

namespace Region

instance : Coe Region (Set (Fin 4 → ℝ)) :=
  ⟨Region.carrier⟩

end Region

/-- Two regions are spacelike separated when every difference vector between
their points is spacelike. -/
def SpacelikeSeparatedRegions (B₁ B₂ : Region) : Prop :=
  ∀ x ∈ (B₁ : Set (Fin 4 → ℝ)), ∀ y ∈ (B₂ : Set (Fin 4 → ℝ)),
    SpacelikeSeparated 4 x y ∧ SpacelikeSeparated 4 y x

/-- Spacelike separation of regions is symmetric. -/
theorem spacelikeSeparatedRegions_symm {B₁ B₂ : Region} :
    SpacelikeSeparatedRegions B₁ B₂ ↔ SpacelikeSeparatedRegions B₂ B₁ := by
  constructor
  · intro h x hx y hy
    exact ⟨(h y hy x hx).2, (h y hy x hx).1⟩
  · intro h x hx y hy
    exact ⟨(h y hy x hx).2, (h y hy x hx).1⟩

/-- A Haag-Kastler-style net of local observable algebras.

The field `map` is the isotony morphism associated to a region inclusion, and
`map_id`/`map_comp` record the functor laws for the region poset.
-/
structure LocalNet where
  A : Region → Type _
  [A_semiring : ∀ R, Semiring (A R)]
  [A_algebra : ∀ R, Algebra ℂ (A R)]
  [A_star : ∀ R, Star (A R)]
  [A_cstar : ∀ R, CStarAlgebra (A R)]
  map : ∀ {R S : Region}, Region.carrier R ⊆ Region.carrier S →
    StarAlgHom ℂ (A R) (A S)
  map_id : ∀ R, map (R := R) (S := R) (Subset.refl (Region.carrier R)) =
    StarAlgHom.id ℂ (A R)
  map_comp :
    ∀ {R S T : Region}
      (hRS : Region.carrier R ⊆ Region.carrier S)
      (hST : Region.carrier S ⊆ Region.carrier T),
        map (Subset.trans hRS hST) = (map hST).comp (map hRS)

namespace LocalNet

attribute [instance] LocalNet.A_semiring LocalNet.A_algebra LocalNet.A_star LocalNet.A_cstar

variable (N : LocalNet)

/-- The isotony map for an inclusion `R ⊆ S`. -/
def isotony (N : LocalNet) {R S : Region} (h : Region.carrier R ⊆ Region.carrier S) :
    StarAlgHom ℂ (N.A R) (N.A S) :=
  N.map h

@[simp] theorem isotony_refl (R : Region) :
    N.isotony (Subset.refl (Region.carrier R)) = StarAlgHom.id ℂ (N.A R) :=
  LocalNet.map_id N R

theorem isotony_comp {R S T : Region}
    (hRS : Region.carrier R ⊆ Region.carrier S)
    (hST : Region.carrier S ⊆ Region.carrier T) :
    N.isotony (Subset.trans hRS hST) = (N.isotony hST).comp (N.isotony hRS) :=
  LocalNet.map_comp N hRS hST

end LocalNet

/-- A minimal bundled quasilocal algebra associated to a local net. -/
structure QuasiLocal (N : LocalNet) where
  quasilocal : Type _
  [quasi_semiring : Semiring quasilocal]
  [quasi_algebra : Algebra ℂ quasilocal]
  [quasi_star : Star quasilocal]
  [quasi_cstar : CStarAlgebra quasilocal]
  ι : ∀ R : Region, StarAlgHom ℂ (N.A R) quasilocal
  dense_union : Prop

namespace QuasiLocal

attribute [instance] QuasiLocal.quasi_semiring QuasiLocal.quasi_algebra QuasiLocal.quasi_star
  QuasiLocal.quasi_cstar

end QuasiLocal

end

end QFT
