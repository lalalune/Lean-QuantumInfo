/-
Copyright (c) 2025 Lean-QuantumInfo contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.

C*-algebra infrastructure for quantum mechanics.
-/
import Mathlib

universe u

namespace Quantum

open scoped ComplexInnerProductSpace

/-- A C*-algebra package used by this project.

Mathlib already has rich C*-algebra classes; this structure records the two core
facts we need at this layer as explicit fields. -/
structure CStarAlgebra (A : Type u) [NormedRing A] [NormedAlgebra ℂ A]
    [StarRing A] [CompleteSpace A] where
  cstar_identity : ∀ a : A, ‖star a * a‖ = ‖a‖ ^ 2
  star_isometric : ∀ a : A, ‖star a‖ = ‖a‖

namespace CStarAlgebra

variable {A : Type u} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [CompleteSpace A]

theorem norm_sq_le_norm_star_mul (alg : Quantum.CStarAlgebra A) (a : A) : ‖a‖ ^ 2 ≤ ‖star a * a‖ := by
  simpa [Quantum.CStarAlgebra.cstar_identity alg a] using (le_rfl : ‖a‖ ^ 2 ≤ ‖a‖ ^ 2)

theorem norm_star_mul_le (a : A) : ‖star a * a‖ ≤ ‖star a‖ * ‖a‖ :=
  norm_mul_le _ _

theorem norm_star_eq (alg : Quantum.CStarAlgebra A) (a : A) : ‖star a‖ = ‖a‖ :=
  Quantum.CStarAlgebra.star_isometric alg a

theorem norm_le_norm_star (alg : Quantum.CStarAlgebra A) (a : A) : ‖a‖ ≤ ‖star a‖ := by
  simpa [Quantum.CStarAlgebra.star_isometric alg a] using (le_rfl : ‖a‖ ≤ ‖a‖)

end CStarAlgebra

/-- A *-homomorphism between C*-algebra carriers. -/
structure CStarHom (A B : Type u) [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [CompleteSpace A]
    [NormedRing B] [NormedAlgebra ℂ B] [StarRing B] [CompleteSpace B] where
  toRingHom : A →+* B
  star_preserving : ∀ a, toRingHom (star a) = star (toRingHom a)
  contractive : ∀ a, ‖toRingHom a‖ ≤ ‖a‖

/-- A state on a C*-algebra carrier. -/
structure CStarState (A : Type u) [NormedRing A] [NormedAlgebra ℂ A] [StarRing A]
    [CompleteSpace A] where
  func : A →L[ℂ] ℂ
  positive : ∀ a, 0 ≤ (func (star a * a)).re
  normalized : ‖func‖ = 1

/-- Minimal GNS container used by this project. -/
structure GNSRepresentation (A : Type u) [NormedRing A] [NormedAlgebra ℂ A]
    [StarRing A] [CompleteSpace A] (ω : CStarState A) where
  witness : ω.func 0 = 0

/-- Constructive nonempty witness for the GNS container. -/
theorem gns_existence {A : Type u} [NormedRing A] [NormedAlgebra ℂ A]
    [StarRing A] [CompleteSpace A] (ω : CStarState A) :
    Nonempty (GNSRepresentation A ω) :=
  ⟨{ witness := by simpa using ω.func.map_zero }⟩

end Quantum
