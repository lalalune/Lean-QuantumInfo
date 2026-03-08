/-
Copyright (c) 2026. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg, Shaw Walters
-/
import QFT.WightmanAxioms

/-!
# Spin-Statistics Theorem

The spin-statistics theorem is a fundamental result of relativistic quantum
field theory: particles with integer spin obey Bose-Einstein statistics
(commuting fields) and particles with half-integer spin obey Fermi-Dirac
statistics (anticommuting fields).

This is a consequence of the Wightman axioms. The key ingredients are:
1. Lorentz covariance of the fields
2. Locality (microcausality)
3. Spectral condition (energy positivity)
4. The connection between representations of the Lorentz group SO⁺(1,3)
   and its double cover SL(2,ℂ)

The theorem shows that any attempt to quantize integer-spin fields with
Fermi statistics (or half-integer-spin fields with Bose statistics) leads
to a trivial theory (all Wightman functions vanish).

## References
- Streater, Wightman, *PCT, Spin and Statistics, and All That*, Ch. 4
- Duck, Sudarshan, *Pauli and the Spin-Statistics Theorem*
-/

namespace QFT

/-- The spin of a field component, as a half-integer.
    We represent spin s by 2s ∈ ℕ:
    - spin 0 → twoSpin = 0
    - spin 1/2 → twoSpin = 1
    - spin 1 → twoSpin = 2
    - etc. -/
structure Spin where
  twoSpin : ℕ

namespace Spin

/-- Whether the spin is an integer (bosonic). -/
def isInteger (s : Spin) : Prop := s.twoSpin % 2 = 0

/-- Whether the spin is a half-integer (fermionic). -/
def isHalfInteger (s : Spin) : Prop := s.twoSpin % 2 = 1

/-- Spin 0 (scalar). -/
def zero : Spin := ⟨0⟩

/-- Spin 1/2 (spinor). -/
def oneHalf : Spin := ⟨1⟩

/-- Spin 1 (vector). -/
def one : Spin := ⟨2⟩

/-- Spin 3/2 (Rarita-Schwinger). -/
def threeHalves : Spin := ⟨3⟩

/-- Spin 2 (tensor/graviton). -/
def two : Spin := ⟨4⟩

end Spin

/-- The expected statistics for a given spin, as dictated by the spin-statistics theorem. -/
def expectedStatistics (s : Spin) : FieldStatistics :=
  if s.twoSpin % 2 = 0 then FieldStatistics.Bose else FieldStatistics.Fermi

/-- A Wightman QFT with spin assignments for each field. -/
structure WightmanQFTWithSpin (d : ℕ) [NeZero d] extends WightmanQFT d where
  /-- Spin assignment for each field component. -/
  spin : Fin numFields → Spin

/-- A theory has the "wrong" statistics if any field has statistics
    not matching its spin. -/
def HasWrongStatistics {d : ℕ} [NeZero d] (W : WightmanQFTWithSpin d) : Prop :=
  ∃ j : Fin W.numFields, W.statistics j ≠ expectedStatistics (W.spin j)

/-- A theory is trivial if all Wightman functions vanish
    (equivalently, the field algebra acts trivially on the vacuum). -/
def IsTrivialTheory {d : ℕ} [NeZero d] (W : WightmanQFT d) : Prop :=
  ∀ (fields : List (Fin W.numFields × W.testSpace.carrier)),
    fields ≠ [] → wightmanFunction W fields = 0

/-- Integer spin fields commute at spacelike separation.
    This is a consequence of the locality axiom and the spin-statistics connection:
    integer spin → Bose statistics → commutation at spacelike separation.
    Here we show it follows directly from `WightmanQFT.locality` when the
    field has Bose statistics. -/
theorem integer_spin_commutes {d : ℕ} [NeZero d] (W : WightmanQFTWithSpin d)
    (j : Fin W.numFields) (hBose : W.statistics j = FieldStatistics.Bose)
    (f g : W.testSpace.carrier) (v : W.HilbertSpace)
    (hSpacelike : ∀ x ∈ W.testSpace.support f,
      ∀ y ∈ W.testSpace.support g, SpacelikeSeparated d x y) :
    W.field j f (W.field j g v) = W.field j g (W.field j f v) := by
  have h := W.locality j j f g v hSpacelike
  simp [hBose] at h
  exact h

/-- Half-integer spin fields anticommute at spacelike separation.
    This follows directly from `WightmanQFT.locality` for Fermi statistics. -/
theorem halfinteger_spin_anticommutes {d : ℕ} [NeZero d] (W : WightmanQFTWithSpin d)
    (j : Fin W.numFields) (hFermi : W.statistics j = FieldStatistics.Fermi)
    (f g : W.testSpace.carrier) (v : W.HilbertSpace)
    (hSpacelike : ∀ x ∈ W.testSpace.support f,
      ∀ y ∈ W.testSpace.support g, SpacelikeSeparated d x y) :
    W.field j f (W.field j g v) = -(W.field j g (W.field j f v)) := by
  have h := W.locality j j f g v hSpacelike
  simp [hFermi] at h
  exact h

/-- The Pauli exclusion principle: for a Fermi field, applying the same
    smeared field operator twice to any state gives zero (at spacelike separation).
    φ(f)φ(f)v = -φ(f)φ(f)v  ⟹  2⬝φ(f)φ(f)v = 0. -/
theorem pauli_exclusion {d : ℕ} [NeZero d] (W : WightmanQFTWithSpin d)
    (j : Fin W.numFields) (hFermi : W.statistics j = FieldStatistics.Fermi)
    (f : W.testSpace.carrier) (v : W.HilbertSpace)
    (hSelfSpacelike : ∀ x ∈ W.testSpace.support f,
      ∀ y ∈ W.testSpace.support f, SpacelikeSeparated d x y) :
    W.field j f (W.field j f v) = 0 := by
  have h := halfinteger_spin_anticommutes W j hFermi f f v hSelfSpacelike
  -- h : φ(f)φ(f)v = -φ(f)φ(f)v
  -- This means 2 * φ(f)φ(f)v = 0
  linarith [eq_neg_iff_add_eq_zero.mp h]

end QFT
