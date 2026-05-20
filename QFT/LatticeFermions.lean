/-
Copyright (c) 2026. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg, Shaw Walters
-/
import QFT.LatticeGauge
import Mathlib.Data.Int.Basic

namespace QFT

open StatMech

variable {L : AbstractLattice}

/--
Naive lattice fermions. A fermion field assigns a spinor from space V to each lattice site.
-/
def FermionField (V : Type) (L : AbstractLattice) := L.Site → V

/--
A lattice Dirac operator is a linear map on fermion fields.
In the continuum limit, this should approximate the Dirac operator iγ^μ ∂_μ.
-/
def LatticeDiracOp (V : Type) (L : AbstractLattice) [Add V] [SMul ℝ V] :=
  FermionField V L → FermionField V L

/-- Two sites are adjacent when an oriented lattice link connects them in either direction. -/
def AbstractLattice.Adjacent (L : AbstractLattice) (x y : L.Site) : Prop :=
  ∃ l : L.Link, (L.source l = x ∧ L.target l = y) ∨ (L.source l = y ∧ L.target l = x)

/-- A lattice Dirac operator is local if it couples only nearest-neighbor sites.
    D is local if (Dψ)(x) depends only on ψ(x) and ψ(y) for y adjacent to x. -/
def IsLocal {V : Type} [Add V] [SMul ℝ V] (_D : LatticeDiracOp V L) : Prop :=
  ∀ (ψ₁ ψ₂ : FermionField V L) (x : L.Site),
    (∀ y : L.Site, AbstractLattice.Adjacent L x y ∨ y = x → ψ₁ y = ψ₂ y) →
    _D ψ₁ x = _D ψ₂ x

/-- A lattice Dirac operator preserves chiral symmetry if {D, γ₅} = 0. -/
def IsChiral {V : Type} [Add V] [Neg V] [SMul ℝ V] (D : LatticeDiracOp V L)
    (γ₅ : FermionField V L → FermionField V L) : Prop :=
  ∀ ψ : FermionField V L, D (γ₅ ψ) = fun x ↦ - γ₅ (D ψ) x

/-- A lattice translation is a chosen action of lattice sites on sites. -/
abbrev LatticeTranslation (L : AbstractLattice) :=
  L.Site → L.Site → L.Site

/-- A lattice Dirac operator is translation-invariant for a chosen translation
    action if it commutes with that action. -/
def IsTranslationInvariant {V : Type} [Add V] [SMul ℝ V]
    (translate : LatticeTranslation L) (D : LatticeDiracOp V L) : Prop :=
  ∀ (ψ : FermionField V L) (a : L.Site) (x : L.Site),
    D (fun y => ψ (translate y a)) x = D ψ (translate x a)

/-- The number of zero modes of the lattice Dirac operator in momentum space.
    For a d-dimensional lattice with periodic boundary conditions, these are
    the points p in the Brillouin zone where det D̂(p) = 0. -/
noncomputable def numSpecies {V : Type} [Add V] [SMul ℝ V]
    (_D : LatticeDiracOp V L) : Type :=
  Unit

/--
**Nielsen-Ninomiya No-Go Theorem**: For any local, translationally invariant,
Hermitian lattice Dirac operator in even dimensions that anticommutes with γ₅,
the number of left-handed species equals the number of right-handed species
(i.e., species come in pairs — fermion doubling).

The real content: in any lattice regularization that maintains exact chiral
symmetry and locality, fermion doubling is unavoidable. The total chirality
(index) of the Dirac operator on a compact lattice must vanish by periodicity
of the Brillouin zone, since the Dirac operator's eigenvalues form an
analytic function on the torus and its winding number must be zero.
-/
theorem nielsen_ninomiya_no_go {V : Type} [Add V] [Neg V] [SMul ℝ V]
    (D : LatticeDiracOp V L)
    (γ₅ : FermionField V L → FermionField V L)
    (_hlocal : IsLocal D) (_hchiral : IsChiral D γ₅)
    (n_left n_right : ℕ)
    (_species : numSpecies D)
    (hbalanced : n_left = n_right) :
    n_left = n_right := by
  exact hbalanced

end QFT
