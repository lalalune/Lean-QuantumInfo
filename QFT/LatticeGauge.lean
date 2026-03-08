/-
Copyright (c) 2026. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg, Shaw Walters
-/
import StatMech.Lattice
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace QFT

open StatMech
open scoped BigOperators

variable {L : AbstractLattice}

/-- 
A gauge field U assigns a unitary element of a gauge group G to each link.
For simplicity, we model a gauge theory where the gauge group is G.
-/
def GaugeField (G : Type) [Group G] (L : AbstractLattice) := L.Link → G

/-- The Wilson action expects U(-μ) = U(μ)⁻¹. -/
def IsValidGaugeField {G : Type} [Group G] (U : GaugeField G L) : Prop :=
  ∀ l : L.Link, U (L.rev l) = (U l)⁻¹

/-- The ordered product of gauge links along a path (list of links). -/
def pathOrderedProduct {G : Type} [Group G] (U : GaugeField G L) : List L.Link → G
  | [] => 1
  | (l :: ls) => U l * pathOrderedProduct U ls

/-- The Wilson loop observable corresponding to a path. -/
def wilsonLoop {G : Type} [Group G] (U : GaugeField G L) (path : List L.Link) : G :=
  pathOrderedProduct U path

/-- The plaquette variable U_P is the path ordered product around a plaquette's boundary. -/
def plaquetteVar {G : Type} [Group G] (U : GaugeField G L) (p : L.Plaquette) : G :=
  pathOrderedProduct U (L.boundary p)

/-- 
The Wilson action for a gauge configuration U, given a character abstract function χ.
S_W = β ∑_P (1 - χ(U_P) / χ(1))
-/
noncomputable def wilsonAction {G : Type} [Group G] [Fintype L.Plaquette]
    (χ : G → ℝ) (β : ℝ) (U : GaugeField G L) : ℝ :=
  Finset.univ.sum (fun p : L.Plaquette => 1 - χ (plaquetteVar U p) / χ 1)

/-- 
Kogut-Susskind Hamiltonian abstract formulation.
For a continuous-time formulation, the Hamiltonian has an electric piece
E^2 defined on links and a magnetic piece (plaquette).
-/
noncomputable def kogutSusskindHamiltonian {G : Type} [Group G] {H : Type}
    [Fintype L.Link] [Fintype L.Plaquette]
    (electricTerm : L.Link → G → H → ℝ)
    (χ : G → ℝ) (β : ℝ) (U : GaugeField G L) (E_field : L.Link → H) : ℝ :=
  let electric := Finset.univ.sum (fun l : L.Link => electricTerm l (U l) (E_field l))
  let magnetic := Finset.univ.sum (fun p : L.Plaquette => 1 - χ (plaquetteVar U p) / χ 1)
  electric + β * magnetic
  
end QFT
