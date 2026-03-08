/-
Copyright (c) 2026. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg, Shaw Walters
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.List.Basic

namespace StatMech

/-- 
An abstract lattice defined by its sites, oriented links, and plaquettes.
This structure is generic enough to support arbitrary graphs, but includes
plaquettes which are necessary for lattice gauge theory.
-/
structure AbstractLattice where
  Site : Type
  siteFintype : Fintype Site
  
  -- Links are directed
  Link : Type
  linkFintype : Fintype Link
  
  source : Link → Site
  target : Link → Site
  
  -- Each link has an opposite link
  rev : Link → Link
  rev_rev : ∀ l, rev (rev l) = l
  rev_source : ∀ l, source (rev l) = target l
  rev_target : ∀ l, target (rev l) = source l
  no_self_rev : ∀ l, rev l ≠ l
  
  -- Plaquettes (faces)
  Plaquette : Type
  plaqFintype : Fintype Plaquette
  
  -- The boundary of a plaquette is a list of oriented links
  boundary : Plaquette → List Link

instance AbstractLattice.instSiteFintype (L : AbstractLattice) : Fintype L.Site := L.siteFintype
instance AbstractLattice.instLinkFintype (L : AbstractLattice) : Fintype L.Link := L.linkFintype
instance AbstractLattice.instPlaqFintype (L : AbstractLattice) : Fintype L.Plaquette := L.plaqFintype

end StatMech
