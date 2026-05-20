import Mathlib

/-!
# Vertex colorings and perfect matchings on `Sym2`

This file collects a small reusable core from
`bafflingbits/graph_vcweight`: finite vertex colorings, symmetric edge
weights on unordered pairs, and perfect matchings represented as finite sets
of `Sym2` edges.
-/

open Classical
open scoped BigOperators

namespace Sym2

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {C : Type*} [Fintype C] [DecidableEq C]

/-- A vertex coloring assigns a color to each vertex. -/
abbrev Coloring (V C : Type*) :=
  V → C

/-- An edge weight function assigns a complex weight to each ordered edge and
the endpoint colors. -/
abbrev EdgeWeight (V C : Type*) :=
  V → V → C → C → ℂ

/-- An edge weight function is symmetric under swapping endpoints and colors. -/
def IsSymmetricWeight (w : EdgeWeight V C) : Prop :=
  ∀ v₁ v₂ c₁ c₂, w v₁ v₂ c₁ c₂ = w v₂ v₁ c₂ c₁

/-- The weight of a particular ordered edge under a coloring. -/
noncomputable def edgeWeightPair (w : EdgeWeight V C) (x : Coloring V C) (u v : V) : ℂ :=
  w u v (x u) (x v)

omit [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C] in
lemma edgeWeightPair_symm {w : EdgeWeight V C} (hw : IsSymmetricWeight w)
    (x : Coloring V C) (u v : V) :
    edgeWeightPair w x u v = edgeWeightPair w x v u := by
  dsimp [edgeWeightPair]
  exact hw u v (x u) (x v)

/-- A symmetric edge weight as a function on unordered pairs. -/
noncomputable def edgeWeight (w : EdgeWeight V C) (hw : IsSymmetricWeight w)
    (x : Coloring V C) : Sym2 V → ℂ :=
  Sym2.lift ⟨edgeWeightPair w x, edgeWeightPair_symm hw x⟩

/-- A monochrome coloring assigns the same color to every vertex. -/
def IsMonochrome (x : Coloring V C) : Prop :=
  ∀ u v : V, x u = x v

/-- The constant coloring assigning a fixed color to every vertex. -/
noncomputable def monoColoring (a : C) : Coloring V C :=
  fun _ ↦ a

omit [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C] in
lemma isMonochrome_monoColoring (a : C) :
    IsMonochrome (monoColoring a : Coloring V C) := by
  intro u v
  rfl

/-- A perfect matching on a vertex set `U`: every vertex in `U` is incident to
exactly one edge in `M`, all edge endpoints lie in `U`, and there are no
self-loops. -/
def IsPerfectMatchingOn (U : Finset V) (M : Finset (Sym2 V)) : Prop :=
  (∀ v ∈ U, ∃! e, e ∈ M ∧ v ∈ e) ∧
    (∀ e ∈ M, ∀ v, v ∈ e → v ∈ U) ∧
      (∀ v : V, _root_.Sym2.mk v v ∉ M)

/-- The finite set of all perfect matchings on a vertex set `U`. -/
noncomputable def perfectMatchingsOn (U : Finset V) : Finset (Finset (Sym2 V)) :=
  (Finset.univ : Finset (Sym2 V)).powerset.filter fun M ↦ IsPerfectMatchingOn U M

/-- A perfect matching on the full finite vertex set. -/
def IsPerfectMatching (M : Finset (Sym2 V)) : Prop :=
  IsPerfectMatchingOn Finset.univ M

/-- The finite set of all perfect matchings on the full finite vertex set. -/
noncomputable def perfectMatchings (V : Type*) [Fintype V] [DecidableEq V] :
    Finset (Finset (Sym2 V)) :=
  perfectMatchingsOn Finset.univ

/-- The perfect-matching amplitude restricted to a vertex subset. -/
noncomputable def matchingAmplitudeOn (U : Finset V) (w : EdgeWeight V C)
    (hw : IsSymmetricWeight w) (x : Coloring V C) : ℂ :=
  ∑ P ∈ perfectMatchingsOn U, ∏ e ∈ P, edgeWeight w hw x e

/-- The full perfect-matching amplitude. -/
noncomputable def matchingAmplitude (w : EdgeWeight V C) (hw : IsSymmetricWeight w)
    (x : Coloring V C) : ℂ :=
  matchingAmplitudeOn Finset.univ w hw x

end Sym2
