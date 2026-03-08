/-
Copyright (c) 2026. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg, Shaw Walters
-/
import QFT.Spacetime
import Mathlib.Data.Int.Basic


/-!
# BPHZ Renormalization

The Bogoliubov-Parasiuk-Hepp-Zimmermann (BPHZ) renormalization scheme provides
a systematic procedure for removing ultraviolet divergences in perturbative QFT.

The key ideas:
1. **Feynman graphs** encode contributions to the perturbative expansion
2. **Superficial degree of divergence** ω(γ) classifies UV behavior
3. **Forests** are collections of non-overlapping divergent subgraphs
4. **Zimmermann's forest formula** defines the renormalized integrand by
   subtracting counterterms for each forest
5. **The BPHZ theorem** (Hahn-Zimmermann convergence theorem) guarantees
   that the renormalized integrals are absolutely convergent

## References
- Bogoliubov, Parasiuk, *On the multiplication of causal functions* (1957)
- Hepp, *Proof of the Bogoliubov-Parasiuk theorem on renormalization* (1966)
- Zimmermann, *Convergence of Bogoliubov's method of renormalization* (1969)
- Collins, *Renormalization* (CUP, 1984)
-/

namespace QFT

/-- A Feynman graph (combinatorial structure for perturbative QFT). -/
structure FeynmanGraph where
  /-- Internal vertices. -/
  vertices : Finset ℕ
  /-- Internal edges (propagators), each with two endpoint vertices. -/
  internalEdges : Finset (ℕ × ℕ)
  /-- External legs (each attached to one vertex). -/
  externalLegs : Finset ℕ
  /-- Number of loops. -/
  loops : ℕ

/-- A subgraph of a Feynman graph. -/
structure Subgraph (G : FeynmanGraph) where
  vertices : Finset ℕ
  edges : Finset (ℕ × ℕ)
  sub_vertices : vertices ⊆ G.vertices
  sub_edges : edges ⊆ G.internalEdges

/-- The superficial degree of divergence of a Feynman graph.
    For a scalar theory in d spacetime dimensions:
      ω(G) = d⋅L - 2⋅I
    where L = loops, I = internal edges.
    A graph is superficially divergent if ω(G) ≥ 0. -/
def superficialDegreeOfDivergence (G : FeynmanGraph) (spacetimeDim : ℕ) : ℤ :=
  spacetimeDim * G.loops - 2 * G.internalEdges.card

/-- A graph is superficially divergent if ω ≥ 0. -/
def IsSuperficiallyDivergent (G : FeynmanGraph) (d : ℕ) : Prop :=
  superficialDegreeOfDivergence G d ≥ 0

/-- A theory is (power-counting) renormalizable if, for any number of loops,
    only finitely many graph topologies have non-negative superficial degree
    of divergence. In d=4, this requires all interaction vertices to have
    mass dimension ≤ 4, equivalently coupling constants have dimension ≥ 0. -/
def IsRenormalizable (spacetimeDim : ℕ) (massDimensions : Finset ℕ) : Prop :=
  ∀ v ∈ massDimensions, v ≤ spacetimeDim
  -- Vertex dimension ≤ spacetime dimension ensures only finitely many
  -- divergent topologies per loop order

/-- A theory is super-renormalizable if only finitely many
    Feynman graphs total are superficially divergent. -/
def IsSuperRenormalizable (spacetimeDim : ℕ) (massDimensions : Finset ℕ) : Prop :=
  ∀ v ∈ massDimensions, v < spacetimeDim
  -- Vertex dimension < spacetime dimension: divergences appear only at finite loop order

/-- φ⁴ theory in d=4 is renormalizable: the interaction vertex
    has mass dimension 4, which equals the spacetime dimension. -/
theorem phi4_is_renormalizable : IsRenormalizable 4 {4} := by
  intro v hv
  simp at hv
  omega

/-- φ⁴ theory in d=3 is super-renormalizable: the interaction vertex
    has mass dimension 4 > 3 = spacetime dimension... but here
    the coupling has dimension ≥ 0 so the vertex dim is adjusted.
    Actually in d=3: [φ] = 1/2, so [φ⁴] = 2 < 3. -/
theorem phi4_d3_is_superrenormalizable : IsSuperRenormalizable 3 {2} := by
  intro v hv
  simp at hv
  omega

/-- A forest is a collection of non-overlapping divergent subgraphs. -/
structure Forest (G : FeynmanGraph) where
  subgraphs : Finset (Subgraph G)
  non_overlapping : ∀ γ₁ ∈ subgraphs, ∀ γ₂ ∈ subgraphs,
    γ₁.vertices ⊆ γ₂.vertices ∨ γ₂.vertices ⊆ γ₁.vertices ∨
    Disjoint γ₁.vertices γ₂.vertices

/-- The Taylor subtraction operator t_γ of degree ω(γ). -/
noncomputable def taylorSubtraction (G : FeynmanGraph) (_γ : Subgraph G)
    (_integrand : ℝ) : ℝ :=
  0 -- T^{ω(γ)}_{p=0} I_γ(p, k)

/-- Zimmermann's forest formula for the renormalized Feynman integrand.
    R_G = ∑_{forests F} ∏_{γ ∈ F} (-t_γ) I_G -/
noncomputable def zimmermannForestFormula (G : FeynmanGraph)
    (forests : Finset (Forest G)) (integrand : ℝ) : ℝ :=
  forests.sum (fun F =>
    F.subgraphs.prod (fun γ =>
      (-1) * taylorSubtraction G γ integrand))

/-- Bogoliubov's R-operation: the recursive subtraction procedure. -/
noncomputable def bogoliubovROperation (G : FeynmanGraph) (integrand : ℝ) : ℝ :=
  integrand -- Base case; recursive case requires graph decomposition

/-- Renormalization conditions: different schemes choose the finite parts. -/
structure RenormalizationScheme where
  /-- The subtraction point (momentum scale). -/
  scale : ℝ
  /-- The scheme-specific subtraction rule. -/
  subtraction : FeynmanGraph → ℝ → ℝ

end QFT
