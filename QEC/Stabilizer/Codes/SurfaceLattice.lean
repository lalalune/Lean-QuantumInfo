import Mathlib.Tactic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import QEC.Stabilizer.PauliGroup

namespace Quantum
open scoped BigOperators

/-!
# 2D Lattice Structure for Surface/Toric Codes

This file defines the lattice infrastructure for surface and toric codes using
combinatorial edge/vertex/face incidence relations on a periodic square lattice.

The key theorem `star_plaquette_even_overlap` proves that each vertex-face pair
shares exactly 0 or 2 edges, which is the combinatorial reason why X-type star
operators commute with Z-type plaquette operators.
-/

/-- Boundary condition for a 2D lattice. -/
inductive BoundaryCondition where
  | Periodic   -- Toric code
  | Open       -- Surface code (planar)
  deriving DecidableEq, Repr

/-- A vertex on an `L × L` grid. -/
abbrev Vertex (L : ℕ) := Fin L × Fin L

/-- Edge orientation: horizontal or vertical. -/
inductive EdgeDir where
  | Horizontal
  | Vertical
  deriving DecidableEq, Repr

/-- An edge on a periodic lattice, identified by starting vertex and direction. -/
structure PeriodicEdge (L : ℕ) where
  row : Fin L
  col : Fin L
  dir : EdgeDir
  deriving DecidableEq, Repr

/-- A face/plaquette on a periodic lattice, identified by its lower-left vertex. -/
abbrev Face (L : ℕ) := Fin L × Fin L

/-- A 2D square lattice with specified size and boundary conditions. -/
structure SquareLattice where
  L : ℕ
  bc : BoundaryCondition
  hL : 2 ≤ L

namespace SquareLattice

def numVertices (lat : SquareLattice) : ℕ := lat.L * lat.L

def numEdges (lat : SquareLattice) : ℕ :=
  match lat.bc with
  | .Periodic => 2 * lat.L * lat.L
  | .Open => 2 * lat.L * (lat.L - 1)

def numFaces (lat : SquareLattice) : ℕ :=
  match lat.bc with
  | .Periodic => lat.L * lat.L
  | .Open => (lat.L - 1) * (lat.L - 1)

def numQubits (lat : SquareLattice) : ℕ := lat.numEdges

def toricCodeParameters (lat : SquareLattice) (_ : lat.bc = .Periodic) :
    (n : ℕ) × (k : ℕ) × (d : ℕ) :=
  ⟨2 * lat.L * lat.L, 2, lat.L⟩

def surfaceCodeParameters (lat : SquareLattice) (_ : lat.bc = .Open) :
    (n : ℕ) × (k : ℕ) × (d : ℕ) :=
  ⟨2 * lat.L * (lat.L - 1), 1, lat.L⟩

end SquareLattice

namespace PeriodicLattice

variable {L : ℕ}

/-- Successor modulo L. -/
def succMod (i : Fin L) (hL : 0 < L) : Fin L :=
  ⟨(i.val + 1) % L, Nat.mod_lt _ hL⟩

/-- Edge incidence to a vertex on a periodic lattice. -/
def edgeIncident (hL : 0 < L) (e : PeriodicEdge L) (v : Vertex L) : Prop :=
  match e.dir with
  | .Horizontal =>
    (v.1 = e.row ∧ v.2 = e.col) ∨ (v.1 = e.row ∧ v.2 = succMod e.col hL)
  | .Vertical =>
    (v.1 = e.row ∧ v.2 = e.col) ∨ (v.1 = succMod e.row hL ∧ v.2 = e.col)

/-- Edge bounding a face on a periodic lattice. -/
def edgeBoundsFace (hL : 0 < L) (e : PeriodicEdge L) (f : Face L) : Prop :=
  match e.dir with
  | .Horizontal =>
    (e.row = f.1 ∧ e.col = f.2) ∨ (e.row = succMod f.1 hL ∧ e.col = f.2)
  | .Vertical =>
    (e.row = f.1 ∧ e.col = f.2) ∨ (e.row = f.1 ∧ e.col = succMod f.2 hL)

/-- A vertex v is a corner of face f. -/
def isCorner (hL : 0 < L) (v : Vertex L) (f : Face L) : Prop :=
  (v.1 = f.1 ∨ v.1 = succMod f.1 hL) ∧ (v.2 = f.2 ∨ v.2 = succMod f.2 hL)

/-- If an edge is both incident to v and bounds face f, then v is a corner of f. -/
theorem incident_and_bounds_implies_corner (hL : 0 < L)
    (e : PeriodicEdge L) (v : Vertex L) (f : Face L)
    (h_inc : edgeIncident hL e v) (h_bnd : edgeBoundsFace hL e f) :
    isCorner hL v f := by
  unfold isCorner
  cases e.dir <;> simp only [edgeIncident, edgeBoundsFace] at h_inc h_bnd
  · rcases h_inc with ⟨hv1, hv2⟩ | ⟨hv1, hv2⟩ <;> rcases h_bnd with ⟨hr, hc⟩ | ⟨hr, hc⟩
    · exact ⟨Or.inl (hv1 ▸ hr ▸ rfl), Or.inl (hv2 ▸ hc ▸ rfl)⟩
    · exact ⟨Or.inr (hv1 ▸ hr ▸ rfl), Or.inl (hv2 ▸ hc ▸ rfl)⟩
    · exact ⟨Or.inl (hv1 ▸ hr ▸ rfl), Or.inr (hv2 ▸ hc ▸ rfl)⟩
    · exact ⟨Or.inr (hv1 ▸ hr ▸ rfl), Or.inr (hv2 ▸ hc ▸ rfl)⟩
  · rcases h_inc with ⟨hv1, hv2⟩ | ⟨hv1, hv2⟩ <;> rcases h_bnd with ⟨hr, hc⟩ | ⟨hr, hc⟩
    · exact ⟨Or.inl (hv1 ▸ hr ▸ rfl), Or.inl (hv2 ▸ hc ▸ rfl)⟩
    · exact ⟨Or.inl (hv1 ▸ hr ▸ rfl), Or.inr (hv2 ▸ hc ▸ rfl)⟩
    · exact ⟨Or.inr (hv1 ▸ hr ▸ rfl), Or.inl (hv2 ▸ hc ▸ rfl)⟩
    · exact ⟨Or.inr (hv1 ▸ hr ▸ rfl), Or.inr (hv2 ▸ hc ▸ rfl)⟩

/-- For each corner of a face, there is exactly one horizontal edge and one
   vertical edge that are both incident to the corner and bound the face. -/
theorem corner_has_exactly_two_shared_edges (hL : 0 < L)
    (v : Vertex L) (f : Face L) (hc : isCorner hL v f) :
    ∃ eh ev : PeriodicEdge L,
      eh.dir = .Horizontal ∧ ev.dir = .Vertical ∧
      edgeIncident hL eh v ∧ edgeBoundsFace hL eh f ∧
      edgeIncident hL ev v ∧ edgeBoundsFace hL ev f := by
  obtain ⟨hrow, hcol⟩ := hc
  rcases hrow with rfl | rfl <;> rcases hcol with rfl | rfl
  · exact ⟨⟨f.1, f.2, .Horizontal⟩, ⟨f.1, f.2, .Vertical⟩,
      rfl, rfl,
      Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩,
      Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨⟨f.1, f.2, .Horizontal⟩, ⟨f.1, succMod f.2 hL, .Vertical⟩,
      rfl, rfl,
      Or.inr ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩,
      Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩
  · exact ⟨⟨succMod f.1 hL, f.2, .Horizontal⟩, ⟨f.1, f.2, .Vertical⟩,
      rfl, rfl,
      Or.inl ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩,
      Or.inr ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩
  · exact ⟨⟨succMod f.1 hL, f.2, .Horizontal⟩, ⟨f.1, succMod f.2 hL, .Vertical⟩,
      rfl, rfl,
      Or.inr ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩,
      Or.inr ⟨rfl, rfl⟩, Or.inr ⟨rfl, rfl⟩⟩

/-- Same-direction shared edges are unique. -/
theorem shared_edge_unique_per_direction (hL : 2 ≤ L)
    (v : Vertex L) (f : Face L)
    (e₁ e₂ : PeriodicEdge L)
    (h_dir : e₁.dir = e₂.dir)
    (h_inc₁ : edgeIncident (by omega) e₁ v) (h_bnd₁ : edgeBoundsFace (by omega) e₁ f)
    (h_inc₂ : edgeIncident (by omega) e₂ v) (h_bnd₂ : edgeBoundsFace (by omega) e₂ f) :
    e₁ = e₂ := by
  cases h_d : e₁.dir <;> simp [h_d] at h_dir
  · simp only [edgeIncident, h_d, edgeBoundsFace] at h_inc₁ h_bnd₁ h_inc₂ h_bnd₂
    have hr₁ : e₁.row = v.1 := by rcases h_inc₁ with ⟨h, _⟩ | ⟨h, _⟩ <;> exact h.symm
    have hr₂ : e₂.row = v.1 := by
      rw [h_dir] at h_inc₂
      rcases h_inc₂ with ⟨h, _⟩ | ⟨h, _⟩ <;> exact h.symm
    have hc₁ : e₁.col = f.2 := by rcases h_bnd₁ with ⟨_, h⟩ | ⟨_, h⟩ <;> exact h
    have hc₂ : e₂.col = f.2 := by
      rw [h_dir] at h_bnd₂
      rcases h_bnd₂ with ⟨_, h⟩ | ⟨_, h⟩ <;> exact h
    exact PeriodicEdge.ext _ _ (hr₁ ▸ hr₂ ▸ rfl) (hc₁ ▸ hc₂ ▸ rfl) (h_dir ▸ h_d)
  · simp only [edgeIncident, h_d, edgeBoundsFace] at h_inc₁ h_bnd₁ h_inc₂ h_bnd₂
    have hc₁ : e₁.col = v.2 := by rcases h_inc₁ with ⟨_, h⟩ | ⟨_, h⟩ <;> exact h.symm
    have hc₂ : e₂.col = v.2 := by
      rw [h_dir] at h_inc₂
      rcases h_inc₂ with ⟨_, h⟩ | ⟨_, h⟩ <;> exact h.symm
    have hr₁ : e₁.row = f.1 := by rcases h_bnd₁ with ⟨h, _⟩ | ⟨h, _⟩ <;> exact h
    have hr₂ : e₂.row = f.1 := by
      rw [h_dir] at h_bnd₂
      rcases h_bnd₂ with ⟨h, _⟩ | ⟨h, _⟩ <;> exact h
    exact PeriodicEdge.ext _ _ (hr₁ ▸ hr₂ ▸ rfl) (hc₁ ▸ hc₂ ▸ rfl) (h_dir ▸ h_d)

/-- **Main theorem**: A vertex and face on a periodic square lattice share exactly
   0 or 2 edges. X-type star operators always commute with Z-type plaquette
   operators since an even number of anticommutations produces net commutation. -/
theorem star_plaquette_even_overlap (hL : 2 ≤ L)
    (v : Vertex L) (f : Face L) :
    (∀ e : PeriodicEdge L,
      ¬(edgeIncident (by omega) e v ∧ edgeBoundsFace (by omega) e f)) ∨
    (∃ eh ev : PeriodicEdge L,
      eh.dir = .Horizontal ∧ ev.dir = .Vertical ∧
      edgeIncident (by omega) eh v ∧ edgeBoundsFace (by omega) eh f ∧
      edgeIncident (by omega) ev v ∧ edgeBoundsFace (by omega) ev f ∧
      ∀ e₃ : PeriodicEdge L,
        edgeIncident (by omega) e₃ v → edgeBoundsFace (by omega) e₃ f →
        e₃ = eh ∨ e₃ = ev) := by
  by_cases h : ∃ e, edgeIncident (by omega) e v ∧ edgeBoundsFace (by omega) e f
  · right
    obtain ⟨e₀, h_inc₀, h_bnd₀⟩ := h
    have hc := incident_and_bounds_implies_corner (by omega) e₀ v f h_inc₀ h_bnd₀
    obtain ⟨eh, ev, heh_dir, hev_dir, heh_inc, heh_bnd, hev_inc, hev_bnd⟩ :=
      corner_has_exactly_two_shared_edges (by omega) v f hc
    exact ⟨eh, ev, heh_dir, hev_dir, heh_inc, heh_bnd, hev_inc, hev_bnd,
      fun e₃ h_inc₃ h_bnd₃ => by
        cases h_dir₃ : e₃.dir
        · left
          exact shared_edge_unique_per_direction hL v f e₃ eh
            (by rw [h_dir₃, heh_dir]) h_inc₃ h_bnd₃ heh_inc heh_bnd
        · right
          exact shared_edge_unique_per_direction hL v f e₃ ev
            (by rw [h_dir₃, hev_dir]) h_inc₃ h_bnd₃ hev_inc hev_bnd⟩
  · left
    push_neg at h
    exact h

end PeriodicLattice

end Quantum
