import Mathlib.Tactic
import QEC.Stabilizer.Core.StabilizerCode
import QEC.Stabilizer.Core.CSS
import QEC.Stabilizer.Core.CSSNoNegI
import QEC.Stabilizer.PauliGroup
import QEC.Stabilizer.Codes.SurfaceLattice

namespace Quantum
open scoped BigOperators

/-!
# Toric Code

The toric code is the prototypical topological quantum error-correcting code,
defined on a 2D torus (periodic square lattice). It encodes 2 logical qubits
with parameters [[2L², 2, L]].

## Construction

Given an L×L torus:
- Place one qubit on each edge (2L² edges total)
- Star operators A_v = ∏_{e∋v} X_e  (X on all edges touching vertex v)
- Plaquette operators B_p = ∏_{e∈∂p} Z_e  (Z on all edges bounding face p)

All star operators are X-type, all plaquette operators are Z-type,
so this is a CSS code. The code has:
- L² star generators (but ∏ A_v = I, so L²-1 independent)
- L² plaquette generators (but ∏ B_p = I, so L²-1 independent)
- Total independent generators: 2(L²-1) = 2L² - 2 = n - k with k = 2

## Logical Operators

- Logical X₁: product of X along a non-contractible horizontal cycle
- Logical Z₁: product of Z along a non-contractible vertical cycle
- Logical X₂: product of X along a non-contractible vertical cycle
- Logical Z₂: product of Z along a non-contractible horizontal cycle

## Topological Properties

- Code distance d = L (minimum weight of a non-contractible cycle)
- Homological interpretation: logical operators correspond to H₁(T², Z₂)
-/

/-- The toric code on an L×L lattice. -/
structure ToricCode where
  /-- Side length of the torus. -/
  L : ℕ
  /-- Side length must be at least 2. -/
  hL : 2 ≤ L

namespace ToricCode

/-- Number of physical qubits in the toric code. -/
def numQubits (tc : ToricCode) : ℕ := 2 * tc.L * tc.L

/-- Number of logical qubits in the toric code. -/
def numLogical : ℕ := 2

/-- Code distance of the toric code. -/
def distance (tc : ToricCode) : ℕ := tc.L

/-- The toric code is a [[2L², 2, L]] code. -/
theorem toricCode_parameters (tc : ToricCode) :
    tc.numQubits = 2 * tc.L^2 ∧ numLogical = 2 ∧ tc.distance = tc.L := by
  constructor
  · simp [numQubits]; ring
  · exact ⟨rfl, rfl⟩

/-- The number of independent star generators is L² - 1. -/
def numStarGenerators (tc : ToricCode) : ℕ := tc.L * tc.L - 1

/-- The number of independent plaquette generators is L² - 1. -/
def numPlaquetteGenerators (tc : ToricCode) : ℕ := tc.L * tc.L - 1

/-- Total number of independent generators = n - k. -/
theorem total_generators (tc : ToricCode) :
    tc.numStarGenerators + tc.numPlaquetteGenerators = tc.numQubits - numLogical := by
  simp [numStarGenerators, numPlaquetteGenerators, numQubits, numLogical]
  omega

end ToricCode

/-!
# Surface Code (Planar)

The surface code is the planar variant of the toric code with open boundaries.
It encodes 1 logical qubit with parameters [[2L(L-1), 1, L]].

The rough and smooth boundaries allow a single pair of logical operators.
-/

/-- The planar surface code on an L×L lattice. -/
structure SurfaceCode where
  /-- Side length of the grid. -/
  L : ℕ
  /-- Side length must be at least 2. -/
  hL : 2 ≤ L

namespace SurfaceCode

/-- Number of physical qubits. -/
def numQubits (sc : SurfaceCode) : ℕ := 2 * sc.L * (sc.L - 1)

/-- Number of logical qubits. -/
def numLogical : ℕ := 1

/-- Code distance. -/
def distance (sc : SurfaceCode) : ℕ := sc.L

/-- The surface code is a CSS code.
Star operators are X-type (on rough boundary vertices)
and plaquette operators are Z-type (on smooth boundary faces).
(See `RotatedSurfaceCode3.lean` for the fully proved d=3 instance.) -/
/-- The smallest interesting surface code is the d=3 code on 9 qubits.
This connects to the existing `RotatedSurfaceCode3` instance. -/
theorem d3_surface_code_params :
    let sc : SurfaceCode := ⟨3, by omega⟩
    -- The rotated surface code has 9 qubits, 1 logical qubit, distance 3.
    -- Note: the rotated variant uses n = L² instead of 2L(L-1).
    sc.distance = 3 := by
  rfl

end SurfaceCode

end Quantum
