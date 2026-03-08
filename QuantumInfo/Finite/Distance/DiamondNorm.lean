/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.Finite.CPTPMap
import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm

/-! # Diamond-Norm Infrastructure

This file provides a conservative, fully proved foundation layer:

- `MatrixMap.diamondNormRaw` is the usual supremum expression over ancilla-
  extended trace norms.
- `MatrixMap.diamondNorm` wraps that expression with `max 0 ...`, so basic
  order properties are available without relying on currently-missing global
  boundedness proofs.
- `CPTPMap.diamondDistance` is induced from `diamondNorm`.

Stronger properties (triangle inequality, channel bounds, contractivity, etc.)
are intentionally deferred until the required analytic lemmas are formalized.
-/

noncomputable section

open scoped Matrix ComplexOrder MatrixMap

variable {dIn dOut : Type*} [Fintype dIn] [Fintype dOut] [DecidableEq dIn] [DecidableEq dOut]

namespace MatrixMap

/-- Raw diamond-norm expression from the standard finite-dimensional formula.

This keeps the mathematically standard optimization object in the codebase. -/
def diamondNormRaw (Φ : MatrixMap dIn dOut ℂ) : ℝ :=
  sSup { x : ℝ | ∃ (ρ : Matrix (dIn × dIn) (dIn × dIn) ℂ),
    ρ.PosSemidef ∧ ρ.trace = 1 ∧
    x = Matrix.traceNorm ((Φ ⊗ₖₘ MatrixMap.id dIn ℂ) ρ) }

/-- Conservative diamond norm used by downstream code.

`max 0` ensures nonnegativity independently of the current state of global
boundedness lemmas for `diamondNormRaw`. -/
def diamondNorm (Φ : MatrixMap dIn dOut ℂ) : ℝ :=
  max 0 (diamondNormRaw Φ)

/-- Nonnegativity of the conservative diamond norm. -/
theorem diamondNorm_nonneg (Φ : MatrixMap dIn dOut ℂ) : 0 ≤ diamondNorm Φ := by
  unfold diamondNorm
  exact le_max_left _ _

end MatrixMap

namespace CPTPMap

variable [DecidableEq dIn] [DecidableEq dOut]

/-- Diamond distance induced by `MatrixMap.diamondNorm`. -/
def diamondDistance (Λ₁ Λ₂ : CPTPMap dIn dOut) : ℝ :=
  MatrixMap.diamondNorm (Λ₁.map - Λ₂.map)

/-- Diamond distance is non-negative. -/
theorem diamondDistance_nonneg (Λ₁ Λ₂ : CPTPMap dIn dOut) :
    0 ≤ diamondDistance Λ₁ Λ₂ :=
  MatrixMap.diamondNorm_nonneg _

end CPTPMap

end
