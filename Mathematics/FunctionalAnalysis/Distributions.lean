/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antigravity
-/
import Mathlib.Analysis.Distribution.SchwartzSpace

/-! # Distributions in Finite Dimension

This file provides a concrete finite-dimensional model of tempered distributions
using Schwartz functions on `Fin n → ℝ`.
-/

noncomputable section
open scoped SchwartzMap

namespace Mathematics.FunctionalAnalysis

/-- Test functions in dimension `n`: Schwartz functions `ℝⁿ → ℂ`. -/
abbrev TestFunctionCarrier (n : ℕ) : Type := 𝓢((Fin n → ℝ), ℂ)

/-- A (tempered) distribution is a continuous linear functional on test functions. -/
abbrev Distribution (n : ℕ) : Type := TestFunctionCarrier n →L[ℝ] ℂ

/-- The Dirac delta distribution at the origin in `ℝⁿ`. -/
noncomputable def diracDelta (n : ℕ) : Distribution n :=
  SchwartzMap.delta (𝕜 := ℝ) (F := ℂ) (0 : Fin n → ℝ)

end Mathematics.FunctionalAnalysis
