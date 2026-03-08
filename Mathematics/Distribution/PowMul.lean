/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Mathematics.Distribution.Basic
/-!

## The multiple of a Schwartz map by `x`

In this module we define the continuous linear map from the Schwartz space
`𝓢(ℝ, 𝕜)` to itself which takes a Schwartz map `η` to the Schwartz map `x * η`.

NOTE: This file requires SchwartzMap (Mathlib.Analysis.Distribution.SchwartzSpace)
which is not available in this Mathlib build; the implementation is intentionally deferred.

-/
noncomputable section

namespace Distribution

variable (𝕜 : Type) {E F : Type} [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [NormedSpace ℝ E]

end Distribution
