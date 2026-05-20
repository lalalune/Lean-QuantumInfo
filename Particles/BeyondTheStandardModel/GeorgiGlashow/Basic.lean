/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Particles.StandardModel.Basic
/-!

# The Georgi-Glashow Model

The Georgi-Glashow model is a grand unified theory that unifies the Standard Model gauge group into
`SU(5)`.

-/

namespace GeorgiGlashow

/-- The gauge group of the Georgi-Glashow model. -/
abbrev GaugeGroupI : Type := Matrix.specialUnitaryGroup (Fin 5) ℂ

end GeorgiGlashow
