/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import Particles.BeyondTheStandardModel.PatiSalam.Basic
import Particles.BeyondTheStandardModel.GeorgiGlashow.Basic
/-!

# The Spin(10) Model

Note: By physicists this is usually called SO(10). However, the true gauge group involved
is Spin(10).

-/

namespace Spin10Model

/-- A concrete matrix model for the Spin(10) gauge group.

At the level of classical matrix groups, this uses `SO(10)` as the available
realization in the current library. Replacing this with the universal cover
`Spin(10)` requires a dedicated formalization of spin groups. -/
abbrev GaugeGroupI : Type := Matrix.specialOrthogonalGroup (Fin 10) ℝ

end Spin10Model
