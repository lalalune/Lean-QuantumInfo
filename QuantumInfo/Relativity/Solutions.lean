import Mathlib
import QuantumInfo.Relativity.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Exponential

namespace Relativity

-- For exact solutions we typically use 4D spacetime
abbrev Spacetime4 := LocalGeometry 4

/-- Schwarzschild metric in spherical coordinates (t, r, θ, φ)
We provide a function that takes mass M and coordinates (t, r, θ, φ)
and returns the metric tensor g_{μν}. We use signature (-+++).
0: t, 1: r, 2: θ, 3: φ -/
noncomputable def SchwarzschildMetricTensor (M r θ : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  let r_s := 2 * M
  Matrix.diagonal ![
    -(1 - r_s / r),
    (1 - r_s / r)⁻¹,
    r^2,
    r^2 * (Real.sin θ)^2
  ]

/-- FLRW metric in comoving coordinates (t, r, θ, φ)
a(t) is the scale factor, k is the spatial curvature (-1, 0, 1). -/
noncomputable def FLRWMetricTensor (a : ℝ) (k r θ : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ![
    -1,
    a^2 / (1 - k * r^2),
    a^2 * r^2,
    a^2 * r^2 * (Real.sin θ)^2
  ]

/-- Kerr metric in Boyer-Lindquist coordinates (t, r, θ, φ)
M is mass, a is spin parameter (J/M). -/
noncomputable def KerrMetricTensor (M a_spin r θ : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  let sigma := r^2 + a_spin^2 * (Real.cos θ)^2
  let delta := r^2 - 2 * M * r + a_spin^2
  let M1 := -(1 - 2 * M * r / sigma)
  let M2 := sigma / delta
  let M3 := sigma
  let M4 := (r^2 + a_spin^2 + 2 * M * r * a_spin^2 * (Real.sin θ)^2 / sigma) * (Real.sin θ)^2
  let M14 := - 2 * M * r * a_spin * (Real.sin θ)^2 / sigma
  ![ ![M1, 0, 0, M14],
     ![0, M2, 0, 0],
     ![0, 0, M3, 0],
     ![M14, 0, 0, M4] ]

end Relativity
