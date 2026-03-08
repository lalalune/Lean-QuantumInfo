/-
Copyright (c) 2026 Adam Bornemann. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Adam Bornemann
-/
import QuantumMechanics.UnitaryEvo.Yosida.Basic

/-!
# Yosida Approximation Operators

This file defines the Yosida approximation operators used to construct the
exponential of a self-adjoint operator.

## Main definitions

* `resolventAtIn`: The resolvent `R(in)` at `z = in`
* `resolventAtNegIn`: The resolvent `R(-in)` at `z = -in`
* `yosidaApprox`: The Yosida approximant `Aₙ = n²R(in) - in·I`
* `yosidaApproxSym`: The symmetric Yosida approximant `(n²/2)(R(in) + R(-in))`
* `yosidaJ`: The contractive operator `Jₙ = -in·R(in)`
* `yosidaJNeg`: The contractive operator `Jₙ⁻ = in·R(-in)`
* `yosidaApproxNeg`: The approximant using `R(-in)`

## Main results

* `resolventAtIn_bound`: `‖R(in)‖ ≤ 1/n`

-/

namespace QuantumMechanics.Yosida

open Complex Resolvent Generators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {U_grp : OneParameterUnitaryGroup (H := H)}

/-! ### Resolvent at specific points -/

/-- The resolvent at `z = in` for positive natural `n`. -/
noncomputable def resolventAtIn
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) : H →L[ℂ] H :=
  resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa

/-- The resolvent at `z = -in` for positive natural `n`. -/
noncomputable def resolventAtNegIn
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) : H →L[ℂ] H :=
  resolvent gen (-I * (n : ℂ)) (neg_I_mul_pnat_im_ne_zero n) hsa

/-! ### Yosida approximation operators -/

/-- The Yosida approximant `Aₙ = n²R(in) - in·I`. -/
noncomputable def yosidaApprox
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) : H →L[ℂ] H :=
  (n : ℂ)^2 • resolventAtIn gen hsa n - (I * (n : ℂ)) • ContinuousLinearMap.id ℂ H

/-- The symmetric Yosida approximant `(n²/2)(R(in) + R(-in))`. -/
noncomputable def yosidaApproxSym
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) : H →L[ℂ] H :=
  ((n : ℂ)^2 / 2) • (resolventAtIn gen hsa n + resolventAtNegIn gen hsa n)

/-- The contractive operator `Jₙ = -in·R(in)`. -/
noncomputable def yosidaJ
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) : H →L[ℂ] H :=
  (-I * (n : ℂ)) • resolventAtIn gen hsa n

/-- The contractive operator `Jₙ⁻ = in·R(-in)`. -/
noncomputable def yosidaJNeg
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) : H →L[ℂ] H :=
  (I * (n : ℂ)) • resolventAtNegIn gen hsa n

/-- The approximant using `R(-in)`: `Aₙ⁻ = n²R(-in) + in·I`. -/
noncomputable def yosidaApproxNeg
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) : H →L[ℂ] H :=
  ((n : ℂ)^2) • resolventAtNegIn gen hsa n + (I * (n : ℂ)) • ContinuousLinearMap.id ℂ H

/-! ### Resolvent bounds -/

lemma resolventAtIn_bound
    (gen : Generator U_grp) (hsa : gen.IsSelfAdjoint)
    (n : ℕ+) :
    ‖resolventAtIn gen hsa n‖ ≤ 1 / (n : ℝ) := by
  unfold resolventAtIn
  calc ‖resolvent gen (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n) hsa‖
      ≤ 1 / |(I * (n : ℂ)).im| := resolvent_bound gen hsa (I * (n : ℂ)) (I_mul_pnat_im_ne_zero n)
    _ = 1 / (n : ℝ) := by rw [abs_I_mul_pnat_im]

end QuantumMechanics.Yosida
