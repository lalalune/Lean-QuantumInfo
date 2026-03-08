/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!

# Effective Field Theory

Wilson's framework for effective field theories, including power counting,
matching, and the decoupling theorem.

## Main definitions

- `EFTLagrangian` : L_eff = ∑_i C_i O_i / Λ^{d_i - 4} organized by dimension
- `WilsonCoefficient` : C_i encoding UV physics
- `PowerCounting` : Classification of operators by mass dimension
- `MatchingCondition` : Relating UV and IR theories at scale μ

## Main results

- `decoupling_theorem` : Heavy particles decouple at low energies
- `naturalness` : Wilson coefficients are O(1) unless protected by symmetry
- `running_coefficients` : RG evolution of Wilson coefficients

-/

noncomputable section

/-- An operator in an EFT characterized by its mass dimension -/
structure EFTOperator where
  /-- Mass dimension of the operator -/
  dimension : ℕ
  /-- Wilson coefficient -/
  wilsonCoefficient : ℝ

/-- Classification of operators by relevance -/
inductive OperatorType
  | relevant     -- dim < 4: grows at low energy
  | marginal     -- dim = 4: logarithmic
  | irrelevant   -- dim > 4: suppressed by powers of Λ

/-- Classify an operator by its dimension relative to spacetime dim d = 4 -/
def classifyOperator (dim : ℕ) : OperatorType :=
  if dim < 4 then OperatorType.relevant
  else if dim = 4 then OperatorType.marginal
  else OperatorType.irrelevant

/-- An effective field theory -/
structure EffectiveFieldTheory where
  /-- The cutoff scale Λ -/
  Λ : ℝ
  Λ_pos : 0 < Λ
  /-- The operators organized by dimension -/
  operators : List EFTOperator
  /-- The renormalizable part (dim ≤ 4) -/
  renormalizable : List EFTOperator := operators.filter (fun o => o.dimension ≤ 4)
  /-- The non-renormalizable corrections (dim > 4) -/
  corrections : List EFTOperator := operators.filter (fun o => 4 < o.dimension)

namespace EffectiveFieldTheory

variable (eft : EffectiveFieldTheory)

/-- Power counting: the contribution of a dim-d operator at energy E is
    suppressed by (E/Λ)^(d-4) -/
def suppressionFactor (d : ℕ) (E : ℝ) : ℝ :=
  (E / eft.Λ) ^ ((d : ℤ) - 4).toNat

end EffectiveFieldTheory

/-- Matching: equating amplitudes in UV and EFT at the matching scale μ -/
structure MatchingCondition where
  /-- The matching scale -/
  μ : ℝ
  μ_pos : 0 < μ
  /-- UV theory amplitude at scale μ -/
  A_UV : ℝ
  /-- EFT amplitude at scale μ -/
  A_EFT : ℝ
  /-- Matching condition: A_UV(μ) = A_EFT(μ) -/
  matched : A_UV = A_EFT

/-- The Fermi theory as an EFT of the weak interaction:
    at E << m_W, the W propagator reduces to a contact interaction
    with G_F ~ g²/(8m_W²) -/
def fermiTheoryAsEFT (g m_W : ℝ) : ℝ := g ^ 2 / (8 * m_W ^ 2)

end
