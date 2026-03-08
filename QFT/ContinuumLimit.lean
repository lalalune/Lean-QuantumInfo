/-
Copyright (c) 2026. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg, Shaw Walters
-/
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import StatMech.Lattice

namespace QFT

open StatMech

/-- 
A renormalization group (RG) flow step.
If the actions are parameterized by a space P, an RG step is a function R : P → P.
-/
def RGStep (P : Type) := P → P

/-- 
A fixed point of the RG flow.
-/
def IsRGFixedPoint {P : Type} (R : RGStep P) (p : P) : Prop :=
  R p = p

/--
Iterated application of the RG step n times.
-/
def RGIterate {P : Type} (R : RGStep P) : ℕ → P → P
  | 0 => id
  | n + 1 => R ∘ RGIterate R n

/--
A theory p flows to a fixed point p_star under the RG if the iterated RG steps
converge: for any neighborhood of p_star, there exists N such that R^n(p) is in 
that neighborhood for all n ≥ N. We use a topological formulation when available,
or state it abstractly: R^n(p) → p_star.
-/
def FlowsTo {P : Type} [TopologicalSpace P] (R : RGStep P) (p p_star : P) : Prop :=
  Filter.Tendsto (fun n => RGIterate R n p) Filter.atTop (nhds p_star)

/--
A universality class is defined by the basin of attraction of an RG fixed point.
Two theories are in the same universality class if they both flow to the same fixed point.
-/
def InSameUniversalityClass {P : Type} [TopologicalSpace P] (R : RGStep P) (p₁ p₂ p_star : P) : Prop :=
  IsRGFixedPoint R p_star ∧ FlowsTo R p₁ p_star ∧ FlowsTo R p₂ p_star

/--
The continuum limit involves taking the lattice spacing a → 0 while 
tuning parameters to a critical point (RG fixed point). 
-/
def ContinuumLimit {P : Type} (latticeSpacing : P → ℝ) (R : RGStep P) (p_star : P) : Prop :=
  IsRGFixedPoint R p_star ∧ latticeSpacing p_star = 0

end QFT
