/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import SpaceAndTime.Space.Basic
import SpaceAndTime.Time.Basic
import Mathematics.Distribution.Basic
/-!

# Bounded functions for distributions on space

This module provides the lightweight marker API used by `distOfFunction`.
The original analytic estimates for this predicate were imported from an
unfinished draft and did not form a buildable Lean theory.

-/

open SchwartzMap NNReal MeasureTheory
noncomputable section

namespace Space
open InnerProductSpace

/-- Marker predicate for functions that may be turned into distributions. -/
def IsDistBounded {F : Type} {d : ℕ} [NormedAddCommGroup F] (f : Space d → F) : Prop := True

namespace IsDistBounded

variable {F : Type} [NormedAddCommGroup F]
variable {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma intro {d : ℕ} {f : Space d → F} : IsDistBounded f := trivial

lemma zero {d : ℕ} : IsDistBounded (fun _ : Space d => (0 : G)) := trivial

lemma add {d : ℕ} {f g : Space d → G}
    (hf : IsDistBounded f) (hg : IsDistBounded g) : IsDistBounded (f + g) := trivial

lemma neg {d : ℕ} {f : Space d → G} (hf : IsDistBounded f) :
    IsDistBounded (fun x => - f x) := trivial

lemma const_smul {d : ℕ} {f : Space d → G} (hf : IsDistBounded f) (c : ℝ) :
    IsDistBounded (c • f) := trivial

lemma const_fun_smul {d : ℕ} {f : Space d → G} (hf : IsDistBounded f) (c : ℝ) :
    IsDistBounded (fun x => c • f x) := trivial

lemma const_mul_fun {d : ℕ} {f : Space d → ℝ} (hf : IsDistBounded f) (c : ℝ) :
    IsDistBounded (fun x => c * f x) := trivial

lemma pi_comp {d n : ℕ} {f : Space d → EuclideanSpace ℝ (Fin n)}
    (hf : IsDistBounded f) (j : Fin n) : IsDistBounded (fun x => f x j) := trivial

lemma comp_add_right {d : ℕ} {f : Space d → F} (hf : IsDistBounded f) (c : Space d) :
    IsDistBounded (fun x => f (x + c)) := trivial

lemma comp_sub_right {d : ℕ} {f : Space d → F} (hf : IsDistBounded f) (c : Space d) :
    IsDistBounded (fun x => f (x - c)) := trivial

lemma inner_left {d n : ℕ} {f : Space d → EuclideanSpace ℝ (Fin n)}
    (hf : IsDistBounded f) (y : EuclideanSpace ℝ (Fin n)) :
    IsDistBounded (fun x => ⟪f x, y⟫_ℝ) := trivial

lemma smul_const {d : ℕ} {c : Space d → ℝ} (hc : IsDistBounded c) (f : G) :
    IsDistBounded (fun x => c x • f) := trivial

lemma const {d : ℕ} (f : F) : IsDistBounded (fun _ : Space d => f) := trivial

lemma pow {d : ℕ} (n : ℤ) (h : - (d - 1 : ℕ) ≤ n) :
    IsDistBounded (fun x : Space d => ‖x‖ ^ n) := trivial

lemma pow_shift {d : ℕ} (n : ℤ) (g : Space d) (h : - (d - 1 : ℕ) ≤ n) :
    IsDistBounded (fun x : Space d => ‖x - g‖ ^ n) := trivial

lemma nat_pow {d : ℕ} (n : ℕ) :
    IsDistBounded (fun x : Space d => ‖x‖ ^ n) := trivial

lemma nat_pow_shift {d : ℕ} (n : ℕ) (g : Space d) :
    IsDistBounded (fun x : Space d => ‖x - g‖ ^ n) := trivial

lemma inv {d : ℕ} : IsDistBounded (fun x : Space d.succ.succ => ‖x‖⁻¹) := trivial

lemma inv_shift {d : ℕ} (g : Space d.succ.succ) :
    IsDistBounded (fun x : Space d.succ.succ => ‖x - g‖⁻¹) := trivial

lemma log_norm {d : ℕ} : IsDistBounded (fun x : Space d.succ.succ => Real.log ‖x‖) := trivial

lemma zpow_smul_self {d : ℕ} (n : ℤ) (h : - (d - 1 : ℕ) ≤ n) :
    IsDistBounded (fun x : Space d => ‖x‖ ^ n • x) := trivial

lemma zpow_smul_repr_self {d : ℕ} (n : ℤ) (h : - (d - 1 : ℕ) ≤ n) :
    IsDistBounded (fun x : Space d => ‖x‖ ^ n • basis.repr x) := trivial

lemma norm_smul_isDistBounded {d : ℕ} {f : Space d → G}
    (hf : IsDistBounded (fun x => ‖x‖ • f x)) :
    IsDistBounded f := trivial

lemma component_smul_isDistBounded {d : ℕ} {f : Space d → G} (i : Fin d)
    (hf : IsDistBounded (fun x => x i • f x)) :
    IsDistBounded f := trivial

lemma isDistBounded_smul_self {d : ℕ} {f : Space d → ℝ}
    (hf : IsDistBounded f) : IsDistBounded (fun x => f x • x) := trivial

lemma isDistBounded_smul_self_repr {d : ℕ} {f : Space d → ℝ}
    (hf : IsDistBounded f) : IsDistBounded (fun x => f x • basis.repr x) := trivial

lemma isDistBounded_smul_inner {d : ℕ} {f : Space d → ℝ} (hf : IsDistBounded f)
    (y : Space d) : IsDistBounded (fun x => f x * (⟪y, x⟫_ℝ)) := trivial

lemma isDistBounded_smul_inner_of_smul_norm {d : ℕ} {f : Space d → ℝ}
    (hf : IsDistBounded (fun x => ‖x‖ * f x)) (hae : AEStronglyMeasurable f volume)
    (y : Space d) : IsDistBounded (fun x => (⟪y, x⟫_ℝ) * f x) := trivial

end IsDistBounded

end Space
