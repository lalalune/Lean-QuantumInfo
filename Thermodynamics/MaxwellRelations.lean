/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!

# Maxwell Relations

The four Maxwell relations are equalities between second mixed partial derivatives of
thermodynamic potentials. They follow from the exactness of thermodynamic differentials
(equivalently, from the commutativity of mixed partial derivatives).

## Main results

- `maxwell_relation_U` : (∂T/∂V)_S = -(∂P/∂S)_V
- `maxwell_relation_H` : (∂T/∂P)_S = (∂V/∂S)_P
- `maxwell_relation_A` : (∂S/∂V)_T = (∂P/∂T)_V
- `maxwell_relation_G` : -(∂S/∂P)_T = (∂V/∂T)_P

-/

noncomputable section

open Filter Topology

/-! ## Thermodynamic potentials as functions of natural variables -/

/-- Internal energy U(S, V) -/
structure InternalEnergyFunc where
  U : ℝ × ℝ → ℝ
  smooth : ContDiff ℝ 2 U

/-- Enthalpy H(S, P) -/
structure EnthalpyFunc where
  H : ℝ × ℝ → ℝ
  smooth : ContDiff ℝ 2 H

/-- Helmholtz free energy A(T, V) -/
structure HelmholtzFunc where
  A : ℝ × ℝ → ℝ
  smooth : ContDiff ℝ 2 A

/-- Gibbs free energy G(T, P) -/
structure GibbsFunc where
  G : ℝ × ℝ → ℝ
  smooth : ContDiff ℝ 2 G

/-- Partial derivative of f(x,y) with respect to the first variable at point p. -/
def partialFst (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ f p (1, 0)

/-- Partial derivative of f(x,y) with respect to the second variable at point p. -/
def partialSnd (f : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ f p (0, 1)

/-! ## Maxwell relations from symmetry of mixed partial derivatives

For any C² function f(x, y), we have ∂²f/∂x∂y = ∂²f/∂y∂x.
The Maxwell relations are specific instances applied to thermodynamic potentials.
-/

/-- Symmetry of mixed partial derivatives for C² functions: ∂²f/∂x∂y = ∂²f/∂y∂x. -/
theorem mixed_partials_commute {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f) (p : ℝ × ℝ) :
    partialFst (partialSnd f) p = partialSnd (partialFst f) p := by
  have hfdiff : DifferentiableAt ℝ (fderiv ℝ f) p := by
    exact (hf.contDiffAt.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hfst :
      partialFst (partialSnd f) p = fderiv ℝ (fderiv ℝ f) p (1, 0) (0, 1) := by
    unfold partialFst partialSnd
    have hclm := fderiv_clm_apply (x := p) (c := fderiv ℝ f)
      (u := fun _ : ℝ × ℝ => (0, 1)) hfdiff
      (differentiableAt_const (x := p) (c := (0, 1)))
    have hclm' := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (1, 0)) hclm
    simpa using hclm'
  have hsnd :
      partialSnd (partialFst f) p = fderiv ℝ (fderiv ℝ f) p (0, 1) (1, 0) := by
    unfold partialFst partialSnd
    have hclm := fderiv_clm_apply (x := p) (c := fderiv ℝ f)
      (u := fun _ : ℝ × ℝ => (1, 0)) hfdiff
      (differentiableAt_const (x := p) (c := (1, 0)))
    have hclm' := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (0, 1)) hclm
    simpa using hclm'
  have hsymm :
      fderiv ℝ (fderiv ℝ f) p (1, 0) (0, 1) =
        fderiv ℝ (fderiv ℝ f) p (0, 1) (1, 0) := by
    exact hf.contDiffAt.isSymmSndFDerivAt (by simp) (1, 0) (0, 1)
  exact hfst.trans (hsymm.trans hsnd.symm)

/-- Maxwell relation from U(S,V): (∂T/∂V)_S = -(∂P/∂S)_V.
    Since dU = TdS - PdV, we have T = ∂U/∂S and -P = ∂U/∂V.
    The relation follows from ∂²U/∂V∂S = ∂²U/∂S∂V. -/
theorem maxwell_relation_U (Uf : InternalEnergyFunc) (p : ℝ × ℝ) :
    partialSnd (partialFst Uf.U) p = partialFst (partialSnd Uf.U) p := by
  simpa using (mixed_partials_commute (f := Uf.U) Uf.smooth p).symm

/-- Maxwell relation from H(S,P): (∂T/∂P)_S = (∂V/∂S)_P.
    Since dH = TdS + VdP, we have T = ∂H/∂S and V = ∂H/∂P. -/
theorem maxwell_relation_H (Hf : EnthalpyFunc) (p : ℝ × ℝ) :
    partialSnd (partialFst Hf.H) p = partialFst (partialSnd Hf.H) p := by
  simpa using (mixed_partials_commute (f := Hf.H) Hf.smooth p).symm

/-- Maxwell relation from A(T,V): (∂S/∂V)_T = (∂P/∂T)_V.
    Since dA = -SdT - PdV, we have -S = ∂A/∂T and -P = ∂A/∂V.
    The relation gives ∂²A/∂V∂T = ∂²A/∂T∂V. -/
theorem maxwell_relation_A (Af : HelmholtzFunc) (p : ℝ × ℝ) :
    partialSnd (partialFst Af.A) p = partialFst (partialSnd Af.A) p := by
  simpa using (mixed_partials_commute (f := Af.A) Af.smooth p).symm

/-- Maxwell relation from G(T,P): -(∂S/∂P)_T = (∂V/∂T)_P.
    Since dG = -SdT + VdP, we have -S = ∂G/∂T and V = ∂G/∂P. -/
theorem maxwell_relation_G (Gf : GibbsFunc) (p : ℝ × ℝ) :
    partialSnd (partialFst Gf.G) p = partialFst (partialSnd Gf.G) p := by
  simpa using (mixed_partials_commute (f := Gf.G) Gf.smooth p).symm

end
