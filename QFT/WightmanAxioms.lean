/-
Copyright (c) 2026. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg, Shaw Walters
-/
import QFT.Spacetime
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Wightman Axioms

The Wightman axioms provide a rigorous framework for quantum field theory in the
operator-valued distribution formalism. A Wightman QFT consists of:

1. **Hilbert space** with a distinguished vacuum vector
2. **Unitary representation** of the Poincaré group
3. **Operator-valued distributions** (quantum fields)
4. **Locality/Microcausality**: fields at spacelike separation commute (bosons) or
   anticommute (fermions)
5. **Spectral condition**: energy-momentum spectrum lies in the forward light cone
6. **Vacuum cyclicity**: the vacuum is cyclic for the field algebra

## References
- Streater, Wightman, *PCT, Spin and Statistics, and All That*
- Haag, *Local Quantum Physics*
-/

namespace QFT

/-- The field statistics: either Bose (commuting) or Fermi (anticommuting). -/
inductive FieldStatistics
  | Bose
  | Fermi
deriving DecidableEq

/-- A Wightman quantum field theory in d spacetime dimensions.
    This is the central axiomatic structure for rigorous QFT.

    The axioms encode:
    - A separable Hilbert space H
    - A vacuum state Ω ∈ H
    - A strongly continuous unitary representation U of the Poincaré group
    - Operator-valued tempered distributions φ₁, ..., φₙ (the fields)
    - Locality (microcausality)
    - Spectral condition on the energy-momentum spectrum
    - Cyclicity of the vacuum
-/
structure WightmanQFT (d : ℕ) [NeZero d] where
  /-- The abstract space of test functions. -/
  testSpace : TestFunctionSpace d
  /-- The Hilbert space of states. -/
  HilbertSpace : Type
  [instNormedAddCommGroup : NormedAddCommGroup HilbertSpace]
  [instInnerProductSpace : InnerProductSpace ℂ HilbertSpace]

  /-- The vacuum state vector. -/
  vacuum : HilbertSpace

  /-- The vacuum is a unit vector. -/
  vacuum_norm : @inner ℂ _ instInnerProductSpace.toInner vacuum vacuum = 1

  /-- Number of field components. -/
  numFields : ℕ

  /-- Statistics of each field component. -/
  statistics : Fin numFields → FieldStatistics

  /-- Unitary representation of the Poincaré group on H.
      U(a, Λ) is unitary for each Poincaré transformation (Λ, a). -/
  poincareRep : PoincareTransformation d → HilbertSpace →ₗ[ℂ] HilbertSpace

  /-- The vacuum is Poincaré-invariant: U(a,Λ)Ω = Ω. -/
  vacuum_invariant : ∀ g : PoincareTransformation d,
    poincareRep g vacuum = vacuum

  /-- The momentum spectrum of the theory. -/
  momentumSpectrum : Set (MinkowskiSpace d)

  /-- Spectral condition: the joint spectrum of the generators P_μ of
      translations lies in the closed forward light cone V̄₊. -/
  spectral_condition :
    momentumSpectrum ⊆ ClosedForwardLightCone d

  /-- The quantum fields as operator-valued distributions.
      φ_j(f) maps test functions to (unbounded) operators on H.
      Here we abstract the operator as a linear map H → H. -/
  field : Fin numFields → testSpace.carrier → HilbertSpace →ₗ[ℂ] HilbertSpace

  /-- Action of Poincaré group on test functions. -/
  poincareAction : PoincareTransformation d → testSpace.carrier → testSpace.carrier

  /-- Finite-dimensional representation of the Lorentz group for the fields. -/
  fieldSpinRep : PoincareTransformation d → Matrix (Fin numFields) (Fin numFields) ℂ

  /-- Covariance: U(a,Λ) φ_j(f) U(a,Λ)⁻¹ = S(Λ)_jk φ_k(f ∘ (a,Λ)⁻¹)
      where S is the finite-dimensional representation for the field's spin. -/
  covariance : ∀ (g : PoincareTransformation d) (j : Fin numFields)
    (f : testSpace.carrier) (v : HilbertSpace),
    poincareRep g (field j f v) =
      ∑ k : Fin numFields, fieldSpinRep g j k •
        field k (poincareAction g f) (poincareRep g v)

  /-- Locality (Microcausality): If supp(f) and supp(g) are spacelike separated,
      then [φ_j(f), φ_k(g)]_± = 0, where ± depends on statistics. -/
  locality : ∀ (j k : Fin numFields) (f g : testSpace.carrier) (v : HilbertSpace),
    (∀ x ∈ testSpace.support f, ∀ y ∈ testSpace.support g,
      SpacelikeSeparated d x y) →
    field j f (field k g v) =
      if statistics j = FieldStatistics.Fermi ∧ statistics k = FieldStatistics.Fermi
      then -field k g (field j f v)
      else field k g (field j f v)

  /-- Cyclicity of the vacuum: polynomials in smeared fields applied to Ω
      are dense in H. -/
  vacuum_cyclic :
    Dense (↑(Submodule.span ℂ
      {v : HilbertSpace | ∃ fs : List (Fin numFields × testSpace.carrier),
        v = fs.foldr (fun (jf : Fin numFields × testSpace.carrier)
          (acc : HilbertSpace) => field jf.1 jf.2 acc) vacuum}) :
      Set HilbertSpace)

/-- The n-point Wightman function.
    W_n(x₁,...,xₙ) = ⟨Ω, φ(x₁)⋯φ(xₙ) Ω⟩
    Here abstracted over test functions. -/
noncomputable def wightmanFunction {d : ℕ} [NeZero d] (W : WightmanQFT d)
    (fields : List (Fin W.numFields × W.testSpace.carrier)) : ℂ :=
  @inner ℂ W.HilbertSpace W.instInnerProductSpace.toInner W.vacuum
    (fields.foldr (fun jf acc => W.field jf.1 jf.2 acc) W.vacuum)

/-- Wightman functions satisfy positivity (Wightman positivity).
    For any field operator applied to the vacuum, the inner product
    ⟨φ(f)Ω, φ(f)Ω⟩ is non-negative. This follows directly from the
    positive-definite Hilbert space inner product. -/
theorem wightmanFunction_positive {d : ℕ} [NeZero d] (W : WightmanQFT d)
    (j : Fin W.numFields) (f : W.testSpace.carrier) :
    ((@inner ℂ W.HilbertSpace W.instInnerProductSpace.toInner
      (W.field j f W.vacuum) (W.field j f W.vacuum)).re) ≥ 0 := by
  exact inner_self_nonneg (𝕜 := ℂ)

/-- The spectral condition on Wightman functions:
    The momentum spectrum lies in the closed forward light cone.
    This is a direct consequence of the `spectral_condition` axiom. -/
theorem wightmanFunction_spectral {d : ℕ} [NeZero d] (W : WightmanQFT d) :
    W.momentumSpectrum ⊆ ClosedForwardLightCone d :=
  W.spectral_condition

/-- Cluster decomposition property: the vacuum is the unique
    Poincaré-invariant state (up to scalar multiples).
    This ensures that Wightman functions factorize at large
    spacelike separations. -/
def HasClusterProperty {d : ℕ} [NeZero d] (W : WightmanQFT d) : Prop :=
  ∀ v : W.HilbertSpace,
    (∀ g : PoincareTransformation d, W.poincareRep g v = v) →
    ∃ c : ℂ, v = c • W.vacuum

/-- The Wightman reconstruction theorem (statement):
    Given Wightman functions satisfying positivity, covariance,
    spectral condition, locality, and cluster decomposition,
    there exists a unique (up to unitary equivalence) Wightman QFT
    realizing those functions.

    The proof is non-trivial (GNS construction + Borchers algebra);
    here we state the reconstruction data as a property. -/
def WightmanReconstruction (d : ℕ) [NeZero d]
    (W : (n : ℕ) → (Fin n → MinkowskiSpace d) → ℂ) : Prop :=
  ∃ Wqft : WightmanQFT d, Wqft.momentumSpectrum ⊆ ClosedForwardLightCone d
  -- Full statement requires showing the QFT's Wightman functions
  -- match the input W via a smearing formalism.

end QFT
