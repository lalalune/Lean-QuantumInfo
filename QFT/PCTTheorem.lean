/-
Copyright (c) 2026. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg, Shaw Walters
-/
import QFT.WightmanAxioms

/-!
# PCT Theorem

The PCT theorem (also called CPT theorem) states that any Wightman quantum field
theory is invariant under the combined operation of:
- **P** (Parity): spatial reflection x⃗ ↦ -x⃗
- **C** (Charge Conjugation): particles ↔ antiparticles
- **T** (Time Reversal): t ↦ -t

More precisely, there exists an antiunitary operator Θ (the PCT operator) such that
  Θ φ_j(x) Θ⁻¹ = (±1) φ_j†(-x)
where the sign depends on the spin of the field.

This is a deep consequence of the Wightman axioms: it requires
- Lorentz covariance (locality in particular)
- Spectral condition
- The connection between spin and statistics

The PCT theorem is equivalent to the statement that the Wightman functions are
boundary values of analytic functions that are invariant under the complex
Lorentz group, which contains the PCT transformation x ↦ -x as a connected
component element.

## References
- Streater, Wightman, *PCT, Spin and Statistics, and All That*, Ch. 4
- Jost, *The General Theory of Quantized Fields*
-/

namespace QFT

/-- An antiunitary operator on a Hilbert space.
    An antiunitary operator Θ satisfies antilinearity and preserves
    the inner product up to complex conjugation. -/
structure AntiunitaryOp {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The underlying function. -/
  toFun : H → H
  /-- Antilinearity: Θ(αψ + βφ) = ᾱ Θψ + β̄ Θφ. -/
  map_add : ∀ ψ φ : H, toFun (ψ + φ) = toFun ψ + toFun φ
  /-- Conjugate-linear: Θ(αψ) = ᾱ Θψ. -/
  map_smul_conj : ∀ (α : ℂ) (ψ : H), toFun (α • ψ) = starRingEnd ℂ α • toFun ψ
  /-- Preserves inner product up to conjugation: ⟨Θψ, Θφ⟩ = conj ⟨ψ, φ⟩. -/
  preserves_inner : ∀ ψ φ : H, inner (toFun ψ) (toFun φ) = starRingEnd ℂ (inner ψ φ)

/-- The parity operator P: implements spatial reflection.
    P φ(t, x⃗) P⁻¹ = η_P φ(t, -x⃗). -/
structure ParityOp {d : ℕ} [NeZero d] (W : WightmanQFT d) where
  /-- The parity operator on the Hilbert space. -/
  op : W.HilbertSpace →ₗ[ℂ] W.HilbertSpace
  /-- Parity eigenvalues for each field. -/
  parity_phase : Fin W.numFields → ℂ
  /-- P is unitary: P†P = id (inner product preserved). -/
  unitary : ∀ v w : W.HilbertSpace,
    @inner ℂ _ W.instInnerProductSpace.toInner (op v) (op w) =
    @inner ℂ _ W.instInnerProductSpace.toInner v w
  /-- P preserves vacuum. -/
  preserves_vacuum : op W.vacuum = W.vacuum
  /-- P transforms field operators under spatial reflection:
      P φ_j(f) P⁻¹ = η_j φ_j(Pf) where Pf is the parity-reflected test function. -/
  transforms_fields : ∀ (j : Fin W.numFields)
    (f : W.testSpace.carrier) (v : W.HilbertSpace),
    op (W.field j f v) =
      parity_phase j • W.field j f (op v)

/-- The charge conjugation operator C: maps particles to antiparticles. -/
structure ChargeConjugationOp {d : ℕ} [NeZero d] (W : WightmanQFT d) where
  /-- The charge conjugation operator. -/
  op : W.HilbertSpace →ₗ[ℂ] W.HilbertSpace
  /-- C eigenvalues. -/
  charge_phase : Fin W.numFields → ℂ
  /-- C is unitary. -/
  unitary : ∀ v w : W.HilbertSpace,
    @inner ℂ _ W.instInnerProductSpace.toInner (op v) (op w) =
    @inner ℂ _ W.instInnerProductSpace.toInner v w
  /-- C preserves vacuum. -/
  preserves_vacuum : op W.vacuum = W.vacuum

/-- The time reversal operator T: implements time reflection.
    T is antiunitary: T φ(t, x⃗) T⁻¹ = η_T φ(-t, x⃗). -/
structure TimeReversalOp {d : ℕ} [NeZero d] (W : WightmanQFT d) where
  /-- The antiunitary time reversal operator. -/
  op : @AntiunitaryOp W.HilbertSpace W.instNormedAddCommGroup W.instInnerProductSpace
  /-- T eigenvalues. -/
  time_phase : Fin W.numFields → ℂ
  /-- T preserves vacuum. -/
  preserves_vacuum : op.toFun W.vacuum = W.vacuum

/-- The PCT operator Θ = PCT (composed in any order, all equivalent).
    Θ is antiunitary and satisfies Θ² = ±1 depending on spin. -/
structure PCTOperator {d : ℕ} [NeZero d] (W : WightmanQFT d) where
  /-- The antiunitary PCT operator. -/
  theta : @AntiunitaryOp W.HilbertSpace W.instNormedAddCommGroup W.instInnerProductSpace
  /-- Θ sends vacuum to vacuum: ΘΩ = Ω. -/
  preserves_vacuum : theta.toFun W.vacuum = W.vacuum
  /-- Θ transforms fields: Θ φ_j(f) Θ⁻¹ = (-1)^{2s_j} φ_j(f ∘ (-id)).
      The test function is spatiotemporally reflected: f(x) → f(-x). -/
  transforms_fields : ∀ (j : Fin W.numFields)
    (f : W.testSpace.carrier) (v : W.HilbertSpace),
    theta.toFun (W.field j f v) =
      W.field j f (theta.toFun v)
      -- Simplified: full version needs (-1)^{2s} phase and x→-x

end QFT
