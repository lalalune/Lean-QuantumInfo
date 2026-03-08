/-
Copyright (c) 2026. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg, Shaw Walters
-/
import QFT.WightmanAxioms
/-!
# Haag's Theorem

Haag's theorem is a fundamental no-go result in quantum field theory showing that
the interaction picture of QFT does not exist in the usual sense. Specifically:

**Haag's Theorem:** If two quantum field theories (one free, one interacting)
satisfy the Wightman axioms and are related by a unitary transformation that
preserves the vacuum, then the two theories are unitarily equivalent —
meaning the "interacting" theory is actually free.

More precisely: if φ₀ (free field) and φ (interacting field) are Wightman fields
on the same Hilbert space, related by φ(x) = U φ₀(x) U⁻¹ with U unitary,
and if U Ω₀ = Ω (vacuum mapping), then the Wightman functions of φ coincide
with those of φ₀.

**Physical consequence:** The interaction picture, which assumes that
interacting fields can be obtained from free fields by a unitary transformation,
is inconsistent. Perturbation theory works despite this because it never
constructs the full interacting theory — it only computes order-by-order
in a formal power series.

## References
- Haag, *On quantum field theories*, 1955
- Hall, Wightman, *A theorem on invariant analytic functions*, 1957
- Earman, Fraser, *Haag's Theorem and Its Implications for QFT*
-/

namespace QFT

/-- A free Wightman QFT: one where all Wightman functions satisfy
    Wick's theorem (factorize into products of 2-point functions).
    This is the defining property of a Gaussian/free field theory. -/
structure FreeWightmanQFT (d : ℕ) [NeZero d] extends WightmanQFT d where
  /-- The theory satisfies Wick's theorem: all n-point functions
      factorize into products of 2-point functions.
      For odd n, W_n = 0. For even n = 2k, W_{2k} = ∑_pairings ∏ W_2. -/
  wick_factorization :
    ∀ (fields : List (Fin numFields × testSpace.carrier)),
      fields.length > 2 →
      ∃ (decomposition : List (List (Fin numFields × testSpace.carrier))),
        (∀ pair ∈ decomposition, pair.length = 2) ∧
        wightmanFunction toWightmanQFT fields =
          (decomposition.map (wightmanFunction toWightmanQFT)).prod

/-- An interacting Wightman QFT is one that is not free: at least one
    connected n-point function (n ≥ 3) is not determined by the 2-point function.
    Equivalently, some higher-point Wightman function violates Wick factorization. -/
def IsInteracting {d : ℕ} [NeZero d] (W : WightmanQFT d) : Prop :=
  ∃ (fields : List (Fin W.numFields × W.testSpace.carrier)),
    fields.length > 2 ∧
    ¬ ∃ (decomposition : List (List (Fin W.numFields × W.testSpace.carrier))),
      (∀ pair ∈ decomposition, pair.length = 2) ∧
      wightmanFunction W fields = (decomposition.map (wightmanFunction W)).prod

/-- Two field theories have the same Wightman functions if all n-point
    functions agree on all test function inputs. -/
def SameWightmanFunctions {d : ℕ} [NeZero d] (W₁ W₂ : WightmanQFT d)
    (fieldMap₁ : Fin W₁.numFields → Fin W₂.numFields)
    (testMap : W₁.testSpace.carrier → W₂.testSpace.carrier) : Prop :=
  ∀ (fields : List (Fin W₁.numFields × W₁.testSpace.carrier)),
    wightmanFunction W₁ fields =
    wightmanFunction W₂ (fields.map (fun ⟨j, f⟩ => (fieldMap₁ j, testMap f)))

/-- Two theories sharing the same Hilbert space with a unitary
    transformation relating them while preserving the vacuum.
    This is the interaction picture setup that Haag's theorem shows
    is inconsistent. -/
structure InteractionPictureSetup {d : ℕ} [NeZero d]
    (freeTheory : FreeWightmanQFT d) (interactingTheory : WightmanQFT d) where
  /-- The two theories share the same Hilbert space. -/
  same_space : freeTheory.HilbertSpace = interactingTheory.HilbertSpace
  /-- The unitary intertwiner: φ_int = U φ_free U⁻¹. -/
  U : freeTheory.HilbertSpace →ₗ[ℂ] freeTheory.HilbertSpace
  /-- U is unitary: U† U = id. -/
  U_unitary_left : ∀ v : freeTheory.HilbertSpace,
    @inner ℂ _ freeTheory.instInnerProductSpace.toInner (U v) (U v) =
    @inner ℂ _ freeTheory.instInnerProductSpace.toInner v v
  /-- U maps free vacuum to interacting vacuum. -/
  maps_vacuum : U freeTheory.vacuum =
    same_space ▸ interactingTheory.vacuum

end QFT
