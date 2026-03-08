import Mechanics.CanonicalQuantization
import Mechanics.Symplectic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Weyl Quantization and Deformation Quantization

Formalizes the Weyl-Wigner formalism connecting classical phase-space functions
to quantum operators, and the Moyal star product as a deformation of
pointwise multiplication.

## Main Definitions
- `PhaseSpaceFunction`: classical observable as a function ℝ²ⁿ → ℝ
- `WignerFunction`: quasi-probability representation of a quantum state
- `MoyalBracket`: the quantum deformation of the Poisson bracket
- `StarProduct`: associative product f ★ g on phase-space functions
- `ClassicalLimit`: formal ℏ → 0 limit recovers classical mechanics

## References
- H. Weyl, *The Theory of Groups and Quantum Mechanics* (1928)
- J.E. Moyal, *Quantum mechanics as a statistical theory* (1949)
- M.V. Berry, *Semi-classical mechanics in phase space: a study of Wigner's function* (1977)
-/

noncomputable section

open Matrix Finset BigOperators

namespace Mechanics

/-- A function on 2n-dimensional phase space. -/
abbrev PhaseSpaceFunction (n : ℕ) := PhasePoint n → ℝ

/-- A complex-valued phase-space function (for Wigner functions). -/
abbrev PhaseSpaceFunctionC (n : ℕ) := PhasePoint n → ℂ

/-- The Wigner function is a quasi-probability distribution on phase space
    that encodes a quantum state. Given as a structure with its properties. -/
structure WignerFunction (n : ℕ) where
  /-- The Wigner function W(q, p). -/
  W : PhaseSpaceFunction n
  /-- Normalization: ∫ W dq dp = 1. -/
  normalized : ∫ x, W x = 1
  /-- Marginals give non-negative probability distributions. -/
  marginals_nonneg : 
    (∀ q : Fin n → ℝ, 0 ≤ ∫ p, W (PhasePoint.mk q p)) ∧
    (∀ p : Fin n → ℝ, 0 ≤ ∫ q, W (PhasePoint.mk q p))

/-- The Moyal bracket {f, g}_★ is the quantum deformation of the Poisson bracket:
    {f, g}_★ = (2/ℏ) sin(ℏ/2 · {·, ·}) applied to (f, g)
    To first order: {f, g}_★ ≈ {f, g}_Poisson + O(ℏ²)

    We represent it using the gradient-based formula. -/
def moyalBracketFirstOrder {n : ℕ} (hbar : ℝ)
    (grad_f grad_g : Fin (2 * n) → ℝ) : ℝ :=
  poissonBracketAt (canonicalSymplecticMatrix n) grad_f grad_g

/-- The star product to zeroth order in ℏ is just pointwise multiplication:
    (f ★ g)(z) = f(z) · g(z) + O(ℏ). -/
def starProductZerothOrder {n : ℕ} (f g : PhaseSpaceFunction n) : PhaseSpaceFunction n :=
  fun z => f z * g z

/-- The first-order correction to the star product:
    (f ★ g)(z) = fg + (iℏ/2){f, g} + O(ℏ²)
    where the Poisson bracket contribution is computed from gradients. -/
def starProductFirstOrder {n : ℕ} (hbar : ℝ)
    (f g : PhaseSpaceFunction n)
    (grad_f grad_g : PhasePoint n → (Fin (2 * n) → ℝ)) : PhaseSpaceFunction n :=
  fun z => f z * g z + (hbar / 2) * poissonBracketAt (canonicalSymplecticMatrix n) (grad_f z) (grad_g z)

/-- The star product is associative (to all orders in ℏ).
    At zeroth order this is just associativity of multiplication. -/
theorem starProductZerothOrder_assoc {n : ℕ}
    (f g h : PhaseSpaceFunction n) (z : PhasePoint n) :
    starProductZerothOrder f (starProductZerothOrder g h) z =
    starProductZerothOrder (starProductZerothOrder f g) h z := by
  simp [starProductZerothOrder, mul_assoc]

/-- Classical limit: as ℏ → 0, the star product reduces to pointwise multiplication. -/
theorem classical_limit_star_product {n : ℕ}
    (f g : PhaseSpaceFunction n)
    (grad_f grad_g : PhasePoint n → (Fin (2 * n) → ℝ)) (z : PhasePoint n) :
    starProductFirstOrder 0 f g grad_f grad_g z = f z * g z := by
  simp [starProductFirstOrder, zero_div, zero_mul, add_zero]

/-- Classical limit: as ℏ → 0, the Moyal bracket reduces to the Poisson bracket. -/
theorem classical_limit_moyal {n : ℕ}
    (grad_f grad_g : Fin (2 * n) → ℝ) :
    moyalBracketFirstOrder 0 grad_f grad_g =
    poissonBracketAt (canonicalSymplecticMatrix n) grad_f grad_g := by
  simp [moyalBracketFirstOrder]

/-- The Weyl correspondence maps a phase-space function to an operator.
    Formally: Â = ∫ a(q, p) Δ(q, p) dq dp / (2πℏ)ⁿ
    where Δ is the Stratonovich-Weyl quantizer kernel.
    We represent this as an abstract structure. -/
structure WeylQuantizationMap (n d : ℕ) where
  /-- The Weyl quantizer maps classical phase-space functions to quantum operators. -/
  quantize : PhaseSpaceFunction n → Matrix (Fin d) (Fin d) ℂ
  /-- The quantizer is linear. -/
  linear : ∀ (c₁ c₂ : ℝ) (f₁ f₂ : PhaseSpaceFunction n),
    quantize (fun z => c₁ * f₁ z + c₂ * f₂ z) = 
      c₁ • quantize f₁ + c₂ • quantize f₂
  /-- Real symbols map to Hermitian operators. -/
  hermitian : ∀ f : PhaseSpaceFunction n, Matrix.IsHermitian (quantize f)

end Mechanics
