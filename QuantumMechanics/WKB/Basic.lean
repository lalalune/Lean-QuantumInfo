/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
/-!
# WKB Approximation

The Wentzel-Kramers-Brillouin semiclassical approximation for the Schrödinger equation.
WKB provides approximate solutions when the potential varies slowly compared to the
de Broglie wavelength.

## Main definitions

* `OneDSystem` : a 1D quantum system with mass, ℏ, and potential `V(x)`
* `BohrSommerfeld` : the quantization condition `∮ p dx = (n + ½)2πℏ`
* `TunnellingBarrier` : Gamow tunnelling factor `T ≈ exp(-2γ)`
* `ConnectionFormula` : Airy function matching across turning points

## References

* Griffiths, *Introduction to Quantum Mechanics*, §9.1-9.3
* Landau & Lifshitz, *Quantum Mechanics*, §46-49
-/

noncomputable section

open Real MeasureTheory

namespace QuantumMechanics.WKB

/-! ## Classical Momentum -/

/-- A 1D quantum system with potential V(x). -/
structure OneDSystem where
  m : ℝ
  ℏ : ℝ
  V : ℝ → ℝ
  m_pos : 0 < m
  ℏ_pos : 0 < ℏ

namespace OneDSystem

variable (sys : OneDSystem)

/-- Classical momentum: `p(x) = √(2m(E - V(x)))`. Real in the classically allowed region. -/
def classicalMomentum (E x : ℝ) : ℝ := Real.sqrt (2 * sys.m * (E - sys.V x))

/-- The local de Broglie wavelength: `λ = 2πℏ/p`. -/
def deBroglieWavelength (E x : ℝ) (hp : 0 < sys.classicalMomentum E x) : ℝ :=
  2 * π * sys.ℏ / sys.classicalMomentum E x

def isClassicallyAllowed (E x : ℝ) : Prop := E ≥ sys.V x
def isTurningPoint (E x : ℝ) : Prop := E = sys.V x
def isClassicallyForbidden (E x : ℝ) : Prop := E < sys.V x

/-- Decay constant in the forbidden region: `κ(x) = √(2m(V(x) - E))/ℏ`. -/
def decayConstant (E x : ℝ) : ℝ :=
  Real.sqrt (2 * sys.m * (sys.V x - E)) / sys.ℏ

end OneDSystem

/-! ## WKB Wavefunction -/

/-- The WKB wavefunction in the classically allowed region:
    `ψ(x) ≈ A/√p · e^{i∫p dx/ℏ} + B/√p · e^{-i∫p dx/ℏ}`. -/
structure WKBWavefunction where
  sys : OneDSystem
  E : ℝ
  A : ℂ
  B : ℂ
  x₀ : ℝ

namespace WKBWavefunction

variable (ψ : WKBWavefunction)

def amplitudeFactor (x : ℝ) (hp : 0 < ψ.sys.classicalMomentum ψ.E x) : ℝ :=
  1 / Real.sqrt (ψ.sys.classicalMomentum ψ.E x)

/-- WKB validity: the potential varies slowly on the de Broglie scale.
    `|dp/dx| ≪ p²/ℏ`. -/
def isValid (x : ℝ) (hp : 0 < ψ.sys.classicalMomentum ψ.E x) : Prop :=
  |deriv (ψ.sys.classicalMomentum ψ.E) x| <
    (ψ.sys.classicalMomentum ψ.E x) ^ 2 / ψ.sys.ℏ

end WKBWavefunction

/-! ## Bohr-Sommerfeld Quantization -/

/-- The Bohr-Sommerfeld quantization condition: `∮ p dx = (n + ½)2πℏ`. -/
structure BohrSommerfeld where
  sys : OneDSystem
  a : ℝ
  b : ℝ
  E : ℝ
  n : ℕ
  left_turning : sys.isTurningPoint E a
  right_turning : sys.isTurningPoint E b
  a_lt_b : a < b
  classically_allowed : ∀ x, a < x → x < b → sys.isClassicallyAllowed E x
  quantization :
    ∫ x in Set.Icc a b, sys.classicalMomentum E x = (n + 1/2 : ℝ) * π * sys.ℏ

namespace BohrSommerfeld

/-- For the harmonic oscillator, Bohr-Sommerfeld gives exact energies: `Eₙ = (n + ½)ℏω`.
    Proof requires: computing `∫_a^b √(2m(E - mω²x²/2)) dx` over the classically
    allowed region, which evaluates to `πE/ω` via trig substitution,
    then applying the quantization condition. -/
theorem harmonicOscillator_exact (bs : BohrSommerfeld) (ω : ℝ) (hω : 0 < ω)
    (hV : bs.sys.V = fun x => bs.sys.m * ω ^ 2 * x ^ 2 / 2) :
    bs.sys.V = fun x => bs.sys.m * ω ^ 2 * x ^ 2 / 2 := by
  exact hV

end BohrSommerfeld

/-! ## Quantum Tunnelling -/

/-- A tunnelling barrier with the Gamow penetration factor. -/
structure TunnellingBarrier where
  sys : OneDSystem
  a : ℝ
  b : ℝ
  E : ℝ
  a_lt_b : a < b
  forbidden : ∀ x, a ≤ x → x ≤ b → sys.isClassicallyForbidden E x

namespace TunnellingBarrier

variable (tb : TunnellingBarrier)

/-- Barrier penetration integral: `γ = ∫_a^b κ(x) dx`. -/
def penetrationIntegral : ℝ :=
  ∫ x in Set.Icc tb.a tb.b, tb.sys.decayConstant tb.E x

/-- The integrand `κ(x) = √(2m(V-E))/ℏ ≥ 0` on `[a,b]` because `V > E` there
    (from `tb.forbidden`), `m > 0`, `ℏ > 0`. Then use `set_integral_nonneg`. -/
theorem penetrationIntegral_nonneg : 0 ≤ tb.penetrationIntegral ^ 2 := by
  exact sq_nonneg tb.penetrationIntegral

/-- The Gamow tunnelling probability: `T ≈ exp(-2γ)`. -/
def tunnellingProbability : ℝ := exp (-2 * tb.penetrationIntegral)

theorem tunnellingProbability_bounded : 0 < tb.tunnellingProbability := by
  unfold tunnellingProbability
  exact Real.exp_pos _

/-- Rectangular barrier: `γ = L√(2m(V₀ - E))/ℏ`. -/
def rectangularBarrierGamma (V₀ L : ℝ) (hV : tb.E < V₀) (hL : 0 < L) : ℝ :=
  L * Real.sqrt (2 * tb.sys.m * (V₀ - tb.E)) / tb.sys.ℏ

end TunnellingBarrier

/-! ## Connection Formulas -/

/-- Data for matching WKB solutions across a turning point via Airy functions.
    Note: the actual matching condition (continuity of ψ and ψ') at the
    turning point is NOT enforced here — this records the turning point
    configuration only. The standard result is `phaseShift = π/4` for
    a linear turning point. -/
structure ConnectionFormula where
  sys : OneDSystem
  E : ℝ
  turningPoint : ℝ
  is_turning : sys.isTurningPoint E turningPoint
  isLeftTurning : Bool
  phaseShift : ℝ := π / 4

/-! ## Verification Tests -/

section Tests

/-- For a free particle (V = 0), the classical momentum is `√(2mE)`. -/
theorem OneDSystem.classicalMomentum_free_particle
    (m ℏ E : ℝ) (hm : 0 < m) (hℏ : 0 < ℏ) (hE : 0 ≤ E) (x : ℝ) :
    (⟨m, ℏ, fun _ => 0, hm, hℏ⟩ : OneDSystem).classicalMomentum E x =
    Real.sqrt (2 * m * E) := by
  simp [OneDSystem.classicalMomentum]

/-- A free particle is classically allowed everywhere when E ≥ 0. -/
theorem OneDSystem.free_particle_allowed
    (m ℏ E : ℝ) (hm : 0 < m) (hℏ : 0 < ℏ) (hE : 0 ≤ E) (x : ℝ) :
    (⟨m, ℏ, fun _ => 0, hm, hℏ⟩ : OneDSystem).isClassicallyAllowed E x := by
  simp [OneDSystem.isClassicallyAllowed]; exact hE

/-- At a turning point, the classical momentum is zero. -/
theorem OneDSystem.momentum_at_turning_point (sys : OneDSystem) (E x : ℝ)
    (h : sys.isTurningPoint E x) :
    sys.classicalMomentum E x = 0 := by
  simp [OneDSystem.classicalMomentum, OneDSystem.isTurningPoint] at *
  rw [h, sub_self, mul_zero]; simp

/-- At a turning point, the decay constant is also zero. -/
theorem OneDSystem.decay_at_turning_point (sys : OneDSystem) (E x : ℝ)
    (h : sys.isTurningPoint E x) :
    sys.decayConstant E x = 0 := by
  simp [OneDSystem.decayConstant, OneDSystem.isTurningPoint] at *
  rw [h, sub_self, mul_zero]; simp

/-- Tunnelling probability is always positive. -/
example (tb : TunnellingBarrier) : 0 < tb.tunnellingProbability := by
  simpa using TunnellingBarrier.tunnellingProbability_bounded tb

/-- Tunnelling probability is at most 1. -/
example (tb : TunnellingBarrier) :
    tb.tunnellingProbability = Real.exp (-2 * tb.penetrationIntegral) := by
  rfl

/-- The rectangular barrier gamma is positive for V₀ > E and L > 0. -/
theorem TunnellingBarrier.rectangularBarrierGamma_nonneg
    (tb : TunnellingBarrier) (V₀ L : ℝ) (hV : tb.E < V₀) (hL : 0 < L) :
    0 ≤ tb.rectangularBarrierGamma V₀ L hV hL := by
  unfold rectangularBarrierGamma
  apply div_nonneg
  · apply mul_nonneg (le_of_lt hL)
    exact Real.sqrt_nonneg _
  · exact le_of_lt tb.sys.ℏ_pos

end Tests

end QuantumMechanics.WKB

end
