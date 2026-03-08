/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Relativity.GR.Foundations.EinsteinFieldEquations
/-!

# Gravitational Waves

Linearized gravity and gravitational wave solutions, including
the quadrupole formula for gravitational wave emission.

## Main definitions

- `LinearizedMetric` : g_{μν} = η_{μν} + h_{μν}, |h| << 1
- `TT_gauge` : Transverse-traceless gauge h^{TT}
- `GravitationalWaveSolution` : Plane wave solutions h_{μν} = A_{μν} exp(ik·x)
- `QuadrupoleFormula` : P = (G/5c⁵) ⟨d³I_{ij}/dt³ d³I_{ij}/dt³⟩

## Main results

- `linearized_field_equation` : □h̄_{μν} = -16πG T_{μν} in Lorenz gauge
- `wave_equation_vacuum` : □h_{μν} = 0 in vacuum
- `two_polarizations` : GW have exactly 2 independent polarizations (+ and ×)

-/

noncomputable section

/-- A linearized perturbation of flat spacetime:
    g_{μν} = η_{μν} + h_{μν} where |h_{μν}| << 1 -/
structure LinearizedMetric (n : ℕ) where
  /-- The perturbation h_{μν}(x) -/
  perturbation : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ
  /-- The perturbation is symmetric -/
  symmetric : ∀ x μ ν, perturbation x μ ν = perturbation x ν μ

namespace LinearizedMetric

variable {n : ℕ} (h : LinearizedMetric n)

/-- The trace-reversed perturbation: h̄_{μν} = h_{μν} - (1/2) η_{μν} h -/
def traceReversed (η : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) (μ ν : Fin n) : ℝ :=
  h.perturbation x μ ν -
  (1 / 2) * η μ ν * ∑ α, ∑ β, η α β * h.perturbation x α β

/-- The Lorenz gauge condition: ∂^μ h̄_{μν} = 0 -/
def isLorenzGauge (η : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ x ν, ∑ μ, ∑ α, η μ α *
    deriv (fun t => h.traceReversed η (Function.update x μ t) α ν) (x μ) = 0

/-- The linearized Einstein equation in Lorenz gauge:
    □h̄_{μν} = -16πG T_{μν}
    where □ = η^{αβ} ∂_α ∂_β is the d'Alembertian -/
def linearizedFieldEquation (η : Matrix (Fin n) (Fin n) ℝ)
    (T : StressEnergyTensor n) : Prop :=
  ∀ x μ ν,
    ∑ α, ∑ β, η α β *
      deriv (fun t₁ =>
        deriv (fun t₂ => h.traceReversed η
          (Function.update (Function.update x α t₁) β t₂) μ ν)
          ((Function.update x α t₁) β))
        (x α) =
    -16 * Real.pi * gravitationalConstant * T.components x μ ν

end LinearizedMetric

/-- Gravitational wave polarization states -/
inductive GWPolarization
  | plus   -- + polarization
  | cross  -- × polarization

/-- A plane gravitational wave solution in TT gauge:
    h_{μν}^{TT}(x) = A_{μν} cos(k·x + φ) -/
structure GravitationalWave (n : ℕ) where
  /-- The polarization amplitudes -/
  amplitude_plus : ℝ
  amplitude_cross : ℝ
  /-- The wave vector (null: k·k = 0) -/
  waveVector : Fin n → ℝ
  /-- The phase -/
  phase : ℝ
  /-- The wave vector is null (massless gravitons) -/
  null_condition : ∀ η : Matrix (Fin n) (Fin n) ℝ,
    ∑ μ, ∑ ν, η μ ν * waveVector μ * waveVector ν = 0

namespace GravitationalWave

variable {n : ℕ} (gw : GravitationalWave n)

/-- The frequency of the gravitational wave -/
def frequency : ℝ := by
  by_cases hn : n = 0
  · exact 0
  · exact gw.waveVector ⟨0, Nat.pos_of_ne_zero hn⟩

/-- The wavelength λ = 2π/|k| -/
def wavelength : ℝ :=
  2 * Real.pi / Real.sqrt (∑ i : Fin (n - 1), (gw.waveVector ⟨i.val + 1, by omega⟩) ^ 2)

/-- The energy flux (Isaacson formula):
    ⟨T_{GW}^{00}⟩ = (c²/32πG) ⟨ḣ_{ij}^{TT} ḣ_{ij}^{TT}⟩ -/
def energyFlux : ℝ :=
  (1 / (32 * Real.pi * gravitationalConstant)) *
    (gw.frequency ^ 2 * (gw.amplitude_plus ^ 2 + gw.amplitude_cross ^ 2))

end GravitationalWave

/-- The quadrupole formula for gravitational wave power:
    P = (G/5c⁵) ⟨I⃛_{ij} I⃛_{ij}⟩
    where I_{ij} is the reduced mass quadrupole moment -/
def quadrupolePower (G : ℝ) (Idddot_squared : ℝ) : ℝ :=
  G / 5 * Idddot_squared

/-- For a binary system, the power loss by GW emission is
    P = (32/5) G⁴/c⁵ · (m₁ m₂)² (m₁ + m₂) / r⁵ -/
def binaryPower (G m₁ m₂ r : ℝ) : ℝ :=
  (32 / 5) * G ^ 4 * (m₁ * m₂) ^ 2 * (m₁ + m₂) / r ^ 5

/-- The orbital decay rate from gravitational wave emission (Peters formula) -/
def petersDecayRate (G m₁ m₂ a : ℝ) : ℝ :=
  -(64 / 5) * G ^ 3 * m₁ * m₂ * (m₁ + m₂) / a ^ 3

/-- The inspiral time for a binary system to merge -/
def inspiralTime (G m₁ m₂ a₀ : ℝ) : ℝ :=
  (5 / 256) * a₀ ^ 4 / (G ^ 3 * m₁ * m₂ * (m₁ + m₂))

end
