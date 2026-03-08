/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import StatMech.BoltzmannConstant

/-!
# Fluctuation-Dissipation Relations

Formalization of the fluctuation-dissipation theorem and related identities connecting
thermal fluctuations to response functions in statistical mechanical systems.

## Main definitions

* `LinearResponseFunction` : the response of an observable to an external perturbation
* `SpectralDensity` : the spectral density of fluctuations
* `FluctuationDissipation` : the FDT relating response to equilibrium fluctuations
* `EinsteinRelation` : the relation between diffusion and mobility
* `NyquistFormula` : Johnson-Nyquist noise in electrical circuits
* `SusceptibilityFromFluctuations` : isothermal susceptibility from variance

## References

* R. Kubo, "The fluctuation-dissipation theorem", Rep. Prog. Phys. 29 (1966) 255
* L.D. Landau & E.M. Lifshitz, *Statistical Physics*, §124-126
-/

noncomputable section

open Real Constants

namespace StatMech

/-! ## Response Functions -/

/-- A linear response function χ(ω) connecting an observable's response to an applied field.
    The response at frequency ω is `⟨δA(ω)⟩ = χ(ω) · F(ω)`. -/
structure LinearResponseFunction where
  /-- Real part of the susceptibility (reactive part). -/
  χ' : ℝ → ℝ
  /-- Imaginary part of the susceptibility (dissipative part). -/
  χ'' : ℝ → ℝ
  /-- The dissipative part is odd: χ''(-ω) = -χ''(ω). -/
  χ''_odd : ∀ ω, χ'' (-ω) = -χ'' ω
  /-- The reactive part is even: χ'(-ω) = χ'(ω). -/
  χ'_even : ∀ ω, χ' (-ω) = χ' ω

namespace LinearResponseFunction

variable (χ : LinearResponseFunction)

/-- The full complex susceptibility χ(ω) = χ'(ω) + i·χ''(ω). -/
def susceptibility (ω : ℝ) : ℂ :=
  ⟨χ.χ' ω, χ.χ'' ω⟩

/-- The static susceptibility (zero-frequency response). -/
def staticSusceptibility : ℝ := χ.χ' 0

/-- At zero frequency, the imaginary part vanishes. -/
theorem χ''_zero : χ.χ'' 0 = 0 := by
  have h := χ.χ''_odd 0
  simp at h
  linarith

end LinearResponseFunction

/-! ## Spectral Density -/

/-- The spectral density S(ω) of fluctuations in an observable A.
    `S(ω) = ∫ dt e^{iωt} ⟨A(t)A(0)⟩` -/
structure SpectralDensity where
  /-- The spectral density function. -/
  S : ℝ → ℝ
  /-- Spectral density is non-negative (for classical systems). -/
  S_nonneg : ∀ ω, 0 ≤ S ω

/-! ## Fluctuation-Dissipation Theorem -/

/-- The classical fluctuation-dissipation theorem:
    `S(ω) = (2kT/ω) χ''(ω)` for `ω > 0`.
    This relates the spectral density of equilibrium fluctuations to the
    dissipative part of the linear response function. -/
structure FluctuationDissipationTheorem where
  temperature : ℝ
  response : LinearResponseFunction
  spectral : SpectralDensity
  temp_pos : 0 < temperature
  /-- The classical FDT relation. -/
  fdt_classical : ∀ ω, 0 < ω →
    spectral.S ω = 2 * kB * temperature / ω * response.χ'' ω

namespace FluctuationDissipationTheorem

variable (fdt : FluctuationDissipationTheorem)

/-- The quantum fluctuation-dissipation theorem uses the Bose-Einstein factor:
    `S(ω) = 2ℏ · n_B(ω) · χ''(ω)` where `n_B(ω) = 1/(e^{βℏω} - 1)`. -/
def quantumSpectralDensity (ℏ : ℝ) (ω : ℝ) (hω : ω ≠ 0) : ℝ :=
  let β := 1 / (kB * fdt.temperature)
  2 * ℏ * (1 / (exp (β * ℏ * ω) - 1)) * fdt.response.χ'' ω

/-- Unfolding `quantumSpectralDensity` to its explicit Bose-Einstein form.
    Note: this is definitional; it does NOT prove the classical limit
    `n_B(ω) → kT/(ℏω)` as `ℏω/kT → 0`, which would require analysis of `exp`. -/
theorem quantumSpectralDensity_unfold (ℏ ω : ℝ) (hω : ω ≠ 0) :
    fdt.quantumSpectralDensity ℏ ω hω =
    2 * ℏ * (1 / (exp (ℏ * ω / (kB * fdt.temperature)) - 1)) * fdt.response.χ'' ω := by
  simp only [quantumSpectralDensity]
  have h : 1 / (kB * fdt.temperature) * ℏ * ω = ℏ * ω / (kB * fdt.temperature) := by ring
  rw [h]

end FluctuationDissipationTheorem

/-! ## Einstein Relation -/

/-- The Einstein relation connecting diffusion coefficient D to mobility μ:
    `D = μ kT` (also `D = kT / (6πηa)` for a sphere in Stokes flow). -/
structure EinsteinRelation where
  diffusionCoeff : ℝ
  mobility : ℝ
  temperature : ℝ
  diffusion_pos : 0 < diffusionCoeff
  mobility_pos : 0 < mobility
  temp_pos : 0 < temperature
  /-- D = μ kT -/
  relation : diffusionCoeff = mobility * kB * temperature

namespace EinsteinRelation

variable (er : EinsteinRelation)

/-- The Stokes-Einstein relation: `D = kT / (6πηa)` for a sphere of radius `a`
    in a fluid with viscosity `η`. -/
def stokesEinstein (η a : ℝ) (hη : 0 < η) (ha : 0 < a) : ℝ :=
  kB * er.temperature / (6 * π * η * a)

/-- Mobility from Einstein relation. -/
theorem mobility_eq :
    er.mobility = er.diffusionCoeff / (kB * er.temperature) := by
  have hkT : kB * er.temperature ≠ 0 := ne_of_gt (mul_pos kB_pos er.temp_pos)
  rw [er.relation, mul_assoc, mul_div_cancel_right₀ _ hkT]

end EinsteinRelation

/-! ## Nyquist Formula -/

/-- The Johnson-Nyquist formula for thermal noise voltage across a resistor:
    `⟨V²⟩ = 4 kT R Δf`, where R is resistance and Δf is bandwidth. -/
structure NyquistFormula where
  resistance : ℝ
  temperature : ℝ
  bandwidth : ℝ
  resistance_pos : 0 < resistance
  temp_pos : 0 < temperature
  bandwidth_pos : 0 < bandwidth

namespace NyquistFormula

variable (nf : NyquistFormula)

/-- The mean-square noise voltage. -/
def meanSquareVoltage : ℝ :=
  4 * kB * nf.temperature * nf.resistance * nf.bandwidth

/-- The mean-square voltage is positive. -/
theorem meanSquareVoltage_pos : 0 < nf.meanSquareVoltage := by
  unfold meanSquareVoltage
  apply mul_pos (mul_pos (mul_pos (mul_pos (by positivity) kB_pos) nf.temp_pos)
    nf.resistance_pos) nf.bandwidth_pos

/-- The RMS noise voltage. -/
def rmsVoltage : ℝ := Real.sqrt nf.meanSquareVoltage

/-- RMS voltage is non-negative. -/
theorem rmsVoltage_nonneg : 0 ≤ nf.rmsVoltage :=
  Real.sqrt_nonneg _

/-- The noise spectral density is flat (white noise): `S_V(f) = 4kTR`. -/
def voltageSpectralDensity : ℝ := 4 * kB * nf.temperature * nf.resistance

end NyquistFormula

/-! ## Susceptibility from Fluctuations -/

/-- The isothermal susceptibility of an observable A is proportional to its variance:
    `χ_T = β ⟨(δA)²⟩ = β (⟨A²⟩ - ⟨A⟩²)`. -/
structure SusceptibilityFromFluctuations where
  β : ℝ
  meanA : ℝ
  meanA_sq : ℝ
  β_pos : 0 < β
  /-- ⟨A²⟩ ≥ ⟨A⟩² (Cauchy-Schwarz). -/
  cauchy_schwarz : meanA ^ 2 ≤ meanA_sq

namespace SusceptibilityFromFluctuations

variable (sf : SusceptibilityFromFluctuations)

/-- The variance of A. -/
def variance : ℝ := sf.meanA_sq - sf.meanA ^ 2

/-- Variance is non-negative. -/
theorem variance_nonneg : 0 ≤ sf.variance := by
  unfold variance
  linarith [sf.cauchy_schwarz]

/-- The isothermal susceptibility. -/
def susceptibility : ℝ := sf.β * sf.variance

/-- Susceptibility is non-negative. -/
theorem susceptibility_nonneg : 0 ≤ sf.susceptibility := by
  unfold susceptibility
  exact mul_nonneg (le_of_lt sf.β_pos) sf.variance_nonneg

end SusceptibilityFromFluctuations

/-! ## Onsager Reciprocal Relations -/

/-- Onsager's reciprocal relations: the matrix of transport coefficients is symmetric
    when proper thermodynamic forces and fluxes are used.
    `L_{ij} = L_{ji}` where `J_i = Σ_j L_{ij} X_j`. -/
structure OnsagerRelations (n : ℕ) where
  /-- The matrix of transport (kinetic) coefficients. -/
  L : Fin n → Fin n → ℝ
  /-- Onsager reciprocity: L is symmetric. -/
  reciprocity : ∀ i j, L i j = L j i
  /-- Positive semi-definiteness (second law constraint). -/
  positive_semidefinite : ∀ x : Fin n → ℝ,
    0 ≤ ∑ i, ∑ j, L i j * x i * x j

namespace OnsagerRelations

variable {n : ℕ} (ons : OnsagerRelations n)

/-- The entropy production rate σ = Σ_{ij} L_{ij} X_i X_j ≥ 0. -/
def entropyProductionRate (forces : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, ons.L i j * forces i * forces j

/-- Entropy production is non-negative (second law). -/
theorem entropyProductionRate_nonneg (forces : Fin n → ℝ) :
    0 ≤ ons.entropyProductionRate forces :=
  ons.positive_semidefinite forces

/-- The flux driven by thermodynamic forces. -/
def flux (forces : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j, ons.L i j * forces j

end OnsagerRelations

/-! ## Verification Tests -/

section Tests

/-- The imaginary part of the response function vanishes at zero frequency. -/
example (χ : LinearResponseFunction) : χ.χ'' 0 = 0 := χ.χ''_zero

/-- The static susceptibility is just the real part at ω = 0. -/
example (χ : LinearResponseFunction) : χ.staticSusceptibility = χ.χ' 0 := rfl

/-- The Einstein relation can be solved for mobility. -/
example (er : EinsteinRelation) :
    er.mobility = er.diffusionCoeff / (kB * er.temperature) :=
  er.mobility_eq

/-- The RMS voltage is non-negative. -/
example (nf : NyquistFormula) : 0 ≤ nf.rmsVoltage := nf.rmsVoltage_nonneg

/-- The mean-square voltage is positive. -/
example (nf : NyquistFormula) : 0 < nf.meanSquareVoltage := nf.meanSquareVoltage_pos

/-- Variance is non-negative (Cauchy-Schwarz). -/
example (sf : SusceptibilityFromFluctuations) : 0 ≤ sf.variance :=
  sf.variance_nonneg

/-- Susceptibility is non-negative. -/
example (sf : SusceptibilityFromFluctuations) : 0 ≤ sf.susceptibility :=
  sf.susceptibility_nonneg

/-- Zero variance means ⟨A²⟩ = ⟨A⟩² (no fluctuations). -/
theorem SusceptibilityFromFluctuations.variance_zero_iff
    (sf : SusceptibilityFromFluctuations)
    (h : sf.variance = 0) :
    sf.meanA_sq = sf.meanA ^ 2 := by
  unfold SusceptibilityFromFluctuations.variance at h; linarith

/-- Zero variance implies zero susceptibility. -/
theorem SusceptibilityFromFluctuations.zero_variance_zero_susceptibility
    (sf : SusceptibilityFromFluctuations)
    (h : sf.variance = 0) :
    sf.susceptibility = 0 := by
  simp [SusceptibilityFromFluctuations.susceptibility, h]

/-- Onsager relations are indeed symmetric. -/
example {n : ℕ} (ons : OnsagerRelations n) (i j : Fin n) :
    ons.L i j = ons.L j i :=
  ons.reciprocity i j

/-- Entropy production with zero forces is zero. -/
theorem OnsagerRelations.entropyProductionRate_zero
    {n : ℕ} (ons : OnsagerRelations n) :
    ons.entropyProductionRate 0 = 0 := by
  simp [OnsagerRelations.entropyProductionRate]

/-- Flux with zero forces is zero. -/
theorem OnsagerRelations.flux_zero
    {n : ℕ} (ons : OnsagerRelations n) (i : Fin n) :
    ons.flux 0 i = 0 := by
  simp [OnsagerRelations.flux]

end Tests

end StatMech

end
