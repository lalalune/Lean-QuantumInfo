import Relativity.GR.KerrMetric.Components
import Relativity.GR.KerrMetric.HorizonsErgospheres
import Relativity.GR.KerrMetric.RingSingularity
import Relativity.GR.KerrMetric.Thermodynamics
/-!
# Horizon Area and Extremal Limit

Canonical definitions for Kerr black hole horizon area and extremal limit theorems.
Consolidated to avoid duplication with `KerrMetric.lean` and `Exploration.lean`.

**Connection to entropy:** S_BH = A/(4ℓ_P²) where ℓ_P is Planck length (Bekenstein-Hawking).
-/

namespace Kerr.Extensions
open Kerr.Components Kerr.Horizons Kerr.Ring Kerr.Thermodynamics

/-- Surface area of outer event horizon: A = 4π(r_+² + a²) -/
noncomputable def horizon_area (p : KerrParams) : ℝ :=
  4 * Real.pi * ((r_plus p)^2 + p.a^2)

/-- The horizon area is always positive. -/
theorem horizon_area_positive (p : KerrParams) :
    horizon_area p > 0 := by
  unfold horizon_area
  have h_rplus_pos : r_plus p > 0 := r_plus_positive p
  have h1 : (r_plus p)^2 > 0 := sq_pos_of_pos h_rplus_pos
  have h2 : p.a^2 ≥ 0 := sq_nonneg p.a
  have h3 : (r_plus p)^2 + p.a^2 > 0 := by linarith
  have h4 : Real.pi > 0 := Real.pi_pos
  have h5 : 4 * Real.pi > 0 := by linarith
  exact mul_pos h5 h3

/-- In Schwarzschild (a = 0), the horizon area equals 16πM². -/
theorem schwarzschild_area (M : ℝ) (hM : 0 < M) :
    horizon_area (schwarzschildParams M hM) = 16 * Real.pi * M^2 := by
  unfold horizon_area schwarzschildParams r_plus
  simp
  have h_discrim : M^2 - 0 = M^2 := by ring
  have h_sqrt : Real.sqrt (M^2 - 0) = M := by
    rw [h_discrim]
    exact Real.sqrt_sq (le_of_lt hM)
  have h_rplus : M + Real.sqrt (M^2 - 0) = 2 * M := by
    rw [h_sqrt]
    ring
  calc 4 * Real.pi * ((M + Real.sqrt (M^2))^2)
      = 4 * Real.pi * (M + Real.sqrt (M^2 - 0))^2 := by ring_nf
    _ = 4 * Real.pi * (2 * M)^2 := by rw [h_rplus]
    _ = 4 * Real.pi * (4 * M^2) := by ring
    _ = 16 * Real.pi * M^2 := by ring

def extremalKerrParams (M : ℝ) (hM : 0 < M) : KerrParams :=
  ⟨M, M, hM, by rw [abs_of_pos hM]⟩

theorem extremal_horizons_merge (M : ℝ) (hM : 0 < M) :
    let p := extremalKerrParams M hM
    r_plus p = r_minus p := by
  unfold extremalKerrParams r_plus r_minus
  simp

theorem extremal_zero_surface_gravity (M : ℝ) (hM : 0 < M) :
    let p := extremalKerrParams M hM
    surface_gravity_outer p = 0 := by
  unfold surface_gravity_outer extremalKerrParams r_plus r_minus
  simp

theorem extremal_zero_temperature (M : ℝ) (hM : 0 < M) :
    let p := extremalKerrParams M hM
    hawkingTemperature p = 0 := by
  unfold hawkingTemperature
  have h_kappa : surface_gravity_outer (extremalKerrParams M hM) = 0 :=
    extremal_zero_surface_gravity M hM
  ring_nf
  rw [h_kappa]
  simp

theorem extremal_positive_area' (M : ℝ) (hM : 0 < M) :
    let p := extremalKerrParams M hM
    horizon_area p > 0 := by
  unfold horizon_area extremalKerrParams r_plus
  simp
  have h_discrim : M^2 - M^2 = 0 := by ring
  have h_sqrt : Real.sqrt (M^2 - M^2) = 0 := by
    rw [h_discrim, Real.sqrt_zero]
  have h_rplus : M + Real.sqrt (M^2 - M^2) = M := by
    rw [h_sqrt]
    ring
  have h_rplus_sq : (M + Real.sqrt (M^2 - M^2))^2 = M^2 := by
    rw [h_rplus]
  rw [h_rplus_sq.symm]
  simp
  have h1 : M^2 > 0 := sq_pos_of_pos hM
  have h2 : M^2 + M^2 > 0 := by linarith
  have h3 : Real.pi > 0 := Real.pi_pos
  have h4 : 4 * Real.pi > 0 := by linarith
  exact mul_pos h4 h2

def vacuum_solution_valid_at (p : KerrParams) (x : BoyerLindquistCoords) : Prop :=
  x.r ≥ r_minus p ∧ Sigma_K p x.r x.θ ≠ 0

theorem kerr_exterior_only_extensions' (p : KerrParams) :
    ∀ (x : BoyerLindquistCoords),
      x.r < r_minus p →
      ¬(vacuum_solution_valid_at p x) := by
  intro x hx
  unfold vacuum_solution_valid_at
  push_neg
  intro _
  linarith

theorem extremal_discriminant_zero (M : ℝ) (hM : 0 < M) :
    let p := extremalKerrParams M hM
    p.M^2 - p.a^2 = 0 := by
  unfold extremalKerrParams
  simp

theorem extremal_temperatures_equal (M : ℝ) (hM : 0 < M) :
    let p := extremalKerrParams M hM
    innerHorizonTemperature p = hawkingTemperature p ∧
    hawkingTemperature p = 0 := by
  constructor
  · unfold innerHorizonTemperature hawkingTemperature surface_gravity_inner surface_gravity_outer
    unfold extremalKerrParams r_plus r_minus
    have h_discrim : M^2 - M^2 = 0 := by ring
    have h_sqrt : Real.sqrt (M^2 - M^2) = 0 := by
      rw [h_discrim, Real.sqrt_zero]
    have h_numer : (M + Real.sqrt (M^2 - M^2)) - (M - Real.sqrt (M^2 - M^2)) = 0 := by
      calc (M + Real.sqrt (M^2 - M^2)) - (M - Real.sqrt (M^2 - M^2))
          = 2 * Real.sqrt (M^2 - M^2) := by ring
        _ = 2 * 0 := by rw [h_sqrt]
        _ = 0 := by ring
    simp
  · unfold hawkingTemperature surface_gravity_outer extremalKerrParams r_plus r_minus
    have h_discrim : M^2 - M^2 = 0 := by ring
    have h_sqrt : Real.sqrt (M^2 - M^2) = 0 := by
      rw [h_discrim, Real.sqrt_zero]
    have h_numer : (M + Real.sqrt (M^2 - M^2)) - (M - Real.sqrt (M^2 - M^2)) = 0 := by
      calc (M + Real.sqrt (M^2 - M^2)) - (M - Real.sqrt (M^2 - M^2))
          = 2 * Real.sqrt (M^2 - M^2) := by ring
        _ = 2 * 0 := by rw [h_sqrt]
        _ = 0 := by ring
    simp

theorem extremal_positive_area (M : ℝ) (hM : 0 < M) :
    let p := extremalKerrParams M hM
    horizon_area p > 0 := by
  unfold horizon_area extremalKerrParams r_plus
  simp
  have h1 : M^2 > 0 := sq_pos_of_pos hM
  have h2 : M^2 + M^2 > 0 := by linarith
  have h3 : Real.pi > 0 := Real.pi_pos
  have h4 : 4 * Real.pi > 0 := by linarith
  exact mul_pos h4 h2

theorem extremal_area_value (M : ℝ) (hM : 0 < M) :
    let p := extremalKerrParams M hM
    horizon_area p = 8 * Real.pi * M^2 := by
  unfold horizon_area extremalKerrParams r_plus
  simp
  have h_discrim : M^2 - M^2 = 0 := by ring
  have h_sqrt : Real.sqrt (M^2 - M^2) = 0 := by
    rw [h_discrim, Real.sqrt_zero]
  have h_rplus : M + Real.sqrt (M^2 - M^2) = M := by
    calc M + Real.sqrt (M^2 - M^2)
        = M + 0 := by rw [h_sqrt]
      _ = M := by ring
  rw [h_rplus.symm]
  ring

end Kerr.Extensions
