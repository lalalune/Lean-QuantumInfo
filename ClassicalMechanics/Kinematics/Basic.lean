/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Inspired by ATOMSLab/LeanChemicalTheories kinematic equations.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
/-!
# Kinematic Equations of Motion

The four kinematic equations for constant acceleration, proven both for scalar (ℝ)
and vector (normed space) motion.

1. `v(t) = v₀ + a·t`
2. `x(t) = x₀ + v₀·t + ½a·t²`
3. `x(t) = x₀ + ½(v(t) + v₀)·t`
4. `v(t)² = v₀² + 2a·(x(t) - x₀)`

## References

* ATOMSLab/LeanChemicalTheories, arXiv:2210.12150
-/

noncomputable section

open Real MeasureTheory

/-! ## Motion structure -/

/-- Position, velocity, and acceleration related by differentiation. -/
structure Motion (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  position : ℝ → E
  velocity : ℝ → E
  acceleration : ℝ → E
  vel_eq_deriv_pos : velocity = deriv position
  acc_eq_deriv_vel : acceleration = deriv velocity

namespace Motion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem acc_eq_deriv2 (m : Motion E) :
    m.acceleration = deriv (deriv m.position) := by
  rw [m.acc_eq_deriv_vel, m.vel_eq_deriv_pos]

end Motion

/-! ## Scalar kinematic equations (ℝ-valued) -/

namespace ScalarKinematics

variable (x v a : ℝ → ℝ) (α : ℝ)

theorem velocity_eq_const_accel_times_time
    (hv : ∀ t, HasDerivAt x (v t) t)
    (ha : ∀ t, HasDerivAt v (a t) t)
    (h_const : a = fun _ => α)
    (hv_diff : Differentiable ℝ v) :
    v = fun t => α * t + v 0 := by
  have ha' : ∀ t, HasDerivAt v α t := fun t => by
    have := ha t; rw [show a t = α from congr_fun h_const t] at this; exact this
  funext t
  have key : v t - v 0 = α * t := by
    have h1 := (intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := 0) (b := t) (fun s _ => ha' s)
      intervalIntegrable_const).symm
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm] at h1
    linarith
  linarith

theorem position_eq_const_accel
    (hv : ∀ t, HasDerivAt x (v t) t)
    (ha : ∀ t, HasDerivAt v (a t) t)
    (h_const : a = fun _ => α)
    (hv_diff : Differentiable ℝ v)
    (hx_diff : Differentiable ℝ x) :
    x = fun t => α * t ^ 2 / 2 + v 0 * t + x 0 := by
  have hv_eq := velocity_eq_const_accel_times_time x v a α hv ha h_const hv_diff
  funext t
  have hv' : ∀ s, HasDerivAt x (α * s + v 0) s := fun s => by
    have := hv s; rw [show v s = α * s + v 0 from congr_fun hv_eq s] at this; exact this
  have hint : IntervalIntegrable (fun s => α * s + v 0) volume 0 t :=
    Continuous.intervalIntegrable (by fun_prop) 0 t
  have hg : ∀ s ∈ Set.uIcc 0 t,
      HasDerivAt (fun s => α * s ^ 2 / 2 + v 0 * s) (α * s + v 0) s := by
    intro s _
    have h1 : HasDerivAt (fun s => s ^ 2) (2 * s) s := by
      simpa using hasDerivAt_pow 2 s
    have h2 : HasDerivAt (fun s => α / 2 * s ^ 2) (α / 2 * (2 * s)) s :=
      h1.const_mul (α / 2)
    have h3 : HasDerivAt (fun s => v 0 * s) (v 0) s := by
      simpa using (hasDerivAt_id s).const_mul (v 0)
    have h4 := h2.add h3
    convert h4 using 1
    · ext x; simp only [Pi.add_apply]; ring
    · ring
  have ftc_g := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t) hg hint
  have ftc_x := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := 0) (b := t) (fun s _ => hv' s) hint
  simp only [mul_zero] at ftc_g
  linarith [ftc_x, ftc_g]

theorem position_eq_average_velocity
    (hv : ∀ t, HasDerivAt x (v t) t)
    (ha : ∀ t, HasDerivAt v (a t) t)
    (h_const : a = fun _ => α)
    (hv_diff : Differentiable ℝ v)
    (hx_diff : Differentiable ℝ x) :
    ∀ t, x t = (v t + v 0) * t / 2 + x 0 := by
  intro t
  rw [velocity_eq_const_accel_times_time x v a α hv ha h_const hv_diff,
      position_eq_const_accel x v a α hv ha h_const hv_diff hx_diff]
  ring

theorem velocity_sq_eq
    (hv : ∀ t, HasDerivAt x (v t) t)
    (ha : ∀ t, HasDerivAt v (a t) t)
    (h_const : a = fun _ => α)
    (hv_diff : Differentiable ℝ v)
    (hx_diff : Differentiable ℝ x) :
    ∀ t, v t ^ 2 = v 0 ^ 2 + 2 * α * (x t - x 0) := by
  intro t
  rw [velocity_eq_const_accel_times_time x v a α hv ha h_const hv_diff,
      position_eq_const_accel x v a α hv ha h_const hv_diff hx_diff]
  ring

end ScalarKinematics

/-! ## Vector kinematic equations -/

namespace VectorKinematics

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (m : Motion E) (𝔸 : E)

theorem velocity_const_accel
    (h_const : m.acceleration = fun _ => 𝔸)
    (hv_diff : Differentiable ℝ m.velocity) :
    m.velocity = fun t => t • 𝔸 + m.velocity 0 := by
  funext t
  have ha : ∀ s, HasDerivAt m.velocity 𝔸 s := by
    intro s
    have h := (hv_diff s).hasDerivAt
    have heq : deriv m.velocity s = 𝔸 := by
      rw [m.acc_eq_deriv_vel.symm]; exact congr_fun h_const s
    rw [heq] at h; exact h
  have key : m.velocity t - m.velocity 0 = t • 𝔸 := by
    have h1 := (intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := 0) (b := t) (fun s _ => ha s)
      intervalIntegrable_const).symm
    rw [intervalIntegral.integral_const, sub_zero] at h1
    exact h1
  exact sub_eq_iff_eq_add.mp key

theorem position_const_accel
    (h_const : m.acceleration = fun _ => 𝔸)
    (hv_diff : Differentiable ℝ m.velocity)
    (hx_diff : Differentiable ℝ m.position) :
    m.position = fun t => (t ^ 2 / 2) • 𝔸 + t • m.velocity 0 + m.position 0 := by
  have hv := velocity_const_accel m 𝔸 h_const hv_diff
  funext t
  have hx : ∀ s, HasDerivAt m.position (s • 𝔸 + m.velocity 0) s := fun s => by
    have h := (hx_diff s).hasDerivAt
    have heq : deriv m.position s = s • 𝔸 + m.velocity 0 := by
      rw [m.vel_eq_deriv_pos.symm]; exact congr_fun hv s
    rw [heq] at h; exact h
  have hint : IntervalIntegrable (fun s => s • 𝔸 + m.velocity 0) volume 0 t :=
    Continuous.intervalIntegrable (by fun_prop) 0 t
  have hg_deriv : ∀ s ∈ Set.uIcc 0 t,
      HasDerivAt (fun s => (s ^ 2 / 2) • 𝔸 + s • m.velocity 0) (s • 𝔸 + m.velocity 0) s := by
    intro s _
    have h1 : HasDerivAt (fun s => s ^ 2 / 2) s s := by
      have := HasDerivAt.div_const (hasDerivAt_pow 2 s) (2 : ℝ)
      simp only [Nat.cast_ofNat] at this
      convert this using 1; ring
    have h2 := HasDerivAt.smul_const h1 𝔸
    have h3 := HasDerivAt.smul_const (hasDerivAt_id s) (m.velocity 0)
    simp only [one_smul] at h3
    exact h2.add h3
  have ftc_g := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t)
    hg_deriv hint
  have ftc_x := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := t)
    (fun s _ => hx s) hint
  have key : m.position t - m.position 0 = (t ^ 2 / 2) • 𝔸 + t • m.velocity 0 := by
    rw [← ftc_x, ftc_g]
    simp [zero_pow, zero_smul, zero_div, add_zero]
  exact sub_eq_iff_eq_add.mp key

end VectorKinematics

/-! ## Projectile Motion -/

namespace ProjectileMotion

/-- 2D projectile motion under uniform gravity. -/
structure Projectile where
  g : ℝ
  v₀x : ℝ
  v₀y : ℝ
  g_pos : 0 < g

namespace Projectile

variable (p : Projectile)

def xPos (t : ℝ) : ℝ := p.v₀x * t
def yPos (t : ℝ) : ℝ := p.v₀y * t - p.g * t ^ 2 / 2
def vx (_ : ℝ) : ℝ := p.v₀x
def vy (t : ℝ) : ℝ := p.v₀y - p.g * t

def timeToApex (hv₀y : 0 < p.v₀y) : ℝ := p.v₀y / p.g
def maxHeight (hv₀y : 0 < p.v₀y) : ℝ := p.v₀y ^ 2 / (2 * p.g)

theorem vy_at_apex (hv₀y : 0 < p.v₀y) :
    p.vy (p.timeToApex hv₀y) = 0 := by
  unfold vy timeToApex
  have hg : p.g ≠ 0 := ne_of_gt p.g_pos
  field_simp; ring

theorem maxHeight_nonneg (hv₀y : 0 < p.v₀y) : 0 ≤ p.maxHeight hv₀y := by
  unfold maxHeight
  exact div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (le_of_lt p.g_pos))

def timeOfFlight (hv₀y : 0 < p.v₀y) : ℝ := 2 * p.v₀y / p.g

theorem yPos_at_flight_time (hv₀y : 0 < p.v₀y) :
    p.yPos (p.timeOfFlight hv₀y) = 0 := by
  simp [yPos, timeOfFlight]; field_simp; ring

def range (hv₀y : 0 < p.v₀y) : ℝ := p.v₀x * p.timeOfFlight hv₀y

theorem range_eq (hv₀y : 0 < p.v₀y) :
    p.range hv₀y = 2 * p.v₀x * p.v₀y / p.g := by
  simp [range, timeOfFlight]; ring

/-! ## Verification Tests -/

section Tests

variable (p : Projectile)

/-- At t = 0, the projectile is at the origin. -/
theorem xPos_at_zero : p.xPos 0 = 0 := by simp [xPos]
theorem yPos_at_zero : p.yPos 0 = 0 := by simp [yPos]

/-- At t = 0, the horizontal velocity equals v₀x. -/
theorem vx_at_zero : p.vx 0 = p.v₀x := rfl

/-- At t = 0, the vertical velocity equals v₀y. -/
theorem vy_at_zero : p.vy 0 = p.v₀y := by simp [vy]

/-- A purely horizontal projectile (v₀y = 0) has zero initial vertical velocity. -/
theorem vy_horizontal_at_zero (hv₀y : p.v₀y = 0) : p.vy 0 = 0 := by
  simp [vy, hv₀y]

/-- Horizontal velocity is constant over time. -/
theorem vx_constant (t₁ t₂ : ℝ) : p.vx t₁ = p.vx t₂ := rfl

/-- The range is zero when horizontal velocity is zero. -/
theorem range_zero_vx (hv₀x : p.v₀x = 0) (hv₀y : 0 < p.v₀y) :
    p.range hv₀y = 0 := by
  simp [range, hv₀x]

/-- The time of flight is twice the time to apex. -/
theorem timeOfFlight_eq_twice_apex (hv₀y : 0 < p.v₀y) :
    p.timeOfFlight hv₀y = 2 * p.timeToApex hv₀y := by
  simp only [timeOfFlight, timeToApex, mul_div_assoc]

/-- The max height formula is consistent with yPos at the apex. -/
theorem yPos_at_apex (hv₀y : 0 < p.v₀y) :
    p.yPos (p.timeToApex hv₀y) = p.maxHeight hv₀y := by
  simp [yPos, timeToApex, maxHeight]
  field_simp; ring

end Tests

end Projectile

end ProjectileMotion

end
