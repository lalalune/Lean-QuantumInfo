import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# EUV Lithography: Tin Droplet Geometry and Kinematics

Formal algebra for Rayleigh-Plateau droplet sizing, ballistic trajectory, and
pre-pulse disk geometry.
-/

noncomputable section

open Real

/-- Inviscid Rayleigh-Plateau fastest-growing wavelength model. -/
def rayleighPlateauWavelength (D_jet : ℝ) : ℝ :=
  2 * π * D_jet / sqrt 2

theorem rayleighPlateauWavelength_pos {D_jet : ℝ} (hD : 0 < D_jet) :
    0 < rayleighPlateauWavelength D_jet := by
  unfold rayleighPlateauWavelength
  positivity

/-- Larger liquid-jet diameter gives a longer fastest-growing Rayleigh-Plateau wavelength. -/
theorem rayleighPlateauWavelength_increases_with_jet_diameter {D₁ D₂ : ℝ}
    (hD : D₁ < D₂) :
    rayleighPlateauWavelength D₁ < rayleighPlateauWavelength D₂ := by
  unfold rayleighPlateauWavelength
  exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hD (mul_pos two_pos pi_pos))
    (sqrt_pos_of_pos (by norm_num))

/-- The inviscid model fixes `λ_RP / D_jet = 2π / √2` for nonzero jet diameter. -/
theorem rayleighPlateauWavelength_over_diameter {D_jet : ℝ} (hD : D_jet ≠ 0) :
    rayleighPlateauWavelength D_jet / D_jet = 2 * π / sqrt 2 := by
  unfold rayleighPlateauWavelength
  field_simp [hD]

/-- Empirical EUV tin droplet diameter estimate, `d_drop ≈ 1.89 D_jet`. -/
def dropletDiameter (D_jet : ℝ) : ℝ := 1.89 * D_jet

theorem dropletDiameter_pos {D_jet : ℝ} (hD : 0 < D_jet) :
    0 < dropletDiameter D_jet := by
  unfold dropletDiameter
  positivity

theorem dropletDiameter_increases_with_jet_diameter {D₁ D₂ : ℝ} (hD : D₁ < D₂) :
    dropletDiameter D₁ < dropletDiameter D₂ := by
  unfold dropletDiameter
  exact mul_lt_mul_of_pos_left hD (by norm_num)

/-- The empirical droplet/jet diameter ratio is the constant `1.89`. -/
theorem dropletDiameter_over_jet_diameter {D_jet : ℝ} (hD : D_jet ≠ 0) :
    dropletDiameter D_jet / D_jet = 1.89 := by
  unfold dropletDiameter
  field_simp [hD]

/-- Sphere volume in terms of diameter. -/
def sphereVolumeFromDiameter (d : ℝ) : ℝ := (4 / 3) * π * (d / 2) ^ 3

/-- Volume of one cylindrical jet segment that pinches off into a droplet. -/
def jetSegmentVolume (D_jet lambda_RP : ℝ) : ℝ :=
  π * (D_jet / 2) ^ 2 * lambda_RP

/-- Rayleigh-Plateau volume balance gives `d_drop^3 = 3/2 D_jet^2 λ_RP`. -/
theorem sphere_eq_jetSegmentVolume_iff_cubic {d_drop D_jet lambda_RP : ℝ} :
    sphereVolumeFromDiameter d_drop = jetSegmentVolume D_jet lambda_RP ↔
      d_drop ^ 3 = (3 / 2) * D_jet ^ 2 * lambda_RP := by
  unfold sphereVolumeFromDiameter jetSegmentVolume
  constructor
  · intro h
    have hcalc : π * d_drop ^ 3 / 6 = π * D_jet ^ 2 * lambda_RP / 4 := by
      calc
        π * d_drop ^ 3 / 6 = (4 / 3) * π * (d_drop / 2) ^ 3 := by ring
        _ = π * (D_jet / 2) ^ 2 * lambda_RP := h
        _ = π * D_jet ^ 2 * lambda_RP / 4 := by ring
    have hmul := congrArg (fun x : ℝ => x * (12 / π)) hcalc
    field_simp [pi_ne_zero] at hmul
    linarith
  · intro h
    calc
      (4 / 3) * π * (d_drop / 2) ^ 3 = π * d_drop ^ 3 / 6 := by ring
      _ = π * ((3 / 2) * D_jet ^ 2 * lambda_RP) / 6 := by rw [h]
      _ = π * (D_jet / 2) ^ 2 * lambda_RP := by ring

/-- Cubed droplet diameter implied by the inviscid Rayleigh-Plateau wavelength. -/
def rayleighPlateauDropletDiameterCubed (D_jet : ℝ) : ℝ :=
  (3 / 2) * D_jet ^ 2 * rayleighPlateauWavelength D_jet

theorem rayleighPlateauDropletDiameterCubed_pos {D_jet : ℝ} (hD : 0 < D_jet) :
    0 < rayleighPlateauDropletDiameterCubed D_jet := by
  unfold rayleighPlateauDropletDiameterCubed
  exact mul_pos (mul_pos (by norm_num) (sq_pos_of_pos hD)) (rayleighPlateauWavelength_pos hD)

/-- The inviscid Rayleigh-Plateau model fixes `d_drop^3 / D_jet^3 = 3π/√2`. -/
theorem rayleighPlateauDropletDiameterCubed_ratio {D_jet : ℝ} (hD : D_jet ≠ 0) :
    rayleighPlateauDropletDiameterCubed D_jet / D_jet ^ 3 = 3 * π / sqrt 2 := by
  unfold rayleighPlateauDropletDiameterCubed rayleighPlateauWavelength
  field_simp [hD]

/-- Horizontal droplet trajectory. -/
def dropletX (v₀ t : ℝ) : ℝ := v₀ * t

theorem dropletX_zero_time (v₀ : ℝ) :
    dropletX v₀ 0 = 0 := by
  simp [dropletX]

theorem dropletX_increases_with_time {v₀ t₁ t₂ : ℝ} (hv : 0 < v₀) (ht : t₁ < t₂) :
    dropletX v₀ t₁ < dropletX v₀ t₂ := by
  unfold dropletX
  exact mul_lt_mul_of_pos_left ht hv

/-- The horizontal droplet velocity is constant. -/
theorem dropletX_derivative (v₀ t : ℝ) :
    HasDerivAt (dropletX v₀) v₀ t := by
  unfold dropletX
  simpa using (hasDerivAt_id t).const_mul v₀

/-- Horizontal position error from timing jitter: `Δx = v₀ σ_t`. -/
def timingJitterDisplacement (v₀ sigma_t : ℝ) : ℝ := v₀ * sigma_t

theorem timingJitterDisplacement_eq_position_error (v₀ sigma_t : ℝ) :
    timingJitterDisplacement v₀ sigma_t = dropletX v₀ sigma_t := rfl

theorem timingJitterDisplacement_pos {v₀ sigma_t : ℝ}
    (hv : 0 < v₀) (hsigma : 0 < sigma_t) :
    0 < timingJitterDisplacement v₀ sigma_t := by
  unfold timingJitterDisplacement
  positivity

theorem timingJitterDisplacement_increases_with_jitter {v₀ sigma₁ sigma₂ : ℝ}
    (hv : 0 < v₀) (hsigma : sigma₁ < sigma₂) :
    timingJitterDisplacement v₀ sigma₁ < timingJitterDisplacement v₀ sigma₂ := by
  unfold timingJitterDisplacement
  exact mul_lt_mul_of_pos_left hsigma hv

/-- Vertical droplet trajectory under gravity, with launch height chosen as zero. -/
def dropletY (g t : ℝ) : ℝ := -(1 / 2) * g * t ^ 2

theorem dropletY_zero_time (g : ℝ) :
    dropletY g 0 = 0 := by
  simp [dropletY]

/-- Vertical droplet velocity under gravity is `-g t`. -/
theorem dropletY_derivative (g t : ℝ) :
    HasDerivAt (dropletY g) (-(g * t)) t := by
  unfold dropletY
  convert ((hasDerivAt_id t).pow 2).const_mul (-(1 / 2) * g) using 1
  simp only [id_eq]
  ring

/-- The vertical velocity derivative is the constant acceleration `-g`. -/
def dropletVerticalVelocity (g t : ℝ) : ℝ := -(g * t)

theorem dropletVerticalVelocity_derivative (g t : ℝ) :
    HasDerivAt (dropletVerticalVelocity g) (-g) t := by
  unfold dropletVerticalVelocity
  convert (hasDerivAt_id t).const_mul (-g) using 1
  · funext y
    simp only [id_eq]
    ring
  · ring

theorem dropletY_nonpos {g t : ℝ} (hg : 0 ≤ g) :
    dropletY g t ≤ 0 := by
  unfold dropletY
  nlinarith [sq_nonneg t]

/-- For positive gravity and nonnegative times, later droplets sit lower in the chosen coordinates. -/
theorem dropletY_decreases_with_time {g t₁ t₂ : ℝ}
    (hg : 0 < g) (ht₁ : 0 ≤ t₁) (ht : t₁ < t₂) :
    dropletY g t₂ < dropletY g t₁ := by
  unfold dropletY
  have ht2 : 0 < t₂ := lt_of_le_of_lt ht₁ ht
  have hsquare : t₁ ^ 2 < t₂ ^ 2 := by
    have hprod : 0 < (t₂ - t₁) * (t₂ + t₁) :=
      mul_pos (sub_pos.mpr ht) (add_pos_of_pos_of_nonneg ht2 ht₁)
    nlinarith
  nlinarith

/-- Diameter after pre-pulse expansion by a dimensionless expansion factor. -/
def expandedDiskDiameter (factor d_drop : ℝ) : ℝ := factor * d_drop

theorem expandedDiskDiameter_pos {factor d_drop : ℝ} (hf : 0 < factor) (hd : 0 < d_drop) :
    0 < expandedDiskDiameter factor d_drop := by
  unfold expandedDiskDiameter
  positivity

/-- Tenfold pre-pulse expansion gives `D_disk = 10 d_drop`. -/
theorem expandedDiskDiameter_tenX (d_drop : ℝ) :
    expandedDiskDiameter 10 d_drop = 10 * d_drop := rfl

/-- Thin disk/cylinder volume in terms of diameter and thickness. -/
def diskVolume (D h : ℝ) : ℝ := π * (D / 2) ^ 2 * h

/-- Geometric cross-section of a spherical droplet presented to the laser. -/
def dropletCrossSection (d : ℝ) : ℝ := π * (d / 2) ^ 2

theorem dropletCrossSection_pos {d : ℝ} (hd : 0 < d) :
    0 < dropletCrossSection d := by
  unfold dropletCrossSection
  positivity

/-- A larger droplet intercepts a larger geometric laser area. -/
theorem dropletCrossSection_increases_with_diameter {d₁ d₂ : ℝ}
    (hd₁ : 0 < d₁) (hd : d₁ < d₂) :
    dropletCrossSection d₁ < dropletCrossSection d₂ := by
  unfold dropletCrossSection
  apply mul_lt_mul_of_pos_left _ pi_pos
  have hhalf : d₁ / 2 < d₂ / 2 := div_lt_div_of_pos_right hd two_pos
  have hhalf_pos : 0 < d₁ / 2 := div_pos hd₁ two_pos
  exact sq_lt_sq' (by linarith) hhalf

/-- Laser pulse energy from average power and repetition rate. -/
def pulseEnergy (P_avg f_rep : ℝ) : ℝ := P_avg / f_rep

theorem pulseEnergy_pos {P_avg f_rep : ℝ} (hP : 0 < P_avg) (hf : 0 < f_rep) :
    0 < pulseEnergy P_avg f_rep :=
  div_pos hP hf

/-- At fixed repetition rate, pulse energy grows with average laser power. -/
theorem pulseEnergy_increases_with_average_power {P₁ P₂ f_rep : ℝ}
    (hP : P₁ < P₂) (hf : 0 < f_rep) :
    pulseEnergy P₁ f_rep < pulseEnergy P₂ f_rep :=
  div_lt_div_of_pos_right hP hf

/-- At fixed average power, higher repetition rate lowers energy per pulse. -/
theorem pulseEnergy_decreases_with_rep_rate {P_avg f₁ f₂ : ℝ}
    (hP : 0 < P_avg) (hf₁ : 0 < f₁) (hf : f₁ < f₂) :
    pulseEnergy P_avg f₂ < pulseEnergy P_avg f₁ :=
  div_lt_div_of_pos_left hP hf₁ hf

/-- Laser energy intercepted by a droplet from fluence times projected area. -/
def interceptedLaserEnergy (fluence d : ℝ) : ℝ :=
  fluence * dropletCrossSection d

theorem interceptedLaserEnergy_pos {fluence d : ℝ} (hF : 0 < fluence) (hd : 0 < d) :
    0 < interceptedLaserEnergy fluence d := by
  unfold interceptedLaserEnergy
  exact mul_pos hF (dropletCrossSection_pos hd)

theorem interceptedLaserEnergy_increases_with_fluence {F₁ F₂ d : ℝ}
    (hF : F₁ < F₂) (hd : 0 < d) :
    interceptedLaserEnergy F₁ d < interceptedLaserEnergy F₂ d := by
  unfold interceptedLaserEnergy
  exact mul_lt_mul_of_pos_right hF (dropletCrossSection_pos hd)

theorem interceptedLaserEnergy_increases_with_diameter {fluence d₁ d₂ : ℝ}
    (hF : 0 < fluence) (hd₁ : 0 < d₁) (hd : d₁ < d₂) :
    interceptedLaserEnergy fluence d₁ < interceptedLaserEnergy fluence d₂ := by
  unfold interceptedLaserEnergy
  exact mul_lt_mul_of_pos_left (dropletCrossSection_increases_with_diameter hd₁ hd) hF

/-- Disk thickness obtained by conserving volume when a spherical droplet expands by `factor`. -/
def volumeConservingDiskThickness (factor d : ℝ) : ℝ :=
  2 * d / (3 * factor ^ 2)

theorem sphereVolumeFromDiameter_pos {d : ℝ} (hd : 0 < d) :
    0 < sphereVolumeFromDiameter d := by
  unfold sphereVolumeFromDiameter
  positivity

theorem diskVolume_pos {D h : ℝ} (hD : 0 < D) (hh : 0 < h) :
    0 < diskVolume D h := by
  unfold diskVolume
  positivity

theorem volumeConservingDiskThickness_pos {factor d : ℝ}
    (hf : 0 < factor) (hd : 0 < d) :
    0 < volumeConservingDiskThickness factor d := by
  unfold volumeConservingDiskThickness
  positivity

theorem volumeConservingDiskThickness_decreases_with_expansion {factor₁ factor₂ d : ℝ}
    (hf₁ : 0 < factor₁) (hf : factor₁ < factor₂) (hd : 0 < d) :
    volumeConservingDiskThickness factor₂ d < volumeConservingDiskThickness factor₁ d := by
  unfold volumeConservingDiskThickness
  have hf2sq : factor₁ ^ 2 < factor₂ ^ 2 := by
    nlinarith [mul_pos hf₁ hf₁, mul_lt_mul_of_pos_left hf hf₁,
      mul_lt_mul_of_pos_right hf (lt_trans hf₁ hf)]
  have hden1 : 0 < 3 * factor₁ ^ 2 := mul_pos (by norm_num) (sq_pos_of_pos hf₁)
  have hden : 3 * factor₁ ^ 2 < 3 * factor₂ ^ 2 :=
    mul_lt_mul_of_pos_left hf2sq (by norm_num)
  exact div_lt_div_of_pos_left (mul_pos two_pos hd) hden1 hden

theorem volumeConservingDisk_preserves_volume {factor d : ℝ}
    (hf : factor ≠ 0) :
    diskVolume (factor * d) (volumeConservingDiskThickness factor d) =
      sphereVolumeFromDiameter d := by
  unfold diskVolume volumeConservingDiskThickness sphereVolumeFromDiameter
  field_simp [hf]
  ring

end
