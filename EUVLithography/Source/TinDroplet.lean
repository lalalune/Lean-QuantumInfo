import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

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

/-- Empirical EUV tin droplet diameter estimate, `d_drop ≈ 1.89 D_jet`. -/
def dropletDiameter (D_jet : ℝ) : ℝ := 1.89 * D_jet

theorem dropletDiameter_pos {D_jet : ℝ} (hD : 0 < D_jet) :
    0 < dropletDiameter D_jet := by
  unfold dropletDiameter
  positivity

/-- Horizontal droplet trajectory. -/
def dropletX (v₀ t : ℝ) : ℝ := v₀ * t

/-- Vertical droplet trajectory under gravity, with launch height chosen as zero. -/
def dropletY (g t : ℝ) : ℝ := -(1 / 2) * g * t ^ 2

theorem dropletY_nonpos {g t : ℝ} (hg : 0 ≤ g) :
    dropletY g t ≤ 0 := by
  unfold dropletY
  nlinarith [sq_nonneg t]

/-- Diameter after pre-pulse expansion by a dimensionless expansion factor. -/
def expandedDiskDiameter (factor d_drop : ℝ) : ℝ := factor * d_drop

theorem expandedDiskDiameter_pos {factor d_drop : ℝ} (hf : 0 < factor) (hd : 0 < d_drop) :
    0 < expandedDiskDiameter factor d_drop := by
  unfold expandedDiskDiameter
  positivity

/-- Sphere volume in terms of diameter. -/
def sphereVolumeFromDiameter (d : ℝ) : ℝ := (4 / 3) * π * (d / 2) ^ 3

/-- Thin disk/cylinder volume in terms of diameter and thickness. -/
def diskVolume (D h : ℝ) : ℝ := π * (D / 2) ^ 2 * h

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

theorem volumeConservingDisk_preserves_volume {factor d : ℝ}
    (hf : factor ≠ 0) :
    diskVolume (factor * d) (volumeConservingDiskThickness factor d) =
      sphereVolumeFromDiameter d := by
  unfold diskVolume volumeConservingDiskThickness sphereVolumeFromDiameter
  field_simp [hf]
  ring

end
