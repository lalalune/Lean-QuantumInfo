/-
Copyright (c) 2025 PhysLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

-- Source domain: CO₂ laser optics, tin target, and EUV emission
import EUVLithography.Source.GaussianBeam
import EUVLithography.Source.AblationPressure
import EUVLithography.Source.TinDroplet
import EUVLithography.Source.EUVEmission

-- Plasma physics: frequency, IB heating, ionization, thermodynamics
import EUVLithography.Plasma.PlasmaFrequency
import EUVLithography.Plasma.InverseBremsstrahlung
import EUVLithography.Plasma.SahaEquation
import EUVLithography.Plasma.Thermodynamics

-- Wave and thin-film optics: Fresnel, Bragg, transfer matrix, radiometry
import EUVLithography.Optics.FresnelEquations
import EUVLithography.Optics.BraggCondition
import EUVLithography.Optics.TransferMatrix
import EUVLithography.Optics.Etendue

-- Gas physics: Beer-Lambert attenuation and vacuum requirements
import EUVLithography.GasPhysics.BeerLambert

-- Mirror contamination and cleaning chemistry
import EUVLithography.Contamination.MirrorPhysics

-- Image formation: illumination, reflective mask, projection optics
import EUVLithography.ImageFormation.Illumination
import EUVLithography.ImageFormation.Mask
import EUVLithography.ImageFormation.ProjectionOptics

-- Photoresist: photo-chemistry, acid diffusion, shot noise
import EUVLithography.Resist.DillModel
import EUVLithography.Resist.AcidDiffusion
import EUVLithography.Resist.ShotNoise

-- Numeric sanity checks against report values
import EUVLithography.Numerics.ReportChecks

/-!

# EUV Lithography — Complete Mathematical Formalization

This library formalizes all physical processes in an Extreme Ultraviolet (EUV)
lithography machine, organized by physics/math domain.

## Domain Structure

### Source Physics (`Source/`)
- **GaussianBeam**: Gaussian laser beam, Rayleigh range, focused intensity
- **AblationPressure**: CO₂ laser ablation, scaling with intensity
- **TinDroplet**: Rayleigh-Plateau breakup, droplet trajectory, pre-pulse geometry
- **EUVEmission**: Photon energy, conversion efficiency, Einstein A coefficient

### Plasma Physics (`Plasma/`)
- **PlasmaFrequency**: ω_p, critical density n_c, refractive index, group velocity
- **InverseBremsstrahlung**: IB absorption coefficient, ponderomotive energy
- **SahaEquation**: Saha ionization equilibrium, quantum concentration
- **Thermodynamics**: Plasma pressure, electron-ion coupling, temperature relaxation

### Wave and Thin-Film Optics (`Optics/`)
- **FresnelEquations**: Fresnel reflectance Rs/Rp, Snell's law, critical angle
- **BraggCondition**: Mo/Si multilayer Bragg condition, Debye-Waller roughness factor
- **TransferMatrix**: Transfer matrix method for multilayer stacks
- **Etendue**: Solid angle, collection efficiency, radiance conservation

### Gas Physics (`GasPhysics/`)
- **BeerLambert**: Beer-Lambert attenuation, absorption length ∝ 1/P, vacuum requirements

### Contamination Physics (`Contamination/`)
- **MirrorPhysics**: Sn deposition flux (∝ 1/R²), reflectivity degradation,
  H-radical cleaning (Sn + 4H* → SnH₄↑), steady-state Sn density,
  carbon contamination rate

### Image Formation (`ImageFormation/`)
- **Illumination**: Partial coherence, illumination NA = σ × NA_proj
- **Mask**: Reflective mask contrast, 3D shadow, diffraction grating condition, demagnification
- **ProjectionOptics**: Rayleigh resolution, Abbe limit, depth of focus,
  Strehl ratio, wavefront requirement (W_rms < λ/60 → S > 0.98)

### Photoresist (`Resist/`)
- **DillModel**: Inhibitor/acid concentration, diffusion blur, dissolution rate (Mack model)
- **AcidDiffusion**: Fickian diffusion length σ = √(2Dt), Gaussian blur kernel,
  contrast attenuation factor exp(-2π²σ²/p²) for pitch p
- **ShotNoise**: Poisson photon statistics, LER = (CD/2)/√N̄, dose-LER scaling

## Physical Process Summary (EUV photon journey)

1. CO₂ laser (10.6 μm) focused to ~15 μm on Sn droplet → ablation pressure
2. Pre-pulse creates thin disk; main pulse forms plasma (T_e ≈ 30–40 eV)
3. Inverse bremsstrahlung heats plasma; Saha equilibrium gives Sn⁸⁺–Sn¹⁴⁺
4. These ions emit 13.5 nm photons (4d→4f transitions, CE ≈ 6%)
5. Mo/Si collector mirror (R ≈ 70%, 40 bilayers, Bragg at θ = 0) focuses EUV
6. Tin contamination cleaned by H radicals; carbon cleaned by EUV-activated H
7. Illumination condenser (etendue-matched) reshapes beam for uniform illumination
8. Reflective TaN/Mo/Si mask (R_ML ≈ 65%, R_abs ≈ 0.5%, contrast ≈ 0.985)
9. Six-mirror projection system (NA = 0.33–0.55) demagnifies 4×
10. Resolution R = k₁λ/NA ≈ 12 nm; DoF = k₂λ/NA² ≈ 40–120 nm
11. Wavefront error W_rms < λ/60 → Strehl > 0.98
12. Resist: M(D) = M₀ exp(-CD), acid diffuses σ = √(2D_acid t_PEB)
13. Shot noise: ~2700 photons per 10×10 nm feature → LER ≈ CD/(2√N̄)
14. Vacuum: P < 10 Pa required (EUV absorbed in air in < 1 mm)

-/
