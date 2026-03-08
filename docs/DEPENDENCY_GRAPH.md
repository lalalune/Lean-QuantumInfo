# Lean-QuantumInfo Dependency Graph

Canonical dependency order (simple → complex) for building and understanding the codebase.

---

## Layer 1: Foundation

- **Mathematics** — Fin, List, Calculus, Distribution, InnerProductSpace, VariationalCalculus, Geometry (Riemannian, PseudoRiemannian), FDerivCurry, DataStructures, KroneckerDelta, LinearMaps, PiTensorProduct, RatComplexNum, SO3, SchurTriangulation, SpecialFunctions, Trigonometry
- **Units** — Core, Basic, WithDim (Speed, Area, Pressure, Momentum, Velocity, Mass, Energy), Dimension, domain-specific (Astro, Bio, Chemistry, Crystallography, Earth, Electromagnetism, Fluids, Information, Materials, Mechanics, Metallurgy, Minerals, Optics, Qinfo, Radiation, Relativity, Stats, Thermal, Waves)

### Layer 1 Review
| Item | Status |
|------|--------|
| **Completeness** | ✓ Mathematics and Units modules match codebase |
| **Stubs/Axioms** | ✓ **Mathematics.FunctionalAnalysis.Distributions REMOVED** — import removed from Mathematics.lean; use Mathematics.Distribution.Basic (Mathlib SchwartzSpace). |
| **Notes** | Units.Basic has TODO for SI computability; `inner_top_equiv_norm` and HasVarAdjoint chain noted in AXIOMS.md |

---

## Layer 2: Classical Physics

- **ClassicalInfo** — Prob, Distribution, Entropy, Channel, Capacity
- **ClassicalMechanics** — Basic, EulerLagrange, HamiltonsEquations, HarmonicOscillator, Pendulum, RigidBody, WaveEquation; also CanonicalTransformations, CentralForce, DampedHarmonicOscillator, FluidDynamics, HamiltonJacobi, Kinematics, Lagrangian, Mass, Scattering, Vibrations
- **Thermodynamics** — Basic, Temperature, IdealGas, GibbsFreeEnergy, Laws, MaxwellRelations

### Layer 2 Review
| Item | Status |
|------|--------|
| **Completeness** | ⚠ ClassicalInfo.lean has **Channel** and **Capacity** commented out in root (files exist) |
| **Stubs/Axioms** | ⚠ ClassicalMechanics: `WaveEquation/Basic.lean` (14 sorries), `RigidBody/SolidSphere.lean`, `Pendulum/SlidingPendulum.lean`, `Pendulum/CoplanarDoublePendulum.lean` (sorryful per AXIOMS.md) |
| **Notes** | ClassicalInfo (Prob, Distribution, Entropy) has no axioms |

---

## Layer 3: Mechanics & Symplectic

- **Mechanics** — Symplectic → Hamilton → Lagrange → CanonicalQuantization → WeylQuantization, Poincare; also Noether, PathIntegral, Wigner

### Layer 3 Review
| Item | Status |
|------|--------|
| **Completeness** | ✓ All modules present |
| **Stubs/Axioms** | ✓ None found in Mechanics |
| **Notes** | Dependency chain as stated |

---

## Layer 4: Space-Time Structure

- **SpaceAndTime** — Space (Basic, Derivatives, Norm, Slice, …), Time (Basic, Derivatives, TimeMan, TimeTransMan, TimeUnit), SpaceTime (Basic, Boosts, Derivatives, LorentzAction, TimeSlice), TimeAndSpace (Basic, ConstantTimeDist)

### Layer 4 Review
| Item | Status |
|------|--------|
| **Completeness** | ✓ Space, Time, SpaceTime, Derivatives all present |
| **Stubs/Axioms** | ⚠ Many sorries in: `Space/IsDistBounded.lean`, `Space/Norm.lean`, `Space/ConstantSliceDist.lean`, `TimeAndSpace/Basic.lean`, `SpaceTime/LorentzAction.lean`. SpaceTime continuities noted in AXIOMS.md |
| **Notes** | Curl.lean proofs marked **PROVED** in AXIOMS.md |

---

## Layer 5: Electromagnetism & Optics

- **Electromagnetism** — Kinematics (Boosts, ElectricField, EMPotential, FieldStrength, MagneticField, ScalarPotential, VectorPotential), Dynamics, Vacuum (Constant, HarmonicWave, IsPlaneWave), MaxwellEquations, Radiation, WaveEquation, PointParticle
- **Optics** — Basic, GeometricOptics, Polarization, WaveOptics

### Layer 5 Review
| Item | Status |
|------|--------|
| **Completeness** | ✓ Modules match |
| **Stubs/Axioms** | ✓ None found |
| **Notes** | — |

---

## Layer 6: Relativity

- **Relativity** — SR/MinkowskiSpacetime, LorentzGroup (Basic, Boosts, Restricted, Rotations, ToVector, …), Tensors (RealTensor, ComplexTensor, Contraction, …), Kerr metric (Components → Horizons → RingSingularity → Thermodynamics → Extensions), LorentzBoost (Ott, TTime, Jacobson)

### Layer 6 Review
| Item | Status |
|------|--------|
| **Completeness** | ✓ LorentzGroup, Tensors exist (imported transitively via GR/Kerr). Relativity.lean root imports GR, LorentzBoost, SR |
| **Stubs/Axioms** | ⚠ `LorentzGroup/Boosts/Generalized.lean` (sorryful), `Tensors/RealTensor/ToComplex.lean` (sorryful), `Schwarzschild/Bornemann.lean` (thermal axiom) per AXIOMS.md |
| **Notes** | **ConnesRovelli** not found in codebase — remove from graph |

---

## Layer 7: Quantum Mechanics

- **QuantumMechanics** — Uncertainty (Heisenberg, Robertson, Schrodinger), InformationGeometry (Fisher, CramerRao — under `QuantumMechanics/InformationGeometry/`), SpectralTheory (BochnerRoute, CayleyTransform, DiracEquation, FunctionalCalc, ResolventRoute), UnitaryEvo (Stone, Yosida, Resolvent)

### Layer 7 Review
| Item | Status |
|------|--------|
| **Completeness** | ✓ InformationGeometry exists; pulled in via `Uncertainty/CramerRao.lean` (not in QuantumMechanics.lean root) |
| **Stubs/Axioms** | ⚠ Per AXIOMS.md: Cayley/FunctionalCalc axiomatized; Generator-spectral integral; RelThermo proof_omitted; Dirac conservation; Modular/KMS axiomatized |
| **Notes** | Uncertainty.CramerRao has "Axiom I (Quantum Fisher Information)" |

---

## Layer 8: Quantum Information

- **QuantumInfo** — MState, Braket, CPTPMap, Entropy, Capacity, POVM, Instrument, Distance, Ensemble, Pinching, Qubit, ResourceTheory, ForMathlib (Lieb, TraceNorm, …)

### Layer 8 Review
| Item | Status |
|------|--------|
| **Completeness** | ✓ Modules match |
| **Stubs/Axioms** | ⚠ Per AXIOMS.md: Entropy (inner_log, sandwiched Rényi, SSA, unitary_conj); Fidelity; TraceDistance; Entanglement; Lieb/TraceNorm; Capacity; exists_kraus; Unbundled |
| **Notes** | See AXIOMS.md §1 for discharge paths |

---

## Layer 9: QEC & QFT

- **QEC** — Foundations (Basic, Gates, Tensor; KnillLaflamme exists in Foundations/ but not imported by Foundations.lean), Stabilizer, Codes (RepetitionCode in root; Steane7, ToricCode, Shor9, etc. under Stabilizer/Codes)
- **QFT** — Spacetime, WightmanAxioms, OsterwalderSchrader, PerturbationTheory (WickAlgebra, WickContraction; **FeynmanDiagrams** not present)

### Layer 9 Review
| Item | Status |
|------|--------|
| **Completeness** | ⚠ QEC: `KnillLaflamme` not in Foundations.lean root. QFT: **FeynmanDiagrams** not implemented |
| **Stubs/Axioms** | ⚠ QFT: Wightman/OS typed stubs per AXIOMS.md; Particles/Wick permutation sorryful |
| **Notes** | QEC root imports Foundations, RepetitionCode, Stabilizer |

---

## Layer 10: Particle Physics

- **Particles** — StandardModel, BeyondTheStandardModel (RHN, TwoHDM, …), SuperSymmetry, AnomalyCancellation

### Layer 10 Review
| Item | Status |
|------|--------|
| **Completeness** | ✓ Modules exist |
| **Stubs/Axioms** | ⚠ Particles/StandardModel/Basic.lean (sorryful), Wick permutation in QFT |
| **Notes** | — |

---

## Layer 11: Applied & Specialized

- **StatMech** — BoltzmannConstant, CanonicalEnsemble, GrandCanonicalEnsemble, Hamiltonian, IdealGas, Ising, Lattice, MolecularDynamics, NonEquilibrium, PhaseTransitions, QuantumStatistics, RenormalizationGroup, ThermoQuantities
- **Cosmology** — Basic, DarkEnergy, FLRW, Inflation
- **CondensedMatter** — Basic, BlochTheorem, QuantumHall, Superconductivity, TightBindingChain
- **StringTheory** — Basic, BosonicString, FTheory (SU5, Charges, Fluxes, Quanta)

### Layer 11 Review
| Item | Status |
|------|--------|
| **Completeness** | ✓ Modules expanded to match actual structure |
| **Stubs/Axioms** | ⚠ Cosmology/FLRW/Basic.lean (sorryful) per AXIOMS.md |
| **Notes** | StatMech has more submodules than originally listed |

---

## Bridge Modules (no circular deps)

- `QuantumInfo/QEC/*` → imports from `QEC` (correct direction)
- `QEC` does not import from `QuantumInfo`

---

## Module Path Note

Imports use direct paths (e.g. `Mathematics.Calculus.Divergence`, `ClassicalMechanics.EulerLagrange`) without a `PhysLean.` prefix.

---

## Summary of Corrections Made

| Layer | Change |
|-------|--------|
| 1 | Expanded Mathematics/Units; documented FunctionalAnalysis.Distributions stub |
| 2 | Noted Channel/Capacity commented out; added ClassicalMechanics submodules; documented sorries |
| 3 | Added Noether, PathIntegral, Wigner |
| 4 | Documented sorries in Space/Time modules |
| 5 | No changes (clean) |
| 6 | Removed ConnesRovelli; documented LorentzGroup/Tensors structure |
| 7 | Clarified InformationGeometry location; documented axiomatized pieces |
| 8 | Documented QuantumInfo axioms (see AXIOMS.md) |
| 9 | KnillLaflamme not in Foundations root; removed FeynmanDiagrams |
| 10 | Documented StandardModel sorry |
| 11 | Expanded StatMech, CondensedMatter, StringTheory to match codebase |
