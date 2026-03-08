# Theorem Spine Map (Physics + QI)

This document tracks the project-level theorem spine across finite-dimensional
quantum information, QEC, infinite-dimensional operator algebras, QFT, and
adjacent physics domains.

## 1. Finite-Dimensional Quantum Information

Core channel layer (CPTP/duality):
- `QuantumInfo/Finite/CPTPMap/CPTP.lean`
- `QuantumInfo/Finite/CPTPMap/Dual.lean`
- `QuantumInfo/Finite/CPTPMap/MatrixMap.lean`
- `QuantumInfo/Finite/CPTPMap/Unbundled.lean`

Entropy/information layer:
- `QuantumInfo/Finite/Entropy/VonNeumann.lean`
- `QuantumInfo/Finite/Entropy/Relative.lean`
- `QuantumInfo/Finite/Entropy/SSA.lean`
- `QuantumInfo/Finite/Entropy/Holevo.lean`
- `QuantumInfo/Finite/Entropy/MinMax.lean`
- `QuantumInfo/Finite/Entropy/Schumacher.lean`

Capacity/coding/resource layer:
- `QuantumInfo/Finite/Capacity.lean`
- `QuantumInfo/Finite/ResourceTheory/ResourceTheory.lean`
- `QuantumInfo/Finite/ResourceTheory/HypothesisTesting.lean`
- `QuantumInfo/Finite/ResourceTheory/SteinsLemma.lean`
- `QuantumInfo/Finite/Entanglement.lean`
- `QuantumInfo/Finite/Pinching.lean`

Current status:
- Channel core has concrete proofs for composition/equivalence operations.
- Entropy/capacity/resource modules include proven backbone results plus
  conservative proxy definitions where full analytic infrastructure is pending.

## 2. Quantum Error Correction (QEC)

Knill-Laflamme + foundational gates/tensors:
- `QEC/Foundations/KnillLaflamme.lean`
- `QEC/Foundations/Gates.lean`
- `QEC/Foundations/Tensor.lean`
- `QEC/Foundations/ThresholdTheorem.lean`

Stabilizer and binary symplectic layer:
- `QEC/Stabilizer/Core/*.lean`
- `QEC/Stabilizer/BinarySymplectic/*.lean`
- `QEC/Stabilizer/PauliGroup*.lean`

Code constructions:
- `QEC/Stabilizer/Codes/RepetitionCode3.lean`
- `QEC/Stabilizer/Codes/Steane7.lean`
- `QEC/Stabilizer/Codes/Shor9.lean`
- `QEC/Stabilizer/Codes/ToricCode.lean`
- `QEC/Stabilizer/Codes/RotatedSurfaceCode3.lean`

Current status:
- Knill-Laflamme condition and threshold-style statements are formalized.
- Stabilizer/check-matrix stack is connected through decidable linear-independence criteria.

## 3. Infinite-Dimensional Operator-Algebra Spine

C*-algebra and states:
- `QuantumInfo/InfiniteDim/CStarAlgebra.lean`
- `QuantumInfo/InfiniteDim/VonNeumann.lean`

Trace/Hilbert-Schmidt/spectral interfaces:
- `QuantumInfo/InfiniteDim/TraceClass.lean`
- `QuantumInfo/InfiniteDim/HilbertSchmidt.lean`
- `QuantumInfo/InfiniteDim/SpectralTheorem.lean`

CCR/Fock links:
- `QuantumInfo/InfiniteDim/CCR.lean`
- `QuantumInfo/InfiniteDim/FockSpace.lean`

Current status:
- Trace-class and Hilbert-Schmidt predicates now use norm-bounded witnesses.
- KMS/ground-state interface now has a nontrivial ground-state predicate.
- Spectral/PVM layer remains interface-first (with constructive witnesses).

## 4. QFT Spine

Axiomatic layer:
- `QFT/WightmanAxioms.lean`
- `QFT/OsterwalderSchrader.lean`
- `QFT/PCTTheorem.lean`
- `QFT/HaagsTheorem.lean`

Perturbative/renormalization layer:
- `QFT/PerturbationTheory/**/*.lean`
- `QFT/BPHZRenormalization.lean`
- `QFT/ConnesKreimerHopf.lean`
- `QFT/EffectiveFieldTheory.lean`

Symmetry/representation/anomaly layer:
- `QFT/YangMills.lean`
- `QFT/SpinStatistics.lean`
- `QFT/AnomalyCancellation/**/*.lean`

Current status:
- Broad theorem skeleton exists across all three layers.
- Several modules are currently theorem maps/backbones rather than full analytic completions.

## 5. Relativity + QFT Interface

Lorentz/modular/thermal structure:
- `Relativity/LorentzBoost/ConnesRovelli.lean`
- `Relativity/LorentzBoost/Jacobson.lean`
- `Relativity/LorentzBoost/Ott.lean`
- `QuantumInfo/InfiniteDim/VonNeumann.lean` (Tomita-Takesaki + KMS interfaces)

Curved spacetime + Hawking/Unruh-style interfaces:
- `Relativity/GR/**/*.lean`
- `Cosmology/HawkingRadiation/Basic.lean`

Current status:
- Modular/KMS interface is wired.
- Curved-spacetime/QFT links are present as formal interface layers with selected concrete lemmas.

## 6. Domain Theorem Maps

Condensed matter:
- `CondensedMatter/Basic.lean`
- `CondensedMatter/TightBindingChain/Basic.lean`
- `CondensedMatter/BlochTheorem/Basic.lean`
- `CondensedMatter/QuantumHall/Basic.lean`
- `CondensedMatter/Superconductivity/BCS.lean`

Statistical mechanics:
- `StatMech/CanonicalEnsemble/*.lean`
- `StatMech/GrandCanonicalEnsemble/Basic.lean`
- `StatMech/NonEquilibrium/Jarzynski.lean`
- `StatMech/PhaseTransitions/LandauTheory.lean`
- `StatMech/RenormalizationGroup/Basic.lean`

Cosmology:
- `Cosmology/Basic.lean`
- `Cosmology/FLRW/Basic.lean`
- `Cosmology/Inflation/Basic.lean`
- `Cosmology/DarkEnergy/Basic.lean`
- `Cosmology/HawkingRadiation/Basic.lean`

Particle physics:
- `Particles/StandardModel/**/*.lean`
- `Particles/FlavorPhysics/CKMMatrix/**/*.lean`
- `Particles/BeyondTheStandardModel/**/*.lean`
- `Particles/SuperSymmetry/**/*.lean`

Current status:
- Each domain has an explicit theorem-map module path and canonical flagship files.
- Ongoing work focuses on upgrading map-level statements to deeper analytic proofs.
