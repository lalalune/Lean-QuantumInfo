# The Leaning Of Everything

A Lean 4 formal library covering quantum information theory, quantum mechanics, relativity,
field theory, and the mathematical infrastructure that ties them together.

## Relationship to Physlib

In March 2026, this repository's quantum information line merged with PhysLean/HEPLean to form
[Physlib](https://github.com/leanprover-community/physlib) under `leanprover-community`. All
content from the May 2026 snapshot of physlib has since been fully integrated here. New development
on the physics-formalization side continues upstream in physlib.

This repository remains the primary home for:

- the **Generalized Quantum Stein's Lemma** proof and its dependencies
- **Quantum Error Correction** formalization (absent from physlib)
- **Classical Information Theory** (absent from physlib)
- **Statistical Mechanics** (more extensive coverage than physlib)
- ongoing work in quantum mechanics, field theory, and cosmology that extends beyond physlib

## Flagship Result

The guiding goal of this repository was a machine-checked proof of the
[Generalized Quantum Stein's Lemma](https://arxiv.org/abs/2408.02722v1).
The full proof — every lemma checked — was completed in April 2026.

```
QuantumInfo/Finite/ResourceTheory/SteinsLemma.lean
  limit_hypotesting_eq_limit_rel_entropy
```

See [arXiv:2510.08672](https://arxiv.org/abs/2510.08672) for the accompanying report.
Thanks to Leonardo Lessa, Rodolfo Soldati, and Hayata Yamasaki for substantial contributions.

## What We Have That Physlib Doesn't

| Area | ~Decls | ~Lines | Notes |
|------|-------:|-------:|-------|
| `QEC` | 1 280 | 25 500 | Quantum error correction: stabilizer codes, fault tolerance, threshold theorems |
| `ClassicalInfo` | 113 | 1 200 | Classical channels, Shannon entropy, capacity |
| `StatMech` | 330 | 5 200 | Partition functions, thermodynamic limits |
| Extended `QuantumInfo` | 2 050 | 36 200 | Full Stein's Lemma chain, sandwiched Rényi entropy, SSA, resource theories |
| Extended `QuantumMechanics` | 2 260 | 46 700 | Infinite-dimensional operators, hydrogen atom, Laplace-Runge-Lenz vector |
| `EUVLithography` | — | 3 300 | Applied semiconductor physics (EUV source, plasma, resist, optics) |

## Scope

**~15 000 declarations, ~440 000 lines of Lean** across:

- `QuantumInfo` — quantum states, channels, entropy, resource theory, capacity
- `QEC` — quantum error correction codes and threshold bounds
- `ClassicalInfo` — classical Shannon theory
- `StatMech` — statistical mechanics foundations
- `QuantumMechanics` — infinite-dimensional Hilbert space operators, hydrogen atom
- `Relativity` — Lorentz tensors, spinors, real and complex tensor species
- `QFT` — perturbation theory, Wick algebra
- `SpaceAndTime` — Schwartz space, distributions, spatial/spacetime derivatives
- `Mathematics` — variational calculus, distributions, special functions
- `ClassicalMechanics` — Lagrangian/Hamiltonian mechanics, harmonic oscillator
- `Electromagnetism` — EM potential, Maxwell theory
- `Cosmology` — FLRW metric, Friedmann equations, Hubble parameter
- `Particles` — Standard Model, SUSY, anomaly cancellation
- `StringTheory` — F-theory charge assignments
- `Thermodynamics`, `CondensedMatter`, `Optics`, `ClassicalFieldTheory` — early coverage
- `Mathematics`, `Units`, `Meta` — shared infrastructure, dimensional analysis, linting

## Build

```bash
lake exe cache get
lake build
```

Targeted builds:

```bash
lake build QuantumInfo
lake build QEC
lake build ClassicalInfo
```

## Repository Layout

```
QuantumInfo/ForMathlib/   HermitianMat, MatrixNorm, analysis facts — candidates for mathlib
QuantumInfo/Finite/       Finite-dimensional QI: states, channels, entropy, resource theory
QEC/                      Quantum error correction
ClassicalInfo/            Classical information theory
StatMech/                 Statistical mechanics
QuantumMechanics/         Infinite-dimensional QM: operators, hydrogen atom
Relativity/               Lorentz tensors, spinors, SL(2,C)
QFT/                      Quantum field theory
SpaceAndTime/             Schwartz space, distributions, spatial derivatives
Mathematics/              Variational calculus, distributions, special functions
ClassicalMechanics/       Lagrangian/Hamiltonian mechanics
Electromagnetism/         EM potential and kinematics
Cosmology/                FLRW metric, Friedmann equations
Particles/                Particle physics: SM, MSSM, anomaly cancellation
StringTheory/             F-theory charges
EUVLithography/           Applied EUV semiconductor physics
Units/                    Dimensional analysis
Meta/                     Project tooling and linting
```

## License and Citation

Released under the MIT License; see [LICENSE](./LICENSE).

```bibtex
@misc{theleaningofeverything,
  author       = {Meiburg, Alex and contributors},
  title        = {The Leaning Of Everything},
  year         = {2026},
  howpublished = {\url{https://github.com/lalalune/TheLeaningOfEverything}},
}
```
