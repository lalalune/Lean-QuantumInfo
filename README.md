# Lean-QuantumInfo

`Lean-QuantumInfo` is a Lean 4 formalization project centered on finite-dimensional quantum
information theory, with supporting classical information theory and statistical mechanics modules.
The repository also contains mathlib-adjacent infrastructure under `QuantumInfo/ForMathlib` for
matrix, Hermitian, and channel arguments that do not fit cleanly in upstream mathlib yet.

## Current build surface

The current `lakefile.lean` defines three libraries:

- `QuantumInfo`
- `ClassicalInfo`
- `StatMech`

Those are the supported entry points for `lake build`. The repository may contain additional draft
modules or exploratory trees, but only modules wired into `lakefile.lean` are part of the default
package build.

## What is in scope

The main body of the project currently covers:

- finite-dimensional quantum states, channels, entropy, capacity, entanglement, and resource theory
- classical probability, distributions, and entropy
- supporting matrix/Hermitian/operator lemmas needed by the quantum library
- early statistical mechanics infrastructure

The finite-dimensional quantum information library remains the core of the repository.

## Build

```bash
lake update
lake build
```

Useful targeted builds:

```bash
lake build QuantumInfo
lake build ClassicalInfo
lake build StatMech
```

## Repository layout

- `QuantumInfo/`: quantum information theory and supporting mathlib extensions
- `ClassicalInfo/`: finite classical information theory
- `StatMech/`: statistical mechanics modules
- `DOC.md`: high-level documentation of major definitions and conventions
- `TODO.md`: project task and theorem tracking

## Project direction

The long-term goal is a reusable Lean library for quantum information theory with a clean API
surface and progressively fewer proof gaps. Recent work has focused on:

- strengthening the low-level matrix/channel layer
- isolating reusable finite-dimensional infrastructure
- replacing local one-off arguments with portable lemmas and reusable APIs

## License and citation

This repository is released under the MIT License; see [LICENSE](./LICENSE).

If you cite the repository, use:

```bibtex
@misc{meiburg2024quantuminfo,
  author = {Meiburg, Alex},
  title = {Quantum Information in Lean},
  year = {2024},
  publisher = {GitHub},
  journal = {GitHub repository},
  howpublished = {\url{https://github.com/Timeroot/Lean-QuantumInfo}},
}
```
