# Lean-QuantumInfo Project Structure

This document maps all libraries, their locations, and import conventions for humans and AI agents.

## Library Layout (21 lean_lib targets)

Each library has a **root `.lean` file** at project root and a **directory** of the same name. The root file re-exports submodules.

| Library | Root File | Directory | Layer (see DEPENDENCY_GRAPH.md) |
|---------|-----------|-----------|----------------------------------|
| Mathematics | `Mathematics.lean` | `Mathematics/` | 1 |
| Units | `Units.lean` | `Units/` | 1 |
| ClassicalInfo | `ClassicalInfo.lean` | `ClassicalInfo/` | 2 |
| ClassicalMechanics | `ClassicalMechanics.lean` | `ClassicalMechanics/` | 2 |
| Thermodynamics | `Thermodynamics.lean` | `Thermodynamics/` | 2 |
| Mechanics | `Mechanics.lean` | `Mechanics/` | 3 |
| SpaceAndTime | `SpaceAndTime.lean` | `SpaceAndTime/` | 4 |
| Electromagnetism | `Electromagnetism.lean` | `Electromagnetism/` | 5 |
| Optics | `Optics.lean` | `Optics/` | 5 |
| Relativity | `Relativity.lean` | `Relativity/` | 6 |
| QuantumMechanics | `QuantumMechanics.lean` | `QuantumMechanics/` | 7 |
| QuantumInfo | `QuantumInfo.lean` | `QuantumInfo/` | 8 |
| QEC | `QEC.lean` | `QEC/` | 9 |
| QFT | `QFT.lean` | `QFT/` | 9 |
| Particles | `Particles.lean` | `Particles/` | 10 |
| StatMech | `StatMech.lean` | `StatMech/` | 11 |
| Cosmology | `Cosmology.lean` | `Cosmology/` | 11 |
| CondensedMatter | `CondensedMatter.lean` | `CondensedMatter/` | 11 |
| StringTheory | `StringTheory.lean` | `StringTheory/` | 11 |
| Physics | `Physics.lean` | `Physics/` | meta |
| Meta | (implicit) | `Meta/` | tooling |

## Import Conventions

- **No shared prefix**: Imports use direct paths like `QuantumInfo.Finite.Capacity`, `Mathematics.Calculus.Divergence` — there is no `PhysLean.` or similar wrapper.
- **Submodule paths**: `LibName.lean` → `LibName.SubModule.SubSub` corresponds to file `LibName/SubModule/SubSub.lean`.
- **Cross-library imports**: Libraries import each other by module name, e.g. `import QuantumInfo.Finite.Entropy` from a QEC file.

## Scratch / Non-Library Code

- **Location**: `scratch/`
- **Purpose**: One-off local files that are **not** part of any `lean_lib` and are not built by `lake build`.
- **Do not** import from scratch in production modules.

## Build & Dependencies

- **lakefile.lean**: Defines all 21 `lean_lib` targets. Package name: `quantumInfo`.
- **Dependency order**: See `docs/DEPENDENCY_GRAPH.md` for layer order (Layer 1 = foundation, Layer 11 = applied).
- **External deps**: mathlib, doc-gen4 (see lakefile.lean).

## Key Files for Agents

- `AXIOMS.md` — axiom/sorry inventory and discharge paths
- `docs/REFINEMENT_PLAN.md` — proof refinement plan and tier ordering
- `docs/THEOREM_SPINES.md` — theorem spine map across QI/QEC/QFT/relativity and adjacent domains
- `docs/LIBRARY_ARCHITECTURE.md` — production layer contract and import rules
- `docs/API_SURFACE.md` — stable public import paths
- `docs/STYLE_GUIDE.md` — theorem/module style policy
- `docs/USING_THE_LIBRARY.md` — downstream usage guide
- `docs/COURSE_PATHS.md` — course prelude import ladder
- `docs/VERSIONING.md` — release and compatibility policy
- `docs/LIBRARY_READINESS_REPORT.md` — release gate checklist
- `TODO.md` — task tracking
- `DOC.md` — main definition documentation
