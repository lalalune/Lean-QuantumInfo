# API Surface

This file defines the stable import surface for downstream users.

## Stable Root Imports

- `Mathematics`
- `Units`
- `ClassicalInfo`
- `ClassicalMechanics`
- `Thermodynamics`
- `Mechanics`
- `SpaceAndTime`
- `Electromagnetism`
- `Optics`
- `Relativity`
- `QuantumMechanics`
- `QuantumInfo`
- `QEC`
- `QFT`
- `Particles`
- `StatMech`
- `Cosmology`
- `CondensedMatter`
- `StringTheory`
- `Physics`

## Stable Course Imports

- `QuantumInfo.CoursePrelude.Level1`
- `QuantumInfo.CoursePrelude.Level2`
- `QuantumInfo.CoursePrelude.Level3`

## Stability Expectations

- Paths above are considered stable API paths.
- Symbol-level naming can evolve, but path-level breakage requires a major version bump.
- New public modules may be added in minor releases.

## Non-API Paths

- `Meta/**`
- `scratch/**`
- `.lake/**`

These are not supported for downstream imports.
