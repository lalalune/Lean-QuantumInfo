# Library Architecture

This document defines the production architecture for Lean-QuantumInfo as a reusable theorem library.

## Layer Contract

Layer numbers are strict and directional.
Allowed imports: same layer or lower layer only.

1. `Mathematics`, `Units`
2. `ClassicalInfo`, `ClassicalMechanics`, `Thermodynamics`
3. `Mechanics`
4. `SpaceAndTime`
5. `Electromagnetism`, `Optics`
6. `Relativity`
7. `QuantumMechanics`
8. `QuantumInfo`
9. `QEC`, `QFT`
10. `Particles`
11. `StatMech`, `Cosmology`, `CondensedMatter`, `StringTheory`

Special:
- `Physics`: integration umbrella, may import all public layers.
- `Meta`: tooling only, excluded from production theorem gates.
- `scratch/`: not part of the library and must never be imported.

## Public Module Policy

Every top-level root module (for example `QuantumInfo.lean`) is public and stable.

Public APIs are consumed through:
- Root umbrella modules (`QuantumInfo`, `QEC`, `QFT`, etc.)
- Course-facing ladders (`QuantumInfo.CoursePrelude.Level1/2/3`)

## Internal vs Public Rules

- Public modules:
  - no `sorry`, `admit`, `axiom`
  - no vacuous stubs (`: Prop := True`)
  - documented assumptions
- Internal helpers may exist but must still compile and satisfy proof gates.

## Change Control

- Any new module must be assigned to a layer before merge.
- Any new cross-library import must satisfy layer order.
- API-breaking changes require a version bump and changelog entry.
