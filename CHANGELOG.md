# Changelog

All notable changes to this project should be documented in this file.

## [Unreleased]

### Added
- Library architecture contract docs (`docs/LIBRARY_ARCHITECTURE.md`)
- Stable API docs (`docs/API_SURFACE.md`)
- Style/versioning/usage/course/readiness docs
- Course prelude modules:
  - `QuantumInfo.CoursePrelude.Level1`
  - `QuantumInfo.CoursePrelude.Level2`
  - `QuantumInfo.CoursePrelude.Level3`
- Consumer test modules under `Test/Consumer`
- Import-layer checker script (`tools/check_import_layers.sh`)
- Theorem index generator (`tools/generate_theorem_index.sh`)
- Combined gate script (`tools/library_gate.sh`)
- CI workflow (`.github/workflows/ci.yml`)

### Changed
- Expanded `lakefile.lean` to declare all top-level `lean_lib` targets.
