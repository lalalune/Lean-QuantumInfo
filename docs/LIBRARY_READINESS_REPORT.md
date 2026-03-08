# Library Readiness Report

Generated status: **in progress**

## Required Gates

- [x] Full `lake build` on clean checkout
- [ ] Foundation audit (`tools/foundation_audit.sh --skip-build`)  
  Current: fails with **44** outstanding `sorry` placeholders in core theorem modules.
- [x] Layer import check (`tools/check_import_layers.sh`)
- [x] Theorem index regenerated (`tools/generate_theorem_index.sh`)
- [x] Consumer tests build (`Test.Consumer.Level1/2/3`)
- [ ] CI workflow green

## Current Notes

- Architecture/API/course prelude scaffolding is in place.
- Enforcement scripts and CI are defined in repository.
- `docs/THEOREM_INDEX.md` has been generated.
- Recent validation results:
  - `lake build` -> pass (warnings only).
  - `lake build Test` -> pass (Level1/2/3 consumer tests all pass).
  - `tools/check_import_layers.sh` -> pass.
  - `tools/generate_theorem_index.sh` -> pass.
  - `tools/library_gate.sh` -> fail only on unresolved proof placeholders (`sorry`).
- Final readiness remains blocked by unresolved proof placeholders in CPTP/duality, entropy/capacity, QEC-adjacent finite QI, and selected statmech modules.
