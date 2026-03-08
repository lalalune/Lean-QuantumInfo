# Versioning Policy

Semantic Versioning is used: `MAJOR.MINOR.PATCH`.

## PATCH

- proof refactors
- internal implementation changes
- doc fixes
- no public path breakage

## MINOR

- new modules/theorems on existing public paths
- new stable public paths
- backwards-compatible extensions

## MAJOR

- removal or rename of stable public module paths
- breaking changes to documented API contracts

## Release Requirements

- CI green
- quality gates pass
- `docs/THEOREM_INDEX.md` regenerated and committed
- changelog updated
