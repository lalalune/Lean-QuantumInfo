# Style Guide

## Theorem Quality

- State the weakest useful assumptions.
- Avoid vacuous theorem statements.
- Prefer canonical theorem names and namespace-qualified concepts.

## Proof Policy

- Disallowed in production modules:
  - `sorry`
  - `admit`
  - `axiom` declarations
  - `: Prop := True` placeholders

## Module Structure

Preferred file pattern per topic:
- `Defs.lean`
- `Basic.lean`
- `Lemmas.lean`
- `Theorems.lean`
- `Instances.lean`

## Imports

- Import only what is needed.
- Respect layer ordering from `docs/LIBRARY_ARCHITECTURE.md`.
- Never import from `scratch/`.

## Documentation

- Public definitions/theorems should include concise docstrings.
- Keep informal claims aligned with formal theorem statements.
