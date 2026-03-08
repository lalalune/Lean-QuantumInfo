# Foundation Gates

This project now has a strict audit script:

- `/Users/shawwalters/Lean-QuantumInfo/tools/foundation_audit.sh`

## What It Checks

1. `lake build` (unless `--skip-build` is passed)
2. No `sorry` tactic usage in Lean sources
3. No explicit `axiom` declarations in Lean sources
4. No `True := by trivial` theorem/lemma-style stubs
5. No `Prop := True` structural stubs

`Meta/**` is excluded from static scans because it intentionally contains linter/tooling references to `sorry`/`axiom` internals.

## Temporary Skip List

Both scripts read:

- `/Users/shawwalters/Lean-QuantumInfo/tools/foundation_skip_paths.txt`

Use this only for files actively being edited elsewhere, then remove entries immediately after handoff.

## Usage

```bash
bash /Users/shawwalters/Lean-QuantumInfo/tools/foundation_audit.sh
```

Fast mode (skip build, static checks only):

```bash
bash /Users/shawwalters/Lean-QuantumInfo/tools/foundation_audit.sh --skip-build
```

## Backlog Report

Generate a full placeholder backlog report:

```bash
bash /Users/shawwalters/Lean-QuantumInfo/tools/foundation_backlog.sh
```

Default output:

- `/Users/shawwalters/Lean-QuantumInfo/docs/FOUNDATION_BACKLOG.md`
