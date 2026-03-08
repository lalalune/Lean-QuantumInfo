# Using The Library

## Quick Start

Import one of the stable root modules:

```lean
import QuantumInfo
import QEC
```

Or import course ladders:

```lean
import QuantumInfo.CoursePrelude.Level1
import QuantumInfo.CoursePrelude.Level2
import QuantumInfo.CoursePrelude.Level3
```

## Choosing Import Depth

- Use root imports for broad access.
- Use specific module imports (for example `QuantumInfo.Finite.CPTPMap`) for faster local builds and cleaner dependencies.

## Theorem Discovery

- Use `#check` and namespace search in editor.
- Use `docs/THEOREM_INDEX.md` for file-level theorem lookup.
- Use `docs/THEOREM_SPINES.md` for domain-level theorem maps.

## Compatibility

- Import paths listed in `docs/API_SURFACE.md` are the supported interface.
- Avoid depending on `Meta/**` and `scratch/**`.
