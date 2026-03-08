import QuantumMechanics.UnitaryEvo.Stone
import QuantumMechanics.UnitaryEvo.Resolvent
import QuantumMechanics.UnitaryEvo.Yosida
import QuantumMechanics.BellsTheorem.CHSH_bounds
import QuantumInfo.InfiniteDim.LogosBridge

/-!
# Logos Integration

Umbrella module that exposes the integrated stable Logos subset together with
finite-dimensional bridge lemmas.

## Imported Logos modules (all axiom-free)

* `UnitaryEvo.Stone` / `Resolvent` / `Yosida` — abstract Stone's theorem.
* `BellsTheorem.CHSH_bounds` — classical and quantum (Tsirelson) CHSH bounds,
  including `tsirelson_bound` for `Matrix (Fin n) (Fin n) ℂ`.

The finite-dimensional bridge (`QuantumInfo.InfiniteDim.LogosBridge`) then
re-exports `stone_finite_dim` (Stone specialised to `EuclideanSpace ℂ d`) and
`tsirelson_bound_transfer` (the CHSH bound re-scoped under `LogosBridge`).

Modules that still carry axioms (KMS, Ott relativity branches, etc.) are
deliberately excluded from this surface.
-/
