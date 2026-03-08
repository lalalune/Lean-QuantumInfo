# Proof Refinement Plan: From Basic Math to Complex Results

**Goal**: Eliminate all `sorry`, `admit`, and non-necessary `axiom` declarations, ensuring every result is proved from foundational mathematics.

## Dependency Order (Bottom-Up)

### Tier 0: Mathlib / ClassicalInfo ✓
- Shannon entropy concavity `H₁_concave`
- Basic linear algebra, trace, eigenvalues

### Tier 1: QuantumInfo Finite Core — Remaining Axioms

| Declaration | File | Status | Dependency |
|-------------|------|--------|------------|
| `vonNeumannEntropy_concave_axiom` | Lieb.lean | axiom | Lieb concavity / analytic interpolation |
| `Sᵥₙ_concave` | Pinching.lean | removed | was proved from vonNeumannEntropy_concave_axiom |
| `inner_log_sub_log_nonneg_axiom` | Relative.lean | axiom | Klein's inequality |
| `inner_log_sub_log_nonneg` | Relative.lean | ✓ proved | uses inner_log_sub_log_nonneg_axiom |
| `Sᵥₙ_concave_nary_axiom` | Pinching.lean | removed | was axiom; depends on Sᵥₙ_concave (also removed) |

**Math route**: Lieb concavity → joint convexity of D(ρ‖σ) → Klein's inequality → Sᵥₙ concavity.

### Tier 2: Downstream (removed / pending)
- `pinching_eq_convex_sum_unitary_conj` — removed from Pinching.lean (was DFT unitaries)
- `Sᵥₙ_pinching_ge`, `qRelativeEnt_pinching_nonneg`, `qRelativeEnt_nonneg_via_pinching` — removed
- `IsCompletelyPositive.piProd` — sorry in Unbundled.lean (Choi + PosSemidef.piProd route)

### Tier 3: Relative Entropy / Stein Lemma
- Multiple axioms in `Entropy/Relative.lean`, `ResourceTheory/SteinsLemma.lean`
- Depend on Tier 1–2

### Tier 4: Relativity / Physics / TraceNorm ✓
- `minkowskiProductMap_toCoord` — ✓ proved
- `PosSemidef.traceNorm_eq_max_tr_U` — ✓ proved
- `traceNorm_mul_le_frobenius` — axiom-consuming; needs SVD or von Neumann trace inequality
- QuantumMechanics spectral/modular axioms — Stone theorem, KMS, Tomita–Takesaki
- QFT Osterwalder–Schrader axioms

### Tier 5: Particles, SpaceAndTime
- TwoHDM GramMatrix, SU5 ChargeSpectrum — representation theory
- SpaceAndTime derivatives/norms — fun_prop / analysis

## Immediate Action Items

1. **Lieb concavity**: Complete analytic interpolation in Mathlib to discharge `vonNeumannEntropy_concave_axiom`.
2. **Sᵥₙ_concave_nary**: Prove from Sᵥₙ_concave by induction on n (Fin.sum_univ_castSucc, Convex.sum_mem).
3. **Klein's inequality**: Reduces to Lieb / joint convexity of D for `inner_log_sub_log_nonneg_axiom`.
4. **Audit axiom declarations**: Replace with `ProofOmitted` or structured TODOs where appropriate.

## Files With Highest Placeholder Density

- `QuantumInfo/Finite/Entropy/Relative.lean`
- `SpaceAndTime/Space/Norm.lean`, `ConstantSliceDist.lean`, `Derivatives/*`
- `Particles/BeyondTheStandardModel/TwoHDM/GramMatrix.lean`
- `QuantumInfo/Finite/ResourceTheory/SteinsLemma.lean`
