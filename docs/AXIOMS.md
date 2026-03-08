# Axioms and Proof Omissions - Catalog and Discharge Plan

This document catalogs all axiomatized results, `sorry`/`proof_omitted` usage, and `sorryful` declarations in the Lean-QuantumInfo codebase. It provides a unified view for fleshing out proofs and ensuring the math hierarchy builds correctly.

---

## 1. Quantum Information

### 1.1 Entropy (QuantumInfo/Finite/Entropy/)
| Declaration | Location | Status | Discharge Path |
|-------------|----------|--------|----------------|
| `inner_log_sub_log_nonneg_axiom` | Relative.lean:379 | axiom | Klein's inequality; needs Lieb concavity (general case; commuting case proved) |
| `qRelativeEnt.lowerSemicontinuous` | Relative.lean:1081 | axiom | Lower semicontinuity of relative entropy |
| `Sᵥₙ_strong_subadditivity_axiom` | SSA.lean:36 | proof_omitted | Strong subadditivity; Lieb–Ruskai |

### 1.2 Distance & Fidelity (QuantumInfo/Finite/Distance/)
| Declaration | Location | Status | Discharge Path |
|-------------|----------|--------|----------------|
| `fidelity_le_one` | Fidelity.lean:72 | axiom-consuming | Needs `traceNorm_mul_le_frobenius` (Hölder); F = ‖√ρ√σ‖₁ ≤ ‖√ρ‖_F ‖√σ‖_F = 1 |
| `fidelity_eq_one_implies_eq` | Fidelity.lean:121 | axiom-consuming | Purification uniqueness / Uhlmann |
| `trace_rpow_half_eq_of_charpoly_roots_eq` | Fidelity.lean:144 | axiom-consuming | Trace equality for matrix square roots (for `fidelity_symm`) |
| `fidelity_channel_nondecreasing` | Fidelity.lean:178 | axiom-consuming | Data-processing; needs Stinespring + Uhlmann |
| `fuchs_van_de_graaf_lower` | TraceDistance.lean:67 | axiom-consuming | 1 - F ≤ T; needs `fidelity_le_one` |
| `fuchs_van_de_graaf_upper` | TraceDistance.lean:74 | axiom-consuming | T ≤ √(1 - F²); needs `fidelity_le_one` |

### 1.3 Entanglement (QuantumInfo/Finite/Entanglement.lean)
| Declaration | Location | Status | Discharge Path |
|-------------|----------|--------|----------------|
| `bound_entangled_exists` | :330 | proof_omitted | Existence of bound entangled states (Horodecki construction) |
| `isPPT_iff_separable_2x2` | :385 | proof_omitted | PPT ≡ separable for 2×2, 2×3 |
| `isPPT_iff_separable_2x3` | :394 | proof_omitted | |
| `distillable_le_log_negativity` | :446 | proof_omitted | LOCC monotonicity |
| `logNegativity_tensor` | :453 | proof_omitted | Additivity |
| `negativity_convex` | :461 | proof_omitted | Convexity of negativity |

### 1.4 Lieb & Trace Norm (QuantumInfo/ForMathlib/)
| Declaration | Location | Status | Discharge Path |
|-------------|----------|--------|----------------|
| `vonNeumannEntropy_concave_axiom` | Lieb.lean:122 | axiom | Lieb concavity; analytic interpolation |
| `traceNorm_eq_max_tr_U` (general) | TraceNorm.lean:219 | axiom-consuming | Needs SVD / von Neumann trace inequality |
| `traceNorm_mul_le_frobenius` | TraceNorm.lean:387 | axiom-consuming | ‖AB‖₁ ≤ ‖A‖_F ‖B‖_F; SVD, von Neumann |

### 1.5 Capacity & CPTP (QuantumInfo/Finite/)
| Declaration | Location | Status | Discharge Path |
|-------------|----------|--------|----------------|
| `id_achievesRate_log_dim` | Capacity.lean:141 | axiom | Identity channel capacity |
| `not_achievesRate_gt_log_dim_in` | Capacity.lean:145 | axiom | Converse |
| `coherentInfo_le_quantumCapacity` | Capacity.lean:209 | axiom | LSD theorem |
| `quantumCapacity_eq_piProd_coherentInfo` | Capacity.lean:213 | axiom | Regularization |

---

## 2. Quantum Mechanics / Spectral Theory

### 2.1 Spectral Measure & Functional Calculus
| Declaration | Location | Status | Discharge Path |
|-------------|----------|--------|----------------|
| Cayley route agreement | FunctionalCalc/Agreement.lean | axiomatized | Spectral theorem |
| Generator-spectral integral | FunctionalCalc/Generator.lean | axiomatized | Borel functional calculus |
| `E B = boundedFunctionalCalculus` | RelThermo.lean:188 | proof_omitted | |
| `U_grp.U t = boundedFunctionalCalculus` | RelThermo.lean:209 | proof_omitted | Stone's theorem |
| Bounded functional calculus products | RelThermo.lean:232 | proof_omitted | |
| `⟨gen.op ψ, ψ⟩ = ∫ s ∂μ` | RelThermo.lean:732 | proof_omitted | Spectral theorem for generator |

### 2.2 Dirac Equation
| Declaration | Location | Status | Discharge Path |
|-------------|----------|--------|----------------|
| `fourDivergence_zero` | Conservation.lean:119 | proof_omitted | Dirac equation |
| `probability_conserved` | Conservation.lean:133 | proof_omitted | |
| Current continuity | Conservation.lean:147,162 | proof_omitted | Distribution theory |
| `dirac_generates_unitary` | Operators.lean | axiomatized | Stone's theorem for Dirac Hamiltonian |

### 2.3 Modular Theory & KMS
| Declaration | Location | Status | Discharge Path |
|-------------|----------|--------|----------------|
| C*-algebra, von Neumann algebra | SubsystemEmergence.lean | axiomatized | Full operator algebra |
| GNS, Tomita-Takesaki | Modular.lean, SubsystemEmergence | axiomatized | Modular theory |
| `modular_is_kms` | KMS/Modular.lean | axiomatized | Main KMS theorem |

---

## 3. Relativity & GR

| Declaration | Location | Status | Discharge Path |
|-------------|----------|--------|----------------|
| Generalized boost | LorentzGroup/Boosts/Generalized.lean:467 | sorryful | Lorentz group structure |
| Real tensor to complex | Tensors/RealTensor/ToComplex.lean:234 | sorryful | Complexification |
| Thermal axiom (Schwarzschild) | Schwarzschild/Bornemann.lean | physical axiom | Black hole thermodynamics |

---

## 4. Classical Mechanics & Cosmology

| Declaration | Location | Status | Discharge Path |
|-------------|----------|--------|----------------|
| Solid sphere inertia | RigidBody/SolidSphere.lean:72 | sorryful | Integration |
| Sliding pendulum | Pendulum/SlidingPendulum.lean:63 | sorryful | ODE solution |
| Coplanar double pendulum | Pendulum/CoplanarDoublePendulum.lean:70 | sorryful | ODE solution |
| FLRW | Cosmology/FLRW/Basic.lean:100 | sorryful | Cosmological solution |

---

## 5. Particles & QFT

| Declaration | Location | Status | Discharge Path |
|-------------|----------|--------|----------------|
| Standard model | Particles/StandardModel/Basic.lean:115,123 | sorryful | Gauge structure |
| Wick permutation | QFT/PerturbationTheory/WickContraction/Perm.lean:68,75 | sorryful | Permutation sign |
| Wightman, OS axioms | QFT/*.lean | typed `True` stubs | Full QFT construction |

---

## 6. Mathematics & Variational Calculus

| Declaration | Location | Status | Discharge Path |
|-------------|----------|--------|----------------|
| `FunctionalAnalysis.Distributions` | Mathematics.lean | **REMOVED** | Import removed; use Mathematics.Distribution.Basic (Mathlib SchwartzSpace) |
| `inner_top_equiv_norm` | InnerProductSpace/Basic.lean:495 | proof_omitted | Normed space topology |
| HasVarAdjoint chain | VariationalCalculus/HasVarAdjoint.lean | proof_omitted | fun_prop; continuity, differentiability |
| SpaceTime continuities | SpaceAndTime/SpaceTime/Basic.lean | proof_omitted | fun_prop |

---

## 7. Unification Guidelines

### Units Hierarchy (Post-Deduplication)
- **Units.Core (Units.SI)**: Single source for `pi_F`, `e_F`, `ln10_F`, `c_light_F`, `h_planck_F`, `k_B_F`, `G_F`, `stefan_boltzmann_F`, `R_gas_F`, `N_A_F`, `F_const_F`
- **Physics.Constants**: ℝ versions (`c`, `ℏ`, `kB`, etc.) for proofs; placeholder values (e.g. 1) for algebraic structure
- **Domain modules** (Chemistry, Astro, Earth, etc.): Import Core; define only domain-specific constants

### Proof Hierarchy
1. **Mathlib** → basic analysis, measure theory, linear algebra
2. **Mathematics/** → project-specific (inner product, variational calculus, distributions)
3. **Physics constants** → used by StatMech, Thermodynamics, QM
4. **QuantumInfo** → entropy, fidelity, capacity (builds on Mathematics)
5. **QuantumMechanics** → spectral theory, Dirac, modular (builds on QuantumInfo + Mathematics)

### Recommended Discharge Order
1. **Low-hanging**: Simple continuity (`fun_prop`), inner_log chain
2. **Medium**: Lieb concavity, trace norm, Fuchs–van de Graaf
3. **High**: Spectral theorem, Stone, KMS, full entanglement theory

### Recently Discharged
- **CPTP.lean**: Fixed `normalized_choi_is_mstate` proof (was using incorrect rewrite; now uses `HermitianMat.trace_eq_one_iff`)
- **exists_kraus / Kraus representation**: Fully proved via `exists_kraus_of_choi_PSD` + `choi_PSD_iff_CP_map` in Unbundled.lean
- **PosSemidef.traceNorm_eq_max_tr_U** (TraceNorm.lean): Fully proved (PSD case; general case still axiom-consuming)

### Reverted / Removed (per user edits)
- **Pinching.lean**: Sᵥₙ_concave, Sᵥₙ_unitary_conj, DFTUnitary, pinching_eq_convex_sum_unitary_conj, Sᵥₙ_concave_nary, Sᵥₙ_pinching_ge, qRelativeEnt_eq_entropy_diff, qRelativeEnt_pinching_nonneg, qRelativeEnt_pinching_commute_nonneg, qRelativeEnt_nonneg_via_pinching — all removed
- **IsCompletelyPositive.piProd** (Unbundled.lean): Proof replaced with sorry (Choi + PosSemidef.piProd route was previously proved)

---

## 8. Duplication Resolved (This Pass)

- **Units**: All mathematical and physical Float constants centralized in `Units/Core.lean` (Units.SI):
  - Math: pi_F, tau_F, e_F, sqrt2_F, sqrt3_F, phi_F, ln2_F, ln10_F, sqrtPi_F, sqrt2Pi_F, euler_gamma_F, log2_e_F, log10_2_F, log2_10_F
  - Physics: c_light_F, h_planck_F, k_B_F, G_F, stefan_boltzmann_F, R_gas_F, N_A_F, F_const_F, g_standard_F, hbar_F, m_e_F, mu0_F, epsilon0_F, e_charge_F, k_coulomb_F
  - Domain modules (Chemistry, Astro, Earth, Fluids, etc.) import Core; only domain-specific constants remain local
- **ε_tsirelson**: Single source in `QuantumMechanics/BellsTheorem/TsirelsonBound.lean`. Imported by CriticalQuestions, ThermMerm, TLHV_P, SharedEnBudget (via TLHV).
- **ThermalCorrelationStructure, KMSConstraint**: Still duplicated in TLHV_P and TLHV/; full unification would require TLHV_P to import from TLHV (modular refactor).
- **dSpacingCubic_F**: Similar logic in Crystallography (Angstrom_F) and Materials (LatticeParam_a_F); different input types, could unify with a common lattice-param abstraction.
