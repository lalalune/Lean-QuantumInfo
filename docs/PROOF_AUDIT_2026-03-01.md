# Proof / Completeness Audit (Snapshot 2026-03-01)

Generated from workspace scan on 2026-03-01.

## Summary Counts
- explicit axioms in `.lean`:        0
- `sorry`/`admit` occurrences in `.lean`:       49
- vacuous stub propositions (`True := by trivial` or `: Prop := True`):       81
- references to `ProofOmitted` / `proof_omitted`:      121
- TODO/stub/placeholder markers in `.lean`:      279

## Compile Breakage Observed
- `lake build` currently fails at `ClassicalInfo/Distribution.lean` (type mismatch around line 145; implicit lambda / expected theorem shape mismatch).

## A. Explicit Axioms (Should Be Zero)
```text
```

## B. Incomplete Proofs (`sorry` / `admit`)
```text
./QuantumInfo/ForMathlib/Misc.lean:25:  sorry
./QuantumInfo/ForMathlib/Misc.lean:29:    ⨆ i, (⟨f i, h i⟩ : ↑s) = ⟨⨆ i, f i, by sorry⟩ := by
./QuantumInfo/ForMathlib/Lieb.lean:20:  sorry
./QuantumInfo/Finite/Capacity.lean:126:  · have : Nonempty d₁ := by sorry--having a CPTPMap should be enough to conclude in- and out-spaces are nonempty
./QuantumInfo/Finite/Capacity.lean:127:    have : Nonempty d₂ := by sorry
./QuantumInfo/Finite/Capacity.lean:129:    sorry--exact Unique.eq_default _
./QuantumInfo/Finite/Capacity.lean:133:    sorry--apply εApproximates_monotone (εApproximates_self default) hε.le
./QuantumInfo/Finite/Capacity.lean:159:  sorry
./QuantumInfo/Finite/Capacity.lean:218:  sorry
./QuantumInfo/Finite/Capacity.lean:223:  sorry
./QuantumInfo/Finite/Entropy/Relative.lean:361:  sorry
./QuantumInfo/Finite/Entropy/Relative.lean:365:  sorry
./QuantumInfo/Finite/Entropy/Relative.lean:383:  sorry
./QuantumInfo/Finite/Entropy/Relative.lean:969:          sorry
./QuantumInfo/Finite/Entropy/Relative.lean:983:  sorry
./QuantumInfo/Finite/Entropy/Relative.lean:991:  sorry
./QuantumInfo/Finite/Entropy/Relative.lean:1067:  sorry
./QuantumInfo/Finite/Entropy/Relative.lean:1073:  sorry
./QuantumInfo/Finite/Entropy/Relative.lean:1084:    sorry
./QuantumInfo/Finite/Entropy/Relative.lean:1106:  sorry
./QuantumInfo/Finite/Entropy/Relative.lean:1120:  sorry
./QuantumInfo/Finite/Entropy/Relative.lean:1125:  sorry
./QuantumInfo/Finite/Entropy/Relative.lean:1131:  sorry
./QuantumInfo/Finite/Entropy/SSA.lean:33:  sorry
./QuantumInfo/Finite/Entropy/SSA.lean:306:--   admit
./QuantumInfo/Finite/Distance/Fidelity.lean:34:  sorry --submultiplicativity of trace and sqrt
./QuantumInfo/Finite/Distance/Fidelity.lean:77:  sorry --break into sqrts
./QuantumInfo/Finite/Distance/Fidelity.lean:81:  sorry
./QuantumInfo/Finite/Ensemble.lean:118:  sorry
./StatMech/ThermoQuantities.lean:89:  sorry
./QuantumInfo/Finite/CPTPMap/CPTP.lean:368:  sorry --TODO: permutations
./QuantumInfo/Finite/CPTPMap/CPTP.lean:455:  sorry
./QuantumInfo/Finite/CPTPMap/MatrixMap.lean:125:  sorry
./QuantumInfo/Finite/CPTPMap/Dual.lean:42:  sorry
./QuantumInfo/Finite/CPTPMap/Dual.lean:49:  sorry
./QuantumInfo/Finite/CPTPMap/Unbundled.lean:747:  sorry
./QuantumInfo/Finite/AxiomatizedEntropy/Defs.lean:143:  sorry
./QuantumInfo/Finite/AxiomatizedEntropy/Defs.lean:159:    sorry --missing simp lemma
./QuantumInfo/Finite/AxiomatizedEntropy/Defs.lean:177:    sorry--TODO
./QuantumInfo/Finite/AxiomatizedEntropy/Defs.lean:182:  sorry --Tomamichel, https://www.marcotom.info/files/entropy-masterclass2022.pdf, (1.28)
./QuantumInfo/Finite/AxiomatizedEntropy/Defs.lean:211:    sorry
./QuantumInfo/Finite/AxiomatizedEntropy/Defs.lean:215:    sorry --log ("min nonzero eigenvalue of σ" / "max eigenvalue of ρ") should work
./QuantumInfo/Finite/AxiomatizedEntropy/Defs.lean:224:    sorry
./QuantumInfo/Finite/AxiomatizedEntropy/Defs.lean:230:  sorry --Tomamichel, https://www.marcotom.info/files/entropy-masterclass2022.pdf, (1.28)
./QuantumInfo/Finite/AxiomatizedEntropy/Renyi.lean:19:    sorry⟩
./Particles/BeyondTheStandardModel/TwoHDM/GramMatrix.lean:207:  sorry
./Particles/BeyondTheStandardModel/TwoHDM/GramMatrix.lean:220:  sorry
./Particles/BeyondTheStandardModel/TwoHDM/GramMatrix.lean:416:    ∃ H : TwoHiggsDoublet, H.gramVector = v := by sorry
./Particles/BeyondTheStandardModel/TwoHDM/GramMatrix.lean:426:    sorry
```

### B1. `sorry`/`admit` by File (descending)
```text
  13 ./QuantumInfo/Finite/Entropy/Relative.lean
   8 ./QuantumInfo/Finite/AxiomatizedEntropy/Defs.lean
   7 ./QuantumInfo/Finite/Capacity.lean
   4 ./Particles/BeyondTheStandardModel/TwoHDM/GramMatrix.lean
   3 ./QuantumInfo/Finite/Distance/Fidelity.lean
   2 ./QuantumInfo/ForMathlib/Misc.lean
   2 ./QuantumInfo/Finite/Entropy/SSA.lean
   2 ./QuantumInfo/Finite/CPTPMap/Dual.lean
   2 ./QuantumInfo/Finite/CPTPMap/CPTP.lean
   1 ./StatMech/ThermoQuantities.lean
   1 ./QuantumInfo/ForMathlib/Lieb.lean
   1 ./QuantumInfo/Finite/Ensemble.lean
   1 ./QuantumInfo/Finite/CPTPMap/Unbundled.lean
   1 ./QuantumInfo/Finite/CPTPMap/MatrixMap.lean
   1 ./QuantumInfo/Finite/AxiomatizedEntropy/Renyi.lean
```

## C. Vacuous Propositions (`True := by trivial` / `: Prop := True`)
```text
./ClassicalMechanics/CentralForce/Basic.lean:115:    True := by trivial
./ClassicalMechanics/CentralForce/Basic.lean:119:    True := by trivial
./ClassicalMechanics/CentralForce/Basic.lean:124:    True := by trivial
./ClassicalMechanics/CentralForce/Basic.lean:141:    True := by trivial
./StatMech/PhaseTransitions/LandauTheory.lean:84:    True := by trivial
./StatMech/PhaseTransitions/LandauTheory.lean:99:    True := by trivial
./CondensedMatter/BlochTheorem/Basic.lean:86:    True := by trivial
./StatMech/MolecularDynamics/LennardJones.lean:170:    (hdist_symm : ∀ a b, dist a b = dist b a) : True := by trivial
./Physics/ActionPrinciple/Basic.lean:79:  conservation : Prop := True
./Physics/Holography/QECSpacetime.lean:44:  isometry_exists : Prop := True -- STUB: encoding isometry existence
./Physics/Holography/QECSpacetime.lean:71:  monotonicity : Prop := True -- STUB: monotonicity of reconstruction
./Physics/Holography/QECSpacetime.lean:99:  perfect_tensors : Prop := True -- STUB: perfect tensor property
./QFT/HaagsTheorem.lean:41:  is_free : Prop := True
./QFT/HaagsTheorem.lean:54:  isUnitary : Prop := True  -- STUB: should state actual unitarity
./QFT/HaagsTheorem.lean:56:  intertwines_fields : Prop := True  -- STUB: should state field intertwining
./QFT/HaagsTheorem.lean:66:  U_unitary : Prop := True  -- STUB: should state actual unitarity
./QFT/HaagsTheorem.lean:67:  maps_vacuum : Prop := True  -- STUB: should state vacuum mapping
./QFT/HaagsTheorem.lean:84:    True := by trivial
./QFT/HaagsTheorem.lean:105:    True := by trivial
./QFT/HaagsTheorem.lean:114:    True := by trivial
./QFT/BRSTCohomology.lean:97:    (_state : BRSTField 𝔤 d) : Prop := True
./QFT/BRSTCohomology.lean:101:    (_state : BRSTField 𝔤 d) : Prop := True
./Mechanics/PathIntegral.lean:87:  unitarity : Prop := True
./Mechanics/Poincare.lean:79:    True := by trivial
./Mechanics/Poincare.lean:99:    True := by trivial
./Mathematics/DataStructures/Matrix/LieTrace.lean:34:    (A : Matrix m m 𝕂) : True := by trivial
./Mathematics/DataStructures/Matrix/LieTrace.lean:39:    (A : Matrix n n ℝ) : True := by trivial
./QuantumInfo/InfiniteDim/CStarAlgebra.lean:60:  witness : Prop := True
./Mathematics/Trigonometry/Tanh.lean:135:lemma tanh_hasTemperateGrowth : True := by trivial -- STUB: Function.HasTemperateGrowth not in this Mathlib version
./Mathematics/Trigonometry/Tanh.lean:189:lemma tanh_const_mul_hasTemperateGrowth (κ : ℝ) : True := by trivial
./QuantumMechanics/HydrogenAtom/Basic.lean:96:    True := by trivial
./QuantumMechanics/HydrogenAtom/Basic.lean:120:    True := by trivial
./QuantumMechanics/HydrogenAtom/Basic.lean:128:    True := by trivial
./QuantumMechanics/WKB/Basic.lean:117:    (hV : bs.sys.V = fun x => bs.sys.m * ω ^ 2 * x ^ 2 / 2) : True := by trivial
./QuantumMechanics/WKB/Basic.lean:142:theorem penetrationIntegral_nonneg : True := by trivial
./QuantumMechanics/WKB/Basic.lean:147:theorem tunnellingProbability_bounded : True := by trivial
./QuantumMechanics/WKB/Basic.lean:202:example (tb : TunnellingBarrier) : True := by trivial
./QuantumMechanics/WKB/Basic.lean:205:example (tb : TunnellingBarrier) : True := by trivial
./QuantumInfo/Finite/AxiomatizedEntropy/Defs.lean:243:  -- convex : True := by trivial
./QuantumMechanics/ModularTheory/SubsystemEmergence.lean:107:  complete : Prop := True -- STUB: completeness + C*-identity
./QuantumMechanics/ModularTheory/SubsystemEmergence.lean:111:  has_predual : True := by trivial -- STUB: weak* closure / predual
./QuantumMechanics/ModularTheory/SubsystemEmergence.lean:119:  continuous' : Prop := True -- STUB: continuity
./QuantumMechanics/ModularTheory/SubsystemEmergence.lean:130:    (_ω : State A) : Prop := True  -- placeholder
./QuantumMechanics/ModularTheory/SubsystemEmergence.lean:205:  Ω_cyclic : Prop := True -- STUB: cyclicity of Ω
./QuantumMechanics/ModularTheory/KMS/Modular.lean:88:  has_predual : True := by trivial -- STUB: predual condition
./QuantumMechanics/BellsTheorem/ThermalBell/OptimalBudget.lean:41:theorem thermal_bounded_by_integral (M : ThermalHVModel Λ) : True := by trivial
./QuantumMechanics/BellsTheorem/ThermalBell/OptimalBudget.lean:45:    (h : CHSHOptimalPattern M δ) : True := by trivial
./QFT/WightmanAxioms.lean:126:    True := by trivial
./QFT/WightmanAxioms.lean:131:    True := by trivial
./QFT/WightmanAxioms.lean:137:    True := by trivial
./QFT/WightmanAxioms.lean:142:    True := by trivial
./QFT/WightmanAxioms.lean:148:    True := by trivial
./QuantumMechanics/BellsTheorem/OtherInequalities/CGLMP.lean:84:theorem classical_cglmp_bound (P : JointDistribution d) : True := by trivial
./QFT/Anomalies.lean:98:  jacobian_equals_anomaly : Prop := True -- STUB: J = exp(-2i ∫ α(x) (1/16π²) Tr(F ∧ F) d⁴x)
./QFT/Anomalies.lean:118:  vector_ward_identity : Prop := True
./QFT/Anomalies.lean:121:  axial_ward_violated : Prop := True
./QuantumMechanics/BellsTheorem/ThermalBell/SharedEnBudget.lean:216:theorem integral_constraint_bounds_thermal : True := by trivial
./QFT/YangMills.lean:46:  jacobi : Prop := True
./QFT/YangMills.lean:80:    True := by trivial
./QFT/YangMills.lean:117:    True := by trivial
./QFT/OsterwalderSchrader.lean:61:  regularity : Prop := True -- STUB: S_n ∈ S'(ℝ^{dn} \ diagonals)
./QFT/OsterwalderSchrader.lean:65:  euclidean_covariance : Prop := True -- STUB: S_n(Rx₁+a, ..., Rxₙ+a) = S_n(x₁, ..., xₙ) for (R,a) ∈ E(d)
./QFT/OsterwalderSchrader.lean:73:  os_positivity : Prop := True -- STUB: ∑ᵢⱼ ∫ S_{m+n}(θx₁,...,θxₘ,y₁,...,yₙ) f̄ₘ(x) fₙ(y) ≥ 0
./QFT/OsterwalderSchrader.lean:77:  symmetry : Prop := True -- STUB: S_n(x_{σ(1)},...,x_{σ(n)}) = S_n(x₁,...,xₙ) for σ ∈ Sₙ
./QFT/OsterwalderSchrader.lean:81:  cluster : Prop := True -- STUB: lim_{|a|→∞} S_{m+n}(x₁,...,xₘ,y₁+a,...,yₙ+a) = Sₘ(x₁,...,xₘ) ⋅ Sₙ
./QFT/OsterwalderSchrader.lean:92:    True := by trivial
./QFT/OsterwalderSchrader.lean:106:    True := by trivial
./QFT/OsterwalderSchrader.lean:112:    True := by trivial
./QFT/PCTTheorem.lean:46:  antilinear : Prop := True -- STUB: Θ(αψ + βφ) = ᾱ Θψ + β̄ Θφ
./QFT/PCTTheorem.lean:47:  preserves_inner : Prop := True -- STUB: ⟨Θψ, Θφ⟩ = conj ⟨ψ, φ⟩
./QFT/PCTTheorem.lean:56:  unitary : Prop := True -- STUB: P†P = PP† = 1
./QFT/PCTTheorem.lean:58:  transforms_fields : Prop := True -- STUB: P φ_j(t,x⃗) P⁻¹ = η_j φ_j(t,-x⃗)
./QFT/PCTTheorem.lean:65:  unitary : Prop := True
./QFT/PCTTheorem.lean:66:  transforms_fields : Prop := True -- STUB: C φ_j(x) C⁻¹ = η_C,j φ_j†(x)
./QFT/PCTTheorem.lean:73:  transforms_fields : Prop := True -- STUB: T φ_j(t,x⃗) T⁻¹ = η_T,j φ_j(-t,x⃗)
./QFT/PCTTheorem.lean:83:  transforms_fields : Prop := True
./QFT/PCTTheorem.lean:108:    True := by trivial
./QFT/PCTTheorem.lean:115:    True := by trivial
./QFT/ConnesKreimerHopf.lean:118:    True := by trivial
./QFT/ConnesKreimerHopf.lean:131:    True := by trivial
./QFT/ConnesKreimerHopf.lean:146:    True := by trivial
```

### C1. Vacuous Stubs by File (descending)
```text
  10 ./QFT/PCTTheorem.lean
   8 ./QFT/OsterwalderSchrader.lean
   8 ./QFT/HaagsTheorem.lean
   5 ./QuantumMechanics/WKB/Basic.lean
   5 ./QuantumMechanics/ModularTheory/SubsystemEmergence.lean
   5 ./QFT/WightmanAxioms.lean
   4 ./ClassicalMechanics/CentralForce/Basic.lean
   3 ./QuantumMechanics/HydrogenAtom/Basic.lean
   3 ./QFT/YangMills.lean
   3 ./QFT/ConnesKreimerHopf.lean
   3 ./QFT/Anomalies.lean
   3 ./Physics/Holography/QECSpacetime.lean
   2 ./StatMech/PhaseTransitions/LandauTheory.lean
   2 ./QuantumMechanics/BellsTheorem/ThermalBell/OptimalBudget.lean
   2 ./QFT/BRSTCohomology.lean
   2 ./Mechanics/Poincare.lean
   2 ./Mathematics/Trigonometry/Tanh.lean
   2 ./Mathematics/DataStructures/Matrix/LieTrace.lean
   1 ./StatMech/MolecularDynamics/LennardJones.lean
   1 ./QuantumMechanics/ModularTheory/KMS/Modular.lean
   1 ./QuantumMechanics/BellsTheorem/ThermalBell/SharedEnBudget.lean
   1 ./QuantumMechanics/BellsTheorem/OtherInequalities/CGLMP.lean
   1 ./QuantumInfo/InfiniteDim/CStarAlgebra.lean
   1 ./QuantumInfo/Finite/AxiomatizedEntropy/Defs.lean
   1 ./Physics/ActionPrinciple/Basic.lean
   1 ./Mechanics/PathIntegral.lean
   1 ./CondensedMatter/BlochTheorem/Basic.lean
```

## D. `ProofOmitted` / `proof_omitted` References
```text
./StatMech/MolecularDynamics/LennardJones.lean:9:import QuantumInfo.ForMathlib.ProofOmitted
./Optics/GeometricOptics/Basic.lean:8:import QuantumInfo.ForMathlib.ProofOmitted
./Cosmology/Inflation/Basic.lean:8:import QuantumInfo.ForMathlib.ProofOmitted
./Physics/Entropy/Hierarchy.lean:11:import QuantumInfo.ForMathlib.ProofOmitted
./Physics/InformationGravity/BekensteinBound.lean:8:import QuantumInfo.ForMathlib.ProofOmitted
./Physics/ActionPrinciple/Basic.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./Physics/Holography/QECSpacetime.lean:6:import QuantumInfo.ForMathlib.ProofOmitted
./Particles/SuperSymmetry/SU5/ChargeSpectrum/AllowsTerm.lean:8:import QuantumInfo.ForMathlib.ProofOmitted
./Particles/SuperSymmetry/SU5/ChargeSpectrum/Map.lean:8:import QuantumInfo.ForMathlib.ProofOmitted
./Particles/SuperSymmetry/SU5/ChargeSpectrum/Completions.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./Particles/SuperSymmetry/SU5/ChargeSpectrum/MinimallyAllowsTerm/OfFinset.lean:8:import QuantumInfo.ForMathlib.ProofOmitted
./CondensedMatter/Superconductivity/BCS.lean:9:import QuantumInfo.ForMathlib.ProofOmitted
./Thermodynamics/MaxwellRelations.lean:8:import QuantumInfo.ForMathlib.ProofOmitted
./Mechanics/Hamilton.lean:3:import QuantumInfo.ForMathlib.ProofOmitted
./Mathematics/Calculus/AdjFDeriv.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./Mathematics/Calculus/Divergence.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./Mechanics/PathIntegral.lean:3:import QuantumInfo.ForMathlib.ProofOmitted
./Mechanics/Symplectic.lean:6:import QuantumInfo.ForMathlib.ProofOmitted
./SpaceAndTime/SpaceTime/TimeSlice.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./Mechanics/Wigner.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./Mathematics/FDerivCurry.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./SpaceAndTime/Space/Slice.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./SpaceAndTime/Space/IsDistBounded.lean:9:import QuantumInfo.ForMathlib.ProofOmitted
./Mathematics/SpecialFunctions/PhysHermite.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./SpaceAndTime/Space/RadialAngularMeasure.lean:9:import QuantumInfo.ForMathlib.ProofOmitted
./SpaceAndTime/Space/Basic.lean:13:import QuantumInfo.ForMathlib.ProofOmitted
./SpaceAndTime/Space/DistOfFunction.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./SpaceAndTime/Space/ConstantSliceDist.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./Mathematics/DataStructures/Matrix/LieTrace.lean:9:import QuantumInfo.ForMathlib.ProofOmitted
./SpaceAndTime/Space/Norm.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./SpaceAndTime/Space/CrossProduct.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./QuantumMechanics/WKB/Basic.lean:10:import QuantumInfo.ForMathlib.ProofOmitted
./Mathematics/Trigonometry/Tanh.lean:9:import QuantumInfo.ForMathlib.ProofOmitted
./QuantumInfo/InfiniteDim/CStarAlgebra.lean:8:import QuantumInfo.ForMathlib.ProofOmitted
./Relativity/LorentzGroup/Boosts/Generalized.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./Relativity/LorentzGroup/ToVector.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./Particles/SuperSymmetry/SU5/ChargeSpectrum/MinimallyAllowsTerm/FinsetTerms.lean:8:import QuantumInfo.ForMathlib.ProofOmitted
./Relativity/LorentzGroup/Rotations.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./Mathematics/VariationalCalculus/HasVarGradient.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./SpaceAndTime/TimeAndSpace/Basic.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./SpaceAndTime/SpaceTime/Basic.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./Mathematics/VariationalCalculus/Basic.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./Relativity/LorentzGroup/Restricted/FromBoostRotation.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./Mathematics/VariationalCalculus/IsTestFunction.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./SpaceAndTime/SpaceTime/Derivatives.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./SpaceAndTime/SpaceTime/LorentzAction.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./QuantumMechanics/PerturbationTheory/Basic.lean:8:import QuantumInfo.ForMathlib.ProofOmitted
./QuantumMechanics/BerryPhase/Basic.lean:8:import QuantumInfo.ForMathlib.ProofOmitted
./Relativity/Schwarzschild/Bornemann.lean:29:import QuantumInfo.ForMathlib.ProofOmitted
./QuantumMechanics/ModularTheory/SubsystemEmergence.lean:11:import QuantumInfo.ForMathlib.ProofOmitted
./Relativity/GR/Foundations/EinsteinFieldEquations.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./QuantumInfo/Finite/Entropy/Holevo.lean:9:import QuantumInfo.ForMathlib.ProofOmitted
./SpaceAndTime/TimeAndSpace/ConstantTimeDist.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./QuantumInfo/Finite/Entropy/MinMax.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./QuantumMechanics/SpectralTheory/RelThermo.lean:120:import QuantumInfo.ForMathlib.ProofOmitted
./SpaceAndTime/Space/Derivatives/Grad.lean:6:import QuantumInfo.ForMathlib.ProofOmitted
./Relativity/Tensors/RealTensor/Vector/MinkowskiProduct.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./QuantumMechanics/ModularTheory/KMS/Modular.lean:8:import QuantumInfo.ForMathlib.ProofOmitted
./QuantumMechanics/SpectralTheory/DiracEquation/Conservation.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./Particles/SuperSymmetry/SU5/ChargeSpectrum/OfPotentialTerm.lean:8:import QuantumInfo.ForMathlib.ProofOmitted
./Units/Crystallography.lean:11:import QuantumInfo.ForMathlib.ProofOmitted
./Relativity/Tensors/RealTensor/Vector/Pre/Contraction.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./QuantumMechanics/SpectralTheory/DiracEquation/Operators.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./QuantumMechanics/ScatteringTheory/Basic.lean:8:import QuantumInfo.ForMathlib.ProofOmitted
./QuantumMechanics/AngularMomentum/Basic.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./Relativity/Tensors/RealTensor/Vector/Basic.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./QuantumMechanics/SpectralTheory/DiracEquation/SpectralTheory.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./SpaceAndTime/Space/Derivatives/Curl.lean:8:import QuantumInfo.ForMathlib.ProofOmitted
./SpaceAndTime/Space/Derivatives/Basic.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./Mathematics/VariationalCalculus/HasVarAdjDeriv.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./QuantumMechanics/OneDimension/HarmonicOscillator/TISE.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./QuantumMechanics/SpectralTheory/FunctionalCalc/CrossMeasure.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./Mathematics/VariationalCalculus/HasVarAdjoint.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./QuantumMechanics/OneDimension/HarmonicOscillator/Eigenfunction.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./SpaceAndTime/Space/Derivatives/Div.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./QuantumMechanics/SpectralTheory/FunctionalCalc/Agreement.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./Relativity/Tensors/RealTensor/Velocity/Basic.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./Relativity/Tensors/RealTensor/Basic.lean:8:import QuantumInfo.ForMathlib.ProofOmitted
./QuantumMechanics/SpectralTheory/FunctionalCalc/Generator.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./QuantumMechanics/OneDimension/HilbertSpace/Basic.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./QuantumMechanics/SpectralTheory/FunctionalCalc/Algebraic.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./QuantumMechanics/SpectralTheory/FunctionalCalc/Integral.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./QuantumMechanics/SpectralTheory/ResolventRoute/StonesFormula.lean:8:import QuantumInfo.ForMathlib.ProofOmitted
./Relativity/GR/KerrMetric/Complexity.lean:3:import QuantumInfo.ForMathlib.ProofOmitted
./QuantumMechanics/OneDimension/Operators/Parity.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./QuantumMechanics/SpectralTheory/ResolventRoute/SpectralRepresentation.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./QuantumMechanics/OneDimension/Operators/Commutation.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./QuantumMechanics/SpectralTheory/ResolventRoute/ResolventKernel.lean:9:import QuantumInfo.ForMathlib.ProofOmitted
./QuantumMechanics/OneDimension/Operators/Momentum.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./QuantumMechanics/SpectralTheory/ResolventRoute/StieltjesInversion.lean:9:import QuantumInfo.ForMathlib.ProofOmitted
./SpaceAndTime/Time/Basic.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./Relativity/GR/KerrMetric.lean:121:import QuantumInfo.ForMathlib.ProofOmitted
./QuantumMechanics/SpectralTheory/BochnerRoute/PositiveDefinite.lean:12:import QuantumInfo.ForMathlib.ProofOmitted
./Particles/StandardModel/HiggsBoson/Basic.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./Electromagnetism/MaxwellEquations.lean:6:import QuantumInfo.ForMathlib.ProofOmitted
./QuantumMechanics/BellsTheorem/OtherInequalities/CGLMP.lean:3:import QuantumInfo.ForMathlib.ProofOmitted
./QuantumMechanics/BellsTheorem/OtherInequalities/ThermMerm.lean:25:import QuantumInfo.ForMathlib.ProofOmitted
./Relativity/GR/GravitationalWaves.lean:6:import QuantumInfo.ForMathlib.ProofOmitted
./Particles/BeyondTheStandardModel/TwoHDM/Potential.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./SpaceAndTime/Time/Derivatives.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./Relativity/GR/Foundations/RiemannTensor.lean:6:import QuantumInfo.ForMathlib.ProofOmitted
./SpaceAndTime/Time/TimeTransMan.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./QuantumMechanics/BellsTheorem/TLHV_P.lean:47:import QuantumInfo.ForMathlib.ProofOmitted
./QuantumMechanics/BellsTheorem/TLHV/Measurement.lean:2:import QuantumInfo.ForMathlib.ProofOmitted
./QuantumMechanics/BellsTheorem/TLHV/CriticalQuestions.lean:3:import QuantumInfo.ForMathlib.ProofOmitted
./QFT/PCTTheorem.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./QFT/HaagsTheorem.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./QuantumMechanics/BellsTheorem/ThermalBell/OptimalBudget.lean:3:import QuantumInfo.ForMathlib.ProofOmitted
./QFT/SpinStatistics.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./QFT/BRSTCohomology.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./QFT/ConnesKreimerHopf.lean:9:import QuantumInfo.ForMathlib.ProofOmitted
./QuantumMechanics/BellsTheorem/ThermalBell/SequentialMeasurements.lean:2:import QuantumInfo.ForMathlib.ProofOmitted
./QuantumMechanics/DDimensions/Operators/Position.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./QuantumMechanics/DDimensions/Operators/Commutation.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./QuantumMechanics/BellsTheorem/ThermalBell/SharedEnBudget.lean:2:import QuantumInfo.ForMathlib.ProofOmitted
./QFT/Anomalies.lean:8:import QuantumInfo.ForMathlib.ProofOmitted
./QFT/OsterwalderSchrader.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./Relativity/GR/Foundations/ChristoffelSymbols.lean:7:import QuantumInfo.ForMathlib.ProofOmitted
./Particles/BeyondTheStandardModel/TwoHDM/GramMatrix.lean:9:import QuantumInfo.ForMathlib.ProofOmitted
./Relativity/GR/Foundations/ParallelTransport.lean:6:import QuantumInfo.ForMathlib.ProofOmitted
./QFT/YangMills.lean:10:import QuantumInfo.ForMathlib.ProofOmitted
```

## E. TODO/Stub/Placeholder Markers
```text
./ClassicalMechanics/RigidBody/Basic.lean:26:TODO "MEX5S" "The definition of a rigid body is currently defined via linear maps
./ClassicalMechanics/DampedHarmonicOscillator/Basic.lean:32:This module is currently a placeholder for future implementation. The following results
./ClassicalMechanics/DampedHarmonicOscillator/Basic.lean:67:TODO "DHO01" "Define the DampedHarmonicOscillator structure with mass m, spring constant k,
./ClassicalMechanics/DampedHarmonicOscillator/Basic.lean:70:TODO "DHO04" "Prove that energy is not conserved and derive the energy dissipation rate."
./ClassicalMechanics/DampedHarmonicOscillator/Basic.lean:72:TODO "DHO05" "Derive solutions for the underdamped case (oscillatory with exponential decay)."
./ClassicalMechanics/DampedHarmonicOscillator/Basic.lean:74:TODO "DHO06" "Derive solutions for the critically damped case (fastest non-oscillatory return)."
./ClassicalMechanics/DampedHarmonicOscillator/Basic.lean:76:TODO "DHO07" "Derive solutions for the overdamped case (slow non-oscillatory return)."
./ClassicalMechanics/DampedHarmonicOscillator/Basic.lean:78:TODO "DHO08" "Define and prove properties of the quality factor Q."
./ClassicalMechanics/DampedHarmonicOscillator/Basic.lean:80:TODO "DHO09" "Define and prove properties of the relaxation time τ."
./ClassicalMechanics/DampedHarmonicOscillator/Basic.lean:82:TODO "DHO10" "Prove that the damped harmonic oscillator reduces to the undamped case when γ = 0."
./ClassicalMechanics/DampedHarmonicOscillator/Basic.lean:86:## A. The input data (placeholder)
./ClassicalMechanics/DampedHarmonicOscillator/Basic.lean:122:## B. The natural angular frequency (placeholder)
./ClassicalMechanics/DampedHarmonicOscillator/Basic.lean:210:## E. Damping regimes (placeholder)
./ClassicalMechanics/WaveEquation/HarmonicWave.lean:13:Note TODO `EGU3E` may require considerable effort to be made rigorous and may heavily depend on
./ClassicalMechanics/WaveEquation/HarmonicWave.lean:37:TODO "EGQUA" "Show that the wave equation is invariant under rotations and any direction `s`
./ClassicalMechanics/WaveEquation/HarmonicWave.lean:73:TODO "EGU3E" "Show that any disturbance (subject to certain conditions) can be expressed
./Units/Examples.lean:222:TODO "LCR7N" "Add an example involving derivatives."
./Units/Basic.lean:29:(In fact temperature is not really a fundamental choice, however we leave this as a `TODO`.)
./Units/Basic.lean:194:TODO "LCSAY" "Make SI : UnitChoices computable, probably by
./ClassicalMechanics/HarmonicOscillator/Solution.lean:210:TODO "6VZME" "Implement other initial conditions (deferred to future PRs). For example:
./ClassicalMechanics/HarmonicOscillator/Solution.lean:427:for the given initial conditions. This is currently a TODO.
./ClassicalMechanics/HarmonicOscillator/Solution.lean:870:TODO "6VZI3" "For the classical harmonic oscillator find the time for which it returns to
./ClassicalMechanics/HarmonicOscillator/Solution.lean:873:TODO "6VZJB" "For the classical harmonic oscillator find the times for
./ClassicalMechanics/HarmonicOscillator/Basic.lean:89:TODO "6VZHC" "Create a new folder for the damped harmonic oscillator, initially as a place-holder."
./Units/Minerals.lean:568:  []  -- placeholder pending oxygen-basis normalization implementation
./Units/Minerals.lean:573:  []  -- placeholder pending constrained least-squares solver
./Units/Minerals.lean:578:  (⟨totalFe.val / 2.0⟩, ⟨totalFe.val / 2.0⟩)  -- placeholder equal split
./Units/Minerals.lean:606:    method := "GASP-placeholder" }  -- placeholder pending activity model + K_eq relation
./Units/Minerals.lean:674:  0.0  -- placeholder pending commodity-keyed valuation fold
./ClassicalMechanics/Basic.lean:10:This file is currently a stub.
./ClassicalMechanics/Vibrations/LinearTriatomic.lean:6:import Meta.TODO.Basic
./ClassicalMechanics/Vibrations/LinearTriatomic.lean:16:TODO "L7O4I" "Derive the frequencies of vibaration of a symmetric linear triatomic molecule."
./ClassicalMechanics/Scattering/RigidSphere.lean:6:import Meta.TODO.Basic
./ClassicalMechanics/Scattering/RigidSphere.lean:16:TODO "L7OTP" "Derive the scattering cross section of a perfectly rigid sphere."
./Optics/Basic.lean:10:This file is currently a stub.
./Thermodynamics/Basic.lean:10:This file is currently a stub.
./Units/WithDim/Basic.lean:156:TODO "LPWE4" "Induce instances on `WithDim d M` from instances on `M`."
./QuantumMechanics/OneDimension/HarmonicOscillator/Basic.lean:21:## TODO
./StringTheory/FTheory/SU5/Charges/OfRationalSection.lean:6:import Meta.TODO.Basic
./StringTheory/FTheory/SU5/Charges/OfRationalSection.lean:57:TODO "AETF6" "The results in this file are currently stated, but not proved.
./QuantumMechanics/OneDimension/ReflectionlessPotential/Basic.lean:20:## TODO
./QuantumMechanics/OneDimension/ReflectionlessPotential/Basic.lean:60:TODO: Add theorems about reflectionless potential - the main result is the actual 1d solution
./Mechanics/Poincare.lean:65:-- TODO: minkowskiInner_explicit was stated as `True` — a vacuous stub.
./Mechanics/Poincare.lean:187:-- TODO: massive_standard_on_shell and massless_standard_on_shell were
./Particles/SuperSymmetry/SU5/ChargeSpectrum/PhenoClosed.lean:8:import Meta.TODO.Basic
./Particles/SuperSymmetry/SU5/ChargeSpectrum/PhenoClosed.lean:385:TODO "JGVOQ" "Make the result `viableChargesMultiset` a safe definition, that is to
./CondensedMatter/Basic.lean:10:This file is currently a stub.
./QuantumMechanics/SpectralTheory/RelThermo.lean:855:**Physical meaning**: Unitarity isn't an arbitrary postulate — it's the
./ClassicalInfo/Entropy.lean:128:--TODO:
./ClassicalInfo/Prob.lean:389:--TODO: Upgrade to `StrictAnti`. Even better: bundle negLog as `Prob ≃o ENNRealᵒᵈ`.
./Cosmology/Basic.lean:10:This file is currently a stub.
./Mathematics/FunctionalAnalysis/Distributions.lean:8:-- Replaced with a minimal axiomatized stub since those Mathlib modules are unavailable.
./Mathematics/FunctionalAnalysis/Distributions.lean:11:Axiomatized stub. See Mathematics/Distribution/Basic.lean for the main definitions.
./Mathematics/FunctionalAnalysis/Distributions.lean:16:/-- A stub type for generalized function spaces. -/
./Mathematics/FunctionalAnalysis/Distributions.lean:19:/-- A distribution as a linear functional on test functions (stub). -/
./Mathematics/FunctionalAnalysis/Distributions.lean:24:/-- The Dirac delta (stub). -/
./SpaceAndTime/SpaceTime/Basic.lean:72:TODO "6V2DR" "SpaceTime should be refactored into a structure, or similar, to prevent casting."
./Mathematics/LinearMaps.lean:9:import Meta.TODO.Basic
./Mathematics/LinearMaps.lean:18:TODO "6VZLZ" "Replace the definitions in this file with Mathlib definitions."
./QuantumMechanics/FiniteTarget/HilbertSpace.lean:7:import Meta.TODO.Basic
./SpaceAndTime/Space/Basic.lean:7:import Meta.TODO.Basic
./SpaceAndTime/Space/Basic.lean:32:TODO "HB6RR" "In the above documentation describe the notion of a type, and
./SpaceAndTime/Space/Basic.lean:35:TODO "HB6VC" "Convert `Space` from an `abbrev` to a `def`."
./SpaceAndTime/Space/Basic.lean:390:TODO "HB6YZ" "In the above documentation describe what an instance is, and why
./SpaceAndTime/Space/Basic.lean:393:TODO "HB6WN" "After TODO 'HB6VC', give `Space d` the necessary instances
./SpaceAndTime/Space/Basic.lean:431:TODO "HB6Z4" "In the above documentation describe the notion of a basis
./SpaceAndTime/Space/DistOfFunction.lean:134:TODO "LV5RM" "Add a general lemma specifying the derivative of
./QuantumMechanics/FiniteTarget/Basic.lean:8:import Meta.TODO.Basic
./QuantumMechanics/FiniteTarget/Basic.lean:62:TODO "6VZGG" "Define a smooth structure on `FiniteTarget`."
./QuantumMechanics/ModularTheory/SubsystemEmergence.lean:130:    (_ω : State A) : Prop := True  -- placeholder
./QuantumMechanics/ModularTheory/SubsystemEmergence.lean:220:    The Born rule is a theorem of C*-algebra theory, not a postulate. -/
./QuantumMechanics/DDimensions/Operators/Position.lean:52:TODO "ZGCNP" "Incorporate normRegularizedPow into Space.Norm"
./Mathematics/KroneckerDelta.lean:7:import Meta.TODO.Basic
./Mathematics/KroneckerDelta.lean:15:TODO "YVABB" "Build functionality for working with sums involving Kronecker deltas."
./Mathematics/Distribution/Basic.lean:51:/-- The Fréchet derivative of a distribution (stub). -/
./Mathematics/Distribution/Basic.lean:64:/-- Constant distribution sending every Schwartz function to its integral times `m` (stub). -/
./QuantumInfo/ForMathlib/Minimax.lean:15:--TODO go elsewhere
./QuantumInfo/ForMathlib/Minimax.lean:83:    assumption --why doesn't fun_prop find this assumption? TODO learn
./QuantumInfo/ForMathlib/Minimax.lean:86:    assumption --why doesn't fun_prop find this assumption? TODO
./QuantumInfo/ForMathlib/Minimax.lean:134:    --Why doesn't fun_prop find this, even though this theorem is marked fun_prop? TODO
./QuantumInfo/ForMathlib/Minimax.lean:138:    --Why doesn't fun_prop find this, even though this theorem is marked fun_prop? TODO
./QuantumMechanics/SpectralTheory/BochnerRoute/PositiveDefinite.lean:77:## TODO
./QuantumMechanics/SpectralTheory/BochnerRoute/PositiveDefinite.lean:91:## TODO
./Relativity/Special/TwinParadox/Basic.lean:64:TODO "6V2UQ" "Find the conditions for which the age gap for the twin paradox is zero."
./Relativity/Special/TwinParadox/Basic.lean:139:TODO "7ROQ4" "Do the twin paradox with a non-instantaneous acceleration. This should be done
./QuantumMechanics/ModularTheory/KMS/PeriodicStrip.lean:399:  -- In periodicExtension_continuous, replace the placeholder proof with:
./QuantumInfo/Finite/Capacity.lean:42:# TODO
./QuantumInfo/Finite/Capacity.lean:141:    -- TODO: Instead this proof should be `@[simp] piProd (fun x => id) = id` and `emulates_self`
./Mathematics.lean:10:-- Mathematics.FunctionalAnalysis.Distributions removed: axiomatized stub (opaque TestFunctionCarrier);
./QuantumInfo/Finite/POVM.lean:18:TODO: They can also evolve under CPTP maps themselves (the Heisenberg picture of quantum evolution), they might commute
./QuantumInfo/Finite/POVM.lean:106:    --TODO: Something like `HermitianMat.single` to make this better
./QuantumInfo/Finite/POVM.lean:133:  --TODO: a lemma for Matrix.traceLeft (∑ x, _) = ∑ x, (Matrix.traceLeft _)
./QuantumInfo/Finite/MState.lean:165:--TODO: Bundle as a ContinuousLinearMap.
./QuantumInfo/Finite/MState.lean:387:  · --TODO Cleanup
./QuantumInfo/Finite/MState.lean:419:--TODO: Would be better if there was an `MState.eigenstate` or similar (maybe extending
./QuantumInfo/Finite/MState.lean:427:  --TODO Cleanup
./QuantumInfo/Finite/MState.lean:514:-- TODO:
./QuantumInfo/Finite/MState.lean:545:-- TODO: direct sum (by zero-padding)
./QuantumInfo/Finite/MState.lean:547:--TODO: Spectra of left- and right- partial traces of a pure state are equal.
./QuantumInfo/Finite/MState.lean:604:--TODO: Spectrum of direct sum. Spectrum of partial trace?
./QuantumInfo/Finite/MState.lean:910:--TODO: Separable states are convex
./QuantumInfo/Finite/MState.lean:1024:  rw [spectrum.mem_iff] --TODO make a plain `Matrix` version of this
./QuantumInfo/Finite/MState.lean:1036:--TODO: Swap and assoc for kets.
./QuantumInfo/Finite/MState.lean:1037:--TODO: Connect these to unitaries (when they can be)
./QuantumInfo/Finite/MState.lean:1153:--TODO: This naming is very inconsistent. Should be better about "prod" vs "kron"
./QuantumInfo/Finite/MState.lean:1272:    --TODO this is ridiculous, move to Prob
./QuantumInfo/Finite/Pinching.lean:17:TODO: Generalize to pinching with respect to arbitrary P(O)VM.
./QuantumInfo/Finite/Pinching.lean:207:    -- so that we don't 'abuse' this defeq, TODO. (Maybe even make the coercions between
./QuantumInfo/Finite/Pinching.lean:267:  --TODO Cleanup
./QuantumInfo/Finite/Pinching.lean:300:  --TODO Cleanup
./QuantumInfo/Finite/Pinching.lean:350:  --TODO Cleanup
./QuantumInfo/Finite/Entanglement.lean:20:TODO:
./QuantumInfo/Finite/Entanglement.lean:111:-- TODO: make `le_convex_roof`, `convex_roof_le`, `le_mixed_convex_roof` and `mixed_convex_roof_le` if-and-only-if statements.
./QuantumInfo/Finite/Braket.lean:39:  --TODO: change to `vec : EuclideanSpace ℂ d` / `normalized' : ‖vec‖ = 1`
./QuantumInfo/Finite/AxiomatizedEntropy/Defs.lean:177:    sorry--TODO
./QuantumInfo/Finite/AxiomatizedEntropy/Defs.lean:242:  -- /-- Entropy is convex. TODO def? Or do we even need this? -/
./QuantumInfo/Finite/CPTPMap/CPTP.lean:194:--TODO: of_equiv (id) = id
./QuantumInfo/Finite/CPTPMap/CPTP.lean:234:    --TODO: make Matrix.traceLeft a linear map, a `MatrixMap`.
./QuantumInfo/Finite/CPTPMap/CPTP.lean:368:  sorry --TODO: permutations
./QuantumInfo/Finite/CPTPMap/CPTP.lean:436:--TODO:
./QuantumInfo/Finite/CPTPMap/CPTP.lean:475:--TODO: Constructing this will probably need Kraus operators first.
./QuantumInfo/Finite/CPTPMap/CPTP.lean:495:--TODO Theorem: `purify` is unique up to unitary equivalence.
./QuantumInfo/Finite/CPTPMap/CPTP.lean:497:--TODO: Best to rewrite the "zero_prep / prep / append" as one CPTPMap.append channel when we
./QuantumInfo/Finite/ResourceTheory/HypothesisTesting.lean:158:    --Why is the following three bundled together not a theorem? Is it, and I can't find it? TODO
./QuantumInfo/Finite/ResourceTheory/HypothesisTesting.lean:164:--TODO: Maybe we should define these two instances.
./QuantumInfo/Finite/ResourceTheory/HypothesisTesting.lean:507:  change 0 < b at hb_pos --TODO simp thm / lemma
./QuantumInfo/Finite/ResourceTheory/HypothesisTesting.lean:510:  · change 0 < (min c 1) * b --TODO simp thm / lemma
./QuantumInfo/Finite/CPTPMap/MatrixMap.lean:285:  --TODO: Cleanup, these two branches are nearly identical (separate lemma?)
./QuantumInfo/Finite/Distance/Fidelity.lean:83:--TODO: Real.arccos ∘ fidelity forms a metric (triangle inequality), the Fubini–Study metric.
./Electromagnetism/Current/CircularCoil.lean:16:This module is currently a stub, but will eventually contain the electrostatics of a
./Electromagnetism/Current/CircularCoil.lean:32:TODO "TCGIW" "Copying the structure of the electrostatics of an infinite wire,
./QuantumInfo/Finite/CPTPMap/Dual.lean:51:--TODO Cleanup, find home, abstract out to HermitianMats...?
./QuantumInfo/Finite/CPTPMap/Dual.lean:71:    --TODO Cleanup. Should be all in terms of HermitianMat
./QuantumInfo/Finite/CPTPMap/Dual.lean:408:/-- Version of `HPMap.inner_hermDual` that uses HermitiaMat.inner directly. TODO cleanup -/
./QuantumInfo/Finite/CPTPMap/Dual.lean:441:  rw [HermitianMat.inner_one, HermitianMat.inner_one] --TODO change to Inner.inner
./QuantumInfo/Finite/CPTPMap/Dual.lean:442:  exact congr(Complex.re $(h v)) --TODO: HPMap with IsTracePreserving give the HermitianMat.trace version
./QuantumInfo/Finite/CPTPMap/Bundled.lean:106:  have hNeg := h M⁻ M.negPart_le_zero --TODO: this is named incorrectly
./QuantumInfo/Finite/Entropy/Relative.lean:188:  intro h rfl; simp at h--should be grind[= map_zero] but I don't know why. TODO.
./QuantumInfo/Finite/Entropy/Relative.lean:195:--PULLOUT to MState.lean. TODO: Rename to `pos`, and rename the existing `MState.pos` to `nonneg`.
./QuantumInfo/Finite/Entropy/Relative.lean:418:--TODO Cleanup. Ugh.
./QuantumInfo/Finite/Entropy/Relative.lean:472:--TODO: Generalize to arbitrary PSD matrices.
./QuantumInfo/Finite/Entropy/Relative.lean:551:--TODO: Generalize to arbitrary PSD matrices.
./QuantumInfo/Finite/Entropy/Relative.lean:552:--TODO: Rewrite the proof using the `ker_le_of_ker_kron_le_left` lemma, and the fact that
./QuantumInfo/Finite/Entropy/Relative.lean:632:--TODO: Generalize to RCLike.
./QuantumInfo/Finite/Entropy/Relative.lean:884:  --TODO: Maybe SandwichedRelRentropy should actually be defined differently for α = 0?
./QuantumInfo/Finite/Entropy/Relative.lean:1097:TODO:
./Electromagnetism/Basic.lean:40:TODO "6V2UZ" "Charge density and current density should be generalized to signed measures,
./QuantumInfo/Finite/CPTPMap/Unbundled.lean:165:--TODO: Closed under composition, kronecker products, it's iff M.choi_matrix.traceLeft = 1...
./QuantumInfo/Finite/CPTPMap/Unbundled.lean:287:  --TODO Cleanup
./QuantumInfo/Finite/CPTPMap/Unbundled.lean:365:  --TODO clean up this mess (but, thanks Aristotle)
./QuantumInfo/Finite/CPTPMap/Unbundled.lean:559:  --TODO: This is identical to congruence_CP
./QuantumInfo/Finite/CPTPMap/Unbundled.lean:566:    --TODO cleanup. Thanks Aristotle
./QuantumInfo/Finite/Entropy/VonNeumann.lean:21:/- # TODO / Goals:
./QuantumInfo/Finite/Entropy/VonNeumann.lean:46:--TODO:
./QuantumInfo/Finite/Entropy/VonNeumann.lean:138:/-- Von Neumann entropy is unchanged under SWAP. TODO: All unitaries-/
./QuantumInfo/Finite/Entropy/VonNeumann.lean:173:--TODO Cleanup
./QuantumInfo/Finite/ResourceTheory/ResourceTheory.lean:159:--       --The fact that the fully mixed state is PosDef should be stated somewhere else... TODO
./QuantumInfo/Finite/Entropy/Holevo.lean:62:/-- Conservative Holevo-style bound available with the current placeholder
./QuantumInfo/Finite/ResourceTheory/SteinsLemma.lean:101:          --TODO: should be `bound`, ideally
./QuantumInfo/Finite/ResourceTheory/SteinsLemma.lean:106:          --TODO: should be `bound`, ideally
./QuantumInfo/Finite/ResourceTheory/SteinsLemma.lean:188:-- TODO: Commutation and order relations about `proj_le` specified in the text
./QuantumInfo/Finite/ResourceTheory/SteinsLemma.lean:577:  --Thanks Aristotle. TODO Cleanup
./QuantumInfo/Finite/ResourceTheory/SteinsLemma.lean:711:--TODO: would be nice to write a `Mixable` thing for mixing `k` things according to a distribution,
./QuantumInfo/Finite/ResourceTheory/SteinsLemma.lean:780:  · --This `(fun x => Real.log 3) =o[Filter.atTop] fun x => x` really should be its own fact, TODO
./QuantumInfo/Finite/ResourceTheory/SteinsLemma.lean:906:  --TODO make this its own definition: Normalizing a matrix to give a tr-1 op.
./QuantumInfo/Finite/ResourceTheory/SteinsLemma.lean:1069:  · apply HermitianMat.inner_ge_zero --TODO: Positivity extension for HermitianMat.inner
./QuantumInfo/Finite/ResourceTheory/SteinsLemma.lean:1070:    · apply MState.zero_le  --TODO: Positivity extension for MState
./QuantumInfo/Finite/ResourceTheory/SteinsLemma.lean:1071:    · apply HermitianMat.proj_le_nonneg --TODO: Positivity extension for projections
./QuantumInfo/Finite/ResourceTheory/SteinsLemma.lean:1375:        -- TODO streamline what's below
./QuantumInfo/Finite/ResourceTheory/SteinsLemma.lean:1379:        -- TODO this needs to be extracted from here, it's badly redundant
./QuantumInfo/Finite/ResourceTheory/SteinsLemma.lean:1437:              rfl --TODO: Lemma to work with this better
./QuantumInfo/Finite/ResourceTheory/SteinsLemma.lean:1481:              rfl --TODO: Lemma to work with this better (see above TODO)
./QuantumInfo/Finite/ResourceTheory/SteinsLemma.lean:1972:     --TODO: Should we have an HDiv Prob Nat instance?
./QuantumInfo/Finite/ResourceTheory/SteinsLemma.lean:2003:          --This should just be `simp` or `bound` at this point. TODO.
./QuantumInfo/Finite/Entropy/SSA.lean:76:--TODO Cleanup
./Electromagnetism/Charge/ChargeUnit.lean:9:import Meta.TODO.Basic
./QuantumInfo/ForMathlib/ContinuousSup.lean:67:of a compact set. -/ --TODO: Can `ProperSpace` be relaxed to `CompleteSpace` here?
./QuantumInfo/ForMathlib/Matrix.lean:839:--Should be combined the above...? TODO Cleanup
./QuantumInfo/ForMathlib/Matrix.lean:910:  --TODO cfc_cont_tac
./QuantumInfo/ForMathlib/Matrix.lean:1200:    --wtf do better. TODO
./QuantumInfo/ForMathlib/Matrix.lean:1617:--TODO: Can this be used for `Matrix.reindex_eq_conj` cleanup?
./QuantumInfo/ForMathlib/Isometry.lean:287:--TODO: All of these have Pi versions (instead of the "just two" operators versions below),
./QuantumInfo/ForMathlib/Isometry.lean:627:--TODO: Make Iff version.
./Relativity/Tensors/RealTensor/Derivative.lean:66:TODO "6V2CQ" "Prove that the derivative obeys the following equivariant
./QuantumInfo/ForMathlib/SionMinimax.lean:425:    --TODO: On newer Mathlib this is just `grind [inf_le_iff, le_trans]`
./QuantumInfo/ForMathlib/SionMinimax.lean:650:      -- TODO: On a newer mathlib this line is just `grind`
./QuantumInfo/ForMathlib/HermitianMat/Proj.lean:100:  --TODO Cleanup
./QuantumInfo/ForMathlib/HermitianMat/Proj.lean:198:  --TODO: Should do a `HermitianMat.cfc_pow`.
./QuantumInfo/ForMathlib/HermitianMat/Proj.lean:206:  --TODO: Should do a `HermitianMat.cfc_pow`.
./QuantumInfo/ForMathlib/HermitianMat/Proj.lean:220:  --TODO: Should do a `HermitianMat.cfc_comp_neg`?
./QuantumInfo/ForMathlib/HermitianMat/Proj.lean:228:  --TODO: Should do a `HermitianMat.cfc_comp_neg`?
./QuantumInfo/ForMathlib/HermitianMat/Proj.lean:246:  --TODO better API.
./QuantumInfo/ForMathlib/HermitianMat/Proj.lean:385:--TODO: When we upgrade `cfc_continuous` from 𝕜 to ℂ, we upgrade these too.
./QuantumInfo/ForMathlib/HermitianMat/Proj.lean:476:    rw [← zero_smul ℝ 1, ← cfc_const A, negPart_eq_cfc_ite] at h --TODO cfc_zero
./QuantumInfo/ForMathlib/HermitianMat/CfcOrder.lean:48:/- TODO: Write a version of this that holds more broadly for some sets. Esp closed intervals of reals,
./QuantumInfo/ForMathlib/HermitianMat/CfcOrder.lean:67:/-- TODO: See above -/
./QuantumInfo/ForMathlib/HermitianMat/CfcOrder.lean:91:  · simpa using Matrix.PosDef.add_posSemidef hA hAB₂ --ew. abuse. TODO Cleanup
./QuantumInfo/ForMathlib/HermitianMat/CfcOrder.lean:118:  --TODO Cleanup
./QuantumInfo/ForMathlib/HermitianMat/CfcOrder.lean:176:  --TODO cleanup
./Particles/StandardModel/Basic.lean:15:TODO "6V2FP" "Redefine the gauge group as a quotient of SU(3) x SU(2) x U(1) by a subgroup of ℤ₆."
./QuantumInfo/ForMathlib/HermitianMat/CFC.lean:301:--TODO: Generalize this to real matrices (really, RCLike) too. The theorem below
./QuantumInfo/ForMathlib/HermitianMat/CFC.lean:316:--   · --This whole block should just be `positivity`. TODO fix.
./QuantumInfo/ForMathlib/HermitianMat/CFC.lean:349:  --TODO Cleanup. Surely SURELY this is already in Mathlib? (Esp. as an Iff)
./QuantumInfo/ForMathlib/HermitianMat/CFC.lean:643:  --TODO Cleanup
./QuantumInfo/ForMathlib/HermitianMat/Basic.lean:164:--TODO: Would be good to figure out the general (not just RCLike) version of this.
./QuantumInfo/ForMathlib/HermitianMat/Order.lean:65:  --TODO Cleanup
./QuantumInfo/ForMathlib/HermitianMat/Order.lean:98:--Without these shortcut instances, `gcongr` fails to close certain goals...? Why? TODO
./QuantumInfo/ForMathlib/HermitianMat/Order.lean:184:  --TODO Cleanup
./QuantumInfo/ForMathlib/HermitianMat/Order.lean:209:  --TODO Cleanup
./QuantumInfo/ForMathlib/HermitianMat/Order.lean:234:  --TODO Cleanup
./QuantumInfo/ForMathlib/HermitianMat/Order.lean:259:  --TODO Cleanup
./QuantumInfo/ForMathlib/HermitianMat/Inner.lean:208:--TODO cleanup
./QuantumInfo/ForMathlib/HermitianMat/Inner.lean:458:--TODO: The PosDef matrices are open *within* the HermitianMat space (not in the ambient space of matrices.)
./QuantumInfo/ForMathlib/HermitianMat/Jordan.lean:133:--TODO: Upgrade this to NonAssocCommRing, see #28604 in Mathlib
./Particles/StandardModel/HiggsBoson/Basic.lean:406:TODO "6V2IS" "Make `HiggsBundle` an associated bundle."
./Particles/StandardModel/HiggsBoson/Basic.lean:741:TODO "6V2MV" "Define the global gauge action on HiggsField."
./Particles/StandardModel/HiggsBoson/Basic.lean:742:TODO "6V2M3" "Prove `⟪φ1, φ2⟫_H` invariant under the global gauge action. (norm_map_of_mem_unitary)"
./Particles/StandardModel/HiggsBoson/Basic.lean:743:TODO "6V2NA" "Prove invariance of potential under global gauge action."
./QuantumInfo/Finite/ResourceTheory/FreeState.lean:255:    --This is TERRIBLE. There has to be a better way. TODO Cleanup
./QuantumInfo/Finite/ResourceTheory/FreeState.lean:424:  · simp --should be `finiteness`, TODO debug
./Mathematics/Trigonometry/Tanh.lean:18:## TODO
./Particles/BeyondTheStandardModel/RHN/AnomalyCancellation/Ordinary/DimSevenPlane.lean:140:TODO "7SQUT" "Remove the definitions of elements `(SM 3).Charges` B₀, B₁ etc, here are
./SpaceAndTime/Space/LengthUnit.lean:198:TODO "ITXJV" "For each unit of charge give the reference the literature where it's definition
./Electromagnetism/Dynamics/KineticTerm.lean:21:In this implementation we have set `μ₀ = 1`. It is a TODO to introduce this constant.
./Electromagnetism/Dynamics/Lagrangian.lean:21:In this implementation we set `μ₀ = 1`. It is a TODO to introduce this constant.
./Relativity/Tensors/Color/Basic.lean:9:import Meta.TODO.Basic
./Relativity/Tensors/Basic.lean:619:TODO "6VZ3C" "Prove that if `σ` satisfies `PermCond c c1 σ` then `PermCond.inv σ h`
./Relativity/Tensors/Evaluation.lean:129:TODO "6VZ6G" "Add lemmas related to the interaction of evalT and permT, prodT and contrT."
./Relativity/Tensors/Contraction/Pure.lean:580:TODO "63B7X" "Prove lemmas relating to the commutation rules of `dropPair` and `prodP`."
./QFT/PerturbationTheory/WickAlgebra/Basic.lean:277:TODO "7ERJ3" "The lemma `bosonicProjF_mem_ideal` has a proof which is really long.
./QFT/Anomalies.lean:101:    TODO: Real statement: lim_{M→∞} Tr(γ₅ e^{-D²/M²}) = (1/16π²) F_μν F̃^μν. -/
./QFT/Anomalies.lean:125:    TODO: Real statement: the chiral anomaly is one-loop exact. -/
./QFT/OsterwalderSchrader.lean:90:    TODO: Real statement: ∃ W : WightmanQFT d, W's Wightman functions Wick-rotate to osData.schwinger. -/
./QFT/OsterwalderSchrader.lean:103:    TODO: Real statement: os_positivity → positive-definite inner product on reconstructed H. -/
./QFT/OsterwalderSchrader.lean:110:    TODO: Real statement: Sₙ = ∫ φ(x₁)⋯φ(xₙ) dμ(φ) → OS positivity. -/
./Relativity/LorentzGroup/Boosts/Generalized.lean:466:the TODO item `FXQ45` is completed.
./Relativity/LorentzGroup/Basic.lean:7:import Meta.TODO.Basic
./Relativity/LorentzGroup/Basic.lean:21:TODO "6VZHM" "Define the Lie group structure on the Lorentz group."
./Relativity/LorentzAlgebra/Basis.lean:7:import Meta.TODO.Basic
./Relativity/LorentzAlgebra/Basis.lean:40:TODO "6VZKA" can be completed by proving linear independence and spanning of these
./Relativity/LorentzAlgebra/Basis.lean:145:## TODO: Properties of Generators
./Relativity/LorentzAlgebra/Basis.lean:151:TODO "BOOST_SYM" "Prove that boost generators are symmetric: \
./Relativity/LorentzAlgebra/Basis.lean:154:TODO "BOOST_TRACE" "Prove that boost generators are traceless: \
./Relativity/LorentzAlgebra/Basis.lean:157:TODO "ROT_ANTISYM" "Prove that rotation generators are antisymmetric: \
./Relativity/LorentzAlgebra/Basis.lean:160:TODO "ROT_TRACE" "Prove that rotation generators are traceless: \
./Relativity/LorentzGroup/Restricted/Basic.lean:11:This file is currently a stub.
./Relativity/LorentzGroup/Restricted/Basic.lean:15:TODO "6VZNP" "Prove that every member of the restricted Lorentz group is
./Relativity/CliffordAlgebra.lean:9:import Meta.TODO.Basic
./Relativity/CliffordAlgebra.lean:28:## TODO
./Relativity/CliffordAlgebra.lean:34:TODO "6VZF2" "Prove injectivity of ofCliffordAlgebra and construct the full isomorphism."
./QFT/AnomalyCancellation/PureU1/BasisLinear.lean:78:TODO "6VZO6" "The definition of `coordinateMap` here may be improved by replacing
./Relativity/LorentzGroup/Orthochronous/Basic.lean:16:TODO "6VZLO" "Prove topological properties of the Orthochronous Lorentz Group."
./QFT/AnomalyCancellation/Basic.lean:69:- J. Open TODO items
./QFT/AnomalyCancellation/Basic.lean:109:TODO "NCRC5" "Replace `ACCSystemChargesMk` with `⟨n⟩` notation everywhere. "
./QFT/AnomalyCancellation/Basic.lean:581:## J. Open TODO items
./QFT/AnomalyCancellation/Basic.lean:583:We give some open TODO items for future work.
./QFT/AnomalyCancellation/Basic.lean:595:TODO "6VZMW" "Anomaly cancellation conditions can be derived formally from the gauge group
./QFT/AnomalyCancellation/Basic.lean:599:TODO "6VZM3" "Anomaly cancellation conditions can be defined using algebraic varieties.
./QFT/HaagsTheorem.lean:39:    **Status**: `is_free` field is typed `True` (stub); needs a real Wick factorization condition. -/
./QFT/ConnesKreimerHopf.lean:115:    TODO: Real statement: ∃ φ₋ φ₊ : CKCharacter H A, φ = φ₋⁻¹ ⋆ φ₊. -/
./QFT/ConnesKreimerHopf.lean:129:    TODO: Real statement: Birkhoff decomposition in C((ε)) reproduces MS-bar. -/
./QFT/ConnesKreimerHopf.lean:144:    TODO: Real statement: Connes-Kreimer antipode = BPHZ R-operation. -/
./QFT/YangMills.lean:77:    TODO: Real statement: fieldStrength(gaugeTransformConnection A θ) = F + [θ, F] infinitesimally. -/
./QFT/YangMills.lean:114:    TODO: Real statement: D_μ F_νρ + D_ν F_ρμ + D_ρ F_μν = 0. -/
./QFT/PerturbationTheory/FieldOpFreeAlgebra/NormalOrder.lean:399:TODO "6V2JJ" "Split the following two lemmas up into smaller parts."
./QFT/LatticeFermions.lean:29:  True -- Locality condition placeholder
./QFT/LatticeFermions.lean:38:  0 -- Counts zeros of det D(p) in BZ placeholder
./QFT/PerturbationTheory/WickContraction/Perm.lean:16:## TODO
./QFT/AnomalyCancellation/PureU1/Basic.lean:30:TODO "K3HYF" "The implementation of pure U(1) anomaly cancellation conditions is done
./QuantumMechanics/ModularTheory/KMS/Modular.lean:83:TODO: Define properly using weak topology or preduals.
./QuantumMechanics/ModularTheory/KMS/Modular.lean:105:TODO: Define properly using predual.
./SpaceAndTime/Space/Derivatives/Curl.lean:528:   these had placeholder types (sorry/sorryAx in the statement) -/
./SpaceAndTime/Space/Derivatives/Curl.lean:536:/- distCurl_apply removed: had placeholder type (sorry in the statement) -/
./QFT/SpinStatistics.lean:125:    TODO: Real statement: HasWrongStatistics W → all Wightman functions vanish. -/
./QFT/SpinStatistics.lean:133:    TODO: Real statement: ¬HasWrongStatistics W when hNontrivial holds. -/
./QFT/SpinStatistics.lean:140:    TODO: Real statement: [φ_j(x), φ_j(y)] = 0 when (x-y) spacelike. -/
./QFT/SpinStatistics.lean:148:    TODO: Real statement: {φ_j(x), φ_j(y)} = 0 when (x-y) spacelike. -/
./QFT/SpinStatistics.lean:157:    TODO: Real statement: two identical fermions cannot occupy the same state. -/
./QFT/SpinStatistics.lean:167:    TODO: Real statement: multiple bosons can occupy the same state. -/
```

### E1. TODO/Stub Markers by File (descending, top 200)
```text
  16 ./QuantumInfo/Finite/ResourceTheory/SteinsLemma.lean
  14 ./QuantumInfo/Finite/MState.lean
  12 ./ClassicalMechanics/DampedHarmonicOscillator/Basic.lean
   9 ./QuantumInfo/Finite/Entropy/Relative.lean
   8 ./QuantumInfo/ForMathlib/HermitianMat/Proj.lean
   7 ./Relativity/LorentzAlgebra/Basis.lean
   7 ./QuantumInfo/Finite/CPTPMap/CPTP.lean
   6 ./SpaceAndTime/Space/Basic.lean
   6 ./QuantumInfo/ForMathlib/HermitianMat/Order.lean
   6 ./QFT/SpinStatistics.lean
   6 ./QFT/AnomalyCancellation/Basic.lean
   5 ./Units/Minerals.lean
   5 ./QuantumInfo/ForMathlib/Minimax.lean
   5 ./QuantumInfo/ForMathlib/HermitianMat/CfcOrder.lean
   5 ./QuantumInfo/Finite/Pinching.lean
   5 ./QuantumInfo/Finite/CPTPMap/Unbundled.lean
   5 ./QuantumInfo/Finite/CPTPMap/Dual.lean
   5 ./Mathematics/FunctionalAnalysis/Distributions.lean
   4 ./QuantumInfo/ForMathlib/Matrix.lean
   4 ./QuantumInfo/ForMathlib/HermitianMat/CFC.lean
   4 ./QuantumInfo/Finite/ResourceTheory/HypothesisTesting.lean
   4 ./QuantumInfo/Finite/Entropy/VonNeumann.lean
   4 ./Particles/StandardModel/HiggsBoson/Basic.lean
   4 ./ClassicalMechanics/HarmonicOscillator/Solution.lean
   3 ./Relativity/CliffordAlgebra.lean
   3 ./QuantumInfo/Finite/POVM.lean
   3 ./QFT/OsterwalderSchrader.lean
   3 ./QFT/ConnesKreimerHopf.lean
   3 ./ClassicalMechanics/WaveEquation/HarmonicWave.lean
   2 ./Units/Basic.lean
   2 ./StringTheory/FTheory/SU5/Charges/OfRationalSection.lean
   2 ./SpaceAndTime/Space/Derivatives/Curl.lean
   2 ./Relativity/Special/TwinParadox/Basic.lean
   2 ./Relativity/LorentzGroup/Restricted/Basic.lean
   2 ./Relativity/LorentzGroup/Basic.lean
   2 ./QuantumMechanics/SpectralTheory/BochnerRoute/PositiveDefinite.lean
   2 ./QuantumMechanics/OneDimension/ReflectionlessPotential/Basic.lean
   2 ./QuantumMechanics/ModularTheory/SubsystemEmergence.lean
   2 ./QuantumMechanics/ModularTheory/KMS/Modular.lean
   2 ./QuantumMechanics/FiniteTarget/Basic.lean
   2 ./QuantumInfo/ForMathlib/SionMinimax.lean
   2 ./QuantumInfo/ForMathlib/Isometry.lean
   2 ./QuantumInfo/ForMathlib/HermitianMat/Inner.lean
   2 ./QuantumInfo/Finite/ResourceTheory/FreeState.lean
   2 ./QuantumInfo/Finite/Entanglement.lean
   2 ./QuantumInfo/Finite/Capacity.lean
   2 ./QuantumInfo/Finite/AxiomatizedEntropy/Defs.lean
   2 ./QFT/YangMills.lean
   2 ./QFT/LatticeFermions.lean
   2 ./QFT/Anomalies.lean
   2 ./Particles/SuperSymmetry/SU5/ChargeSpectrum/PhenoClosed.lean
   2 ./Mechanics/Poincare.lean
   2 ./Mathematics/LinearMaps.lean
   2 ./Mathematics/KroneckerDelta.lean
   2 ./Mathematics/Distribution/Basic.lean
   2 ./Electromagnetism/Current/CircularCoil.lean
   2 ./ClassicalMechanics/Vibrations/LinearTriatomic.lean
   2 ./ClassicalMechanics/Scattering/RigidSphere.lean
   1 ./Units/WithDim/Basic.lean
   1 ./Units/Examples.lean
   1 ./Thermodynamics/Basic.lean
   1 ./SpaceAndTime/SpaceTime/Basic.lean
   1 ./SpaceAndTime/Space/LengthUnit.lean
   1 ./SpaceAndTime/Space/DistOfFunction.lean
   1 ./Relativity/Tensors/RealTensor/Derivative.lean
   1 ./Relativity/Tensors/Evaluation.lean
   1 ./Relativity/Tensors/Contraction/Pure.lean
   1 ./Relativity/Tensors/Color/Basic.lean
   1 ./Relativity/Tensors/Basic.lean
   1 ./Relativity/LorentzGroup/Orthochronous/Basic.lean
   1 ./Relativity/LorentzGroup/Boosts/Generalized.lean
   1 ./QuantumMechanics/SpectralTheory/RelThermo.lean
   1 ./QuantumMechanics/OneDimension/HarmonicOscillator/Basic.lean
   1 ./QuantumMechanics/ModularTheory/KMS/PeriodicStrip.lean
   1 ./QuantumMechanics/FiniteTarget/HilbertSpace.lean
   1 ./QuantumMechanics/DDimensions/Operators/Position.lean
   1 ./QuantumInfo/ForMathlib/HermitianMat/Jordan.lean
   1 ./QuantumInfo/ForMathlib/HermitianMat/Basic.lean
   1 ./QuantumInfo/ForMathlib/ContinuousSup.lean
   1 ./QuantumInfo/Finite/ResourceTheory/ResourceTheory.lean
   1 ./QuantumInfo/Finite/Entropy/SSA.lean
   1 ./QuantumInfo/Finite/Entropy/Holevo.lean
   1 ./QuantumInfo/Finite/Distance/Fidelity.lean
   1 ./QuantumInfo/Finite/CPTPMap/MatrixMap.lean
   1 ./QuantumInfo/Finite/CPTPMap/Bundled.lean
   1 ./QuantumInfo/Finite/Braket.lean
   1 ./QFT/PerturbationTheory/WickContraction/Perm.lean
   1 ./QFT/PerturbationTheory/WickAlgebra/Basic.lean
   1 ./QFT/PerturbationTheory/FieldOpFreeAlgebra/NormalOrder.lean
   1 ./QFT/HaagsTheorem.lean
   1 ./QFT/AnomalyCancellation/PureU1/BasisLinear.lean
   1 ./QFT/AnomalyCancellation/PureU1/Basic.lean
   1 ./Particles/StandardModel/Basic.lean
   1 ./Particles/BeyondTheStandardModel/RHN/AnomalyCancellation/Ordinary/DimSevenPlane.lean
   1 ./Optics/Basic.lean
   1 ./Mathematics/Trigonometry/Tanh.lean
   1 ./Mathematics.lean
   1 ./Electromagnetism/Dynamics/Lagrangian.lean
   1 ./Electromagnetism/Dynamics/KineticTerm.lean
   1 ./Electromagnetism/Charge/ChargeUnit.lean
   1 ./Electromagnetism/Basic.lean
   1 ./Cosmology/Basic.lean
   1 ./CondensedMatter/Basic.lean
   1 ./ClassicalMechanics/RigidBody/Basic.lean
   1 ./ClassicalMechanics/HarmonicOscillator/Basic.lean
   1 ./ClassicalMechanics/Basic.lean
   1 ./ClassicalInfo/Prob.lean
   1 ./ClassicalInfo/Entropy.lean
```
