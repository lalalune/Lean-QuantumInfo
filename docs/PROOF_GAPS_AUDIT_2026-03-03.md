# Proof Gaps Audit

Generated: 2026-03-03 14:26:02Z

Scope: QuantumInfo, ClassicalInfo, StatMech

Pattern: code-like lines matching sorry|admit|omitted_proof (excluding lines starting with --).

## Summary

- Total unresolved markers: 86
- Files with unresolved markers: 22

## Top Files

  14 QuantumInfo/Finite/Entropy/Relative.lean
  12 QuantumInfo/Finite/AxiomatizedEntropy/Defs.lean
   7 QuantumInfo/ForMathlib/MatrixNorm/TraceNorm.lean
   7 QuantumInfo/Finite/Capacity.lean
   5 QuantumInfo/Finite/AxiomatizedEntropy/Renyi.lean
   4 QuantumInfo/ForMathlib/Majorization.lean
   4 QuantumInfo/ForMathlib/ALT.lean
   4 QuantumInfo/Finite/Distance/Fidelity.lean
   4 QuantumInfo/Finite/CPTPMap/CPTP.lean
   4 ClassicalInfo/Capacity.lean
   3 StatMech/ThermoQuantities.lean
   3 QuantumInfo/ForMathlib/Matrix.lean
   2 QuantumInfo/Regularized.lean
   2 QuantumInfo/ForMathlib/Misc.lean
   2 QuantumInfo/Finite/Entropy/Klein.lean
   2 QuantumInfo/Finite/CPTPMap/MatrixMap.lean
   2 QuantumInfo/Finite/CPTPMap/Dual.lean
   1 QuantumInfo/ForMathlib/Unitary.lean
   1 QuantumInfo/ForMathlib/CauchyBinet.lean
   1 QuantumInfo/Finite/Entropy/SSA.lean
   1 QuantumInfo/Finite/Ensemble.lean
   1 QuantumInfo/Finite/CPTPMap/Unbundled.lean

## Raw List

ClassicalInfo/Capacity.lean:51:    sorry
ClassicalInfo/Capacity.lean:53:    sorry
ClassicalInfo/Capacity.lean:54:  enc_maps_length := sorry
ClassicalInfo/Capacity.lean:55:  dec_maps_length := sorry
QuantumInfo/Regularized.lean:175:  have := InfRegularized.anti_tendsto (fn := fn) (hl := hl) (hu := hu) (sorry)
QuantumInfo/Regularized.lean:176:  sorry
QuantumInfo/Finite/Capacity.lean:126:  · have : Nonempty d₁ := by sorry--having a CPTPMap should be enough to conclude in- and out-spaces are nonempty
QuantumInfo/Finite/Capacity.lean:127:    have : Nonempty d₂ := by sorry
QuantumInfo/Finite/Capacity.lean:129:    sorry--exact Unique.eq_default _
QuantumInfo/Finite/Capacity.lean:133:    sorry--apply εApproximates_monotone (εApproximates_self default) hε.le
QuantumInfo/Finite/Capacity.lean:159:  sorry
QuantumInfo/Finite/Capacity.lean:218:  sorry
QuantumInfo/Finite/Capacity.lean:223:  sorry
StatMech/ThermoQuantities.lean:85:theorem isn't in mathlib yet. So this is a sorry for now
StatMech/ThermoQuantities.lean:89:  sorry
StatMech/ThermoQuantities.lean:153:  · sorry
QuantumInfo/ForMathlib/ALT.lean:45:  sorry
QuantumInfo/ForMathlib/ALT.lean:55:  sorry
QuantumInfo/ForMathlib/ALT.lean:69:  sorry
QuantumInfo/ForMathlib/ALT.lean:78:  sorry
QuantumInfo/Finite/AxiomatizedEntropy/Defs.lean:143:  sorry
QuantumInfo/Finite/AxiomatizedEntropy/Defs.lean:159:    sorry --missing simp lemma
QuantumInfo/Finite/AxiomatizedEntropy/Defs.lean:169:  DPI := sorry
QuantumInfo/Finite/AxiomatizedEntropy/Defs.lean:170:  of_kron := sorry
QuantumInfo/Finite/AxiomatizedEntropy/Defs.lean:171:  normalized := sorry
QuantumInfo/Finite/AxiomatizedEntropy/Defs.lean:177:    sorry--TODO
QuantumInfo/Finite/AxiomatizedEntropy/Defs.lean:182:  sorry --Tomamichel, https://www.marcotom.info/files/entropy-masterclass2022.pdf, (1.28)
QuantumInfo/Finite/AxiomatizedEntropy/Defs.lean:205:    replace hv : σ.toMat.mulVec v = 0 := sorry --why is this not defeq??
QuantumInfo/Finite/AxiomatizedEntropy/Defs.lean:211:    sorry
QuantumInfo/Finite/AxiomatizedEntropy/Defs.lean:215:    sorry --log ("min nonzero eigenvalue of σ" / "max eigenvalue of ρ") should work
QuantumInfo/Finite/AxiomatizedEntropy/Defs.lean:224:    sorry
QuantumInfo/Finite/AxiomatizedEntropy/Defs.lean:230:  sorry --Tomamichel, https://www.marcotom.info/files/entropy-masterclass2022.pdf, (1.28)
QuantumInfo/Finite/AxiomatizedEntropy/Renyi.lean:19:    sorry⟩
QuantumInfo/Finite/AxiomatizedEntropy/Renyi.lean:26:  DPI := sorry
QuantumInfo/Finite/AxiomatizedEntropy/Renyi.lean:27:  of_kron := sorry
QuantumInfo/Finite/AxiomatizedEntropy/Renyi.lean:28:  normalized := sorry
QuantumInfo/Finite/AxiomatizedEntropy/Renyi.lean:31:  nontrivial := sorry
QuantumInfo/ForMathlib/CauchyBinet.lean:84:  sorry
QuantumInfo/ForMathlib/Misc.lean:20:  sorry
QuantumInfo/ForMathlib/Misc.lean:24:    ⨆ i, (⟨f i, h i⟩ : ↑s) = ⟨⨆ i, f i, by sorry⟩ := by
QuantumInfo/Finite/CPTPMap/CPTP.lean:361:  TP := sorry
QuantumInfo/Finite/CPTPMap/CPTP.lean:367:    piProd Λi = sorry ∘ₘ ((Λi 1) ∘ₘ sorry) :=
QuantumInfo/Finite/CPTPMap/CPTP.lean:368:  sorry --TODO: permutations
QuantumInfo/Finite/CPTPMap/CPTP.lean:455:  sorry
QuantumInfo/Finite/Entropy/Relative.lean:361:  sorry
QuantumInfo/Finite/Entropy/Relative.lean:365:  sorry
QuantumInfo/Finite/Entropy/Relative.lean:383:  sorry
QuantumInfo/Finite/Entropy/Relative.lean:812:  sorry
QuantumInfo/Finite/Entropy/Relative.lean:926:          sorry
QuantumInfo/Finite/Entropy/Relative.lean:940:  sorry
QuantumInfo/Finite/Entropy/Relative.lean:948:  sorry
QuantumInfo/Finite/Entropy/Relative.lean:1024:  sorry
QuantumInfo/Finite/Entropy/Relative.lean:1030:  sorry
QuantumInfo/Finite/Entropy/Relative.lean:1041:    sorry
QuantumInfo/Finite/Entropy/Relative.lean:1063:  sorry
QuantumInfo/Finite/Entropy/Relative.lean:1077:  sorry
QuantumInfo/Finite/Entropy/Relative.lean:1082:  sorry
QuantumInfo/Finite/Entropy/Relative.lean:1088:  sorry
QuantumInfo/ForMathlib/Unitary.lean:72:  sorry --use conj_unitary_eigenspace_equiv
QuantumInfo/Finite/CPTPMap/MatrixMap.lean:125:  sorry
QuantumInfo/Finite/CPTPMap/MatrixMap.lean:364:  Finsupp.basisSingleOne.map sorry
QuantumInfo/ForMathlib/MatrixNorm/TraceNorm.lean:41:  sorry --Diagonalize A
QuantumInfo/ForMathlib/MatrixNorm/TraceNorm.lean:55:      sorry --sum of nonnegative values to zero
QuantumInfo/ForMathlib/MatrixNorm/TraceNorm.lean:57:      sorry --all eigenvalues are zero iff matrix is zero
QuantumInfo/ForMathlib/MatrixNorm/TraceNorm.lean:59:      sorry --sqrt is zero iff matrix is zero
QuantumInfo/ForMathlib/MatrixNorm/TraceNorm.lean:61:      sorry --conj_mul_self is zero iff A is zero
QuantumInfo/ForMathlib/MatrixNorm/TraceNorm.lean:82:  · sorry --need `CFC.sqrt_smul` or similar
QuantumInfo/ForMathlib/MatrixNorm/TraceNorm.lean:86:  sorry
QuantumInfo/ForMathlib/Matrix.lean:396:  sorry
QuantumInfo/ForMathlib/Matrix.lean:400:  sorry
QuantumInfo/ForMathlib/Matrix.lean:1510:  sorry
QuantumInfo/Finite/Ensemble.lean:118:  sorry
QuantumInfo/Finite/Entropy/SSA.lean:33:  sorry
QuantumInfo/Finite/CPTPMap/Unbundled.lean:747:  sorry
QuantumInfo/Finite/Distance/Fidelity.lean:34:  sorry --submultiplicativity of trace and sqrt
QuantumInfo/Finite/Distance/Fidelity.lean:71:  ⟨sorry,
QuantumInfo/Finite/Distance/Fidelity.lean:77:  sorry --break into sqrts
QuantumInfo/Finite/Distance/Fidelity.lean:81:  sorry
QuantumInfo/Finite/CPTPMap/Dual.lean:42:  sorry
QuantumInfo/Finite/CPTPMap/Dual.lean:49:  sorry
QuantumInfo/ForMathlib/Majorization.lean:249:      (compound_isHermitian _ (isHermitian_mul_mul_self A B hA.1 hB.1)) := by sorry
QuantumInfo/ForMathlib/Majorization.lean:251:      (compound_isHermitian _ (isHermitian_mul_self A hA.1)) := by sorry
QuantumInfo/ForMathlib/Majorization.lean:253:      (compound_isHermitian B hB.1) := by sorry
QuantumInfo/ForMathlib/Majorization.lean:272:  sorry
QuantumInfo/Finite/Entropy/Klein.lean:89:  sorry
QuantumInfo/Finite/Entropy/Klein.lean:94:  sorry
