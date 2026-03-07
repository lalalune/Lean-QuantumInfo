/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.Finite.Entropy.VonNeumann

/-!
Quantities of quantum _relative entropy_, namely the (standard) quantum relative
entropy, and generalizations such as sandwiched Rényi relative entropy.
-/

noncomputable section

variable {d d₁ d₂ d₃ : Type*}
variable [Fintype d] [Fintype d₁] [Fintype d₂] [Fintype d₃]
variable [DecidableEq d] [DecidableEq d₁] [DecidableEq d₂] [DecidableEq d₃]
variable {dA dB dC dA₁ dA₂ : Type*}
variable [Fintype dA] [Fintype dB] [Fintype dC] [Fintype dA₁] [Fintype dA₂]
variable [DecidableEq dA] [DecidableEq dB] [DecidableEq dC] [DecidableEq dA₁] [DecidableEq dA₂]
variable {𝕜 : Type*} [RCLike 𝕜]
variable {α : ℝ}


open scoped InnerProductSpace RealInnerProductSpace

/-- Strong subadditivity on a tripartite system -/
theorem Sᵥₙ_strong_subadditivity (ρ₁₂₃ : MState (d₁ × d₂ × d₃)) :
    let ρ₁₂ := ρ₁₂₃.assoc'.traceRight;
    let ρ₂₃ := ρ₁₂₃.traceLeft;
    let ρ₂ := ρ₁₂₃.traceLeft.traceRight;
    Sᵥₙ ρ₁₂₃ + Sᵥₙ ρ₂ ≤ Sᵥₙ ρ₁₂ + Sᵥₙ ρ₂₃ := by
  sorry

/-- "Ordinary" subadditivity of von Neumann entropy -/
theorem Sᵥₙ_subadditivity (ρ : MState (d₁ × d₂)) :
    Sᵥₙ ρ ≤ Sᵥₙ ρ.traceRight + Sᵥₙ ρ.traceLeft := by
  have := Sᵥₙ_strong_subadditivity (ρ.relabel (d₂ := d₁ × Unit × d₂)
    ⟨fun x ↦ (x.1, x.2.2), fun x ↦ (x.1, ⟨(), x.2⟩), fun x ↦ by simp, fun x ↦ by simp⟩)
  simp [Sᵥₙ_relabel] at this
  convert this using 1
  congr 1
  · convert Sᵥₙ_relabel _ (Equiv.prodPUnit _).symm
    exact rfl
  · convert Sᵥₙ_relabel _ (Equiv.punitProd _).symm
    exact rfl

/-- Triangle inequality for pure tripartite states: S(A) ≤ S(B) + S(C). -/
theorem Sᵥₙ_pure_tripartite_triangle (ψ : Ket ((d₁ × d₂) × d₃)) :
    Sᵥₙ (MState.pure ψ).traceRight.traceRight ≤
    Sᵥₙ (MState.pure ψ).traceRight.traceLeft + Sᵥₙ (MState.pure ψ).traceLeft := by
  have h_subadd := Sᵥₙ_subadditivity (MState.pure ψ).assoc.traceLeft
  obtain ⟨ψ', hψ'⟩ : ∃ ψ', (MState.pure ψ).assoc = _ :=
    MState.relabel_pure_exists ψ _
  grind [Sᵥₙ_of_partial_eq, MState.traceLeft_left_assoc,
    MState.traceLeft_right_assoc, MState.traceRight_assoc]

/-- One direction of the Araki-Lieb triangle inequality: S(A) ≤ S(B) + S(AB). -/
theorem Sᵥₙ_triangle_ineq_one_way (ρ : MState (d₁ × d₂)) : Sᵥₙ ρ.traceRight ≤ Sᵥₙ ρ.traceLeft + Sᵥₙ ρ := by
  have := Sᵥₙ_pure_tripartite_triangle ρ.purify
  have := Sᵥₙ_of_partial_eq ρ.purify
  aesop

/-- Araki-Lieb triangle inequality on von Neumann entropy -/
theorem Sᵥₙ_triangle_subaddivity (ρ : MState (d₁ × d₂)) :
    abs (Sᵥₙ ρ.traceRight - Sᵥₙ ρ.traceLeft) ≤ Sᵥₙ ρ := by
  rw [abs_sub_le_iff]
  constructor
  · have := Sᵥₙ_triangle_ineq_one_way ρ
    grind only
  · have := Sᵥₙ_triangle_ineq_one_way ρ.SWAP
    grind only [Sᵥₙ_triangle_ineq_one_way, Sᵥₙ_of_SWAP_eq, MState.traceRight_SWAP,
      MState.traceLeft_SWAP]

section weak_monotonicity
--TODO Cleanup

variable (ρ : MState (dA × dB × dC))

/-
Permutations of the purification system for use in the proof of weak monotonicity.
-/
private def perm_B_ACR : (dA × dB × dC) × (dA × dB × dC) ≃ dB × (dA × dC × (dA × dB × dC)) where
  toFun x := let ((a,b,c), r) := x; (b, (a,c,r))
  invFun x := let (b, (a,c,r)) := x; ((a,b,c), r)
  left_inv := by intro x; simp
  right_inv := by intro x; simp

private def perm_C_ABR : (dA × dB × dC) × (dA × dB × dC) ≃ dC × (dA × dB × (dA × dB × dC)) where
  toFun x := let ((a,b,c), r) := x; (c, (a,b,r))
  invFun x := let (c, (a,b,r)) := x; ((a,b,c), r)
  left_inv := by intro x; simp
  right_inv := by intro x; simp

private def perm_AC_BR : (dA × dB × dC) × (dA × dB × dC) ≃ (dA × dC) × (dB × (dA × dB × dC)) where
  toFun x := let ((a,b,c), r) := x; ((a,c), (b,r))
  invFun x := let ((a,c), (b,r)) := x; ((a,b,c), r)
  left_inv := by intro x; simp
  right_inv := by intro x; simp

private def perm_AB_CR : (dA × dB × dC) × (dA × dB × dC) ≃ (dA × dB) × (dC × (dA × dB × dC)) where
  toFun x := let ((a,b,c), r) := x; ((a,b), (c,r))
  invFun x := let ((a,b), (c,r)) := x; ((a,b,c), r)
  left_inv := by intro x; simp
  right_inv := by intro x; simp

/-- The state on systems A, B, and R, obtained by purifying ρ and tracing out C. -/
private def ρABR (ρ : MState (dA × dB × dC)) : MState (dA × dB × (dA × dB × dC)) :=
  ((MState.pure ρ.purify).relabel perm_C_ABR.symm).traceLeft

private lemma traceRight_relabel_perm_C_ABR
    (ρ : MState ((dA × dB × dC) × (dA × dB × dC))) :
    (ρ.relabel perm_C_ABR.symm).traceRight = ρ.traceRight.traceLeft.traceLeft := by
  ext i j;
  simp [ HermitianMat.traceRight, HermitianMat.traceLeft, perm_C_ABR ];
  simp [ Matrix.traceRight, Matrix.traceLeft ];
  simp [ Fintype.sum_prod_type ];
  exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ac_rfl )

private lemma trace_relabel_purify_eq_rho_C :
    ((MState.pure ρ.purify).relabel perm_C_ABR.symm).traceRight = ρ.traceLeft.traceLeft := by
  have := MState.purify_spec ρ;
  convert traceRight_relabel_perm_C_ABR _ using 1;
  rw [ this ]

private theorem S_B_eq_S_ACR (ρ : MState (dA × dB × dC)) :
    Sᵥₙ ((MState.pure ρ.purify).relabel perm_B_ACR.symm).traceRight = Sᵥₙ ρ.traceLeft.traceRight := by
  have := @MState.purify_spec;
  convert congr_arg Sᵥₙ ( this ρ |> congr_arg ( fun ρ => ρ.traceLeft.traceRight ) ) using 1;
  convert Sᵥₙ_relabel _ _ using 2;
  swap;
  exact Equiv.refl dB;
  ext; simp [ MState.traceRight, MState.traceLeft ] ;
  simp [HermitianMat.traceLeft, HermitianMat.traceRight ];
  simp [ Matrix.traceRight, Matrix.traceLeft ];
  simp [ Fintype.sum_prod_type ];
  exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ac_rfl )

/-
The entropy of the B marginal of the purification is equal to the entropy of the B marginal of the original state.
-/
private lemma S_B_eq_S_B :
    Sᵥₙ (ρABR ρ).traceLeft.traceRight = Sᵥₙ ρ.assoc'.traceRight.traceLeft := by
  convert S_B_eq_S_ACR ρ using 1;
  · congr 1
    ext1
    unfold ρABR;
    ext
    simp [MState.traceLeft, MState.traceRight]
    unfold perm_C_ABR perm_B_ACR
    simp [HermitianMat.traceLeft, HermitianMat.traceRight]
    simp [Matrix.traceLeft, Matrix.traceRight]
    simp [ ← Finset.sum_product']
    exact Finset.sum_bij ( fun x _ => ( x.2.1, x.2.2, x.1 ) ) ( by aesop ) ( by aesop ) ( by aesop ) ( by aesop );
  · simp

/-
The entropy of the ABR state is equal to the entropy of C, since ABCR is pure.
-/
private theorem S_ABR_eq_S_C : Sᵥₙ (ρABR ρ) = Sᵥₙ ρ.traceLeft.traceLeft := by
  rw [ρABR, Sᵥₙ_pure_complement, trace_relabel_purify_eq_rho_C]

/-
The BR marginal of ρABR is equal to the BR marginal of the purification relabeled.
-/
private lemma traceLeft_ρABR_eq_traceLeft_relabel :
    (ρABR ρ).traceLeft = ((MState.pure ρ.purify).relabel perm_AC_BR.symm).traceLeft := by
  unfold ρABR;
  unfold MState.traceLeft;
  congr;
  ext i j
  simp [ HermitianMat.traceLeft];
  simp [ Matrix.traceLeft];
  simp [ perm_C_ABR, perm_AC_BR ];
  simp [ Fintype.sum_prod_type ]

/-
Tracing out B and R from the relabeled state is equivalent to tracing out R, then B from the original state (with appropriate permutations).
-/
private lemma traceRight_relabel_perm_AC_BR (ρ : MState ((dA × dB × dC) × (dA × dB × dC))) :
    (ρ.relabel perm_AC_BR.symm).traceRight = ρ.traceRight.SWAP.assoc.traceLeft.SWAP := by
  unfold MState.traceRight MState.SWAP MState.assoc MState.relabel
  simp [ HermitianMat.traceRight, HermitianMat.traceLeft ];
  simp [ Matrix.traceLeft, Matrix.traceRight, HermitianMat.reindex, Matrix.submatrix ];
  simp [ perm_AC_BR ];
  simp [ Fintype.sum_prod_type ]

/-
Tracing out B and R from the purification gives the marginal state on A and C.
-/
private lemma traceRight_relabel_perm_AC_BR_eq_rho_AC :
    ((MState.pure ρ.purify).relabel perm_AC_BR.symm).traceRight = ρ.SWAP.assoc.traceLeft.SWAP := by
  rw [traceRight_relabel_perm_AC_BR]
  rw [MState.purify_spec]

/-
The entropy of the BR marginal of the purification is equal to the entropy of the AC marginal of the original state.
-/
private lemma S_BR_eq_S_AC :
    Sᵥₙ (ρABR ρ).traceLeft = Sᵥₙ ρ.SWAP.assoc.traceLeft.SWAP := by
  rw [traceLeft_ρABR_eq_traceLeft_relabel]
  rw [Sᵥₙ_pure_complement, traceRight_relabel_perm_AC_BR_eq_rho_AC]

private theorem S_AB_purify_eq_S_AB_rho :
    Sᵥₙ ((MState.pure ρ.purify).relabel perm_AB_CR.symm).traceRight = Sᵥₙ ρ.assoc'.traceRight := by
  have h_trace : ((MState.pure ρ.purify).relabel perm_AB_CR.symm).traceRight = ((MState.pure ρ.purify).traceRight).assoc'.traceRight := by
    ext; simp [MState.traceRight, MState.assoc'];
    simp [HermitianMat.traceRight]
    simp [ Matrix.submatrix, Matrix.traceRight ];
    congr! 2;
    ext i j; simp [ perm_AB_CR ] ;
    exact
      Fintype.sum_prod_type fun x =>
        ρ.purify ((i.1, i.2, x.1), x.2) * (starRingEnd ℂ) (ρ.purify ((j.1, j.2, x.1), x.2));
  aesop

/-
The entropy of the AB marginal of the purification is equal to the entropy of the AB marginal of the original state.
-/
private lemma S_AB_eq_S_AB :
    Sᵥₙ (ρABR ρ).assoc'.traceRight = Sᵥₙ ρ.assoc'.traceRight := by
  have h_marginal : Sᵥₙ ((MState.pure ρ.purify).relabel perm_AB_CR.symm).traceRight = Sᵥₙ ρ.assoc'.traceRight := by
    exact S_AB_purify_eq_S_AB_rho ρ
  convert h_marginal using 2;
  convert MState.ext ?_;
  ext i j; simp [ ρABR ] ;
  simp [ MState.traceLeft, MState.relabel, MState.assoc', perm_AB_CR, perm_C_ABR ];
  simp [ MState.SWAP, MState.assoc]
  simp [ MState.pure ];
  simp [ HermitianMat.traceLeft, HermitianMat.traceRight, HermitianMat.reindex ];
  simp [ Matrix.traceLeft, Matrix.traceRight, Matrix.submatrix, Matrix.vecMulVec ];
  simp [ Fintype.sum_prod_type ];
  simp only [Finset.sum_sigma'];
  refine' Finset.sum_bij ( fun x _ => ⟨ x.snd.snd.snd, x.fst, x.snd.fst, x.snd.snd.fst ⟩ ) _ _ _ _ <;> simp
  · aesop;
  · exact fun b => ⟨ b.2.1, b.2.2.1, b.2.2.2, b.1, rfl ⟩

/-- Weak monotonicity of quantum conditional entropy: S(A|B) + S(A|C) ≥ 0. -/
theorem Sᵥₙ_weak_monotonicity :
    let ρAB := ρ.assoc'.traceRight
    let ρAC := ρ.SWAP.assoc.traceLeft.SWAP
    0 ≤ qConditionalEnt ρAB + qConditionalEnt ρAC := by
  -- Apply strong subadditivity to the state ρABR.
  have h_strong_subadditivity := Sᵥₙ_strong_subadditivity (ρABR ρ)
  -- Substitute the equalities for the entropies of the purifications.
  have _ := S_ABR_eq_S_C ρ
  have _ := S_B_eq_S_B ρ
  have _ := S_AB_eq_S_AB ρ
  have _ := S_BR_eq_S_AC ρ
  grind [qConditionalEnt, MState.traceRight_left_assoc', Sᵥₙ_of_SWAP_eq,
    MState.traceLeft_SWAP, MState.traceLeft_right_assoc, MState.traceRight_SWAP]

end weak_monotonicity

/-- Strong subadditivity, stated in terms of conditional entropies.
  Also called the data processing inequality. H(A|BC) ≤ H(A|B). -/
theorem qConditionalEnt_strong_subadditivity (ρ₁₂₃ : MState (d₁ × d₂ × d₃)) :
    qConditionalEnt ρ₁₂₃ ≤ qConditionalEnt ρ₁₂₃.assoc'.traceRight := by
  have := Sᵥₙ_strong_subadditivity ρ₁₂₃
  dsimp at this
  simp only [qConditionalEnt, MState.traceRight_left_assoc']
  linarith

/-- Strong subadditivity, stated in terms of quantum mutual information.
  I(A;BC) ≥ I(A;B). -/
theorem qMutualInfo_strong_subadditivity (ρ₁₂₃ : MState (d₁ × d₂ × d₃)) :
    qMutualInfo ρ₁₂₃ ≥ qMutualInfo ρ₁₂₃.assoc'.traceRight := by
  have := Sᵥₙ_strong_subadditivity ρ₁₂₃
  dsimp at this
  simp only [qMutualInfo, MState.traceRight_left_assoc', MState.traceRight_right_assoc']
  linarith

/-- The quantum conditional mutual information `QCMI` is nonnegative. -/
theorem qcmi_nonneg (ρ : MState (dA × dB × dC)) :
    0 ≤ qcmi ρ := by
  simp [qcmi, qConditionalEnt]
  have := Sᵥₙ_strong_subadditivity ρ
  linarith

/-- The quantum conditional mutual information `QCMI ρABC` is at most 2 log dA. -/
theorem qcmi_le_2_log_dim (ρ : MState (dA × dB × dC)) :
    qcmi ρ ≤ 2 * Real.log (Fintype.card dA) := by
  have := Sᵥₙ_subadditivity ρ.assoc'.traceRight
  have := abs_le.mp (Sᵥₙ_triangle_subaddivity ρ)
  grind [qcmi, qConditionalEnt, Sᵥₙ_nonneg, Sᵥₙ_le_log_d]

/-- The quantum conditional mutual information `QCMI ρABC` is at most 2 log dC. -/
theorem qcmi_le_2_log_dim' (ρ : MState (dA × dB × dC)) :
    qcmi ρ ≤ 2 * Real.log (Fintype.card dC) := by
  have h_araki_lieb_assoc' : Sᵥₙ ρ.assoc'.traceRight - Sᵥₙ ρ.traceLeft.traceLeft ≤ Sᵥₙ ρ := by
    apply le_of_abs_le
    rw [← ρ.traceLeft_assoc', ← Sᵥₙ_of_assoc'_eq ρ]
    exact Sᵥₙ_triangle_subaddivity ρ.assoc'
  have := Sᵥₙ_subadditivity ρ.traceLeft
  grind [qcmi, qConditionalEnt, Sᵥₙ_le_log_d, MState.traceRight_left_assoc']

-- /-- The chain rule for quantum conditional mutual information:
-- `I(A₁A₂ : C | B) = I(A₁:C|B) + I(A₂:C|BA₁)`.
-- -/
-- theorem qcmi_chain_rule (ρ : MState ((dA₁ × dA₂) × dB × dC)) :
--     let ρA₁BC := ρ.assoc.SWAP.assoc.traceLeft.SWAP;
--     let ρA₂BA₁C : MState (dA₂ × (dA₁ × dB) × dC) :=
--       ((CPTPMap.id ⊗ₖ CPTPMap.assoc').compose (CPTPMap.assoc.compose (CPTPMap.SWAP ⊗ₖ CPTPMap.id))) ρ;
--     qcmi ρ = qcmi ρA₁BC + qcmi ρA₂BA₁C
--      := by
--   proof omitted
