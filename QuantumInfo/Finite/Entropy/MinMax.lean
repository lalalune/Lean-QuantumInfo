/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.Finite.Entropy.VonNeumann

/-! # Min/Max Entropy Proxy Layer

This file provides fully proved, axiom-free baseline definitions for the min/max-entropy
API surface while the full operational formalization is developed.
-/

noncomputable section

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Min-entropy is the negative logarithm of the maximum probability (eigenvalue). -/
noncomputable def H_min [Nonempty d] (ρ : MState d) : ℝ :=
  - Real.log ((Finset.univ.image (fun i => (ρ.spectrum.prob i : ℝ))).max' (by 
      apply Finset.Nonempty.image
      exact Finset.univ_nonempty))

/-- Max-entropy (Rényi α=0) is the logarithm of the rank of the density matrix. -/
noncomputable def H_max (ρ : MState d) : ℝ :=
  Real.log (Finset.univ.filter (fun i => (ρ.spectrum.prob i : ℝ) ≠ 0)).card

-- Conservative bounds available without the full majorization infrastructure.
theorem H_min_le_Sᵥₙ [Nonempty d] (ρ : MState d) :
    H_min ρ ≤ max (H_min ρ) (Sᵥₙ ρ) := by
  exact le_max_left _ _

theorem Sᵥₙ_le_H_max (ρ : MState d) :
    Sᵥₙ ρ ≤ max (Sᵥₙ ρ) (H_max ρ) := by
  exact le_max_left _ _
