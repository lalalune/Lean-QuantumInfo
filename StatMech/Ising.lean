/-
Copyright (c) 2026. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg, Shaw Walters
-/
import StatMech.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exponential

namespace StatMech

open Finset
open scoped BigOperators

variable {L : AbstractLattice}

/-- A spin configuration assigns a Boolean to each site (True ~ +1, False ~ -1). -/
def IsingConfig (L : AbstractLattice) := L.Site → Bool

/-- Finite lattices induce finitely many spin configurations. -/
noncomputable instance instFintypeIsingConfig (L : AbstractLattice) : Fintype (IsingConfig L) := by
  classical
  dsimp [IsingConfig]
  infer_instance

/-- Convert a boolean spin to a real value +1 or -1. -/
def isingSpin (b : Bool) : ℝ := cond b 1 (-1)

/-- 
The Hamiltonian for the classic Ising model.
H(σ) = -J ∑_{⟨i,j⟩} σ_i σ_j - h ∑_i σ_i
We sum over all links, so we divide by 2 to avoid double counting, 
or just let J absorb the factor of 2.
-/
noncomputable def IsingHamiltonian (J h : ℝ) (σ : IsingConfig L) : ℝ :=
  let interaction := ∑ l : L.Link, isingSpin (σ (L.source l)) * isingSpin (σ (L.target l))
  let magnetic := ∑ s : L.Site, isingSpin (σ s)
  (-J / 2) * interaction - h * magnetic

/--
The classical partition function for the Ising model:
Z = ∑_{σ} exp(-β H(σ))
-/
noncomputable def IsingPartitionFunction (β J h : ℝ) : ℝ :=
  ∑ σ : IsingConfig L, Real.exp (-β * IsingHamiltonian J h σ)
  
end StatMech
