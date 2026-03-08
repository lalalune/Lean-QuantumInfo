import QuantumInfo.InfiniteDim.LogosBridge

/-!
# Finite-Dimensional Stone Integration

Finite-core alias surface for the integrated Stone corollary imported through
`QuantumInfo.InfiniteDim.LogosBridge`.
-/

noncomputable section

namespace QuantumInfo
namespace FiniteStone

abbrev FiniteHilbert (d : Type*) := LogosBridge.FiniteHilbert d

/-- Finite-dimensional Stone theorem re-export into a finite-core namespace. -/
theorem stone_finite_dim {d : Type*} [Fintype d] [DecidableEq d] :
    ∀ (U_grp : QuantumMechanics.Generators.OneParameterUnitaryGroup (H := FiniteHilbert d)),
      ∃! (gen : QuantumMechanics.Generators.Generator U_grp), gen.IsSelfAdjoint ∧
        (∀ (hsa : gen.IsSelfAdjoint) (h_dense : Dense (gen.domain : Set (FiniteHilbert d))),
          ∀ t ψ, (U_grp.U t) ψ = (QuantumMechanics.Yosida.exponential gen hsa h_dense t) ψ) :=
  LogosBridge.stone_finite_dim

end FiniteStone
end QuantumInfo
