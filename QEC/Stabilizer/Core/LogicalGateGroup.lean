import QEC.Stabilizer.Core.Normalizer

namespace Quantum
namespace StabilizerGroup

variable {n : ℕ}

/-!
# Logical gate group

This file intentionally keeps only the `logicalGateGroup` naming layer and reuses
the canonical normalizer development from `Normalizer.lean`.

`logicalGateGroup` and `stabilizerNormalizer` are definitionally equal.
-/

/-- The logical gate group is the stabilizer normalizer. -/
def logicalGateGroup (S : StabilizerGroup n) : Subgroup (NQubitGate n) :=
  stabilizerNormalizer S

/-- Convenience rewriting lemma for the definitional equality. -/
@[simp] lemma logicalGateGroup_eq_stabilizerNormalizer (S : StabilizerGroup n) :
    logicalGateGroup S = stabilizerNormalizer S := rfl

/-- U is in the logical gate group iff U maps every codespace state into the codespace. -/
lemma mem_logicalGateGroup_iff (U : NQubitGate n) (S : StabilizerGroup n) :
  U ∈ logicalGateGroup S ↔ ∀ ψ, IsInCodespace ψ S → IsInCodespace (U • ψ) S := by
  simpa [logicalGateGroup] using (mem_normalizer_iff (U := U) (S := S))

/-- U is in the logical gate group iff for every g ∈ S, U† g U stabilizes every codespace state. -/
lemma mem_logicalGateGroup_iff_conjugation (U : NQubitGate n) (S : StabilizerGroup n) :
  U ∈ logicalGateGroup S ↔ ∀ g ∈ S.toSubgroup, ∀ ψ : NQubitState n,
    IsInCodespace ψ S → (star U.val * g.toMatrix * U.val).mulVec ψ.val = ψ.val := by
  simp [logicalGateGroup, stabilizerNormalizer, IsInStabilizerNormalizer]

end StabilizerGroup

end Quantum
