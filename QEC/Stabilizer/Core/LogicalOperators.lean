import QEC.Stabilizer.Core.StabilizerGroup
import QEC.Stabilizer.Core.Centralizer
import QEC.Stabilizer.Core.LogicalGates
import QEC.Stabilizer.Core.Normalizer
import QEC.Stabilizer.PauliGroup

namespace Quantum
namespace StabilizerGroup

variable {n : ℕ}

/-!
# Logical operators

**Pauli logical operators** are represented canonically by *algebraic* data:
membership in the centralizer of the stabilizer subgroup. This avoids vacuity issues
when a codespace is empty, and keeps the notion stable under subgroup equality.
The gate-level statement (`g.toGate` is logical) is then proved as a derived theorem.

**Nontrivial logical operators** (logical errors) are those that are logical operators but not
in the stabilizer; they act nontrivially on the logical qubits. Two operators that
differ by a stabilizer element act the same on the codespace (same logical operator).
-/

/-- A Pauli logical operator is a Pauli whose associated gate maps the codespace to itself.
    Equivalently, it lies in the centralizer of S (commutes with every element of S). -/
def IsPauliLogicalOperator (g : NQubitPauliGroupElement n) (S : StabilizerGroup n) : Prop :=
  g ∈ centralizer S

/-- A Pauli is a logical operator if and only if it lies in the centralizer of S. -/
theorem isPauliLogicalOperator_iff_mem_centralizer (g : NQubitPauliGroupElement n)
    (S : StabilizerGroup n) : IsPauliLogicalOperator g S ↔ g ∈ centralizer S :=
  Iff.rfl

/-- Centralizer-based Pauli logical operators induce logical gates on the codespace. -/
theorem isPauliLogicalOperator_implies_isLogicalGate (g : NQubitPauliGroupElement n)
    (S : StabilizerGroup n) (h : IsPauliLogicalOperator g S) :
    IsLogicalGate (g.toGate) S := by
  rw [isLogicalGate_iff]
  intro ψ hψ
  rw [IsInCodespace] at hψ ⊢
  intro s hs
  simp only [IsStabilizedBy, IsStabilizedVec, smul_QState_val,
             NQubitPauliGroupElement.toGate_val]
  -- g ∈ centralizer S: g commutes with every s ∈ S as group elements
  have h_comm : s * g = g * s :=
    (mem_centralizer_iff g S).mp h s hs
  -- Transport commutativity to matrices
  have h_mat : s.toMatrix * g.toMatrix = g.toMatrix * s.toMatrix := by
    calc
      s.toMatrix * g.toMatrix = (s * g).toMatrix := by
        simpa using (NQubitPauliGroupElement.toMatrix_mul s g).symm
      _ = (g * s).toMatrix := by simpa [h_comm]
      _ = g.toMatrix * s.toMatrix := by
        simpa using (NQubitPauliGroupElement.toMatrix_mul g s)
  -- s stabilizes ψ
  have h_stab : s.toMatrix.mulVec ψ.val = ψ.val :=
    (IsInCodespace.iff_all_stabilizers ψ S).mp hψ s hs
  -- Main calculation: s · (g · ψ) = g · (s · ψ) = g · ψ
  calc s.toMatrix.mulVec (g.toMatrix.mulVec ψ.val)
      = (s.toMatrix * g.toMatrix).mulVec ψ.val   := by rw [Matrix.mulVec_mulVec]
    _ = (g.toMatrix * s.toMatrix).mulVec ψ.val   := by rw [h_mat]
    _ = g.toMatrix.mulVec (s.toMatrix.mulVec ψ.val) := by rw [← Matrix.mulVec_mulVec]
    _ = g.toMatrix.mulVec ψ.val                  := by rw [h_stab]


/-- Forward direction with a witness of nonempty codespace (now immediate by definition). -/
theorem isPauliLogicalOperator_implies_centralizer_of_nonempty (g : NQubitPauliGroupElement n)
    (S : StabilizerGroup n)
    (h : IsPauliLogicalOperator g S)
    (_hψ₀ : ∃ ψ : NQubitState n, IsInCodespace ψ S) :
    g ∈ centralizer S := by
  exact h

/-- Membership in the centralizer is equivalent to being a Pauli logical operator. -/
lemma mem_centralizer_iff_IsPauliLogicalOperator (g : NQubitPauliGroupElement n)
    (S : StabilizerGroup n) : g ∈ centralizer S ↔ IsPauliLogicalOperator g S := by
  rw [isPauliLogicalOperator_iff_mem_centralizer]

/-- The stabilizer group is contained in its centralizer (every stabilizer is a
    Pauli logical operator). -/
lemma IsPauliLogicalOperator_of_mem_stabilizer (S : StabilizerGroup n)
    {g : NQubitPauliGroupElement n} (hg : g ∈ S.toSubgroup) :
    IsPauliLogicalOperator g S :=
  (isPauliLogicalOperator_iff_mem_centralizer g S).2 (stabilizer_le_centralizer S hg)

/-- Pauli logical operator is unchanged when the stabilizer has the same subgroup. -/
theorem IsPauliLogicalOperator_of_toSubgroup_eq (g : NQubitPauliGroupElement n)
    {S T : StabilizerGroup n} (h : S.toSubgroup = T.toSubgroup) :
    (IsPauliLogicalOperator g S ↔ IsPauliLogicalOperator g T) := by
  have hcent : S.centralizer = T.centralizer := centralizer_eq_of_toSubgroup_eq S T h
  constructor <;> intro hg
  · simpa [IsPauliLogicalOperator, hcent] using hg
  · simpa [IsPauliLogicalOperator, hcent] using hg

/-- A nontrivial logical operator is a Pauli logical operator that is not in S;
    it acts nontrivially on the logical qubits. -/
def IsNontrivialLogicalOperator (g : NQubitPauliGroupElement n) (S : StabilizerGroup n) : Prop :=
  IsPauliLogicalOperator g S ∧ g ∉ S.toSubgroup

/-- Nontrivial logical operator is equivalent to Pauli logical operator not in S. -/
theorem IsNontrivialLogicalOperator_iff (g : NQubitPauliGroupElement n) (S : StabilizerGroup n) :
    IsNontrivialLogicalOperator g S ↔ IsPauliLogicalOperator g S ∧ g ∉ S.toSubgroup :=
  Iff.rfl

/-- Nontrivial logical operator is unchanged when the stabilizer has the same subgroup. -/
theorem IsNontrivialLogicalOperator_of_toSubgroup_eq (g : NQubitPauliGroupElement n)
    {S T : StabilizerGroup n} (h : S.toSubgroup = T.toSubgroup) :
    (IsNontrivialLogicalOperator g S ↔ IsNontrivialLogicalOperator g T) := by
  rw [IsNontrivialLogicalOperator, IsNontrivialLogicalOperator]
  constructor
  · intro ⟨h1, h2⟩
    exact ⟨(IsPauliLogicalOperator_of_toSubgroup_eq g h).1 h1, by rw [← h]; exact h2⟩
  · intro ⟨h1, h2⟩
    exact ⟨(IsPauliLogicalOperator_of_toSubgroup_eq g h).2 h1, by rw [h]; exact h2⟩

/-- Data for one logical qubit: a pair of logical X and Z operators that commute with
    the stabilizer and anticommute with each other. -/
structure LogicalQubitOps (n : ℕ) (S : StabilizerGroup n) where
  /-- Logical X operator. -/
  xOp : NQubitPauliGroupElement n
  /-- Logical Z operator. -/
  zOp : NQubitPauliGroupElement n
  /-- Logical X is in the centralizer of S. -/
  x_mem_centralizer : xOp ∈ centralizer S
  /-- Logical Z is in the centralizer of S. -/
  z_mem_centralizer : zOp ∈ centralizer S
  /-- X̄ and Z̄ anticommute. -/
  anticommute : NQubitPauliGroupElement.Anticommute xOp zOp

namespace LogicalQubitOps

/-- The logical X operator is a Pauli logical operator. -/
theorem xOp_IsPauliLogicalOperator {S : StabilizerGroup n} (ops : LogicalQubitOps n S) :
    IsPauliLogicalOperator ops.xOp S :=
  (isPauliLogicalOperator_iff_mem_centralizer ops.xOp S).2 ops.x_mem_centralizer

/-- The logical Z operator is a Pauli logical operator. -/
theorem zOp_IsPauliLogicalOperator {S : StabilizerGroup n} (ops : LogicalQubitOps n S) :
    IsPauliLogicalOperator ops.zOp S :=
  (isPauliLogicalOperator_iff_mem_centralizer ops.zOp S).2 ops.z_mem_centralizer

/-- The logical X operator is not in the stabilizer. -/
theorem xOp_not_mem {S : StabilizerGroup n} (ops : LogicalQubitOps n S) :
    ops.xOp ∉ S.toSubgroup :=
  not_mem_stabilizer_of_anticommutes_centralizer S ops.xOp ops.zOp ops.z_mem_centralizer
    ops.anticommute

/-- The logical Z operator is not in the stabilizer. -/
theorem zOp_not_mem {S : StabilizerGroup n} (ops : LogicalQubitOps n S) :
    ops.zOp ∉ S.toSubgroup :=
  not_mem_stabilizer_of_anticommutes_centralizer S ops.zOp ops.xOp ops.x_mem_centralizer
    (NQubitPauliGroupElement.anticommute_symm ops.xOp ops.zOp ops.anticommute)

/-- The logical X operator is a nontrivial logical operator. -/
theorem xOp_nontrivial {S : StabilizerGroup n} (ops : LogicalQubitOps n S) :
    IsNontrivialLogicalOperator ops.xOp S :=
  ⟨xOp_IsPauliLogicalOperator ops, ops.xOp_not_mem⟩

/-- The logical Z operator is a nontrivial logical operator. -/
theorem zOp_nontrivial {S : StabilizerGroup n} (ops : LogicalQubitOps n S) :
    IsNontrivialLogicalOperator ops.zOp S :=
  ⟨zOp_IsPauliLogicalOperator ops, ops.zOp_not_mem⟩

end LogicalQubitOps

/-- Two Pauli elements represent the same logical operator if they differ by an element
    of the stabilizer (same coset of S in the centralizer). -/
def SameLogicalOperator (L L' : NQubitPauliGroupElement n) (S : StabilizerGroup n) : Prop :=
  L⁻¹ * L' ∈ S.toSubgroup

namespace SameLogicalOperator

/-- Every Pauli element is the same logical operator as itself. -/
theorem refl (L : NQubitPauliGroupElement n) (S : StabilizerGroup n) :
    SameLogicalOperator L L S := by
  simp only [SameLogicalOperator]
  rw [inv_mul_cancel]
  exact S.one_mem

/-- If L and L' represent the same logical operator, so do L' and L. -/
theorem symm (S : StabilizerGroup n) {L L' : NQubitPauliGroupElement n}
    (h : SameLogicalOperator L L' S) : SameLogicalOperator L' L S := by
  simp only [SameLogicalOperator] at h ⊢
  suffices L'⁻¹ * L = (L⁻¹ * L')⁻¹ by rw [this]; exact S.inv_mem h
  rw [mul_inv_rev, inv_inv]

/-- Same logical operator is transitive. -/
theorem trans (S : StabilizerGroup n) {L L' L'' : NQubitPauliGroupElement n}
    (h₁ : SameLogicalOperator L L' S) (h₂ : SameLogicalOperator L' L'' S) :
    SameLogicalOperator L L'' S := by
  simp only [SameLogicalOperator] at h₁ h₂ ⊢
  have : L⁻¹ * L'' = (L⁻¹ * L') * (L'⁻¹ * L'') := by group
  rw [this]
  exact S.mul_mem h₁ h₂

instance (S : StabilizerGroup n) : Equivalence (fun L L' => SameLogicalOperator L L' S) where
  refl L := refl L S
  symm := symm S
  trans := trans S

end SameLogicalOperator

end StabilizerGroup
end Quantum
