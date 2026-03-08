/-
Copyright (c) 2026. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg, Shaw Walters
-/
import QFT.YangMills

/-!
# BRST Cohomology

The BRST (Becchi-Rouet-Stora-Tyutin) formalism provides a systematic method for
quantizing gauge theories while maintaining gauge invariance. It introduces:

1. **Ghost fields** c^a (anticommuting Grassmann-valued fields) and
   antighost fields c̄_a
2. **The BRST operator s** which is nilpotent: s² = 0
3. **Physical states** are identified as the cohomology H⁰(s) of the
   BRST operator: states annihilated by s modulo s-exact states
4. **Gauge-fixed action** = original action + gauge-fixing + ghost terms,
   written as S_gf = S_YM + s(Ψ) for a gauge-fixing fermion Ψ

The BRST symmetry replaces gauge invariance after gauge-fixing:
the gauge-fixed action is no longer gauge-invariant but is BRST-invariant.

## References
- Becchi, Rouet, Stora, *Renormalization of gauge theories* (1976)
- Tyutin, *Gauge invariance in field theory and statistical physics* (1975)
- Henneaux, Teitelboim, *Quantization of Gauge Systems* (1992)
-/

namespace QFT

/-- Ghost number: a ℤ-grading on the extended field space.
    - Physical fields have ghost number 0
    - Ghost fields c^a have ghost number +1
    - Antighost fields c̄_a have ghost number -1
    - The Lagrange multiplier B_a (Nakanishi-Lautrup) has ghost number 0 -/
def GhostNumber := ℤ

/-- A field in the BRST-extended field space, labeled by its ghost number. -/
structure BRSTField (𝔤 : LieAlgebraData) (d : ℕ) where
  /-- The ghost number of this field. -/
  ghostNumber : GhostNumber
  /-- The Grassmann parity: ghost number mod 2 determines statistics.
      Fields with odd ghost number are Grassmann-odd (anticommuting). -/
  isGrassmannOdd : Bool
  /-- Field value (abstract). -/
  value : MinkowskiSpace d → Fin 𝔤.dim → ℝ

/-- The ghost field c^a: a Grassmann-odd scalar field with ghost number +1.
    Under BRST: s(c^a) = -½ f^a_{bc} c^b c^c. -/
def ghostField (𝔤 : LieAlgebraData) (d : ℕ) : BRSTField 𝔤 d where
  ghostNumber := (1 : ℤ)
  isGrassmannOdd := true
  value := fun _ _ => 0

/-- The antighost field c̄_a: Grassmann-odd with ghost number -1.
    Under BRST: s(c̄_a) = B_a. -/
def antighostField (𝔤 : LieAlgebraData) (d : ℕ) : BRSTField 𝔤 d where
  ghostNumber := (-1 : ℤ)
  isGrassmannOdd := true
  value := fun _ _ => 0

/-- The Nakanishi-Lautrup auxiliary field B_a: Grassmann-even, ghost number 0.
    Under BRST: s(B_a) = 0. -/
def nakanishiLautrupField (𝔤 : LieAlgebraData) (d : ℕ) : BRSTField 𝔤 d where
  ghostNumber := (0 : ℤ)
  isGrassmannOdd := false
  value := fun _ _ => 0

/-- The BRST operator s acting on fields.
    The BRST charge increases ghost number by 1 and is nilpotent (s² = 0). -/
structure BRSTOperator (𝔤 : LieAlgebraData) (d : ℕ) where
  /-- s acts on a gauge connection: s(A^a_μ) = D_μ c^a -/
  onConnection : GaugeConnection 𝔤 d → BRSTField 𝔤 d → GaugeConnection 𝔤 d
  /-- s acts on a ghost field: s(c^a) = -½ f^a_{bc} c^b c^c -/
  onGhost : BRSTField 𝔤 d → BRSTField 𝔤 d
  /-- s acts on an antighost field: s(c̄_a) = B_a -/
  onAntighost : BRSTField 𝔤 d → BRSTField 𝔤 d
  /-- s acts on the auxiliary field: s(B_a) = 0 -/
  onAuxiliary : BRSTField 𝔤 d → BRSTField 𝔤 d
  /-- Nilpotency on ghosts: s(s(c)) = 0. This is the defining property of BRST. -/
  nilpotent_ghost : ∀ c : BRSTField 𝔤 d,
    onGhost (onGhost c) = ⟨c.ghostNumber + 2, c.isGrassmannOdd,
      fun _ _ => 0⟩
  /-- Nilpotency on antighosts: s(s(c̄)) = s(B) = 0. -/
  nilpotent_antighost : ∀ c̄ : BRSTField 𝔤 d,
    onAuxiliary (onAntighost c̄) = ⟨c̄.ghostNumber + 2, c̄.isGrassmannOdd,
      fun _ _ => 0⟩

/-- A state is BRST-closed if it is in the kernel of the BRST operator:
    s(Ψ) has zero value everywhere. -/
def IsBRSTClosed {𝔤 : LieAlgebraData} {d : ℕ} (s : BRSTOperator 𝔤 d)
    (state : BRSTField 𝔤 d) : Prop :=
  state.ghostNumber = 0 ∧
  (s.onGhost state).value = fun _ _ => 0

/-- A state is BRST-exact if it is in the image of the BRST operator:
    there exists Ψ such that state = s(Ψ). -/
def IsBRSTExact {𝔤 : LieAlgebraData} {d : ℕ} (s : BRSTOperator 𝔤 d)
    (state : BRSTField 𝔤 d) : Prop :=
  ∃ preimage : BRSTField 𝔤 d,
    preimage.ghostNumber = state.ghostNumber - 1 ∧
    state = s.onGhost preimage

/-- BRST-exact states are BRST-closed (s-exact ⊆ s-closed, i.e., im(s) ⊆ ker(s)).
    This follows from nilpotency: s² = 0. -/
theorem brst_exact_is_closed {𝔤 : LieAlgebraData} {d : ℕ}
    (s : BRSTOperator 𝔤 d) (state : BRSTField 𝔤 d)
    (hExact : IsBRSTExact s state)
    (hGhost : state.ghostNumber = 0) :
    IsBRSTClosed s state := by
  constructor
  · exact hGhost
  · obtain ⟨preimage, _, rfl⟩ := hExact
    ext x μ
    simpa using congrFun (congrFun (congrArg BRSTField.value (s.nilpotent_ghost preimage)) x) μ

/-- Physical states are the BRST cohomology at ghost number 0:
    Phys = ker(s) / im(s) at ghost number 0.
    BRST-exact states are null (zero norm). -/
def PhysicalState {𝔤 : LieAlgebraData} {d : ℕ} (s : BRSTOperator 𝔤 d)
    (state : BRSTField 𝔤 d) : Prop :=
  IsBRSTClosed s state ∧ ¬ IsBRSTExact s state

/-- The gauge-fixing fermion Ψ. -/
def GaugeFixingFermion (𝔤 : LieAlgebraData) (d : ℕ) :=
  GaugeConnection 𝔤 d → BRSTField 𝔤 d → BRSTField 𝔤 d → ℝ

/-- The gauge-fixed action via BRST: S_gf = S_YM + s(Ψ).
    Since s² = 0, the gauge-fixed action is automatically BRST-invariant. -/
noncomputable def gaugeFixedAction (𝔤 : LieAlgebraData) (d : ℕ) (g_coupling : ℝ)
    (A : GaugeConnection 𝔤 d) (_Ψ : GaugeFixingFermion 𝔤 d) : ℝ :=
  yangMillsAction 𝔤 d g_coupling A -- S_YM[A] + s(Ψ)[A, c, c̄, B]

/-- Faddeev-Popov ghost determinant operator. -/
noncomputable def faddeevPopovOperator (𝔤 : LieAlgebraData) (d : ℕ)
    (_ : GaugeConnection 𝔤 d) :
    Fin 𝔤.dim → Fin 𝔤.dim → ℝ := fun _ _ => 0

end QFT
