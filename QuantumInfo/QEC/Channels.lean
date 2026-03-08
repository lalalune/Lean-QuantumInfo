import QEC.Stabilizer.Core.StabilizerCode
import QuantumInfo.Finite.CPTPMap

/-!
# QEC Channel Adapters

Bundled channel adapters from stabilizer-code developments to `QuantumInfo`'s
`CPTPMap` interface.
-/

noncomputable section

namespace QuantumInfo
namespace QECBridge

open Quantum
open Quantum.StabilizerGroup

variable {n k : ℕ}

/-- A pair of encode/decode channels for a stabilizer code `C` into a chosen
logical carrier type `dL`. -/
structure StabilizerChannelAdapters
    (C : StabilizerCode n k)
    (dL : Type*) [Fintype dL] [DecidableEq dL] where
  encode : CPTPMap dL (NQubitBasis n)
  decode : CPTPMap (NQubitBasis n) dL

variable {C : StabilizerCode n k}
variable {dL : Type*} [Fintype dL] [DecidableEq dL]

/-- Exact correctability of a physical noise channel by an adapter pair. -/
def ExactlyCorrects (A : StabilizerChannelAdapters C dL)
    (noise : CPTPMap (NQubitBasis n) (NQubitBasis n)) : Prop :=
  (A.decode ∘ₘ noise) ∘ₘ A.encode = CPTPMap.id

/-- State-level action of exact correctability. -/
theorem ExactlyCorrects.apply_eq_self
    (A : StabilizerChannelAdapters C dL)
    {noise : CPTPMap (NQubitBasis n) (NQubitBasis n)}
    (h : ExactlyCorrects A noise) (ρ : MState dL) :
    ((A.decode ∘ₘ noise) ∘ₘ A.encode) ρ = ρ := by
  simpa [ExactlyCorrects] using congrArg (fun Φ => Φ ρ) h

/-- If `decode ∘ encode = id`, then the adapter exactly corrects identity noise. -/
theorem exactlyCorrects_id_of_leftInverse
    (A : StabilizerChannelAdapters C dL)
    (hleft : A.decode ∘ₘ A.encode = CPTPMap.id) :
    ExactlyCorrects A (CPTPMap.id (dIn := NQubitBasis n)) := by
  simpa [ExactlyCorrects, CPTPMap.compose_assoc, hleft]

/-- Canonical identity adapter on the physical space, useful as a baseline
integration witness for any stabilizer code. -/
def identityAdapters (C : StabilizerCode n k) :
    StabilizerChannelAdapters C (NQubitBasis n) where
  encode := CPTPMap.id
  decode := CPTPMap.id

/-- The identity adapter exactly corrects identity noise. -/
theorem identityAdapters_exactlyCorrects_id (C : StabilizerCode n k) :
    ExactlyCorrects (identityAdapters C) (CPTPMap.id (dIn := NQubitBasis n)) := by
  simp [ExactlyCorrects, identityAdapters, CPTPMap.compose_assoc]

end QECBridge
end QuantumInfo
