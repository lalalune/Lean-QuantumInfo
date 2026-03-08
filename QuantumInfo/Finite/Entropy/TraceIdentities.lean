import Mathlib

/-!
# Finite Trace Identities

Chapter-4 style trace equalities used by entropy/channel proofs.
-/

noncomputable section

open scoped Matrix

namespace QuantumInfo
namespace EntropyTrace

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- Core cyclic-trace identity for rectangular matrices: `Tr(GG*) = Tr(G*G)`. -/
theorem trace_mul_conjTranspose_comm (G : Matrix m n ℂ) :
    (G * Gᴴ).trace = (Gᴴ * G).trace := by
  simpa using Matrix.trace_mul_comm (A := G) (B := Gᴴ)

/-- Real parts of `Tr(GG*)` and `Tr(G*G)` are equal. -/
theorem re_trace_mul_conjTranspose_comm (G : Matrix m n ℂ) :
    Complex.re ((G * Gᴴ).trace) = Complex.re ((Gᴴ * G).trace) := by
  simpa [trace_mul_conjTranspose_comm (G := G)]

/-- Trace of a Kronecker product factorizes. -/
theorem trace_kronecker (A : Matrix m m ℂ) (B : Matrix n n ℂ) :
    (Matrix.kroneckerMap (fun a b => a * b) A B).trace = A.trace * B.trace := by
  simpa using Matrix.trace_kronecker A B

end EntropyTrace
end QuantumInfo
