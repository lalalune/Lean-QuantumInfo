import QEC.Foundations.Foundations

/-!
# Pauli Consistency

Consistency checks between the integrated QEC Pauli gate definitions and the
canonical qubit Pauli matrices used in the finite-dimensional QuantumInfo core.
-/

noncomputable section

namespace QuantumInfo
namespace QECBridge

open Quantum

abbrev quantumInfoX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
abbrev quantumInfoY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -Complex.I; Complex.I, 0]
abbrev quantumInfoZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

theorem qecX_eq_quantumInfoX :
    (Quantum.X : Matrix (Fin 2) (Fin 2) ℂ) = quantumInfoX := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [quantumInfoX, Quantum.X, Quantum.Xmat]

theorem qecY_eq_quantumInfoY :
    (Quantum.Y : Matrix (Fin 2) (Fin 2) ℂ) = quantumInfoY := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [quantumInfoY, Quantum.Y, Quantum.Ymat]

theorem qecZ_eq_quantumInfoZ :
    (Quantum.Z : Matrix (Fin 2) (Fin 2) ℂ) = quantumInfoZ := by
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [quantumInfoZ, Quantum.Z, Quantum.Zmat]

end QECBridge
end QuantumInfo
