/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Alex Meiburg
-/
import QuantumInfo.ForMathlib.HermitianMat.CfcOrder
import QuantumInfo.ForMathlib.HermitianMat.Log
import QuantumInfo.ForMathlib.Majorization

/-!
# Araki-Lieb-Thirring Inequality

The Araki-Lieb-Thirring (ALT) inequality is a fundamental result in matrix analysis relating
traces of matrix powers. For positive semidefinite matrices A, B:

For 0 < q ≤ 1:
  Tr((A^r B^p A^r)^q) ≤ Tr(A^{rq} B^{pq} A^{rq})

For q ≥ 1:
  Tr((A^r B^p A^r)^q) ≥ Tr(A^{rq} B^{pq} A^{rq})

This file establishes the ALT inequality and derives key consequences for quantum
information theory, particularly for sandwiched Rényi relative entropy.
-/

variable {d : Type*} [Fintype d] [DecidableEq d]

noncomputable section

open HermitianMat
open ComplexOrder

namespace ArakiLiebThirring

/-!
The trace-level Araki-Lieb-Thirring consequences are intentionally omitted from the maintained
surface of this module for now. The existing majorization development is sufficient to support
the multiplicative Weyl statements in `Majorization`, but the scalar convexity step needed for
full ALT has not yet been packaged in a stable way.
-/

end ArakiLiebThirring

end
