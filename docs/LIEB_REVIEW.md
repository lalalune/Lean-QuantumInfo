# Lieb Concavity Theorem — Review

## 1. Current State (QuantumInfo/ForMathlib/Lieb.lean)

```lean
theorem LiebConcavity (K : Matrix n m ℂ) (hq : 0 ≤ q) (hr : 0 ≤ r) (hqr : q + r ≤ 1) :
  let F : (HermitianMat m ℂ × HermitianMat n ℂ) → ℝ :=
      fun (x,y) ↦ ((x ^ q).conj K).inner (y ^ r);
    ConcaveOn ℝ .univ F := by
  sorry
```

### Type and notation issues

1. **Conj argument order / semantics**
   - `HermitianMat.conj`: For `B : Matrix m n α`, we have `(A.conj B).mat = B * A.mat * B.conjTranspose`
   - So `A.conj B` = B A B†, i.e. conjugation by `B`
   - `conj` maps `HermitianMat n α → HermitianMat m α` when `B : Matrix m n α`

2. **Dimension mismatch**
   - For `(x ^ q).conj K`: if `x : HermitianMat m ℂ` then `x ^ q : HermitianMat m ℂ`. For `conj K` we need `K : Matrix ? m` (columns of `K` match rows of `x`). With `K : Matrix n m ℂ` we get `K : Matrix n m`, so `K` is `n×m`. That gives `conj K : HermitianMat m α → HermitianMat n α`, so `(x^q).conj K : HermitianMat n ℂ`.
   - For `(y ^ r)`: `y : HermitianMat n ℂ` gives `y ^ r : HermitianMat n ℂ`.
   - So both sides are `HermitianMat n ℂ` — dimensions match.

3. **Wrong trace formula**
   - Current: `((x ^ q).conj K).inner (y ^ r)` = `⟪K x^q K†, y^r⟫` = Re(tr(K x^q K† y^r))
   - Correct Lieb quantity: `Tr(K† A^p K B^{1-p})`
   - So the current statement uses `K x^q K†` instead of `K† x^q K`. These differ unless `K` is square.

---

## 2. Correct Lieb Statement

For 0 ≤ p ≤ 1, the map

`F(A, B) = Tr(K† A^p K B^{1-p})`

is jointly concave in (A, B) for PSD A, B.

### Correct indexing

- `K : Matrix n m ℂ` (so K† is m×n)
- `A : HermitianMat m ℂ` (m×m)
- `B : HermitianMat m ℂ` (m×m)
- `K† A^p K` = (m×n)(m×m)(n×m) = m×m
- `Tr(K† A^p K B^{1-p})` is well-typed

### Expressing via `conj` and inner product

`(A.conj B).mat = B * A.mat * B.conjTranspose` with `B : Matrix m n`, `A : HermitianMat n`.

To get `K† A^p K` we need `B A B†` with B = K†. So we need `K† : Matrix m n` and the middle matrix `A^p : HermitianMat n` (n×n). That gives (m×n)(n×n)(n×m) = m×m. But `K† A^p K` with standard Lieb dimensions requires `A^p : HermitianMat m` (m×m) because A, B are both m×m. So:
- `conj` formulation `(A^p).conj (K†)` works **only when m = n** (square K), since then the middle matrix is m×m in both cases.
- For **rectangular K** (n ≠ m), `(A^p).conj (K.conjTranspose)` does not match `K† A^p K` — the dimensions conflict (conj expects n×n input to produce m×m output, but A is m×m).

**When m = n (square K):**
- `(A^p).conj (K.conjTranspose)` : `HermitianMat m ℂ`
- `B^{1-p}` : `HermitianMat m ℂ`
- `⟪(A^p).conj (K.conjTranspose), B^{1-p}⟫ = Re(tr(K† A^p K B^{1-p}))`

For Hermitian PSD arguments the trace is real, so `Re(tr(...)) = tr(...)`.

**For rectangular K:** use a direct trace definition, e.g. `(K.conjTranspose * (A ^ p).mat * K * (B ^ (1 - p)).mat).trace`, rather than the `conj` + inner form.

### Corrected theorem (sketch)

**Option A — square K only (using conj):**
```lean
-- When n = m (K square)
theorem LiebConcavity (K : Matrix m m ℂ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
  let F : (HermitianMat m ℂ × HermitianMat m ℂ) → ℝ :=
      fun (A, B) ↦ ((A ^ p).conj K.conjTranspose).inner (B ^ (1 - p));
    ConcaveOn ℝ {x | 0 ≤ x.1 ∧ 0 ≤ x.2} F := by
  sorry
```

**Option B — general rectangular K (direct trace):**

For `K : Matrix n m ℂ`, the product `K† A^p K B^{1-p}` has `A : HermitianMat n` (n×n), `B : HermitianMat m` (m×m) — note different dimensions.

```lean
theorem LiebConcavity (K : Matrix n m ℂ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
  let F : (HermitianMat n ℂ × HermitianMat m ℂ) → ℝ :=
      fun (A, B) ↦ RCLike.re ((K.conjTranspose * (A ^ p).mat * K * (B ^ (1 - p)).mat).trace);
    ConcaveOn ℝ {x | 0 ≤ x.1 ∧ 0 ≤ x.2} F := by
  sorry
```

- `A : HermitianMat n ℂ`, `B : HermitianMat m ℂ` — different dimensions when `n ≠ m`
- Domain: PSD pairs `{x | 0 ≤ x.1 ∧ 0 ≤ x.2}` — Lieb concavity is on the PSD cone
- Exponent: `p` and `1-p`

---

## 3. What Exists in the Codebase

### HermitianMat

| Feature | Location | Notes |
|--------|----------|--------|
| `rpow` (A ^ r for r : ℝ) | HermitianMat/CFC.lean | `A.cfc (Real.rpow · r)` |
| `inner` ⟪A,B⟫ = Re(tr(A.mat * B.mat)) | HermitianMat/Inner.lean | `inner_eq_re_trace` |
| `conj` (A.conj B).mat = B * A.mat * B† | HermitianMat/Basic.lean | `conj_apply_mat` |
| `mat_rpow_add`, `rpow_mul` | HermitianMat/CFC.lean | For 0 ≤ A |

### Mathlib

| Feature | Location |
|---------|----------|
| Hadamard three-lines | `Mathlib.Analysis.Complex.Hadamard` — `norm_le_interp_of_mem_verticalClosedStrip` (log M(re z) convex on [l,u]) |
| CFC, trace, etc. | Standard analysis / linear algebra |

---

## 4. Implementation Plan (Hadamard Three-Lines Route)

1. **Fix the Lieb statement**
   - Square K: use `(A^p).conj K.conjTranspose` with A, B in `HermitianMat m ℂ`
   - Rectangular K: use direct trace with A : `HermitianMat n`, B : `HermitianMat m`
   - Restrict to PSD domain `{x | 0 ≤ x.1 ∧ 0 ≤ x.2}`

2. **Analytic extension**
   - Define `F(z) = Tr(K† A^z K B^{1-z})` for z in the strip `0 ≤ Re(z) ≤ 1`
   - This requires **complex powers** `A^z` for z ∈ ℂ; see below.

3. **Complex powers**
   - Define `A^z` for `z : ℂ` and PSD A, e.g. via `exp(z · log A)` or a suitable CFC extension
   - The current CFC is `ℝ → ℝ` only; complex powers are not yet available

4. **Use Hadamard**
   - Show F is holomorphic in the open strip and continuous on the closure
   - Bound F on the boundary
   - Apply Hadamard three-lines to get concavity in p on [0,1]

5. **Reduction**
   - Deduce joint concavity from concavity in p along the segment `(A_t, B_t)` with `A_t = t A_1 + (1-t) A_2`, `B_t = t B_1 + (1-t) B_2`, using the analytic interpolation

---

## 5. HermitianMat Complex Powers (cpow)

**HermitianMat does not currently support complex powers.**

### Current CFC

- `rpow` is defined as `A.cfc (Real.rpow · r)` with `r : ℝ`
- The CFC in this repo uses functions `f : ℝ → ℝ` on the spectrum; `Real.rpow` is real-valued
- There is no `cpow` or `zpow` for `z : ℂ` in the HermitianMat files

### Grep result

```bash
$ grep -r "cpow\|Complex.rpow\|complex.*power" QuantumInfo/
QuantumInfo/Finite/Entropy/Relative.lean:
  lemma Complex.continuousOn_cpow_const_Ioi (z : ℂ) :
```

That is about `Complex.continuousOn_cpow_const_Ioi`, not HermitianMat.

### What would be needed

- **Option A**: CFC for `f : ℝ → ℂ` (or `ℂ → ℂ` restricted to spectrum) so that `A^z = cfc (· ^ z) A` for `z : ℂ`
- **Option B**: Use `A^z = exp(z · log A)` for PD A (log A exists), then extend to PSD by continuity
- **Option C**: Another proof path that avoids complex powers (e.g. differentiation-based convexity proofs instead of Hadamard)

---

## 6. Summary

| Item | Status |
|------|--------|
| Lieb statement (types, conj order) | **Incorrect** — trace uses K…K† not K†…K; for rectangular K, A : `HermitianMat n`, B : `HermitianMat m` |
| Trace formula | **Incorrect** — current uses K…K† instead of K†…K |
| Domain | **Incomplete** — should use PSD cone, not `.univ` |
| HermitianMat cpow for z : ℂ | **Not present** — only `rpow` for r : ℝ |
| Hadamard three-lines | **In Mathlib** — ready to use |
| Implementation path | Blocked on complex powers unless an alternative proof is used |
