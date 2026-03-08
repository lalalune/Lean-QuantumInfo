# P0-P2 Progress (Current Pass)

Date: 2026-02-28

## Closed in this pass

- **Critical build unblock (non-active file)**
  - `QuantumInfo/Finite/CPTPMap/Unbundled.lean`:
    replaced a `Finset.prod_eq_zero_iff` use requiring stronger typeclass
    assumptions with `Finset.prod_eq_zero`, removing the hard build break.

- **P1 algebra base**
  - `QuantumInfo/Finite/Qubit/Basic.lean`:
    added compile-checked Pauli identities:
    - `Qubit.X_mul_X`
    - `Qubit.Z_mul_Z`
    - `Qubit.X_mul_Z_eq_neg_Z_mul_X`

- **P2 qudit base**
  - `QuantumInfo/Finite/Qudit/Basic.lean` (new):
    - `Qudit.Idx`
    - `Qudit.omega`
    - `Qudit.X`
    - `Qudit.Z`
    - entrywise lemmas for `X`/`Z`.

- **P0 trace-identity base**
  - `QuantumInfo/Finite/Entropy/TraceIdentities.lean` (new):
    - `QuantumInfo.EntropyTrace.trace_mul_conjTranspose_comm`
    - `QuantumInfo.EntropyTrace.re_trace_mul_conjTranspose_comm`
    - `QuantumInfo.EntropyTrace.trace_kronecker`

## Active-file skips (per instruction)

- `QuantumInfo/Finite/Pinching.lean`
- `QuantumInfo/Finite/CPTPMap/CPTP.lean`

Both are listed in `tools/foundation_skip_paths.txt` and excluded from static
placeholder audits while active.

## Validation run summary

- `lake build QuantumInfo.Finite.Qudit.Basic`: **pass**
- `lake build QuantumInfo.Finite.Qubit.Basic`: **pass**
- `lake build QuantumInfo.Finite.Entropy.TraceIdentities`: **pass**
- `lake build QuantumInfo.Finite.CPTPMap.Unbundled`: **pass**
- Global `lake build`: **blocked by active skip file**
  (`QuantumInfo/Finite/CPTPMap/CPTP.lean`).

