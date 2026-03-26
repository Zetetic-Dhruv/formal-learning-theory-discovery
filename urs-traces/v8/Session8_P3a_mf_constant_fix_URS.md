---
session: 8
date: 2026-03-26
task_id: P3a
target: mf constant fix (9/delta to 36/delta, epsilon/kmin to epsilon/7)
file: FLT_Proofs/Theorem/Separation.lean
status: closed
---

## P3a: mf constant fix (9/delta -> 36/delta, epsilon/kmin -> epsilon/7)

**File**: `FLT_Proofs/Theorem/Separation.lean`
**Scope**: Lines 991-992 of `mf` definition. Change `9 / delta` to `36 / delta` and `epsilon / (kmin : Real)` to `epsilon / 7`.
**Nature**: 2-line edit to the sample complexity function constants.

### Context

After T0-T8 were all proved, the `mf` function inside `boost_two_thirds_to_pac` still used old constants from the k/2-threshold Chebyshev route:
- `kmin := ceil(9/delta) + 2` -- needed `ceil(36/delta) + 2` for 7/12 threshold
- `epsilon' := epsilon / kmin` -- needed `epsilon / 7` for the 7-rate bound

### What to change

**Line 991**: `9 / delta` -> `36 / delta`
**Line 992**: `epsilon / (kmin : Real)` -> `epsilon / 7`

### Why

The 7/12-fraction boosting architecture (T6) uses:
- Chebyshev threshold 7k/12 (gap k/12, variance k/4, ratio = 36/k)
- So need k >= 36/delta (was 9/delta for k/2 threshold)
- Rate bound: 7 * rate(n) < epsilon, so rate(n) < epsilon/7 (was epsilon/kmin)

### Estimated LOC: ~2 (edit only)

### Guardrails
- A4/A5 checks
- Build must pass (with existing sorry at line 1037)
- Do not touch any helper lemma
