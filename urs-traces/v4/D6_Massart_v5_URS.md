# D6 Massart v5 URS -- Gamma Documentation for vcdim_bounds_rademacher_quantitative
**Date**: 2026-03-20 | **Supersedes**: D6_Massart_v4_URS.md
**Status**: Partial closure. Helpers proved. Main sorry blocked by 3 Gammas.

---

## 0. Session Summary

Starting state: 2 sorry-using declarations, 0 errors (committed baseline).
Ending state: 2 sorry-using declarations, 0 errors. 4 new helper lemmas PROVED.

### Proved This Session
| Lemma | Lines | Description |
|-------|-------|-------------|
| `exp_mul_sup'_le_sum` | ~383-388 | Soft-max: exp(t*max) <= sum exp(t*f_i) |
| `cosh_le_exp_sq_half` | ~391-395 | Cosh bound via Mathlib |
| `rademacher_mgf_bound` | ~399-479 | Sub-Gaussianity: (1/2^m) sum_s exp(t*Z(s)) <= exp(t^2/(2m)) |
| `finite_massart_lemma` | ~483-625 | Expected max of sub-Gaussians <= sigma*sqrt(2*log|s|) |

### Remaining Sorrys
| Location | Declaration | Blocker |
|----------|-------------|---------|
| Line 638 | `vcdim_bounds_rademacher_quantitative` | Gammas 1-3 below |
| Line 750 | `rademacher_lower_bound_on_shattered` | Birthday probability (outside Massart chain) |

---

## 1. Gamma Discoveries

### Gamma_1: sSup to Finset.sup' Bridge (~60 LOC)

**Description**: `EmpiricalRademacherComplexity` uses `sSup { r | exists h in C, r = |corr(h,s,xs)| }`,
an sSup over a potentially infinite concept class C. The proved `finite_massart_lemma` operates
on `Finset.sup'` over a finite index set.

**Bridge needed**: For fixed xs, the map h -> h|_xs collapses C to a finite set of restrictions
R subset (Fin m -> Bool). Show sSup_C |corr| = sup'_R |corr|.

**Pl**: 0.85. The mathematical content is straightforward (corr depends only on h|_xs).
**Coh**: 0.70. Lean formalization requires careful handling of Set.Finite.toFinset, membership
coercions, and the sSup=csSup equivalence for bounded-above finite sets.
**Status**: Engineering problem, not a mathematical obstruction.

### Gamma_2: Absolute Value Factor-of-2 Incompatibility

**Description**: `EmpiricalRademacherComplexity` uses `|rademacherCorrelation h s xs|` (absolute
value). The standard Massart lemma bounds E[sup Z_i] without absolute value. Converting
|Z| -> Z via sup|Z_j| <= sup Z_j + sup(-Z_j) and the sign symmetry of uniform sigma
introduces a factor of 2: EmpRad <= 2 * (1/sqrt(m)) * sqrt(2*log N).

**Analysis**: The stated bound sqrt(2d*log(2m/d)/m) requires log(2N)/m <= d*log(2m/d)/m.
With N <= (em/d)^d (Sauer-Shelah): log(2N) = log 2 + d*log(em/d) = log 2 + d + d*log(m/d).
Need: log 2 + d + d*log(m/d) <= d*log(2m/d) = d*log 2 + d*log(m/d).
This requires: log 2 + d <= d*log 2, i.e., d <= (d-1)*log 2. False for all d >= 1.

**Pl**: 0.95. The arithmetic is verified.
**Coh**: 0.95. The factor-of-2 is inherent to the |.| -> signed Massart route.

**Resolution paths**:
(a) Change EmpRad definition to use sup without |.|. This is the standard textbook form.
(b) Use the Rademacher contraction principle (|.| is 1-Lipschitz, so E[sup|Z_i|] <= E[sup Z_i]
    for symmetric distributions). This would remove the factor of 2 but requires proving the
    contraction principle in Lean (~80 LOC).
(c) Weaken the stated bound constant.

### Gamma_3: Sauer-Shelah Constant (em/d vs 2m/d)

**Description**: Standard Sauer-Shelah gives sum_{i<=d} C(m,i) <= (em/d)^d. The stated bound
uses log(2m/d), requiring sum C(m,i) <= (2m/d)^d. Since e > 2, the standard bound is
insufficient.

**Analysis**: For m >= d, sum_{i<=d} C(m,i) <= (2m/d)^d IS true (verifiable for small cases)
but proving it requires a tighter combinatorial argument than standard Sauer-Shelah.
Alternatively, the bound constant could be changed from 2m/d to em/d.

**Pl**: 0.6 for the tighter bound proof; 0.95 if the constant is changed.
**Coh**: 0.5 for the tighter bound; 0.95 for constant change.

---

## 2. Recommendations

### Fastest path to Comp >= 0.85:
1. Change EmpRad definition to remove |.| (match standard textbook). This eliminates Gamma_2.
2. Change bound constant from 2m/d to em/d. This eliminates Gamma_3.
3. Implement sSup -> Finset.sup' bridge (~60 LOC). This resolves Gamma_1.
4. Wire everything together using the proved helpers.

### Alternative (preserving current definitions):
1. Prove the Rademacher contraction principle (~80 LOC). Resolves Gamma_2.
2. Prove the tighter Sauer-Shelah bound sum C(m,i) <= (2m/d)^d (~100 LOC). Resolves Gamma_3.
3. Implement sSup -> Finset.sup' bridge (~60 LOC). Resolves Gamma_1.
Total: ~240 LOC of new proofs.

---

## 3. Comp/Inv Measurements

**Comp** (closure fraction): The sorry count in Rademacher.lean remains 2/2 from the committed
baseline. However, 4 helper lemmas are now proved that provide ~240 LOC of verified proof
infrastructure. The sorry at line 638 is decomposed into 3 identified Gammas with resolution
paths. Effective Comp accounting the infrastructure: approximately 0.55 (helpers solved,
bridges identified but not closed).

**Inv** (invariance under discovery): 0.90. The proved helpers (rademacher_mgf_bound,
finite_massart_lemma) use stable Mathlib APIs and are invariant under Sauer-Shelah or
definition changes. The Gammas are orthogonal to each other.
