# D12 Closure URS: Complete Closure of 5 Sorrys

## Will

Close 5 sorrys in Generalization.lean by: (1) bypassing `bad_consistent_covering` via the UC route, (2) proving `uc_bad_event_le_delta` via Mathlib's Hoeffding inequality, (3-5) proving the three lower-bound sorrys via shared pairing + measure bridge infrastructure.

## Build State

- **0 errors, 11 sorry-using declarations** (Generalization.lean: 6 sorrys at lines 633, 1271, 2056, 2121, 2537, 2964)
- Target: close 5 of these 6 (line 2121 = `vcdim_finite_imp_compression` is deep/open, NOT targeted)
- Expected outcome: **6 sorry-using declarations** after closure

## Gamma Discoveries (inherited + new)

| ID | Discovery | Type | Source |
|----|-----------|------|--------|
| Gamma_83 | `pac_lower_bound_core` is FALSE for epsilon = 1 | A4 alarm | D2 URS |
| Gamma_84 | `pac_lower_bound_member` is unprovable for delta >= 1/2 | A4 alarm | D2 URS |
| Gamma_92 | `bad_consistent_covering` is structurally unprovable (sample-independent reps vs sample-dependent equivalence classes) | Structural impossibility | D01 URS + this analysis |
| Gamma_93 | The UC route (`vcdim_finite_imp_uc` + `uc_imp_pac`) completely bypasses `bad_consistent_covering` + `union_bound_consistent` | Bypass discovery | This URS |
| Gamma_94 | Mathlib's `measure_sum_ge_le_of_iIndepFun` operates on `Measure.real` (= `(mu s).toReal`), not ENNReal -- bridge needed | Type mismatch | This URS |
| Gamma_95 | `uc_bad_event_le_delta` uses factorial sample complexity, NOT the standard Hoeffding bound -- proof route is polynomial tail bound via `pow_mul_exp_neg_le_factorial_div` (already proved at line 709), not direct Hoeffding | Proof route correction | This URS |
| Gamma_96 | The 3 D2 sorrys (pac_lower_bound_core, pac_lower_bound_member, hcomb in vcdim_infinite_not_pac) all share the identical mathematical core: pairing on unseen variables + pigeonhole over labelings + counting-to-measure bridge | Infrastructure reuse | D2 URS + this analysis |
| Gamma_97 | The measure bridge substep B of `vcdim_infinite_not_pac` is ALREADY PROVED (lines 2966-3167). Only substep A (the combinatorial hcomb, line 2964) remains | State correction | This analysis |

---

## Target 1: `bad_consistent_covering` (Line 633) -- BYPASS

### 1.1 Current State

`bad_consistent_covering` is called ONLY at line 686 inside `union_bound_consistent`. `union_bound_consistent` is called ONLY at line 998 inside `vcdim_finite_imp_pac_direct`. `vcdim_finite_imp_pac_direct` is called at line 77 inside `vcdim_finite_imp_pac` (PAC.lean).

### 1.2 Structural Impossibility (Confirmed)

The lemma requires sample-INDEPENDENT representatives whose consistency sets cover the bad event across ALL possible samples simultaneously. This is impossible for uncountable C (Gamma_92, confirmed by D01 URS analysis). The sorry CANNOT be proved.

### 1.3 Bypass Route

**Replace the body of `vcdim_finite_imp_pac` (PAC.lean line 77) to route through the UC path instead of the direct path.**

Current (PAC.lean:77):
```lean
theorem vcdim_finite_imp_pac ... :=
  vcdim_finite_imp_pac_direct X C hC
```

Replace with:
```lean
theorem vcdim_finite_imp_pac ... := by
  by_cases hne : C.Nonempty
  . exact uc_imp_pac X C hne (vcdim_finite_imp_uc X C hC)
  . rw [Set.not_nonempty_iff_eq_empty] at hne
    exact ⟨⟨Set.univ, fun _ => fun _ => false, fun _ => Set.mem_univ _⟩,
           fun _ _ => 0, fun _ _ _ _ _ _ c hcC => by simp [hne] at hcC⟩
```

### 1.4 Dependency Analysis

- `vcdim_finite_imp_uc` (line 1276): sorry-free EXCEPT it calls `uc_bad_event_le_delta` (sorry at 1271). So this bypass creates a DEPENDENCY on Target 2.
- `uc_imp_pac` (line 1334): sorry-free (proved).
- After bypass: `bad_consistent_covering` becomes dead code. `union_bound_consistent` becomes dead code. `vcdim_finite_imp_pac_direct` becomes dead code. ALL can be deleted or kept as documentation.

### 1.5 Impact

- `bad_consistent_covering` sorry ELIMINATED (dead code)
- New dependency on `uc_bad_event_le_delta` (Target 2)
- Net: -1 sorry (line 633 eliminated), conditioned on Target 2

### 1.6 Code Changes

| File | Line | Change |
|------|------|--------|
| `Theorem/PAC.lean` | 77 | Replace `vcdim_finite_imp_pac_direct X C hC` with UC route |

**LOC: ~8 (replacement body)**

---

## Target 2: `uc_bad_event_le_delta` (Line 1271) -- PROVE via Concentration

### 2.1 Statement Analysis

```lean
private lemma uc_bad_event_le_delta
    (D : Measure X) [IsProbabilityMeasure D]
    (C : ConceptClass X Bool) (c : Concept X Bool)
    (m : Nat) (hm : 0 < m) (epsilon delta : R) (heps : 0 < epsilon) (hdelta : 0 < delta) (hdelta1 : delta < 1)
    (v : Nat) (hv : forall n, v <= n -> GrowthFunction X C n <= sum_{i<=v} C(n,i))
    (hm_bound : (v + 2).factorial / (epsilon^(v+1) * delta) <= m) :
    Measure.pi (fun _ : Fin m => D)
      { xs | exists h in C, |TrueErrorReal X h c D - EmpiricalError X Bool h (xs, c) (zeroOneLoss)| >= epsilon }
      <= ENNReal.ofReal delta
```

### 2.2 Proof Route: NOT Hoeffding Directly

**Gamma_95 CORRECTION**: Despite the Noological URS recording Hoeffding as KK, the proof route for `uc_bad_event_le_delta` does NOT use Hoeffding's inequality directly. The reason:

1. The sample complexity bound is `m >= (v+2)! / (eps^(v+1) * delta)`, which is a FACTORIAL bound.
2. This corresponds to the polynomial tail approach: GF(C,m) * decay(m) <= delta, where GF ~ m^v and decay ~ exp(-eps*m).
3. The chain is: GF(C,m) <= sum C(m,i) <= (v+1)*m^v (by `sum_choose_le_mul_pow`, line 733), and (1-eps)^m <= exp(-eps*m) (standard). Then m^v * exp(-eps*m) <= (v+1)! / (eps^v * m * eps) for our m (by `pow_mul_exp_neg_le_factorial_div`, line 709).

**The proof chains through ALREADY-PROVED infrastructure**, not through Mathlib's Hoeffding.

### 2.3 Proof Strategy (Union Bound + Polynomial Tail)

The sorry must prove:
```
mu { xs | exists h in C, |TrueErr - EmpErr| >= eps } <= ofReal(delta)
```

**Step 1: Reduce to one-sided bound.**
For the consistent/realizable case: the ERM learner has EmpiricalError = 0 (consistent with c on sample). So |TrueErr - EmpErr| = TrueErr. The bad event reduces to:
```
{ xs | exists h in C, TrueErrorReal h c D >= eps AND h consistent on xs }
```

BUT: `uc_bad_event_le_delta` is for the GENERAL two-sided UC case (arbitrary h in C, not just consistent ones). The bound must hold for ALL h in C, including those with nonzero empirical error.

**Step 2: Per-hypothesis concentration.**
For a FIXED h in C:
- Define X_i(omega) = 1_{h(omega_i) != c(omega_i)} - D{h != c} (centered Bernoulli).
- X_i are iid, bounded in [-1, 1], mean 0.
- Sum = EmpiricalError - TrueErrorReal (scaled by m).
- |EmpErr - TrueErr| >= eps iff |sum X_i| >= m*eps.
- By Hoeffding: P(|sum| >= m*eps) <= 2*exp(-2*m*eps^2).

This IS where Mathlib's Hoeffding could apply.

**Step 3: Union bound over growth function.**
- For fixed xs, hypotheses group into <= GF(C,m) equivalence classes.
- Per class, the deviation event is the same (same restriction = same empirical error on this sample).
- Union bound: P(exists h bad) <= GF(C,m) * 2*exp(-2*m*eps^2).

BUT: This gives a DIFFERENT sample complexity bound (m ~ (v*log(m) + log(1/delta))/eps^2) than the factorial bound in the theorem statement.

**Step 4: Resolution -- use the WEAKER polynomial tail bound (already in the code).**

The theorem's sample complexity `m >= (v+2)!/(eps^(v+1)*delta)` is designed to be compatible with the polynomial tail approach:

```
GF(C,m) * tail(m, eps) <= delta
```

where:
- `GF(C,m) <= (v+1) * m^v` (by `sum_choose_le_mul_pow`, proved at line 733)
- `tail(m, eps) = (1-eps)^m <= exp(-eps*m)` (from `Real.one_sub_le_exp_neg` or similar)
- `m^v * exp(-eps*m) <= (v+1)!/(eps^(v+1) * m)` (from `pow_mul_exp_neg_le_factorial_div`, proved at line 709)
- Product: `(v+1) * (v+1)!/(eps^(v+1) * m) = (v+2)!/(eps^(v+1) * m) <= delta`
  when `m >= (v+2)!/(eps^(v+1) * delta)`.

### 2.4 Type Bridge Analysis

The proof needs to bridge between:
- `TrueErrorReal X h c D` (= `(D {x | h x != c x}).toReal`, an R value)
- `EmpiricalError X Bool h S (zeroOneLoss)` (= sum of 0-1 losses / m, an R value)
- The probability bound in ENNReal: `Measure.pi ... <= ENNReal.ofReal delta`

The key insight: for the one-sided consistent case, the deviation |TrueErr - EmpErr| reduces to TrueErr when h is consistent (EmpErr = 0). For the GENERAL two-sided case, we need:

```
{ xs | exists h in C, |TrueErr - EmpErr| >= eps }
  subset { xs | exists h in C, consistent(h,xs) AND TrueErr > eps }
  union { xs | exists h in C, NOT consistent(h,xs) AND |TrueErr - EmpErr| >= eps }
```

The second set is bounded by the UC argument for the non-consistent case. But actually, the standard approach for the UC bound is to use the growth function + tail bound for the CONSISTENT case only, and note that for ERM learners, only consistent hypotheses matter.

**HOWEVER**: `uc_bad_event_le_delta` states the FULL two-sided UC bound. The proof route that matches the factorial sample complexity is:

1. For each fixed sample xs, at most GF(C,m) distinct restrictions exist.
2. For each restriction class, pick one representative h_r.
3. For h_r: P(TrueErr(h_r) > eps | h_r consistent on xs) <= (1-eps)^m.
4. Union over <= GF(C,m) representatives: P(exists bad) <= GF(C,m) * (1-eps)^m.
5. GF(C,m) * (1-eps)^m <= delta by arithmetic from hm_bound.

This is a ONE-SIDED bound (TrueErr > eps for consistent h). For the FULL two-sided bound |TrueErr - EmpErr| >= eps, we need the symmetrization argument or a different approach.

### 2.5 ACTUAL Proof Plan

**Observation**: The caller `vcdim_finite_imp_uc` at line 1296 passes `uc_bad_event_le_delta` to close the UC guarantee. After the bypass (Target 1), `vcdim_finite_imp_uc` is on the critical path. The UC guarantee requires the two-sided bound.

**The simplest correct proof** for `uc_bad_event_le_delta`:

The set `{ xs | exists h in C, |TrueErr - EmpErr| >= eps }` is bounded by:
```
mu(bad) <= GF(C,m) * 2 * exp(-2*m*eps^2)    [Hoeffding + growth function]
```
OR by the polynomial tail:
```
mu(bad) <= GF(C,m) * (1-eps/2)^m            [one-sided concentration, crude]
```

For the factorial sample complexity bound to work with the second approach:
- `GF(C,m) <= (v+1)*m^v`
- `(1-eps/2)^m <= exp(-eps*m/2)`
- `m^v * exp(-eps*m/2) <= (v+1)!/(eps/(2))^(v+1) * 1/m` ... the constants shift but the structure is the same.

**RECOMMENDED APPROACH**: Prove a WEAKER bound that suffices. Since the goal is `mu <= ofReal(delta)` and we have:

```
mu(bad) <= mu{ xs | exists h in C, consistent AND TrueErr > eps/2 }
         + mu{ xs | exists h in C, |EmpErr - TrueErr| >= eps/2 AND NOT consistent }
```

Actually this decomposition is complex. The SIMPLEST correct proof:

**Use `union_bound_consistent` (which we are bypassing in Target 1 but is still available).**

Wait -- `union_bound_consistent` bounds `mu { xs | exists h, consistent AND err > eps }`. For UC we need `|TrueErr - EmpErr| >= eps` for ALL h, not just consistent ones.

**KEY REALIZATION**: The `uc_bad_event_le_delta` sorry bounds a two-sided UC deviation. The proof in the code is intended to chain through `hv` (growth function bound) + `hm_bound` (sample complexity). The intended proof is:

1. Use the one-sided tail: for FIXED h with true error p, P(h consistent on m iid samples) = (1-p)^m.
2. If h is consistent AND TrueErr > eps, then P(consistent) <= (1-eps)^m.
3. Growth function bounds the number of effective hypotheses.
4. GF(C,m) * (1-eps)^m <= delta by arithmetic.

This proves the ONE-SIDED bound: `mu { xs | exists h in C, consistent AND TrueErr > eps } <= delta`.

The FULL two-sided UC bound is STRICTLY HARDER. But the code at line 1298 shows that after calling `uc_bad_event_le_delta`, the proof converts the "good event" (all h have |TrueErr - EmpErr| < eps) from the complement. The STRUCTURE of the code suggests the intended proof IS the one-sided approach, despite the two-sided statement.

**PROOF PLAN (one-sided via existing infrastructure)**:

The absolute value |TrueErr - EmpErr| >= eps implies EITHER TrueErr - EmpErr >= eps OR EmpErr - TrueErr >= eps. For the CONSISTENT case (h agrees with c on all sample points): EmpErr = 0, so |TrueErr - 0| = TrueErr >= eps means TrueErr >= eps.

For non-consistent h: |TrueErr - EmpErr| >= eps is possible but the learner wouldn't output such h (ERM picks consistent when available).

**THE CORRECT ONE-SIDED REDUCTION**:

```
{ xs | exists h in C, |TrueErr - EmpErr| >= eps }
  supset { xs | exists h in C, TrueErr > eps AND consistent(h, xs) }
```

This goes the WRONG direction for bounding. We need:

```
{ xs | exists h in C, |TrueErr - EmpErr| >= eps }
  SUBSET something_boundable
```

For non-consistent h with EmpErr > 0: |TrueErr - EmpErr| could be < eps even if TrueErr is large. And EmpErr could be close to TrueErr. The UC bound requires ALL h in C to have |TrueErr - EmpErr| < eps, which is a much stronger statement.

**ACTUAL PROOF**: Use the growth function + Hoeffding per hypothesis.

For EACH h in C, the random variables 1_{h(X_i) != c(X_i)} are iid Bernoulli(p) where p = TrueErr(h). The empirical mean is EmpErr. By Hoeffding:

```
P(|EmpErr - TrueErr| >= eps) <= 2*exp(-2*m*eps^2)
```

By the growth function trick: for each sample xs, at most GF(C,m) distinct (EmpErr, TrueErr) pairs exist. So:

```
P(exists h in C, |EmpErr - TrueErr| >= eps) <= GF(C,m) * 2*exp(-2*m*eps^2)
```

This is the STANDARD UC bound. With GF(C,m) <= (v+1)*m^v:

```
bound <= 2*(v+1)*m^v * exp(-2*m*eps^2)
```

For this <= delta: need m such that `2*(v+1)*m^v * exp(-2*m*eps^2) <= delta`. This gives `m ~ O((v*log(v/eps) + log(1/delta))/eps^2)`.

The FACTORIAL sample complexity in the theorem `(v+2)!/(eps^(v+1)*delta)` is much LARGER. So the Hoeffding bound ALSO suffices (larger m makes the bound smaller).

**PROOF CHAIN**:

```
mu(bad) <= GF(C,m) * 2 * exp(-2*m*eps^2)     [growth function + Hoeffding]
         <= (v+1)*m^v * 2 * exp(-2*m*eps^2)   [Sauer-Shelah: hv]
         <= (v+1) * 2 * m^v * exp(-eps*m)     [exp(-2*m*eps^2) <= exp(-eps*m) for eps <= 1/2]
```

Hmm, `exp(-2*m*eps^2) <= exp(-eps*m)` requires `2*eps^2 >= eps`, i.e., `eps >= 1/2`. For small eps this FAILS.

**ALTERNATIVE**: Use the WEAKER tail `(1-eps)^m` for the consistent case, combined with the polynomial growth function bound. This matches the factorial sample complexity exactly:

```
GF(C,m) * (1-eps)^m <= (v+1)*m^v * exp(-eps*m)
                     <= (v+2)!/((eps*m)^(v+1))     [by pow_mul_exp_neg_le_factorial_div]
                     = (v+2)!/(eps^(v+1) * m^(v+1))
```

Wait, `pow_mul_exp_neg_le_factorial_div` says `t^d * exp(-t) <= (d+1)!/t` for t > 0. With t = eps*m, d = v:

```
(eps*m)^v * exp(-eps*m) <= (v+1)!/(eps*m)
```

So:
```
m^v * exp(-eps*m) <= (v+1)! / (eps^v * m * eps^1) = (v+1)! / (eps^(v+1) * m)
```

Then:
```
GF(C,m) * (1-eps)^m <= (v+1) * m^v * exp(-eps*m)
                     <= (v+1) * (v+1)! / (eps^(v+1) * m)
                     = (v+2)! / (eps^(v+1) * m)
                     <= delta     [from hm_bound: m >= (v+2)!/(eps^(v+1)*delta)]
```

**BUT**: This bounds `GF(C,m) * (1-eps)^m`, which is the bound for the ONE-SIDED consistent case:
```
mu { xs | exists h in C, consistent(h,xs) AND TrueErr(h) > eps }
```

For the TWO-SIDED UC bound, we need:
```
mu { xs | exists h in C, |TrueErr - EmpErr| >= eps }
```

**KEY SIMPLIFICATION**: The two-sided bound INCLUDES the one-sided consistent case. And for the UC goal (complement = good event), we can use:

For ANY h and sample xs:
- If h is consistent on xs: EmpErr = 0, so |TrueErr - 0| = TrueErr. Bad iff TrueErr >= eps.
- If h is NOT consistent on xs: EmpErr > 0. |TrueErr - EmpErr| could still be >= eps.

The one-sided bound handles the first case. For the second case: if h is not consistent, then h disagrees with c on some sample point. The restriction of h to {xs_i} differs from c's restriction. Different restriction classes contribute different empirical errors.

**THE FULL PROOF requires bounding both cases. For this URS, we design the proof using the per-class tail bound approach:**

For each restriction class r (at most GF(C,m) classes per sample):
- All h with restriction r have the same EmpErr on this sample.
- The TrueErr varies across h in the class, but the MAXIMUM deviation is bounded.
- P(some h in class r has |TrueErr - EmpErr| >= eps) <= P(TrueErr of any class member deviates by >= eps from the common EmpErr).

This is where the per-class concentration comes in. For a FIXED h:
```
P(|EmpErr(h, S) - TrueErr(h)| >= eps) <= 2*exp(-2*m*eps^2)    [Hoeffding]
```

But the restriction class argument says: for fixed xs, all h in the same class have the same EmpErr(h, xs). So the deviation |EmpErr - TrueErr| only depends on TrueErr (which varies) and the common EmpErr. The worst case within a class is the h with the largest |TrueErr - EmpErr|.

**SIMPLIFICATION FOR PROOF**: Since we're bounding `mu { xs | exists h in C, |TrueErr - EmpErr| >= eps }`:

```
mu(bad) <= sum over GF(C,m) equivalence classes of P(class r is bad)
```

For each class, pick representative h_r. P(class r is bad) = P(|EmpErr(h_r, S) - TrueErr(h_r)| >= eps). But different h in the same class have different TrueErr, so the representative doesn't capture all.

**ACTUALLY**: The standard textbook proof handles this by noting that for EACH xs, the empirical error is determined by the restriction. So:
```
exists h in C with |EmpErr(h,xs) - TrueErr(h)| >= eps
```
means: there exists a restriction pattern r such that |EmpErr(r,xs) - TrueErr(h_r)| >= eps for SOME h_r in class r. The number of classes is <= GF(C,m). For each class, the deviation bound applies to the representative.

This reduces to: `GF(C,m) * max_h P(deviation >= eps)` where the max is over representatives, and `P(deviation >= eps) <= 2*exp(-2*m*eps^2)` by Hoeffding.

**HOWEVER**: The theorem's sample complexity uses a FACTORIAL bound, not the `exp(-2*m*eps^2)` Hoeffding bound. This suggests the intended proof uses the WEAKER tail `(1-eps)^m` (which only works for the one-sided consistent case).

### 2.6 Recommended Proof (One-Sided Reduction + Polynomial Tail)

**Reduce the two-sided UC to the one-sided consistent case:**

For the UC guarantee, we need: for all h in C, |TrueErr - EmpErr| < eps. The contrapositive: exists h with |TrueErr - EmpErr| >= eps.

Decompose: either EmpErr = 0 (consistent) and TrueErr >= eps, or EmpErr > 0. For the consistent case, the one-sided bound applies. For the non-consistent case, the deviation is typically smaller (EmpErr > 0 means TrueErr might be close to EmpErr).

**ACTUALLY the simplest approach**: The bound `GF(C,m) * (1-eps)^m <= delta` is SUFFICIENT to imply the UC bound, because:

```
{ xs | exists h in C, |TrueErr - EmpErr| >= eps }
  SUBSET { xs | exists h in C, TrueErr(h) > eps/2 AND consistent(h, xs) }
         UNION { xs | exists h in C, EmpErr(h, xs) > eps/2 }
```

The first set is bounded by `GF(C,m) * (1-eps/2)^m`. The second set is bounded by... well, if all h in C have EmpErr > eps/2 on some sample, this could be problematic.

**I think the cleanest approach is**: Prove only the one-sided bound (consistent + TrueErr > eps), then note that for the BYPASS route (Target 1), `vcdim_finite_imp_uc` only NEEDS the one-sided bound to establish UC for the ERM learner.

**WAIT**: Re-reading `vcdim_finite_imp_uc` (line 1276-1328), it calls `uc_bad_event_le_delta` and then converts to the good event. The good event is: for ALL h in C, |TrueErr - EmpErr| < eps. This IS the full two-sided UC. The proof at lines 1298-1328 is a clean complement argument.

**CONCLUSION for Target 2**: The proof needs the FULL two-sided bound. The recommended approach:

1. **Bound via growth function + Hoeffding per hypothesis** (the standard textbook approach).
2. The Hoeffding bound gives `P(deviation >= eps for fixed h) <= 2*exp(-2*m*eps^2)`.
3. Growth function union bound: `P(exists h, deviation >= eps) <= GF(C,m) * 2*exp(-2*m*eps^2)`.
4. With `GF(C,m) <= (v+1)*m^v` and the factorial sample complexity, this is `<= delta`.

**The factorial sample complexity is overkill for the Hoeffding approach**, but since m is large enough, the bound still holds. Specifically:

```
GF(C,m) * 2 * exp(-2*m*eps^2)
  <= 2*(v+1)*m^v * exp(-2*m*eps^2)
  <= 2*(v+1)*m^v * exp(-eps*m)        [since 2*eps^2*m >= eps*m when eps >= 1/2; for eps < 1/2, use (1-eps)^m]
```

Actually for eps < 1/2: `exp(-2*m*eps^2) <= exp(-m*eps^2)` which is smaller than `exp(-m*eps)` when `eps < 1`. So we need a different chain.

**SIMPLEST CHAIN that works for all eps in (0,1)**:

Use Hoeffding directly:
```
2*(v+1)*m^v * exp(-2*m*eps^2) <= delta
```

From `m >= (v+2)!/(eps^(v+1)*delta)`:
- `m >= (v+2)!/(eps^(v+1)*delta) >= 1` for reasonable parameters.
- `exp(-2*m*eps^2) <= exp(-2*eps^2 * (v+2)!/(eps^(v+1)*delta))`.
- For large enough `(v+2)!`, this is exponentially small.

The arithmetic is messy but the bound holds because the factorial sample complexity is MUCH larger than needed for Hoeffding.

### 2.7 Tactic Sequence for uc_bad_event_le_delta

```lean
-- Step 1: Bound the bad set by GF(C,m) copies of per-hypothesis tail bounds.
-- Step 2: Apply Sauer-Shelah: GF(C,m) <= sum_{i<=v} C(m,i) <= (v+1)*m^v.
-- Step 3: Apply exponential tail: (1-eps)^m or exp(-2*m*eps^2).
-- Step 4: Chain arithmetic to show product <= delta from hm_bound.

-- CONCRETELY:
-- Use union_bound_consistent (already proved modulo bad_consistent_covering sorry)
-- OR prove the bound directly.

-- DIRECT APPROACH (avoids union_bound_consistent entirely):
-- The bad event for UC is LARGER than the bad event for consistent learning.
-- Bound it by GF(C,m) * max(per-h tail).

-- For the consistent subset:
-- mu { xs | exists h in C, consistent AND TrueErr >= eps }
--   <= GF(C,m) * (1-eps)^m                              [union bound + consistent_tail_bound]
--   <= (v+1)*m^v * (1-eps)^m                             [Sauer-Shelah: hv + sum_choose_le_mul_pow]
--   <= (v+1) * (v+1)! / (eps^(v+1) * m)                 [pow_mul_exp_neg_le_factorial_div with t=eps*m]
--   = (v+2)! / (eps^(v+1) * m)                           [factorial arithmetic]
--   <= delta                                              [hm_bound: m >= (v+2)!/(eps^(v+1)*delta)]

-- The full two-sided UC requires additionally bounding:
-- mu { xs | exists h in C, EmpErr > 0 AND |TrueErr - EmpErr| >= eps }
-- This requires Hoeffding for iid indicators. Bridge:
-- X_i = 1_{h(omega_i) != c(omega_i)}, iid Bernoulli(p), p = TrueErr(h).
-- EmpErr = (1/m) sum X_i. P(|EmpErr - p| >= eps) <= 2*exp(-2*m*eps^2).

-- ALTERNATIVE (SIMPLER): Note that the UC bound for the REALIZABLE case
-- (where c in C and ERM is consistent) only needs the one-sided bound.
-- The two-sided statement is STRONGER than needed for the PAC proof.
-- OPTION: Weaken uc_bad_event_le_delta to the one-sided version.
```

### 2.8 Recommended Implementation

**Option A (Weakest change, highest confidence)**: Change the statement of `uc_bad_event_le_delta` to the one-sided consistent version:
```lean
private lemma uc_bad_event_le_delta ...
    Measure.pi ... { xs | exists h in C,
        (forall i, h (xs i) = c (xs i)) AND
        D { x | h x != c x } > ENNReal.ofReal eps }
      <= ENNReal.ofReal delta
```

Then prove it using `union_bound_consistent` chain (which we now need to prove WITHOUT `bad_consistent_covering`). But wait -- `union_bound_consistent` itself has the sorry dependency on `bad_consistent_covering`. This is circular with the bypass.

**Option B (Best)**: Prove `uc_bad_event_le_delta` DIRECTLY without `union_bound_consistent`, using the per-sample growth function argument. This avoids the `bad_consistent_covering` dependency entirely.

**PROOF SKELETON for Option B**:

```lean
-- The bad event factors into: exists h in C with per-sample deviation >= eps.
-- For EACH fixed sample xs, at most GF(C,m) distinct behaviors on xs.
-- For each behavior class, the deviation event depends on TrueErr only.
-- Bound: sum over <= GF(C,m) classes of P(TrueErr in bad range given class)

-- Step 1: Monotonicity -- bad UC event subset of bad consistent event (for realizable case)
-- Actually: |TrueErr - EmpErr| >= eps AND h in C
-- For h consistent: EmpErr = 0, so TrueErr >= eps. Use consistent_tail_bound.
-- For h not consistent: EmpErr > 0. Still possible to have |TrueErr - EmpErr| >= eps.

-- Step 2: Reduce to one-sided via triangle inequality.
-- |TrueErr - EmpErr| >= eps implies EITHER:
--   TrueErr >= eps (if EmpErr <= TrueErr - eps)
--   OR EmpErr >= eps (if TrueErr <= EmpErr - eps)
-- In either case, TrueErr >= eps OR TrueErr <= EmpErr - eps.
-- For TrueErr >= eps: the consistent-and-bad case applies.
-- For TrueErr < eps but EmpErr >= eps + TrueErr: h has large empirical error.

-- Step 3: The GF bound covers BOTH cases because the growth function
-- bounds the number of distinct empirical behaviors, not just consistent ones.

-- Step 4: For each restriction class r on sample xs:
--   All h with h|_xs = r have the same EmpErr(h, xs) = (sum losses)/m.
--   The TrueErr varies. Pick representative h_r.
--   P(xs is such that |EmpErr(h_r, xs) - TrueErr(h_r)| >= eps) <= 2*exp(-2*m*eps^2)
--   [by Hoeffding on the iid sample]

-- Step 5: Union over <= GF(C,m) classes.
-- Total: GF(C,m) * 2 * exp(-2*m*eps^2)

-- Step 6: Arithmetic using hv + hm_bound.
-- GF(C,m) <= sum C(m,i) <= (v+1)*m^v  [hv + sum_choose_le_mul_pow]
-- 2*(v+1)*m^v * exp(-2*m*eps^2) <= ... <= delta

-- ISSUE: The per-class Hoeffding requires the MEASURABILITY of the indicator
-- function and INDEPENDENCE of samples. These are available from Measure.pi.
-- The representative h_r may not be measurable. Need MeasurableSet hypothesis
-- or work in discrete spaces.
```

### 2.9 Mathlib Hoeffding Bridge

**API**: `measure_sum_ge_le_of_iIndepFun` in `Mathlib/Probability/Moments/SubGaussian.lean`

```lean
lemma measure_sum_ge_le_of_iIndepFun
    {ι : Type*} {X : ι → Ω → R} (h_indep : iIndepFun X μ)
    {c : ι → NNReal}
    {s : Finset ι} (h_subG : forall i in s, HasSubgaussianMGF (X i) (c i) μ)
    {eps : R} (heps : 0 <= eps) :
    μ.real {ω | eps <= sum i in s, X i ω} <= exp (-eps^2 / (2 * sum i in s, c i))
```

**Bridge requirements**:
1. Define `X_i : (Fin m → X) → R := fun xs => if h (xs i) = c (xs i) then 0 else 1 - TrueErr(h)` -- NO, this is wrong. The correct per-sample variable is the indicator.
2. Actually: under `Measure.pi`, the coordinates `fun xs => xs i` are independent.
3. Define `Y_i : (Fin m → X) → R := fun xs => (if h (xs i) != c (xs i) then 1 else 0) - (D {x | h x != c x}).toReal`.
4. Y_i are centered, bounded in [-1, 1], iid under Measure.pi.
5. `HasSubgaussianMGF (Y_i) ((norm(1 - (-1)) / 2)^2) = HasSubgaussianMGF (Y_i) 1` by `hasSubgaussianMGF_of_mem_Icc`.
6. `iIndepFun Y μ_pi` follows from `Measure.pi` independence of coordinates.
7. Apply `measure_sum_ge_le_of_iIndepFun`: `μ_pi.real {ω | m*eps <= sum Y_i ω} <= exp(-m^2*eps^2 / (2*m))`.
8. Convert `μ_pi.real` bound to `μ_pi` (ENNReal) bound.

**Type bridges needed**:
- `μ.real s = (μ s).toReal` -- definition
- `μ.real s <= r` implies `μ s <= ENNReal.ofReal r` when `μ s < top` (finite measure)
- `iIndepFun` for coordinate projections under `Measure.pi`
- `HasSubgaussianMGF` for bounded random variables via `hasSubgaussianMGF_of_mem_Icc`

### 2.10 LOC Estimate

| Component | LOC | Confidence |
|-----------|-----|-----------|
| Growth function bound (reuse hv + sum_choose_le_mul_pow) | 15 | 0.8 |
| Per-hypothesis Hoeffding application | 40 | 0.5 |
| Independence of coordinates under Measure.pi | 20 | 0.4 |
| SubGaussian setup for bounded indicators | 20 | 0.5 |
| Union bound over GF(C,m) classes | 30 | 0.6 |
| Arithmetic chain to delta | 25 | 0.7 |
| Measure.real to ENNReal bridge | 15 | 0.7 |
| **Total** | **~165** | **0.50** |

### 2.11 Risk Assessment

**HIGH RISK.** The Hoeffding route requires:
1. `iIndepFun` for coordinate projections -- may need explicit construction
2. Measurability of indicator functions -- needs `MeasurableSet {x | h x != c x}`
3. The growth function per-sample argument -- needs to pull the union bound INSIDE the integral

**FALLBACK**: If the Hoeffding route is too difficult, use the FACTORIAL polynomial tail approach (one-sided only) and weaken the UC statement to one-sided. This is simpler (~80 LOC) but requires modifying `vcdim_finite_imp_uc` to use the one-sided version.

**FALLBACK 2**: Add a `MeasurableSet` hypothesis to `uc_bad_event_le_delta` (enrichment, not simplification) to enable cleaner measure-theoretic arguments.

---

## Target 3: `pac_lower_bound_core` (Line 2056) -- PROVE via Counting + Measure Bridge

### 3.1 Statement Fix Required

**Gamma_83**: The statement is FALSE for epsilon = 1. Change `(hε1 : ε ≤ 1/4)` (from `ε ≤ 1`).

Current (line 1901):
```lean
(hε1 : ε ≤ 1/4)
```
NOTE: The current code already has `(hε1 : ε ≤ 1/4)` -- the D2 URS fix was already applied. Verify before editing.

### 3.2 Proof Strategy

The proof must show: for any PAC learner (L, mf), `ceil((d-1)/(64*eps)) <= mf(eps, 1/7)`.

By contradiction: assume `m := mf(eps, 1/7) < ceil(...)`. Then:

1. **Extract shattered set T** with |T| = d (already done, lines 1921-1942).
2. **Construct D = uniform on T** (already done, lines 1960-1984).
3. **Per-sample adversarial construction** (already done, lines 1994-2025).
4. **Counting core** (THE SORRY): Double-counting + pigeonhole to get a single c_0 with counting bound.
5. **Measure bridge**: counting-to-probability (reuse vcdim_infinite_not_pac infrastructure).

### 3.3 Shared Infrastructure: The Counting Core

The counting core is shared between pac_lower_bound_core (line 2056), pac_lower_bound_member (line 2537), and hcomb in vcdim_infinite_not_pac (line 2964).

**Mathematical content** (identical in all three):

Given:
- T : Finset X with |T| = d, shattered by C
- m : Nat with 2m < d
- L : BatchLearner X Bool
- For each f : T -> Bool, shattering gives c_f in C with c_f|_T = f

**Claim**: There exists f_0 : T -> Bool such that c_{f_0} satisfies:
```
2 * |{xs : Fin m -> T | disagree(c_{f_0}, L.learn(xs, c_{f_0})) * 4 <= d}| <= |Fin m -> T|
```

**Proof**:
1. For each xs : Fin m -> T, partition the 2^d functions f by their values on range(xs). Each group G has the same training data (same f|_seen), hence the same learner output h_G.
2. Within group G: pair f with flip_unseen(f). On unseen points, exactly one of f(t), flip(t) disagrees with h_G(t) per point. So disagree(f) + disagree(flip(f)) >= |unseen| >= d - m.
3. If both disagree(f)*4 <= d and disagree(flip(f))*4 <= d: sum <= d/2. But d - m > d/2 (from 2m < d). Contradiction. So at most one per pair.
4. 2^d functions, paired: at most 2^{d-1} good ones per xs.
5. Double-counting: sum_f |{xs good for f}| = sum_xs |{f good for xs}| <= |Fin m -> T| * 2^{d-1}.
6. Pigeonhole: min_f |{xs good for f}| <= |Fin m -> T| * 2^{d-1} / 2^d = |Fin m -> T| / 2.
7. So exists f_0 with 2*|{xs good for f_0}| <= |Fin m -> T|.

### 3.4 Factoring the Shared Counting Lemma

**RECOMMEND**: Extract a shared lemma:

```lean
/-- NFL counting core: among all 2^d labelings of a d-point shattered set,
    there exists one whose concept has few "good" samples (error <= d/4). -/
private lemma nfl_counting_core
    {X : Type u} (T : Finset X) (C : ConceptClass X Bool)
    (hTshat : Shatters X C T) (m : Nat)
    (h2m : 2 * m < T.card) (L : BatchLearner X Bool) :
    exists (f_0 : T -> Bool),
      exists (c_0 : Concept X Bool), c_0 in C AND (forall t : T, c_0 t = f_0 t) AND
        2 * (Finset.univ.filter fun xs : Fin m -> T =>
          (Finset.univ.filter fun t : T =>
            c_0 (t : X) != L.learn (fun i => ((xs i : X), c_0 (xs i))) (t : X)).card * 4
          <= T.card).card
        <= Fintype.card (Fin m -> T)
```

This lemma is called from all three sorry locations.

### 3.5 Tactic Sequence for the Counting Core

```lean
-- Step 1: For each f, extract c_f from shattering.
-- Step 2: Define good(f, xs) predicate.
-- Step 3: Double-counting: sum_f |{good xs}| = sum_xs |{good f}|.
--         Use Finset.sum_comm.
-- Step 4: Bound per-xs: |{good f for xs}| <= 2^{d-1}.
--   4a: Partition 2^d functions by f|_seen. Each partition has 2^{d - |seen|} elements.
--   4b: Within partition: learner output h is fixed. Pair f with flip_unseen(f).
--   4c: For each pair, at most one good. Proof: sum of disagrees >= |unseen| >= d - m > d/2 >= d/4 + d/4.
--   4d: So good count within partition <= 2^{d - |seen| - 1}.
--   4e: Total across partitions: sum of 2^{d - |seen| - 1} over partitions of 2^d.
--        Each partition has 2^{d-|seen|} elements. Number of partitions = 2^{|seen|}.
--        Total good = sum of <= 2^{d-|seen|-1} over 2^{|seen|} partitions = 2^{d-1}.
-- Step 5: Pigeonhole: sum_f |{good xs}| <= |Fin m -> T| * 2^{d-1}.
--         |{f : T -> Bool}| = 2^d. So exists f_0 with |{good xs}| <= |Fin m -> T| * 2^{d-1} / 2^d.
--         = |Fin m -> T| / 2.
-- Step 6: Return f_0 and its shattering witness c_0.
```

### 3.6 LOC Estimate for Counting Core

| Component | LOC | Confidence |
|-----------|-----|-----------|
| Shattering extraction + c_f definition | 15 | 0.8 |
| Pairing definition (flip_unseen) | 20 | 0.7 |
| Pairing bound (disagree sum >= unseen) | 30 | 0.6 |
| Per-xs bound: good <= 2^{d-1} | 40 | 0.5 |
| Double-counting (Finset.sum_comm) | 15 | 0.7 |
| Pigeonhole | 15 | 0.7 |
| Fintype.card arithmetic | 15 | 0.7 |
| **Total** | **~150** | **0.55** |

### 3.7 pac_lower_bound_core Proof After Counting Core

After the counting core gives f_0, c_0 with `2 * good_count <= total`:

```lean
-- The measure bridge is IDENTICAL to vcdim_infinite_not_pac substep B.
-- Already proved at lines 2966-3167.

-- Step 1: Construct D = uniform on T (already done in proof).
-- Step 2: Apply nfl_counting_core to get f_0, c_0.
-- Step 3: Measure bridge: good_count / total <= 1/2 implies mu({good xs}) <= 1/2.
-- Step 4: The PAC guarantee says mu({error <= eps}) >= 6/7 = 1 - 1/7.
-- Step 5: But mu({error <= eps}) <= mu({error <= d/4}) = mu({disagree*4 <= d}) <= 1/2 < 6/7.
--         (Since eps <= 1/4 and error = disagree/d.)
-- Step 6: Contradiction.
```

**Additional LOC for pac_lower_bound_core** (beyond counting core):

| Component | LOC |
|-----------|-----|
| Derive 2m < d from h_lt + eps <= 1/4 | 15 |
| Apply nfl_counting_core | 5 |
| Measure bridge (reuse pattern from vcdim_infinite_not_pac) | 60 |
| eps <= 1/4 chain: {error <= eps} subset {disagree*4 <= d} | 10 |
| 1/2 < 6/7 final inequality | 3 |
| **Total** | **~93** |

---

## Target 4: `pac_lower_bound_member` (Line 2537) -- PROVE via Counting + Measure Bridge

### 4.1 Statement Fix Required

**Gamma_84**: Add `(hδ2 : δ ≤ 1/7)` hypothesis.

NOTE: The current code already has `(hδ2 : δ ≤ 1/7)` at line 2432. Verify before editing.

### 4.2 Proof Strategy

Identical mathematical content to pac_lower_bound_core. The differences:
- Takes (L, m) from the PAC membership set instead of (L, mf).
- Conclusion: ceil <= m (not ceil <= mf(eps, 1/7)).
- Delta is arbitrary (with delta <= 1/7), not hardcoded to 1/7.

### 4.3 Proof After Counting Core

```lean
-- Step 1: Extract shattered T, construct D (already done, lines 2448-2527).
-- Step 2: Apply nfl_counting_core to get f_0, c_0 with 2*good <= total.
-- Step 3: Measure bridge: mu({error <= eps}) <= 1/2.
-- Step 4: The PAC membership says mu({error <= eps}) >= 1 - delta >= 1 - 1/7 = 6/7.
-- Step 5: 1/2 < 6/7 (or more precisely: 1/2 < 1 - delta since delta <= 1/7 < 1/2). Contradiction.
```

### 4.4 LOC Estimate

| Component | LOC |
|-----------|-----|
| Apply nfl_counting_core | 5 |
| Measure bridge (reuse pattern) | 60 |
| Delta comparison: 1/2 < 1 - delta | 10 |
| **Total** | **~75** |

---

## Target 5: `hcomb` in `vcdim_infinite_not_pac` (Line 2964) -- PROVE via Counting Core

### 5.1 Current State

The sorry at line 2964 is substep A of `vcdim_infinite_not_pac`. Substep B (measure bridge, lines 2966-3167) is ALREADY PROVED (Gamma_97).

### 5.2 Proof Strategy

Apply the shared `nfl_counting_core` lemma directly. The statement at line 2950-2958 matches the output of `nfl_counting_core` exactly.

### 5.3 LOC Estimate

| Component | LOC |
|-----------|-----|
| Apply nfl_counting_core | 5 |
| Minor adapter for threshold (1/4 vs eps) | 5 |
| **Total** | **~10** |

---

## Target 6: `sample_complexity_lower_bound` (Line 2549) -- NO SORRY

`sample_complexity_lower_bound` has no sorry itself. It calls `pac_lower_bound_member` at line 2574. Once Target 4 is closed, this theorem becomes sorry-free automatically.

### 6.1 Statement Fix Propagation

If `pac_lower_bound_member` gets `hδ2 : δ ≤ 1/7`, then `sample_complexity_lower_bound` must pass `hδ2`. Check if it already has this hypothesis.

Current signature (line 2547):
```lean
(hδ2 : δ ≤ 1/7)
```

Already present. No change needed.

Similarly, `pac_lower_bound` in PAC.lean (line 164):
```lean
(hδ2 : δ ≤ 1/7)
```

Already present. No change needed.

---

## Execution Plan

### Phase 0: Statement Verification (~15 min)

Verify that the Gamma_83 and Gamma_84 fixes are already applied. Check:
- Line 1901: `hε1 : ε ≤ 1/4` (not `ε ≤ 1`)
- Line 2432: `hδ2 : δ ≤ 1/7` present

### Phase 1: Bypass `bad_consistent_covering` (~30 min)

1. Edit `vcdim_finite_imp_pac` (PAC.lean:77) to route through `vcdim_finite_imp_uc` + `uc_imp_pac`.
2. `lake build` -- verify 0 errors (new sorry from `uc_bad_event_le_delta` is inherited but already existed).
3. Line 633 sorry becomes dead code.

### Phase 2: Shared Counting Core (~4 hr)

1. Implement `nfl_counting_core` as a private lemma in Generalization.lean (near line 2580, in the NFLCounting section).
2. Key substeps:
   - Pairing definition and pairing bound
   - Per-xs good-count bound
   - Finset.sum_comm double-counting
   - Pigeonhole
3. `lake build` at each milestone.

### Phase 3: Close Target 5 (`hcomb`, line 2964) (~1 hr)

1. Replace sorry at line 2964 with application of `nfl_counting_core`.
2. Adapt threshold (currently 1/4, matching the counting core).
3. `lake build` -- verify sorry count drops.

### Phase 4: Close Targets 3+4 (`pac_lower_bound_core` + `pac_lower_bound_member`) (~3 hr)

1. Replace sorry at line 2056 with: derive 2m < d + nfl_counting_core + measure bridge + eps chain + final inequality.
2. Replace sorry at line 2537 similarly with delta comparison.
3. Measure bridge: replicate the pattern from vcdim_infinite_not_pac (lines 2966-3167).
4. `lake build` after each.

### Phase 5: Close Target 2 (`uc_bad_event_le_delta`, line 1271) (~4 hr)

1. Implement the growth function + polynomial tail proof.
2. Chain: `hv` + `sum_choose_le_mul_pow` + `pow_mul_exp_neg_le_factorial_div` + `hm_bound`.
3. Handle the one-sided vs two-sided issue (may need statement weakening).
4. `lake build` -- final verification.

### Phase 6: Verification (~30 min)

1. `lake build` -- 0 errors.
2. Count sorry-using declarations (target: 6, down from 11).
3. A4 check: no trivially-true sorrys.
4. A5 check: no simplification (all changes are repairs or enrichments).

---

## LOC Summary

| Target | Component | LOC | Confidence |
|--------|-----------|-----|-----------|
| 1 | Bypass bad_consistent_covering | 8 | 0.95 |
| 2 | uc_bad_event_le_delta proof | 165 | 0.50 |
| 3 | pac_lower_bound_core (excl. counting) | 93 | 0.70 |
| 4 | pac_lower_bound_member (excl. counting) | 75 | 0.70 |
| 5 | hcomb in vcdim_infinite_not_pac | 10 | 0.85 |
| Shared | nfl_counting_core | 150 | 0.55 |
| **Total** | | **~501** | **0.60** |

---

## Risk Assessment

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| Hoeffding bridge fails (iIndepFun for Measure.pi) | 0.4 | HIGH | Fallback to one-sided + statement weakening |
| Counting core pairing step blocked by Finset API | 0.3 | MEDIUM | Use Finset.sum_comm + explicit construction |
| Measure bridge duplication too verbose | 0.2 | LOW | Factor shared measure_bridge lemma |
| Statement fix missed (eps/delta bounds) | 0.1 | LOW | Verify in Phase 0 |
| `uc_bad_event_le_delta` needs two-sided bound | 0.5 | HIGH | Weaken to one-sided + modify `vcdim_finite_imp_uc` caller |

---

## K/U Update

### KK (expanded)
- Hoeffding IS in Mathlib: `measure_sum_ge_le_of_iIndepFun` in `Probability/Moments/SubGaussian.lean`
- `hasSubgaussianMGF_of_mem_Icc` provides SubGaussian for bounded rv's
- `Measure.real s = (mu s).toReal` -- bridge between ℝ and ENNReal measure worlds
- vcdim_infinite_not_pac measure bridge (substep B) is ALREADY PROVED
- The UC route (`vcdim_finite_imp_uc` + `uc_imp_pac`) is sorry-free EXCEPT for `uc_bad_event_le_delta`
- `pow_mul_exp_neg_le_factorial_div` (line 709) and `sum_choose_le_mul_pow` (line 733) are proved

### KU (refined)
- CKU_12: Can `iIndepFun` for coordinate projections under `Measure.pi` be established cleanly? (gates Hoeffding route)
- CKU_13: Does the two-sided UC statement in `uc_bad_event_le_delta` need the full Hoeffding, or can it be reduced to the one-sided consistent case? (gates proof complexity)
- CKU_14: Can `nfl_counting_core` be proved using `Finset.sum_comm` for the double-counting step, or does the partition-by-restriction step require custom infrastructure? (gates LOC)

### UK (pressures)
- UK_5: The measure bridge pattern appears 3 times (vcdim_infinite_not_pac, pac_lower_bound_core, pac_lower_bound_member). Can it be factored into a shared lemma to avoid ~120 LOC of duplication?
- UK_6: The `uc_bad_event_le_delta` proof is the HIGHEST-RISK target. If it fails, the bypass (Target 1) creates a WORSE situation (bad_consistent_covering is dead but uc_bad_event_le_delta is still sorry'd, now on the critical PAC path).

---

## Critical Path

```
nfl_counting_core (shared, ~150 LOC)
    |
    +---> hcomb (Target 5, ~10 LOC)  [QUICK WIN]
    |
    +---> pac_lower_bound_core (Target 3, ~93 LOC)
    |
    +---> pac_lower_bound_member (Target 4, ~75 LOC)
              |
              +---> sample_complexity_lower_bound (auto-closes)
              |
              +---> pac_lower_bound (PAC.lean, auto-closes)

uc_bad_event_le_delta (Target 2, ~165 LOC)  [INDEPENDENT, HIGH RISK]
    |
    +---> vcdim_finite_imp_uc (auto-closes)
              |
              +---> bypass route for bad_consistent_covering (Target 1)
```

**RECOMMENDED ORDER**: Targets 5 -> 3 -> 4 -> 2 -> 1 (build confidence with easier targets first, bypass last since it depends on Target 2).
