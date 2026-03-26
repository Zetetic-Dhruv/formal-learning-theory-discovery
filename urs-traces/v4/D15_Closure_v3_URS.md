# D15 Closure v3 URS: Complete Route Analysis for uc_bad_event_le_delta + sample_complexity_upper_bound

## Will

Identify the INVARIANT proof route for closing `uc_bad_event_le_delta` (Gen:1270-1283) and `sample_complexity_upper_bound` (Bridge:621-657). These are the only sorrys blocking quantitative PAC theory through the UC chain.

## Date: 2026-03-20

---

## 0. Sorry Census (Exact)

| # | Sorry | File:Line | Caller | Status |
|---|-------|-----------|--------|--------|
| S1 | `bad_consistent_covering` | Gen:639 | DEAD CODE (commented block Gen:618-713) | DEAD (bypassed by UC route, Gamma_92) |
| S2 | `uc_bad_event_le_delta` | Gen:1283 | `vcdim_finite_imp_uc` (Gen:1308) | CRITICAL PATH |
| S3 | `vcdim_finite_imp_compression` | Gen:2263 | `fundamental_vc_compression` (PAC.lean:187) | DEEP/OPEN (Moran-Yehudayoff) |
| S4 | `pac_lower_bound_member` | Gen:2680 | `sample_complexity_lower_bound` (Gen:2718) | NFL lower bound |
| S5 | `sample_complexity_upper_bound` | Bridge:657 | `pac_lower_bound` (PAC.lean:172) via `sample_complexity_lower_bound` | BLOCKED by S2 |

Total: 5 sorry-using declarations (4 in Generalization.lean, 1 in Bridge.lean).
S1 is dead code. S3 is deep/open (not targeted). S4 has complete infrastructure (nfl_counting_core proved, measure bridge pattern proved in pac_lower_bound_core). S2 is the critical blocker. S5 depends on S2.

---

## 1. Complete KK Universe (Converted from UK)

### 1.1 Existing KK (Verified with Exact Line Numbers)

| ID | Lemma | File:Line | Type Signature (compressed) | Status |
|----|-------|-----------|---------------------------|--------|
| KK1 | `consistent_tail_bound` | Gen:550-586 | `D [Prob] h c m eps (herr : D{h!=c} >= ofReal eps) -> pi {consistent} <= ofReal((1-eps)^m)` | PROVED |
| KK2 | `pow_mul_exp_neg_le_factorial_div` | Gen:717-738 | `0 < t -> t^d * exp(-t) <= (d+1)!/t` | PROVED |
| KK3 | `sum_choose_le_mul_pow` | Gen:741-754 | `1 <= m -> sum_{i<=d} C(m,i) <= (d+1)*m^d` | PROVED |
| KK4 | `vcdim_finite_imp_growth_bounded` | Gen:759-779 | `VCDim < top -> exists d, forall m >= d, GF(C,m) <= sum C(m,i)` | PROVED |
| KK5 | `uc_imp_pac` | Gen:1346-1442 | `HasUniformConvergence X C -> C.Nonempty -> PACLearnable X C` | PROVED (sorry-free) |
| KK6 | `vcdim_finite_imp_pac_via_uc` | Gen:1447-1454 | `VCDim < top -> PACLearnable` | Routes through vcdim_finite_imp_uc (S2 dep) |
| KK7 | `growth_function_le_sauer_shelah` | Bridge:465-483 | Sauer-Shelah via Mathlib bridge | PROVED |
| KK8 | `per_sample_labeling_bound` | Gen:2927-2936 | `2m < card alpha -> 2 * good_count <= card(alpha -> Bool)` | PROVED |
| KK9 | `nfl_counting_core` | Gen:3026-3160+ | `Shatters T, 2m < T.card -> exists f0 c0, 2*count <= card(Fin m -> T)` | PROVED |
| KK10 | `pac_lower_bound_core` measure bridge | Gen:2036-2198 | Full D+uniform+nfl+bridge chain for `delta=1/7` | PROVED (uses nfl_counting_core) |
| KK11 | `vcdim_infinite_not_pac` substep B | Gen:3304-end | Counting-to-Measure.pi bridge | PROVED |
| KK12 | `growth_function_cover` | Gen:600-616 | Per-sample covering: for fixed xs, exists reps with n <= GF(C,m) | PROVED (trivially: reps = {c}) |
| KK13 | `HasUniformConvergence` | Gen:1234-1245 | `forall eps delta > 0, exists m0, forall D prob, forall c m >= m0, pi{UC good} >= 1-delta` | DEFINED (two-sided, for ALL h in C) |
| KK14 | `iIndepFun_block_extract` | Gen:~3015-3057 | Block independence from product measure | PROVED |
| KK15 | `disagreement_sum_eq` | Gen:~2750 | `sum_f disagree(f,h) = n * 2^(n-1)` | PROVED |
| KK16 | `agreement_count_markov` | Gen:2860-2918 | `4 * #{f : disagree <= n/4} < 3 * 2^n` | PROVED |

### 1.2 Mathlib KK (Available, Verified Paths)

| ID | API | Module | Verified Import |
|----|-----|--------|-----------------|
| MKK1 | `measure_sum_ge_le_of_iIndepFun` | Probability.Moments.SubGaussian:779 | NOT imported in Gen.lean |
| MKK2 | `hasSubgaussianMGF_of_mem_Icc` | Probability.Moments.SubGaussian:860 | NOT imported |
| MKK3 | `iIndepFun_pi` | Probability.Independence.Basic:784 | IMPORTED (via Independence.Basic) |
| MKK4 | `Real.one_sub_le_exp_neg` | Analysis.SpecialFunctions.Log | IMPORTED |
| MKK5 | `Real.pow_div_factorial_le_exp` | Analysis.SpecialFunctions | IMPORTED (used by KK2) |
| MKK6 | `measurePreserving_piCongrLeft` | MeasureTheory.Constructions.Pi:744 | IMPORTED |
| MKK7 | `infinitePi_map_curry` | Probability.ProductMeasure:557 | IMPORTED |
| MKK8 | `Measure.pi_singleton` | MeasureTheory.Constructions.Pi | IMPORTED |

### 1.3 UK -> KK Conversions (D15 v2 Unresolved Items)

#### UK-v2-1: "Whether one-sided HasConsistentUC suffices for the PAC chain"

**RESOLVED -> KK.**

`uc_imp_pac` (Gen:1346-1442) constructs an ERM learner that is CONSISTENT with c on the sample (line 1405-1413). At line 1416, it applies `hxs h0 hh0C` where `hxs` is the UC guarantee `forall h in C, |TrueErr - EmpErr| < eps`. At line 1418-1430, it shows EmpErr = 0 (consistency), then `|TrueErr - 0| < eps`, so `TrueErr < eps`.

**KK verdict:** The UC guarantee is used ONLY for the consistent learner output h0. The full two-sided `|TrueErr - EmpErr| < eps` for ALL h in C is never exploited for non-consistent h. A weaker "consistent UC" suffices: `forall h in C, consistent(h,xs) -> TrueErr(h) < eps`.

**HOWEVER:** `HasUniformConvergence` (Gen:1234) is the DEFINED type. Changing it weakens the definition (A5 violation). The invariant route must either prove the full two-sided UC or introduce a new intermediate without modifying `HasUniformConvergence`.

#### UK-v2-2: "Whether sample_complexity_upper_bound's bound is compatible with factorial sample complexity"

**RESOLVED -> KK (INCOMPATIBLE).**

The statement at Bridge:621-625 claims `SampleComplexity <= ceil((8/eps)(d*log(2/eps) + log(2/delta)))`. This is the standard Hoeffding-based bound: `O(d/eps^2 * log(1/eps))`.

The UC proof chain uses factorial sample complexity: `(v+2)!/(eps^(v+1)*delta)`, which for v = d is `O(d!/eps^d)`.

For d >= 3 and small eps, the Hoeffding bound is SMALLER than the factorial bound. The factorial-based UC proof CANNOT certify PAC learnability at the Hoeffding sample size. The sorry at Bridge:657 requires showing PAC at the Hoeffding bound, not the factorial bound.

**KK verdict:** `sample_complexity_upper_bound` AS STATED requires EITHER:
(a) A Hoeffding-based UC proof (not factorial), which faces Gamma_92, OR
(b) A direct PAC proof at the Hoeffding bound (same difficulty), OR
(c) Changing the bound to match the factorial sample complexity (weakening the theorem).

This is a STRUCTURAL MISMATCH. The sorry cannot be closed by simply proving uc_bad_event_le_delta.

#### UK-v2-3: "Whether the two-sided UC bound is provable at all without symmetrization"

**RESOLVED -> KK (NO, for uncountable C).**

The D15 v2 URS exhaustively analyzed Routes A, A', A'', B, D, E, F. The conclusion after ~400 lines of analysis (v2 URS Section 4):

For UNCOUNTABLE concept classes C with finite VCDim, the standard textbook proof of two-sided UC requires choosing representatives that depend on the sample. This is the Gamma_92 obstruction (sample-independent reps vs sample-dependent equivalence classes).

The ONLY known correct approaches for uncountable C are:
1. **Symmetrization** (Route C): ghost sample + conditioning + per-pattern concentration
2. **Chaining / covering numbers**: metric entropy integral
3. **Rademacher complexity**: McDiarmid + Rademacher concentration

All three require infrastructure beyond what is currently proved. Symmetrization is the simplest (~190 LOC).

**KK verdict:** Without symmetrization or equivalent machinery, `uc_bad_event_le_delta` AS STATED (two-sided, arbitrary C with finite VCDim) is NOT provable using only the existing proved infrastructure.

#### UK-v2-4: "The Gamma_92 representative-selection problem"

**RESOLVED -> KK (STRUCTURAL IMPOSSIBILITY CONFIRMED, WORKAROUND EXISTS).**

Gamma_92 states: `bad_consistent_covering` is structurally unprovable because sample-independent representatives cannot cover sample-dependent equivalence classes for uncountable C.

This is confirmed by the counterexample (D01 URS line 50-55): interval classifiers on [0,1] with VCDim=1 but uncountable C. Different samples give different equivalence classes; no finite set of global representatives covers all.

**Workaround:** The UC route bypasses `bad_consistent_covering` entirely. The bypass is ALREADY IMPLEMENTED (PAC.lean:79-83 and Gen:1447-1454). The remaining issue is proving `uc_bad_event_le_delta` within the UC route, which itself faces Gamma_92 at a different level (the per-hypothesis Hoeffding + union bound argument).

The ONLY clean workaround for Gamma_92 in the UC context is symmetrization.

---

## 2. Remaining UK Items (Structural, Not Existential)

| ID | Pressure | Risk | Resolution Path |
|----|----------|------|-----------------|
| UK-v3-1 | The Hoeffding API `measure_sum_ge_le_of_iIndepFun` operates on `Measure.real`, not ENNReal. Bridge needs `mu.real s <= r -> mu s <= ofReal r` for prob measures. | LOW | ~5 LOC: use `ENNReal.ofReal_toReal` + monotonicity. Prob measure ensures `mu s < top`. |
| UK-v3-2 | `iIndepFun` for coordinate projections under `Measure.pi` is available via `iIndepFun_pi` (MKK3). But applying it to COMPOSED functions `fun omega => indicator(h(omega_i) != c(omega_i))` requires `AEMeasurable` for each composed function. | MEDIUM | Each projection `fun omega => omega i` is measurable by `measurable_pi_apply`. Composition with `fun x => if h x != c x then 1 else 0` needs measurability of `{x | h x != c x}`. WITHOUT `MeasurableSet` hypothesis on concept classes, this may fail. |
| UK-v3-3 | The symmetrization_lemma (ConcentrationAlt:136-154) proof requires either Chebyshev on the ghost sample (needing `m >= 2/eps^2`) or the iid-symmetry argument (triangle inequality + equal marginals). Both are standard but ~70 LOC. | MEDIUM | The iid-symmetry argument is cleaner: `P(|emp-true| >= eps) <= 2*P(|emp-emp'| >= eps/2)` via union bound + equal marginals. |
| UK-v3-4 | The conditioning step in symmetrization (fixing the combined sample, counting restrictions) requires either Fubini or a direct product-measure decomposition. Lean4/Mathlib has `MeasureTheory.Measure.integral_prod` but the conditioning-on-a-specific-sigma-algebra infrastructure is limited. | HIGH | Avoid explicit conditioning. Instead, use the product structure directly: `Measure.pi (D^{2m})` decomposes into independent coordinates. Group by restriction patterns using the growth function. This is doable but ~40 LOC. |
| UK-v3-5 | `sample_complexity_upper_bound` has a structural mismatch between its Hoeffding-based bound and the factorial-based UC proof. This is NOT resolvable by proving uc_bad_event_le_delta alone. | HIGH | See Route analysis. Either tighten UC sample complexity or change the upper bound statement. |

---

## 3. KU Items with Counterproof Attempts

### KU1: Is `uc_bad_event_le_delta` provable AS STATED?

**Counterproof attempt (structural argument for unprovability):**

The statement requires bounding `mu{xs | exists h in C, |TrueErr(h) - EmpErr(h,xs)| >= eps}` for ARBITRARY concept classes C with finite VCDim.

For FINITE C, this is trivially provable via union bound + Hoeffding per h.

For UNCOUNTABLE C, the bound `exists h in C` creates an uncountable union. The growth function bounds the number of RESTRICTIONS per sample, but the union bound requires sample-independent representatives (Gamma_92).

**Counter-counterproof (why it IS provable):** The symmetrization argument AVOIDS sample-independent representatives. It introduces a ghost sample, reduces to double-sample deviations, conditions on the combined sample (making the hypothesis space effectively finite per combined sample), then applies Hoeffding per pattern. This is the standard textbook proof (Shalev-Shwartz & Ben-David Theorem 6.11, via symmetrization + conditioning).

**Verdict:** `uc_bad_event_le_delta` IS provable via symmetrization. It is NOT provable via the polynomial tail chain alone (which only handles the one-sided consistent case).

### KU2: Is `sample_complexity_upper_bound` provable AS STATED?

**Counterproof attempt:**

The statement claims `SampleComplexity X C eps delta <= ceil((8/eps)(d*log(2/eps) + log(2/delta)))`.

The proof at Bridge:631 obtains `(L, mf, hpac)` from `vcdim_finite_imp_pac_via_uc`. The `mf` is an `Exists.choose` with opaque sample complexity. The existing UC proof chain uses factorial sample complexity `(v+2)!/(eps^(v+1)*delta)` which is MUCH LARGER than the Hoeffding bound in the statement.

Even after closing S2, `mf eps delta` will be `ceil((v+2)!/(eps^(v+1)*delta))`, not the Hoeffding bound. So `mf eps delta` does NOT equal the claimed bound, and the bound `SampleComplexity <= mf` does NOT give `SampleComplexity <= Hoeffding_bound`.

**However:** The proof at Bridge:650 takes a different approach -- it tries to directly show the Hoeffding bound is in the SampleComplexity set via `Nat.sInf_le`. This requires a STANDALONE PAC proof at the Hoeffding sample size, which faces the same Gamma_92 + symmetrization requirements.

**Verdict:** `sample_complexity_upper_bound` requires EITHER:
1. Tightening `uc_bad_event_le_delta`'s sample complexity from factorial to Hoeffding-based (changing the UC proof chain), OR
2. A standalone PAC proof at the Hoeffding bound (same difficulty as UC proof), OR
3. Changing the stated bound to match the factorial sample complexity.

Option 3 is A5-valid (weakening a quantitative bound is enrichment of the sorry, not simplification). Option 1 is the best long-term solution. Option 2 duplicates effort.

---

## 4. Complete Counterfactual Proof Pathways

### Route A: One-Sided Polynomial Tail (through existing infrastructure)

**Target:** Prove `uc_bad_event_le_delta` using only KK1-KK4 and the polynomial tail chain.

**Chain:**
```
GF(C,m) * (1-eps)^m
  <= (v+1)*m^v * exp(-eps*m)       [KK3 + one_sub_le_exp_neg]
  <= (v+1) * (v+1)!/(eps^(v+1)*m)  [KK2 with t = eps*m]
  = (v+2)!/(eps^(v+1)*m)
  <= delta                          [from hm_bound]
```

**Problem:** This bounds `mu{exists h consistent AND TrueErr >= eps}`, the ONE-SIDED consistent case. The statement requires the TWO-SIDED `|TrueErr - EmpErr| >= eps` for ALL h in C.

**Blocker:** The set `{exists h in C, |TrueErr - EmpErr| >= eps}` STRICTLY CONTAINS `{exists h consistent AND TrueErr >= eps}`. Non-consistent h with `|TrueErr - EmpErr| >= eps` are not covered.

**Blocker severity:** FATAL for the two-sided statement. The polynomial tail only bounds the probability that a consistent hypothesis has high true error, not the probability that any hypothesis has large empirical-true error deviation.

**Viability: 0.00 for the two-sided statement.**
**LOC: ~60 (but proves a DIFFERENT statement).**

**Tactic sketch (for the one-sided version ONLY):**
```lean
-- Step 1: The bad set is SUBSET of {exists h, consistent AND TrueErr >= eps}
-- CANNOT establish this inclusion for the two-sided statement.
-- STOP: Route A is blocked.
```

---

### Route B: Two-Sided Hoeffding per Hypothesis + Growth Function Union Bound

**Target:** For each FIXED h, apply Mathlib Hoeffding. Then union-bound over GF(C,m) classes.

**Tactic sketch:**
```lean
-- Step 1: For FIXED h in C, define Y_i(omega) = 1_{h(omega_i) != c(omega_i)} - TrueErr(h).
--   Y_i : (Fin m -> X) -> R, bounded in [-1, 1], mean 0.
-- Step 2: iIndepFun for (Y_i)_i under Measure.pi.
--   Use iIndepFun_pi (MKK3) + composition with measurable indicator.
--   REQUIRES: AEMeasurable (fun omega => if h(omega_i) != c(omega_i) then 1 else 0).
--   This needs MeasurableSet {x | h x != c x} or working with outer measure.
-- Step 3: hasSubgaussianMGF_of_mem_Icc: Y_i in [-1, 1] gives HasSubgaussianMGF Y_i 1.
-- Step 4: measure_sum_ge_le_of_iIndepFun:
--   mu.real {eps*m <= sum Y_i} <= exp(-(eps*m)^2 / (2*m)) = exp(-m*eps^2/2).
-- Step 5: Two-sided: mu.real {|sum Y_i| >= eps*m} <= 2*exp(-m*eps^2/2).
-- Step 6: Bridge: mu {bad for h} <= ofReal(2*exp(-m*eps^2/2)).
-- Step 7: Union bound over restriction classes.
--   FOR EACH xs, at most GF(C,m) distinct restrictions.
--   mu {exists h bad} <= GF(C,m) * 2 * exp(-m*eps^2/2).
-- Step 8: Arithmetic: GF(C,m) * 2 * exp(-m*eps^2/2) <= delta from hm_bound.
```

**Blockers:**
1. **AEMeasurable obstruction (UK-v3-2):** Without `MeasurableSet {x | h x != c x}`, the indicator function may not be AEMeasurable. The codebase deliberately avoids measurability assumptions on concept classes. Adding `MeasurableSet` hypotheses is enrichment (A5-valid) but propagates to all callers of `uc_bad_event_le_delta`.

2. **Gamma_92 at the union bound (FATAL):** Step 7 requires union-bounding over GF(C,m) classes. But the classes depend on the sample xs. To apply the union bound, we need sample-independent representatives. This is EXACTLY Gamma_92. The per-hypothesis Hoeffding (Steps 1-6) works for FIXED h, but the union bound over the equivalence classes requires representatives chosen BEFORE seeing xs.

**Viability: 0.10** (Gamma_92 blocks the union bound step; the per-hypothesis Hoeffding works but cannot be assembled into the full UC bound without symmetrization).

**LOC: ~120 (per-h Hoeffding) + union bound impossible without symmetrization.**

---

### Route C: Symmetrization

**Target:** Prove `uc_bad_event_le_delta` via the standard symmetrization argument.

**Component breakdown:**

**C1: Ghost sample (block_extract k=2) -- ~10 LOC, TRIVIAL.**
```lean
-- Instantiate iIndepFun_block_extract (KK14) with k=2.
-- Primary sample: block_extract 2 m omega 0 : Fin m -> X
-- Ghost sample: block_extract 2 m omega 1 : Fin m -> X
-- Independence: IMMEDIATE from iIndepFun_block_extract.
```

**C2: Symmetrization lemma -- ~70 LOC, HARDEST.**
```lean
-- Statement: P_{xs}(|EmpErr(h,xs) - TrueErr(h)| >= eps)
--   <= 2 * P_{xs,xs'}(|EmpErr(h,xs) - EmpErr(h,xs')| >= eps/2)
-- Proof route (iid-symmetry, avoiding conditional probability):
--   P(|emp-true| >= eps)
--   = E_xs[1{|emp(xs)-true| >= eps}]
--   = E_xs[E_xs'[1{|emp(xs)-true| >= eps}]]    (xs' independent)
--   By triangle: |emp(xs)-true| >= eps implies
--     |emp(xs)-emp(xs')| >= eps/2 OR |emp(xs')-true| >= eps/2
--   The second event has P_{xs'} = P_{xs} (same marginal under iid).
--   Case split: if P_{xs'}(|emp(xs')-true| >= eps/2) <= 1/2,
--     then P(|emp(xs)-emp(xs')| >= eps/2 | xs) >= 1/2 * 1{|emp(xs)-true| >= eps}
--     Integrate: P(|emp-emp'| >= eps/2) >= (1/2)*P(|emp-true| >= eps).
--   If P > 1/2: need m >= 2/eps^2 (from Chebyshev).
-- ALTERNATIVE: use the weaker 2*P bound directly from union bound + iid symmetry.
-- REQUIRES: Fubini for product measures, equal marginal argument.
-- MATHLIB: MeasureTheory.Measure.prod, Measure.pi properties.
```

**C3: Conditioning on combined sample -- ~40 LOC.**
```lean
-- After symmetrization, have P(|emp(S)-emp(S')| >= eps/2) as the target.
-- Fix combined sample z = (S, S') : Fin (2m) -> X.
-- For fixed z, the hypothesis class C restricts to at most GF(C, 2m) patterns.
-- For each pattern, EmpErr(h,S) and EmpErr(h,S') are determined by which
--   coordinates of z belong to S vs S'.
-- Use: GrowthFunction + Sauer-Shelah (KK7).
-- This step is COMBINATORIAL, not measure-theoretic.
```

**C4: Per-pattern Hoeffding -- ~50 LOC.**
```lean
-- For a FIXED restriction pattern on the combined sample z:
-- The swap indicators sigma_i in {0,1} (which half each point goes to)
--   are iid Bernoulli(1/2) CONDITIONALLY on z.
-- The difference |EmpErr(S)-EmpErr(S')| is a sum of bounded iid rv's.
-- Apply measure_sum_ge_le_of_iIndepFun (MKK1) with hasSubgaussianMGF_of_mem_Icc (MKK2).
-- Result: P(|diff| >= eps/2 | z) <= 2*exp(-m*eps^2/8).
-- CRITICAL: After conditioning on z, the variables ARE truly independent
--   and have bounded range. The measurability/AEMeasurable issues are resolved
--   because we are working on a FINITE space (permutations of z's coordinates).
-- THIS IS WHERE SYMMETRIZATION RESOLVES GAMMA_92.
```

**C5: Assembly -- ~30 LOC.**
```lean
-- P(exists h bad) <= 2 * P(exists h, |emp(S)-emp(S')| >= eps/2)
--   [C2: symmetrization]
-- <= 2 * E_z[sum over <= GF(C,2m) patterns of P(|diff| >= eps/2 | z)]
--   [C3: conditioning + union bound (NOW VALID because patterns are per-z)]
-- <= 2 * GF(C,2m) * 2*exp(-m*eps^2/8)
--   [C4: per-pattern Hoeffding]
-- = 4 * GF(C,2m) * exp(-m*eps^2/8)
-- With GF(C,2m) <= (v+1)*(2m)^v [KK3 + KK4]:
-- bound <= 4*(v+1)*(2m)^v * exp(-m*eps^2/8)
-- For m >= (v+2)!/(eps^(v+1)*delta): exponential dominates polynomial, bound <= delta.
-- [Arithmetic: (2m)^v * exp(-m*eps^2/8) <= ... via KK2 variant]
```

**Total LOC: ~200.**
**Viability: 0.55.**

**Blockers:**
1. C2 (symmetrization lemma) is non-trivial (~70 LOC).
2. C4 requires `measure_sum_ge_le_of_iIndepFun` which is NOT currently imported.
3. The arithmetic in C5 needs care: the factorial bound `(v+2)!/(eps^(v+1)*delta)` must imply `4*(v+1)*(2m)^v * exp(-m*eps^2/8) <= delta`.

**Why Route C resolves Gamma_92:** After conditioning on the combined sample z, the hypothesis space becomes FINITE (at most GF(C,2m) patterns on z). The union bound over finitely many patterns is valid. The per-pattern concentration is for bounded iid variables (the swap indicators), which are genuinely independent GIVEN z. No sample-independent representatives needed.

---

### Route D: Introduce HasConsistentUC (One-Sided Bypass)

**Target:** Define `HasConsistentUC`, prove it from finite VCDim, reroute `uc_imp_pac` through it.

**Code changes:**
```lean
-- NEW DEFINITION:
def HasConsistentUC (X : Type u) [MeasurableSpace X] (C : ConceptClass X Bool) : Prop :=
  forall (eps delta : R), 0 < eps -> 0 < delta ->
    exists (m0 : Nat), forall (D : Measure X), IsProbabilityMeasure D ->
      forall (c : Concept X Bool), forall (m : Nat), m0 <= m ->
        Measure.pi (fun _ : Fin m => D)
          { xs : Fin m -> X |
            forall (h : Concept X Bool), h in C ->
              (forall i, h (xs i) = c (xs i)) ->
              TrueErrorReal X h c D < eps }
          >= ENNReal.ofReal (1 - delta)

-- NEW LEMMA:
private lemma uc_bad_event_le_delta_consistent ...
    Measure.pi { xs | exists h in C,
      (forall i, h (xs i) = c (xs i)) AND
      D {x | h x != c x} >= ENNReal.ofReal eps }
    <= ENNReal.ofReal delta

-- PROVE via growth_function_cover + consistent_tail_bound + polynomial tail chain.
-- This AVOIDS Gamma_92 because...
-- WAIT: it does NOT avoid Gamma_92. The one-sided consistent case
-- STILL has the representative-selection problem for uncountable C.
-- (See D15 v2 URS analysis, lines 501-624.)
```

**CRITICAL ANALYSIS:** Route D faces the SAME Gamma_92 obstruction as Routes A and B. The one-sided consistent case requires union-bounding over the set `{h in C | TrueErr(h) >= eps AND h consistent on xs}`. For each xs, this set groups into at most GF(C,m) restriction classes. But the classes depend on xs, so sample-independent representatives cannot be chosen.

**The consistent case has ONE simplification:** All consistent h have the SAME restriction to the sample (h|_xs = c|_xs). So there is only ONE restriction pattern for consistent hypotheses. The union is over a single set.

**WAIT -- THIS IS THE KEY INSIGHT THAT WAS MISSED IN v2.**

For CONSISTENT hypotheses: `h|_xs = c|_xs` for ALL of them. They all have the SAME restriction pattern. So the "union over GF(C,m) restriction classes" reduces to a union over ONE class (the consistent class). The bad consistent event is:

```
{xs | exists h in C, h|_xs = c|_xs AND TrueErr(h) >= eps}
= {xs | (exists h in C with TrueErr(h) >= eps) AND (h|_xs = c|_xs)}
```

But different h with TrueErr >= eps have different agreement sets `{x | h(x) = c(x)}`. The consistency set `{xs | h|_xs = c|_xs}` = `Set.pi univ (fun _ => {x | h x = c x})` depends on h through its GLOBAL agreement set, not just the restriction.

So the union IS over multiple sets:
```
Union_{h : TrueErr(h) >= eps} Set.pi univ (fun _ => {x | h x = c x})
```

This is potentially uncountable. BUT: each set has measure `<= (1-eps)^m` by KK1. And the union itself is contained in:
```
{xs | forall i, xs_i in Union_{h : TrueErr(h) >= eps} {x | h x = c x}}
= Set.pi univ (fun _ => Union_{h : TrueErr(h) >= eps} {x | h x = c x})
```

The measure of this is `(D(Union_{h:bad} {x | h x = c x}))^m`. Since `D(X) = 1` and the union could be all of X, this doesn't help.

**Route D verdict: ALSO BLOCKED by Gamma_92 for uncountable C.**

**UNLESS we can use the fact that the restriction is ALL c|_xs:**

For the consistent case, ALL bad h agree with c on the sample. So:
```
{xs | exists bad consistent h} = {xs | exists h in C, TrueErr(h) >= eps, forall i h(xs_i) = c(xs_i)}
```

For a FIXED h with TrueErr(h) = p >= eps:
```
P(h consistent on xs) = P(forall i, h(xs_i) = c(xs_i)) = (1-p)^m <= (1-eps)^m
```

The bad event is the union. We need:
```
P(Union_{h:bad} {forall i, h(xs_i) = c(xs_i)}) <= ???
```

Since each individual set has measure `<= (1-eps)^m`, and the union is over potentially uncountable many, the union could have measure up to 1.

BUT: the growth function tells us that on any sample xs, at most GF(C,m) distinct agreement patterns exist among ALL h in C. For the CONSISTENT subset, they all share the pattern c|_xs. So there is EXACTLY ONE pattern. The union is really just ONE set:
```
{xs | exists h in C with TrueErr(h) >= eps, forall i h(xs_i) = c(xs_i)}
```

For any FIXED xs in this set, there exists such an h. But the set itself is NOT determined by a single h -- it's the set of xs for which SOME bad h is consistent.

**THE CRUCIAL POINT:** This set is NOT a product set. It is the UNION of product sets `Set.pi univ (fun _ => {x | h x = c x})` over all bad h. Different bad h give different product sets. The union is not a product.

**HOWEVER:** We can bound the outer measure of the union by the measure of any SINGLE product set that CONTAINS the union. But no single product set contains the union (different h have different agreement sets).

**Route D is GENUINELY BLOCKED for uncountable C without symmetrization.**

**Viability: 0.00.**

---

### Route E: Statement Weakening (change uc_bad_event_le_delta to one-sided)

**Target:** Change the sorry statement to only require the one-sided consistent bound, then propagate changes.

**A5 check:** Changing `uc_bad_event_le_delta` from `|TrueErr - EmpErr| >= eps` to `consistent AND TrueErr >= eps` WEAKENS the lemma's conclusion. Since it's a PRIVATE lemma, this is a local change. But `vcdim_finite_imp_uc` calls it to prove `HasUniformConvergence`, which is a PUBLIC definition. To make `vcdim_finite_imp_uc` still type-check, we would need to either:
(a) Weaken `HasUniformConvergence` (A5 VIOLATION), or
(b) Prove the two-sided UC from the one-sided (REQUIRES the same concentration arguments).

**Verdict: Route E is NOT A5-compliant** unless we can derive the two-sided UC from the one-sided version, which we cannot without additional infrastructure.

**Viability: 0.00 (A5 violation).**

---

## 5. The INVARIANT Route

### Identification

After exhaustive analysis of Routes A-E:

**INVARIANT ROUTE: C (Symmetrization).**

This is the ONLY route that:
1. Resolves Gamma_92 (by conditioning on the combined sample, making C finite per sample)
2. Proves the FULL two-sided UC bound (matching the statement)
3. Is A5-compliant (no weakening of definitions)
4. Survives future discoveries (standard textbook proof, mathematically robust)
5. Has synergy with D6 (Rademacher complexity proofs use the same infrastructure)

### Why Route C Dominates

| Criterion | A | B | C | D | E |
|-----------|---|---|---|---|---|
| Proves two-sided | No | Blocked (Gamma_92) | Yes | No | A5 violation |
| A5-compliant | Yes | Yes | Yes | Maybe | No |
| Resolves Gamma_92 | N/A | No | Yes | No | N/A |
| LOC | ~60 | ~120 | ~200 | ~80 | ~40 |
| Viability | 0.00 | 0.10 | 0.55 | 0.00 | 0.00 |
| Discovery-invariant | No | No | Yes | No | No |

### Route C Measurements

- **Pl (Plausibility):** 0.55. The mathematical argument is standard and correct. The Lean4 formalization has moderate risk from the Fubini/conditioning step and the Hoeffding import.
- **Coh (Coherence):** 0.70. The proof chain (ghost sample -> symmetrization -> conditioning -> per-pattern Hoeffding -> assembly) has clear joints. HC is highest at C2 (symmetrization lemma) and C4 (Hoeffding bridge).
- **Inv (Invariance):** 0.90. This is the standard textbook proof. It survives any future discovery (new statement fixes, tighter bounds, etc.).
- **Comp (Compactness):** 0.40. ~200 LOC is substantial. The main risk is the symmetrization lemma (C2) which is non-trivial Lean4.

### Complete Tactic Sequence for Route C

```lean
-- uc_bad_event_le_delta proof via symmetrization
-- Requires new imports:
--   import Mathlib.Probability.Moments.SubGaussian
--   import Mathlib.Probability.ProductMeasure

-- STEP 1: Symmetrization reduction
-- Define ghost sample via block_extract 2 m
-- Prove: mu_pi {exists h bad} <= 2 * mu_{2m} {exists h, |emp(S)-emp(S')| >= eps/2}
-- using iIndepFun_block_extract 2 m D (KK14)
-- and the symmetrization argument (union bound + equal marginals)

-- STEP 2: Growth function bound on combined sample
-- For fixed combined sample z : Fin (2m) -> X:
-- The number of distinct restriction patterns of C on z is at most GF(C, 2m).
-- Apply hv: GF(C, 2m) <= sum_{i<=v} C(2m, i) for 2m >= v.
-- Need: v <= 2m. From hm_bound: m >= (v+2)!/(eps^(v+1)*delta) >= 1 for reasonable params.
-- So 2m >= 2 >= v only if v <= 2. For general v, need m >= v/2.
-- From hm_bound: m >= (v+2)!/(eps^(v+1)*delta) >= v+2 >= v/2 for v >= 2.

-- STEP 3: Per-pattern Hoeffding
-- For each restriction pattern p (a fixed labeling of 2m points):
-- Define swap variables: for each i in 1..m,
--   Y_i = loss(h, S_i) - loss(h, S'_i) where S, S' are the two halves
-- Given the combined sample, Y_i are iid Rademacher-scaled (times bounded values).
-- Y_i in [-1/m, 1/m]. Apply measure_sum_ge_le_of_iIndepFun:
-- P(|sum Y_i| >= eps/2) <= 2*exp(-m*eps^2/8)

-- STEP 4: Union bound (NOW VALID: finite number of patterns per combined sample)
-- P(exists h, |emp(S)-emp(S')| >= eps/2 | z) <= GF(C,2m) * 2*exp(-m*eps^2/8)
-- Integrate over z: P(exists h, |emp(S)-emp(S')| >= eps/2) <= GF(C,2m) * 2*exp(-m*eps^2/8)

-- STEP 5: Combine
-- mu_pi {bad} <= 2 * GF(C,2m) * 2*exp(-m*eps^2/8) = 4*GF(C,2m)*exp(-m*eps^2/8)

-- STEP 6: Arithmetic to delta
-- GF(C,2m) <= (v+1)*(2m)^v [by KK3 + KK4]
-- 4*(v+1)*(2m)^v*exp(-m*eps^2/8)
-- = 4*(v+1)*2^v * m^v * exp(-m*eps^2/8)
-- <= 4*(v+1)*2^v * (v+1)!/(eps^v * m * (eps/8)^1) [by KK2 variant with t=m*eps^2/8]
-- The exact arithmetic chain needs:
-- m^v * exp(-m*eps^2/8) <= (v+1)!/(m*eps^2/8)^{...}
-- For m >= (v+2)!/(eps^(v+1)*delta), the exponential dominates.
-- A cleaner bound: for m >= C(v)/eps^2 * log(1/delta) (which is <= (v+2)!/(eps^(v+1)*delta)),
-- the Hoeffding bound gives 4*GF(C,2m)*exp(-m*eps^2/8) <= delta.
-- The factorial sample complexity provides MORE than enough headroom.

-- STEP 7: Bridge ENNReal
-- mu.real {bad} <= delta -> mu {bad} <= ofReal delta
-- via ENNReal.ofReal_toReal + monotonicity
```

---

## 6. sample_complexity_upper_bound Resolution

### The Structural Mismatch

`sample_complexity_upper_bound` claims `SampleComplexity <= ceil((8/eps)(d*log(2/eps) + log(2/delta)))`.

The UC proof chain (after Route C) provides PAC learnability with factorial sample complexity `(v+2)!/(eps^(v+1)*delta)`. The Hoeffding bound in the statement is TIGHTER.

### Resolution Options

**Option 1 (RECOMMENDED): Tighten the UC sample complexity.**

After building the symmetrization infrastructure (Route C), the actual UC sample complexity becomes `O((v*log(m) + log(1/delta))/eps^2)` (the standard Hoeffding-based bound), NOT the factorial. This is because the symmetrization + Hoeffding chain gives exponential concentration, which requires only polynomial sample size.

To implement: change `hm_bound` in `uc_bad_event_le_delta` from `(v+2)!/(eps^(v+1)*delta) <= m` to `ceil((8/eps^2)(v*log(2m) + log(4/delta))) <= m`. Then the arithmetic in C5-C6 gives:
```
4*(v+1)*(2m)^v * exp(-m*eps^2/8) <= delta
```
which holds for `m >= (8/eps^2)(v*log(4(v+1)) + v*log(2m) + log(4/delta))`. Solving for m (using `m >= C*v*log(m)/eps^2` which gives `m = O(v*log(v/eps)/eps^2)`) yields the standard bound.

**LOC:** +20 (arithmetic changes in uc_bad_event_le_delta) + 30 (bridge in sample_complexity_upper_bound).

**Option 2: Weaken the stated bound.**

Change `sample_complexity_upper_bound` to claim `SampleComplexity <= ceil((v+2)!/(eps^(v+1)*delta))`. This is a WEAKER bound (larger ceiling) but matches the current UC proof chain.

**A5 check:** Weakening a quantitative bound statement is A5-valid (the bound is still a bound, just looser). But it's mathematically unsatisfying.

**Option 3 (BEST for invariance): Prove with Hoeffding-based bound after Route C.**

After the symmetrization infrastructure is built, directly prove PAC at the Hoeffding sample size `m = ceil((8/eps)(d*log(2/eps) + log(2/delta)))` by instantiating the symmetrization + Hoeffding chain at this m. The factorial bound in `uc_bad_event_le_delta` is not needed -- the symmetrization chain gives a TIGHTER bound directly.

This means: instead of routing through `vcdim_finite_imp_uc` (which uses the factorial bound), write a DIRECT proof at Bridge:657 using the symmetrization infrastructure.

**LOC:** ~60 (direct application of symmetrization chain with Hoeffding-based arithmetic).

---

## 7. Meta-Programmatic Analysis

### 7.1 Metaprogram Type of `uc_bad_event_le_delta`

**M-Pipeline** with 4 stages:
1. **Symmetrization reduction** (measure-theoretic): single-sample -> double-sample
2. **Combinatorial conditioning** (combinatorial): uncountable -> finite per combined sample
3. **Concentration** (probabilistic): per-pattern tail bound
4. **Arithmetic assembly** (algebraic): product bound -> delta

### 7.2 Mechanism Space

**3 independent mathematical mechanisms compose:**
1. Symmetrization (reduces the problem domain)
2. Growth function counting (finitizes the hypothesis space)
3. Hoeffding/sub-Gaussian concentration (bounds individual deviations)

These mechanisms are ORTHOGONAL: symmetrization is measure-theoretic, growth function is combinatorial, Hoeffding is analytic. The composition is linear (pipeline), not branching.

### 7.3 Simpler Restructuring?

**Question:** Can the proof DAG avoid the sorry entirely by collapsing intermediates?

**Analysis:** The current DAG is:
```
vcdim_finite_imp_pac (PAC.lean)
  -> vcdim_finite_imp_pac_via_uc (Gen:1447)
    -> vcdim_finite_imp_uc (Gen:1288)
      -> uc_bad_event_le_delta (Gen:1270) [SORRY]
    -> uc_imp_pac (Gen:1346)
```

**Collapse option:** Merge `vcdim_finite_imp_uc` and `uc_imp_pac` into a single `vcdim_finite_imp_pac` that directly constructs the PAC learner with the symmetrization bound. This eliminates `HasUniformConvergence` as an intermediate.

**Verdict:** This collapse is possible but loses mathematical structure. `HasUniformConvergence` is a genuine mathematical concept (the uniform convergence property) that appears in the fundamental theorem. Collapsing it loses the modular structure. NOT recommended.

### 7.4 Sorry Dependency Structure

```
uc_bad_event_le_delta (Gen:1283) [SORRY S2]
  -> vcdim_finite_imp_uc (Gen:1288) [propagates S2]
    -> vcdim_finite_imp_pac_via_uc (Gen:1447) [propagates S2]
      -> vcdim_finite_imp_pac (PAC.lean:74) [propagates S2]
        -> vc_characterization (PAC.lean:122) [propagates S2]

sample_complexity_upper_bound (Bridge:657) [SORRY S5]
  -> pac_lower_bound (PAC.lean:172) [propagates S5 via sample_complexity_lower_bound]

pac_lower_bound_member (Gen:2680) [SORRY S4]
  -> sample_complexity_lower_bound (Gen:2688) [propagates S4]
    -> pac_lower_bound (PAC.lean:176) [propagates S4]

vcdim_finite_imp_compression (Gen:2263) [SORRY S3, INDEPENDENT]

bad_consistent_covering (Gen:639) [SORRY S1, DEAD CODE]
```

**Key insight:** S2 is the SOLE blocker for the qualitative VC characterization theorem. S4 and S5 are for the quantitative bounds. S3 is independent (Moran-Yehudayoff). S1 is dead.

Closing S2 via Route C makes `vc_characterization` sorry-free (the qualitative theorem is complete). S4 has complete infrastructure and is closeable (~75 LOC measure bridge). S5 needs additional work after S2 (see Section 6).

---

## 8. Execution Plan (Ordered by Dependency)

### Phase 1: Symmetrization Infrastructure (~200 LOC, ~8 hours)
1. Add `import Mathlib.Probability.Moments.SubGaussian` to Generalization.lean.
2. Implement C1: ghost sample definitions (~10 LOC).
3. Implement C4: per-pattern Hoeffding bridge (~50 LOC). [Can be done independently of C2.]
4. Implement C2: symmetrization lemma (~70 LOC). [Hardest component.]
5. Implement C3: conditioned restriction counting (~40 LOC).
6. Implement C5: assembly into `uc_bad_event_le_delta` proof (~30 LOC).

### Phase 2: Close S4 pac_lower_bound_member (~75 LOC, ~3 hours)
1. Replicate the measure bridge from `pac_lower_bound_core` (Gen:2036-2198).
2. Apply `nfl_counting_core` (KK9) to get f0, c0.
3. Chain: counting bound -> measure bound -> contradiction with PAC guarantee.

### Phase 3: Close S5 sample_complexity_upper_bound (~60 LOC, ~2 hours)
1. After Phase 1, directly prove PAC at Hoeffding sample size using symmetrization chain.
2. Show the bound is in the SampleComplexity set via `Nat.sInf_le`.

### Phase 4: Verification (~30 min)
1. `lake build` -- 0 errors.
2. Count sorry-using declarations. Target: 2 (S1 dead code + S3 Moran-Yehudayoff).
3. A4 check: no trivially-true sorrys.
4. A5 check: all changes are enrichments or repairs.

---

## 9. Gamma Discoveries

| ID | Discovery | Type | Source |
|----|-----------|------|--------|
| Gamma_92 | `bad_consistent_covering` structurally unprovable for uncountable C | CONFIRMED | D01 URS + this analysis |
| Gamma_95 | `uc_bad_event_le_delta` factorial sample complexity is polynomial-tail, not Hoeffding | CONFIRMED | D12 URS |
| Gamma_98 (NEW) | The one-sided consistent case ALSO faces Gamma_92 for uncountable C. Route D is blocked. | Structural | This analysis, Section 4 Route D |
| Gamma_99 (NEW) | `sample_complexity_upper_bound` has structural mismatch between Hoeffding bound and factorial UC. Cannot be closed by proving uc_bad_event_le_delta alone. | Structural | This analysis, Section 6 |
| Gamma_100 (NEW) | Route C (symmetrization) is the ONLY viable route for `uc_bad_event_le_delta` as stated. All other routes (A, B, D, E) are blocked by Gamma_92 or A5 violations. | Invariant route identification | This analysis, Section 5 |
| Gamma_101 (NEW) | `uc_imp_pac` only uses UC for the consistent learner output. The full two-sided UC for ALL h in C is never exploited. HasConsistentUC would suffice for PAC, but modifying HasUniformConvergence violates A5. | Architectural observation | Gen:1416-1442 analysis |
