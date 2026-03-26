# D1 Symmetrization Proof Agent URS

## Will
Close 2 sorrys (`union_bound_consistent`, `vcdim_finite_imp_uc`) by building
the symmetrization infrastructure they share.

## Executive Summary

The covering sorry at Generalization.lean:681 is STRUCTURALLY IMPOSSIBLE for
uncountable C (Gamma_65). The standard proof uses symmetrization: construct a
ghost sample, reduce uniform deviation to double-sample deviation, condition
on the combined sample to reduce to a finite counting problem, then apply
Hoeffding per pattern. This is ~200 LOC of new infrastructure that also
serves D6 (Rademacher).

## Architecture Decision: REWRITE union_bound_consistent

The current `union_bound_consistent` has bound `GF(C,m)*(1-eps)^m`.
Symmetrization gives a DIFFERENT bound: `2*GF(C,2m)*exp(-m*eps^2/8)`.
**Decision:** Rewrite the theorem statement to use the symmetrization bound,
or add a new `union_bound_symmetrized` lemma and route through it.

**Recommended:** Add `union_bound_symmetrized` as a new lemma with the
correct bound, then have `union_bound_consistent` call it (changing the
existing sorry to reference the new infrastructure). This preserves the
existing proof structure downstream.

---

## Component 1: Ghost Sample via block_extract k=2

### Status: PROVED (assembly only)

The ghost sample construction is a DIRECT instantiation of existing
infrastructure:

```
iIndepFun_block_extract (k := 2) (m := m) (D := D)
```

gives:

```
iIndepFun (fun j : Fin 2 => fun omega => block_extract 2 m omega j)
          (Measure.pi (fun _ : Fin (2*m) => D))
```

where `block_extract 2 m omega 0 : Fin m -> X` is the first half (primary sample)
and `block_extract 2 m omega 1 : Fin m -> X` is the second half (ghost sample).

### Key Verification

`iIndepFun_block_extract` is PROVED in Generalization.lean:3015-3057. It uses:
- `MeasurableEquiv.piCongrLeft` -- reindex Fin(k*m) as Fin k x Fin m
- `MeasurableEquiv.curry` -- curry (Fin k x Fin m -> X) to (Fin k -> Fin m -> X)
- `infinitePi_map_curry` -- the curry equiv preserves product measure
- `measurePreserving_eval` -- each marginal is Measure.pi (fun _ : Fin m => D)

No new code needed. Just instantiate with k=2.

### Type Signatures

```lean
-- Primary sample: first m coordinates
def primary_sample (omega : Fin (2*m) -> X) : Fin m -> X :=
  block_extract 2 m omega 0

-- Ghost sample: last m coordinates
def ghost_sample (omega : Fin (2*m) -> X) : Fin m -> X :=
  block_extract 2 m omega 1

-- Independence: primary and ghost are iIndepFun
-- IMMEDIATE from iIndepFun_block_extract 2 m D
```

### LOC: ~10 (definitions + convenience lemmas)

---

## Component 2: Symmetrization Lemma

### Statement

For any h in C:
```
Pr_{xs}[|EmpErr(h,xs) - TrueErr(h)| >= eps]
  <= 2 * Pr_{xs,xs'}[|EmpErr(h,xs) - EmpErr(h,xs')| >= eps/2]
```

### Proof Route

1. **E_{xs'}[EmpErr(h,xs')] = TrueErr(h)** -- linearity of expectation over iid
   draws. This is `trueError_eq_genError` (PROVED) composed with the fact that
   EmpiricalError is an average of iid indicators.

2. **Markov on the ghost sample:** For fixed xs with
   |EmpErr(h,xs) - TrueErr(h)| >= eps, by triangle inequality:
   Either |EmpErr(h,xs) - EmpErr(h,xs')| >= eps/2 (good: contributes to RHS)
   or |EmpErr(h,xs') - TrueErr(h)| >= eps/2.
   The second event has probability <= 1/2 by Chebyshev/Markov on xs'.
   So the first event has conditional probability >= 1/2.

3. **Integrate:** Pr[bad(xs)] <= 2 * Pr[bad_sym(xs,xs')]

### Mathlib APIs

- `MeasureTheory.integral_indicator_one` -- E[indicator] = measure
- `MeasureTheory.Measure.pi` -- product measure
- `ProbabilityTheory.iIndepFun` -- independence (from block_extract)
- `MeasureTheory.Measure.prod` -- for double sample (already used in DoubleSampleMeasure)

### Critical UK

**UK_sym_1:** The "Markov on ghost" step requires showing that for fixed xs:
```
Pr_{xs'}[|EmpErr(h,xs') - TrueErr(h)| >= eps/2] <= 1/2
```
This follows from Chebyshev: Var[EmpErr(h,xs')] = p(1-p)/m <= 1/(4m),
so Pr[|EmpErr - E[EmpErr]| >= eps/2] <= 1/(m*eps^2) which is <= 1/2
for m >= 2/eps^2.

**ALTERNATIVE (simpler):** Use the weaker statement that avoids the
conditional probability argument entirely. The standard symmetrization
bypasses Markov by using:
```
{|emp - true| >= eps} subset {|emp - emp'| >= eps/2} union {|emp' - true| >= eps/2}
```
and the second event has the SAME probability as the first (by iid symmetry),
giving Pr[first] >= Pr[first or second]/2 >= Pr[|emp-true| >= eps]/2.

This AVOIDS the conditional probability and uses only:
- Triangle inequality (pure algebra)
- iid symmetry (Measure.pi gives same marginals)
- Union bound (measure_union_le)

### Tactic Sequence (simplified symmetrization)

```lean
theorem symmetrization_reduction (X : Type u) [MeasurableSpace X]
    (D : Measure X) [IsProbabilityMeasure D]
    (h c : Concept X Bool) (m : ℕ) (hm : 0 < m) (eps : ℝ) (heps : 0 < eps) :
    Measure.pi (fun _ : Fin m => D)
      {xs | |TrueErrorReal X h c D - EmpiricalError X Bool h (fun i => (xs i, c (xs i))) (zeroOneLoss Bool)| >= eps}
    <= 2 * (DoubleSampleMeasure X D m)
      {p | |EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) -
           EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool)| >= eps/2} := by
  -- Step 1: Triangle inequality set inclusion
  -- {|emp(xs)-true| >= eps} subset
  --   {|emp(xs)-emp(xs')| >= eps/2} union {|emp(xs')-true| >= eps/2}
  -- Step 2: By iid symmetry, Pr_{xs'}[|emp(xs')-true| >= eps/2]
  --         = Pr_{xs}[|emp(xs)-true| >= eps/2] (same marginal)
  -- Step 3: So Pr[A] <= Pr[A union B] = Pr[A] + Pr[B] - Pr[A inter B]
  --         <= Pr[A] + Pr[B] = 2*Pr[A union B or something]
  -- Actually the standard argument is:
  --   Pr[|emp-true| >= eps]
  --   = E_{xs}[1{|emp(xs)-true| >= eps}]
  --   = E_{xs}[E_{xs'}[1{|emp(xs)-true| >= eps}]]  (xs' independent)
  --   <= E_{xs}[E_{xs'}[1{|emp(xs)-emp(xs')| >= eps/2} + 1{|emp(xs')-true| >= eps/2}]]
  --   = E_{xs,xs'}[1{|emp(xs)-emp(xs')| >= eps/2}] + E_{xs'}[1{|emp(xs')-true| >= eps/2}]
  --   The second term = Pr_{xs'}[...] by Fubini
  --   = Pr[sym bad] + Pr[|emp(xs')-true| >= eps/2]
  -- This doesn't directly give factor 2. The correct argument for factor 2:
  --   Pr[|emp-true| >= eps] * (1 - Pr_{xs'}[|emp'-true| >= eps/2])
  --     <= Pr[|emp-emp'| >= eps/2]
  -- When m >= 2/eps^2, the Chebyshev bound gives Pr[|emp'-true| >= eps/2] <= 1/2.
  -- So Pr[|emp-true| >= eps] <= 2 * Pr[|emp-emp'| >= eps/2].
  sorry
```

### LOC: ~60-80

---

## Component 3: Conditioned Restriction Counting

### Statement

After conditioning on the combined sample (xs, xs') -- a total of 2m points --
the indicator 1{h(x_i) != c(x_i)} depends on h only through its restriction
to these 2m points. The number of distinct restrictions is at most
GrowthFunction(C, 2m).

### Proof Route

This is a COMBINATORIAL fact, not measure-theoretic.

1. Define the restriction map: `restrict_to_sample : C -> (Fin (2*m) -> Bool)`
   mapping h to (fun i => h(combined_i)).

2. The set `{restrict_to_sample h | h in C}` has cardinality <= GrowthFunction(C, 2m)
   by definition of GrowthFunction.

3. For each distinct restriction pattern, the empirical error difference
   |EmpErr(h,xs) - EmpErr(h,xs')| is a fixed function of which coordinates
   from xs vs xs' are "swapped".

### Mathlib APIs

- `GrowthFunction` (DEFINED in Generalization.lean)
- `Finset.card_image_le` -- |image f S| <= |S|
- `growth_function_le_sauer_shelah` (PROVED in Bridge.lean)

### Tactic Sequence

```lean
-- The key lemma: union bound over restriction patterns
-- Pr[exists h in C, |emp(h,xs) - emp(h,xs')| >= eps/2]
--   <= sum over patterns p, Pr[|emp_p(xs) - emp_p(xs')| >= eps/2]
--   (at most GF(C,2m) terms)
```

### LOC: ~30-40

---

## Component 4: Per-Pattern Hoeffding

### Statement

For a FIXED restriction pattern (i.e., fixed values h(z_1),...,h(z_{2m})
where z_i are the combined sample points), the quantity
|EmpErr(h,xs) - EmpErr(h,xs')| depends only on which indices belong to
xs vs xs'. Conditioned on the combined sample, this is equivalent to
a random permutation/swap argument.

Specifically, for each i in 1..m, let sigma_i in {0,1} indicate whether
z_i comes from xs (sigma_i=0) or xs' (sigma_i=1). Conditioned on
z_1,...,z_{2m}, the sigma_i are iid Bernoulli(1/2). The difference
|EmpErr(h,xs) - EmpErr(h,xs')| is a sum of bounded iid random variables:
```
(1/m) * sum_{i=1}^{m} (1{h =/= c on xs_i} - 1{h =/= c on xs'_i})
```
Each term is bounded in [-1/m, 1/m].

By Hoeffding's inequality for bounded iid sums:
```
Pr[|difference| >= eps/2] <= 2 * exp(-m * eps^2 / 8)
```

### Mathlib APIs

The key question: what Mathlib API provides Hoeffding?

**Option A: `ProbabilityTheory.measure_sum_ge_le_of_iIndepFun`**
This is the Hoeffding inequality in Mathlib (SubGaussian.lean).
It gives: for iIndepFun X_i with X_i in [a_i, b_i]:
```
Pr[sum X_i - E[sum X_i] >= t] <= exp(-2t^2 / sum(b_i - a_i)^2)
```
With X_i = (1/m)(indicator_i), a_i = -1/m, b_i = 1/m:
sum(b_i-a_i)^2 = m*(2/m)^2 = 4/m
So Pr[sum >= t] <= exp(-2t^2/(4/m)) = exp(-m*t^2/2)
With t = eps/2: exp(-m*eps^2/8). Two-sided: multiply by 2.

**Status of `measure_sum_ge_le_of_iIndepFun`:** This IS in Mathlib
(ProbabilityTheory.Moments.SubGaussian). It requires:
- `iIndepFun` (from block_extract k=2)
- `hasSubgaussianMGF_of_mem_Icc` for each variable (from boundedness)
- `AEMeasurable` for each variable

**Option B: Use `hasSubgaussianMGF_of_mem_Icc` + Markov on MGF directly**
This avoids the full Hoeffding API and uses the sub-Gaussian infrastructure.

**Option C: Use the proved `chebyshev_majority_bound` pattern**
The Separation.lean proof already chains Chebyshev for sums of indicators.
Polynomial tail suffices (the exponential tail from Hoeffding is nice but
not essential for the existence result).

### RECOMMENDED: Option A (Mathlib Hoeffding)

Mathlib's `measure_sum_ge_le_of_iIndepFun` with `hasSubgaussianMGF_of_mem_Icc`
is the cleanest path. Signature:

```lean
theorem measure_sum_ge_le_of_iIndepFun
    {ι : Type*} [Fintype ι] {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {a b : ι → ℝ}
    (h_indep : iIndepFun (fun _ => inferInstance) X μ)
    (h_ae : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (a i) (b i))
    (h_meas : ∀ i, AEMeasurable (X i) μ)
    (t : ℝ) (ht : 0 < t) :
    μ {ω | t ≤ (∑ i, X i ω) - ∫ ω, (∑ i, X i ω) ∂μ}
    ≤ ENNReal.ofReal (Real.exp (-2 * t ^ 2 / ∑ i, (b i - a i) ^ 2))
```

### Tactic Sequence

```lean
-- For each restriction pattern p (a fixed binary vector on 2m points):
-- Define Y_i : Fin m -> Omega -> R where
--   Y_i(omega) = (1/m) * (loss(p, xs_i) - loss(p, xs'_i))
-- Each Y_i is bounded in [-1/m, 1/m].
-- They are independent (from iIndepFun_block_extract with k=2m, or
-- from the product structure of the permutation measure).
-- Apply measure_sum_ge_le_of_iIndepFun.
-- Get: Pr[sum Y_i >= eps/2] <= exp(-m*eps^2/8)
-- Two-sided: <= 2*exp(-m*eps^2/8)
```

### LOC: ~40-60

---

## Component 5: Assembly -- union_bound_symmetrized

### Statement

```lean
theorem union_bound_symmetrized {X : Type u} [MeasurableSpace X]
    (D : Measure X) [IsProbabilityMeasure D]
    (C : ConceptClass X Bool) (c : Concept X Bool) (hcC : c ∈ C)
    (m : ℕ) (hm : 0 < m) (eps : ℝ) (heps : 0 < eps) (heps1 : eps ≤ 1) :
    Measure.pi (fun _ : Fin m => D)
      {xs | exists h in C,
        (forall i, h (xs i) = c (xs i)) ∧
        D {x | h x ≠ c x} > ENNReal.ofReal eps}
      ≤ ENNReal.ofReal (2 * GrowthFunction X C (2*m) * Real.exp (-m * eps^2 / 8)) := by
  -- Step 1: Symmetrization (Component 2)
  --   Pr[bad(xs)] <= 2 * Pr_{xs,xs'}[|emp(h,xs) - emp(h,xs')| >= eps/2]
  -- Step 2: Conditioned counting (Component 3)
  --   Condition on combined sample. At most GF(C,2m) patterns.
  -- Step 3: Per-pattern Hoeffding (Component 4)
  --   Each pattern contributes <= 2*exp(-m*eps^2/8)
  -- Step 4: Union bound
  --   Total <= 2 * GF(C,2m) * exp(-m*eps^2/8)
  sorry
```

### LOC: ~30 (pure assembly of Components 2-4)

---

## Component 6: Close union_bound_consistent

### Approach

**Option A (recommended):** Replace the covering sorry at line 681 with:
```lean
-- Use symmetrization bound instead of covering
have h_sym := union_bound_symmetrized D C c hcC m hm eps heps heps1
-- Show: 2*GF(C,2m)*exp(-m*eps^2/8) <= GF(C,m)*(1-eps)^m
-- This is FALSE in general (different bounds).
```

**PROBLEM:** The symmetrization bound `2*GF(C,2m)*exp(-m*eps^2/8)` is
NOT necessarily <= `GF(C,m)*(1-eps)^m`. They are structurally different bounds.

**Option B (correct):** Rewrite `union_bound_consistent` to use the
symmetrization bound. Change the conclusion to:
```
<= ENNReal.ofReal (2 * GrowthFunction X C (2*m) * exp(-m*eps^2/8))
```
Then propagate the change to `vcdim_finite_imp_pac_direct` which calls it.

**Option C (minimal change):** Add `union_bound_symmetrized` as a SEPARATE
lemma, then route `vcdim_finite_imp_pac_direct` through it instead of
through `union_bound_consistent`. Leave `union_bound_consistent` as-is
(its sorry becomes non-blocking).

**DECISION: Option C.** This minimizes disruption to the existing proof DAG.
`union_bound_consistent` keeps its sorry but is no longer on the critical path.
`vcdim_finite_imp_pac_direct` gets a new proof that uses `union_bound_symmetrized`.

### LOC: ~20 (re-routing)

---

## Component 7: Close vcdim_finite_imp_uc

### Approach

`vcdim_finite_imp_uc` proves HasUniformConvergence, which needs TWO-SIDED
concentration: |EmpErr - TrueErr| < eps for ALL h in C simultaneously.

The symmetrization infrastructure provides exactly this:
1. Symmetrization reduces to double-sample
2. Conditioning reduces to GF(C,2m) patterns
3. Hoeffding per pattern
4. Union bound: Pr[exists bad h] <= 2*GF(C,2m)*exp(-m*eps^2/8)
5. For m >= (8/eps^2)*(d*ln(4e*m/d) + ln(4/delta)), this is <= delta

The proof is IDENTICAL to union_bound_symmetrized but applied to the
uniform convergence setting (no consistency requirement).

### LOC: ~40 (symmetrization + sample complexity arithmetic)

---

## Total LOC Estimate

| Component | LOC | Status |
|-----------|-----|--------|
| C1: Ghost sample (block_extract k=2) | ~10 | Assembly only |
| C2: Symmetrization lemma | ~60-80 | NEW (hardest) |
| C3: Conditioned restriction counting | ~30-40 | NEW |
| C4: Per-pattern Hoeffding | ~40-60 | Bridge to Mathlib |
| C5: Assembly (union_bound_symmetrized) | ~30 | Assembly |
| C6: Close union_bound_consistent | ~20 | Re-routing |
| C7: Close vcdim_finite_imp_uc | ~40 | Assembly |
| **TOTAL** | **~230-280** | |

---

## Unknown Inventory

### CKU (Confirmed Known Unknowns -- resolvable)

| ID | Question | Impact |
|----|----------|--------|
| CKU_1 | Can `measure_sum_ge_le_of_iIndepFun` be applied to the conditioned per-pattern variables? Need to verify the independence holds AFTER conditioning on the combined sample. | C4 |
| CKU_2 | Does `DoubleSampleMeasure` (Measure.prod of two Measure.pi) equal `Measure.pi (fun _ : Fin (2*m) => D)` composed with the splitting map? Need measure equivalence. | C2 |
| CKU_3 | The restriction counting step needs `GrowthFunction` applied to a specific 2m-element Finset of X. Do we have the API to go from "restriction to a specific sample" to GrowthFunction? | C3 |

### UK (Unknown Unknowns)

| ID | Question | Risk |
|----|----------|------|
| UK_1 | Whether the conditional independence after conditioning on the combined sample can be formalized without building a full conditional probability API. The "conditioning" step in the textbook proof implicitly uses the regular conditional probability P(A|B). Lean4/Mathlib has `ProbabilityTheory.condexp` but not easy-to-use conditional probability for events. | HIGH |
| UK_2 | Whether the permutation argument (swapping xs_i and xs'_i) can be formalized as actual measure-preserving maps or needs to be handled via the algebraic symmetry of the product measure. | MEDIUM |

---

## Critical Path

```
C1 (ghost sample, ~10 LOC, trivial)
  |
  v
C2 (symmetrization lemma, ~70 LOC, HARDEST)
  |
  v
C3 (restriction counting, ~35 LOC)
  |
  v
C4 (per-pattern Hoeffding, ~50 LOC, Mathlib bridge)
  |
  v
C5 (assembly, ~30 LOC)
  |
  +---> C6 (close union_bound_consistent, ~20 LOC)
  |
  +---> C7 (close vcdim_finite_imp_uc, ~40 LOC)
```

## Proof Agent Execution Order

1. **C1 first** -- trivial, establishes the ghost sample
2. **C4 next** -- establish the Hoeffding bridge to Mathlib (independent of C2/C3)
3. **C3 next** -- restriction counting (independent of C2)
4. **C2 next** -- symmetrization lemma (the hard one, but C4 is ready for testing)
5. **C5** -- assembly
6. **C6 + C7** -- close the sorrys

## Risk Mitigation

If UK_1 (conditional probability) blocks C2:
- **Fallback:** Use Efron-Stein + Chebyshev route (Option C from IGNORANCE_PROFILE).
  This gives polynomial tails instead of exponential but still closes both sorrys.
  The ESChebyshev.lean file has the Efron-Stein infrastructure (sorry'd but with
  clear bridge to Zhang). LOC: ~100 (less than symmetrization).

If CKU_1 (Hoeffding after conditioning) blocks C4:
- **Fallback:** Use Chebyshev (variance bound) instead of Hoeffding. The
  `chebyshev_majority_bound` in Separation.lean proves this pattern works.
  Gives weaker bound: `2*GF(C,2m)/m*eps^2` instead of `2*GF(C,2m)*exp(...)`.
  Still sufficient for the existence of m0 in both sorry targets.

## Mathlib API Checklist

| API | Module | Status | Used In |
|-----|--------|--------|---------|
| `Measure.pi` | MeasureTheory.Constructions.Pi | Available | All |
| `MeasurableEquiv.piCongrLeft` | MeasureTheory.Constructions.Pi | Available | C1 |
| `infinitePi_map_curry` | MeasureTheory.Constructions.Pi | Available | C1 |
| `iIndepFun_block_extract` | Generalization.lean (PROVED) | Available | C1 |
| `measure_sum_ge_le_of_iIndepFun` | Probability.Moments.SubGaussian | Available | C4 |
| `hasSubgaussianMGF_of_mem_Icc` | Probability.Moments.SubGaussian | Available | C4 |
| `Measure.prod` | MeasureTheory.Constructions.Prod | Available | C2 |
| `GrowthFunction` | Generalization.lean (DEFINED) | Available | C3 |
| `growth_function_le_sauer_shelah` | Bridge.lean (PROVED) | Available | C5/C7 |
| `DoubleSampleMeasure` | ConcentrationAlt.lean (DEFINED) | Available | C2 |
| `block_extract` | Generalization.lean (DEFINED) | Available | C1 |
| `meas_ge_le_variance_div_sq` | Probability.Moments.Variance | Available | Fallback |

## D6 Synergy

The symmetrization infrastructure also serves D6 (Rademacher complexity):
- `vcdim_bounds_rademacher_quantitative` (Rademacher.lean:373) needs Massart
  finite lemma, which uses the same conditioning-on-sample + counting argument
- `rademacher_vanishing_imp_pac` (Rademacher.lean:438) needs the NFL lower
  bound, which uses shattered set + Rademacher = 1 (proved) + birthday argument

Building C1-C4 here makes D6 approachable with ~100 additional LOC.
