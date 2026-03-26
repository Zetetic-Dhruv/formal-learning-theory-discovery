# D4 Proof Agent URS — Close boost_two_thirds_to_pac

## Measurement State (Pre-Proof)

### Pl (Plausibility) = 0.85
The theorem IS non-trivial: converting Pr >= 2/3 to Pr >= 1-delta genuinely requires
probability amplification. The learner construction is already built (sorry-free).
The event containment is proved. The sample complexity mf is defined. The ONLY
remaining content is the Chebyshev concentration bound composed with block independence.
Risk: the Chebyshev composition with `iIndepFun_block_extract` may have type-matching
issues at the Lean4 level.

### Coh (Coherence) = 0.70
The proof composes 3 layers:
1. Block independence (`iIndepFun_block_extract` — PROVED, Gamma_92)
2. Chebyshev concentration (`meas_ge_le_variance_div_sq` — Mathlib)
3. Majority vote error bound (pointwise argument)

HC at layer 1-2 joint = 0.3: the `iIndepFun_block_extract` output type must match
what Chebyshev expects. `iIndepFun` gives independence of `(Fin (k*m) -> X) -> (Fin m -> X)`
functions. Chebyshev needs `MemLp X 2 mu` for indicator random variables.

HC at layer 2-3 joint = 0.5: Chebyshev bounds P[S >= k/2] where S = sum of indicators.
The majority vote error argument needs P[majority wrong] <= P[S >= k/2]. This step is
COMBINATORIAL (if >= k/2 blocks are bad, majority is wrong) and should have low HC.

### Inv (Invariance) = 0.60
Two proof routes available (Direct Chebyshev vs Recursive median-of-3). The infrastructure
(`iIndepFun_block_extract`) serves both routes. If Chebyshev composition fails, the
recursive route via `probAmpSeq p0 d >= 1 - delta` is available.
Risk: Chebyshev requires `MemLp 2` and `variance` computation. These may have API
friction in Lean4.

### Comp (Completeness) = 0.40
Of the full proof (~200 LOC), approximately:
- 80 LOC proved (learner, mf, event containment, block count) — Session 4
- 20 LOC infrastructure (`iIndepFun_block_extract`) — Session 4 late
- ~100 LOC remaining (Chebyshev composition, majority error, edge cases)

## Obstruction Analysis

### HC_1: iIndepFun -> indicator independence (0.3)
`iIndepFun_block_extract` gives independence of block extraction functions.
But Chebyshev needs independence of INDICATOR random variables X_j = 1{block j bad}.
The composition: X_j = g_j o block_extract_j where g_j is the "is error > epsilon" function.
`IndepFun.comp` (Mathlib) should handle this IF g_j is measurable.
Is `fun (block : Fin m -> X) => (D{x | L.learn(block) x != c x} > eps)` measurable?
This is a PREDICATE on functions, not a function — it's `Set.indicator` of a set in
the product space. Measurability of this set in `Fin m -> X` with `MeasurableSpace.pi`
is the KEY question. Under general `[MeasurableSpace X]`, this set may NOT be measurable.

RESOLUTION: For the existential in PACLearnable, we can use `Set.univ` as the hypothesis
space and work noncomputably. The indicator `1{D{error} > eps}` is a function of the
pushforward measure, which IS measurable if the error set `{x | h x != c x}` is measurable
(given by the `hmeas` hypothesis added in Session 3).

### HC_2: MemLp 2 for indicator variables (0.2)
Indicator variables take values in {0, 1}, so they're in L^p for all p.
`memLp_const` or `Memℒp_indicator` should give this.
Low risk — standard Mathlib.

### HC_3: Variance computation (0.4)
Need: Var[X_j] <= 1/4 (since X_j is Bernoulli(p) with p >= 2/3, Var = p(1-p) <= 1/4).
Then Var[S] = k * Var[X_j] <= k/4 (by independence).
Chebyshev: P[|S - E[S]| >= k/6] <= Var[S]/(k/6)^2 = (k/4)/(k^2/36) = 9/k.
For k >= 9/delta: P[bad] <= delta.

The chain: `IndepFun.variance_sum` (Mathlib:403) gives Var[sum] = sum Var (for
pairwise independent). Then `meas_ge_le_variance_div_sq` (Mathlib:378) gives the bound.

### HC_4: Majority vote correctness (0.1)
If < k/2 blocks are bad, then >= k/2+1 blocks are good (error <= eps each).
For each x, if >= k/2+1 blocks predict correctly, majority is correct.
Error of majority <= D{exists bad block wrong at x} <= sum of block errors <= k*eps.
Use eps/k per block to get majority error <= eps.

Wait — this means mf should use m0(eps/k) not m0(eps). Check the current mf definition
in Separation.lean.

## Inquiry State

### KK (Known)
- `iIndepFun_block_extract` PROVED (Gamma_92)
- Learner construction + mf + event containment PROVED (D4-Boost-v1)
- `meas_ge_le_variance_div_sq` exists in Mathlib (Variance:378)
- `IndepFun.variance_sum` exists in Mathlib (Variance:403)
- `chebyshev_majority_bound` factored as standalone lemma (D4-Boost-v2)
- Block count k >= 9/delta PROVED

### KU (Articulated unknowns)
- CKU_1: Does `iIndepFun_block_extract` compose with indicator functions via `IndepFun.comp`?
- CKU_2: Is the error indicator `1{D{error} > eps}` measurable under `MeasurableSpace.pi`?
- CKU_3: Does `variance_sum_pi` or `IndepFun.variance_sum` apply to our indicator setup?
- CKU_4: What is the exact mf formula? Is it m0(eps) * k or m0(eps/k) * k?
- CKU_5: Can Chebyshev be applied WITHOUT computing exact variance (just upper bound)?

### UK (Pressures)
- UK_1: Whether the measurability issue from D2 (Gamma_91) also affects D4
- UK_2: Whether `MemLp 2` for indicators requires `SigmaFinite` on the product space
- UK_3: Whether the majority vote error bound (k*eps) forces mf to use eps/k per block

### UU (Boundary)
- UU_1: Whether a simpler proof exists that avoids Chebyshev entirely (e.g., direct Chernoff)

## Discovery Task
Close `chebyshev_majority_bound` (Separation:153) and `boost_two_thirds_to_pac` (Separation:180).
The chain: compose `iIndepFun_block_extract` with indicator functions, apply Chebyshev,
connect to majority vote error.

## Protocol
1. Read Separation.lean lines 150-250 for exact sorry context
2. Read `iIndepFun_block_extract` in Generalization.lean to understand its output type
3. Attempt Chebyshev composition: iIndepFun -> indicator independence -> variance bound -> Chebyshev
4. If measurability blocks: use `sorry` for the measurability and document
5. Build after every change
6. Close `chebyshev_majority_bound` first, then `boost_two_thirds_to_pac`
