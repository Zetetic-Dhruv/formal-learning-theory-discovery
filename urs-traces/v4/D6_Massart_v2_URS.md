# D6 Massart v2 URS -- Complete Closure of `vcdim_bounds_rademacher_quantitative`

**Date**: 2026-03-20
**Target**: The single `sorry` at line 435 of `lean4/FLT_Proofs/Complexity/Rademacher.lean`
**Scope**: Bridge lemmas B1-B4 for the Massart finite lemma + Sauer-Shelah chain

---

## 1. AMRT-Organized K/U Universe

### KK: Exact Inventory of Proved Infrastructure

| # | Component | Location | Status | Exact Type/Role |
|---|-----------|----------|--------|-----------------|
| KK_1 | `EmpiricalRademacherComplexity` | Rademacher.lean:205 | DEFINED | `(1/2^m) * sum_sigma sSup { r | exists h in C, r = \|corr(h,sigma,xs)\| }` -- uses `sSup` over `Set R` |
| KK_2 | `RademacherComplexity` | Rademacher.lean:247 | DEFINED | `integral xs, EmpRad(xs) d(Measure.pi D)` |
| KK_3 | `rademacherCorrelation` | Rademacher.lean:177 | DEFINED | `(1/m) * sum_i boolToSign(sigma_i) * boolToSign(h(xs_i))` with `dif m=0 then 0` |
| KK_4 | `empiricalRademacherComplexity_le_one` | Rademacher.lean:213 | PROVED | `EmpRad <= 1` for all xs, all C |
| KK_5 | `rademacher_variance_eq` | Rademacher.lean:122 | PROVED | `sum_sigma (sum_i boolToSign(sigma_i)*a_i)^2 = m * \|SignVector m\|` when `\|a_i\|=1` |
| KK_6 | `empRad_eq_one_of_all_labelings` | Rademacher.lean:349 | PROVED | EmpRad = 1 when every labeling of xs is C-realizable |
| KK_7 | `shatters_subset` | Rademacher.lean:324 | PROVED | Subset of shattered set is shattered |
| KK_8 | `vcdim_zero_rademacher_le_inv_sqrt` | Rademacher.lean:701 | PROVED | VCDim=0 => Rad <= 1/sqrt(m) via Cauchy-Schwarz |
| KK_9 | `analytical_log_sqrt_bound` | Rademacher.lean:838 | PROVED | For large m: 2d*log(2m/d)/m < eps^2 |
| KK_10 | `vcdim_finite_imp_rademacher_vanishing` | Rademacher.lean:910 | PROVED | VCDim < top => uniform Rad vanishing (m0 independent of D) |
| KK_11 | `growth_function_le_sauer_shelah` | Bridge.lean:465 | PROVED | `GrowthFunction X C m <= sum_{i<=d} C(m,i)` for Fintype X, DecidableEq X |
| KK_12 | `card_restrict_le_sauer_shelah_bound` | Bridge.lean:393 | PROVED | `(restrictConceptClass C S).card <= sum_{i<=d} C(\|S\|,i)` |
| KK_13 | `restrictConceptClass` | Bridge.lean:278 | DEFINED | `C.image (fun c => restrictToFinset c S)` : `Finset (S -> Bool)` |
| KK_14 | `restrictToFinset` | Bridge.lean:273 | DEFINED | `fun <x, _> => c x` : restriction of concept to Finset |
| KK_15 | `funcToSubsetFamily` | Bridge.lean:299 | DEFINED | Converts `Finset (S -> Bool)` to `Finset (Finset S)` |
| KK_16 | `boolToSign_abs_eq_one` | Rademacher.lean:35 | PROVED | `\|boolToSign b\| = 1` |
| KK_17 | `boolToSign_sum_zero` | Rademacher.lean:44 | PROVED | `sum_b boolToSign b = 0` |
| KK_18 | `sum_boolToSign_cancel` | Rademacher.lean:80 | PROVED | Rademacher cancellation: sum_sigma boolToSign(sigma_i)*f(sigma) = 0 when f doesn't depend on coord i |

**Mathlib Infrastructure (imported):**

| # | API | File | Exact Signature |
|---|-----|------|-----------------|
| M_1 | `HasSubgaussianMGF` | Mathlib.Probability.Moments.SubGaussian | `structure HasSubgaussianMGF (X : Omega -> R) (c : NNReal) (mu : Measure Omega)` with `integrable_exp_mul` + `mgf_le` |
| M_2 | `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` | SubGaussian.lean:842 | `(hm : AEMeasurable X mu) (hb : ae mu (X in Icc a b)) (hc : integral X mu = 0) : HasSubgaussianMGF X ((norm_nonneg(b-a)/2)^2) mu` |
| M_3 | `measure_sum_ge_le_of_iIndepFun` | SubGaussian.lean:780 | `(h_indep : iIndepFun X mu) (h_subG : forall i in s, HasSubgaussianMGF (X i) (c i) mu) : mu.real {eps <= sum X} <= exp(...)` |
| M_4 | `iIndepFun_pi` | Independence/Basic.lean:784 | `(mX : forall i, AEMeasurable (X i) (mu i)) : iIndepFun (fun i omega => X i (omega i)) (Measure.pi mu)` |
| M_5 | `Measure.pi` | MeasureTheory.Constructions.Pi | Product measure construction |
| M_6 | `Measure.pi_map_pi` | MeasureTheory.Constructions.Pi | Pi of pushforwards = pushforward of pi |

**Zhang Prior Art (NOT imported, for reference):**

| # | API | File | Type |
|---|-----|------|------|
| Z_1 | `expected_max_subGaussian` | SLT/MeasureInfrastructure.lean:181 | `(hX_sgb : forall i in s, forall t, cgf (X i) mu t <= t^2*sigma^2/2) : integral (sup' s X) mu <= sigma * sqrt(2*log\|s\|)` |
| Z_2 | `IsSubGaussianProcess` | SLT/SubGaussian.lean:51 | PseudoMetricSpace-indexed process (NOT needed -- overkill) |

### KU: Key Questions with Counterproof Attempts

**CKU_12: Does uniform measure on `SignVector m` satisfy `iIndepFun` for coordinate projections?**

- **RESOLVED: YES.** Mathlib's `iIndepFun_pi` (Independence/Basic.lean:784) proves EXACTLY this:
  Given `mu : forall i, Measure (Omega_i)` and `X : forall i, Omega_i -> Xi`, then
  `iIndepFun (fun i omega => X i (omega i)) (Measure.pi mu)`.
- Application to our setting: `SignVector m = Fin m -> Bool`. The uniform measure on `SignVector m` IS `Measure.pi (fun _ : Fin m => uniformMeasure Bool)` where `uniformMeasure Bool` assigns 1/2 to each value.
- The coordinate projections `fun i (sigma : SignVector m) => sigma i` are independent under this product measure by `iIndepFun_pi`.
- **Required premise**: `AEMeasurable (fun b => b) (uniformMeasure Bool)` -- trivially true since Bool is discrete and any function on a discrete type is measurable.
- **Type bridge needed**: Our `EmpiricalRademacherComplexity` uses a finite sum `sum_sigma` (over `Fintype (SignVector m)`), NOT an integral over `Measure.pi`. The `1/2^m * sum_sigma f(sigma)` equals `integral f d(counting_measure / 2^m)`. The SubGaussian machinery works with `Measure.pi`, so we need to show that the finite average equals the Measure.pi integral.
- **LOC for bridge**: ~15 lines (show counting measure on `Fin m -> Bool` equals `Measure.pi` of counting measures on Bool).

**CKU_13: Can Massart be proved without SubGaussian (direct exp-moment)?**

- **RESOLVED: YES but SubGaussian is cleaner.** The Massart finite lemma follows from:
  (a) For any lambda > 0: `E[max_j Z_j] <= (1/lambda) * log(E[exp(lambda * max_j Z_j)])`
  (b) `exp(lambda * max) <= sum_j exp(lambda * Z_j)`
  (c) `E[exp(lambda * Z_j)] <= exp(sigma^2 * lambda^2 / 2)` (sub-Gaussian MGF)
  (d) Optimize lambda.
- Steps (a)-(d) can be done with raw exponential estimates without invoking `HasSubgaussianMGF`.
- However, Zhang's `expected_max_subGaussian` already proves this from `cgf` bounds. The cgf approach is essentially the same as SubGaussian but uses the cumulant generating function directly.
- **Recommendation**: Use Zhang's `expected_max_subGaussian` pattern (cgf-based) since it avoids the `HasSubgaussianMGF` structure overhead. OR prove a standalone Massart lemma from scratch (~80 LOC).

**CKU_16 (NEW): Does Mathlib have the Massart finite lemma already?**

- **RESOLVED: NO.** Searched for `expected_max`, `Massart`, `massart_finite` in Mathlib -- no results.
- Mathlib has `measure_sum_ge_le_of_iIndepFun` (Hoeffding inequality for sums) but NOT expected maximum over finite sets.
- Zhang's `expected_max_subGaussian` (SLT/MeasureInfrastructure.lean:181) proves exactly what we need, but it's not in Mathlib and lives in an external library with version mismatch risk.

**CKU_17 (NEW): What is the EXACT type of `EmpiricalRademacherComplexity`?**

- **RESOLVED.** Definition at Rademacher.lean:205:
  ```
  EmpiricalRademacherComplexity X C xs =
    if hm : m = 0 then 0
    else (1 / numSigns) * sum_sigma sSup { r : R | exists h in C, r = |rademacherCorrelation h sigma xs| }
  ```
- Uses `sSup` over a `Set R` (conditional lattice supremum), NOT `Finset.sup` or `iSup`.
- The set `{ r | exists h in C, r = |corr(h,sigma,xs)| }` is the image of C under `h |-> |corr(h,sigma,xs)|`.
- For the Massart proof, we need this sSup to equal a maximum over a finite set (the restriction patterns). This is B1's content.

**CKU_18 (NEW): How does the EmpRad definition interact with the finite restriction set?**

- The `sSup` is over an infinite set (C may be infinite), but the values repeat: `corr(h,sigma,xs)` depends on h only through `(h(xs 0), ..., h(xs (m-1)))`.
- So the set `{ |corr(h,sigma,xs)| : h in C }` has at most `GrowthFunction(C,m)` distinct values.
- The `sSup` of a finite set of reals equals the `max` (i.e., `Finset.sup'`).
- B1 must show: `sSup { r | exists h in C, r = |corr(h,sigma,xs)| } = Finset.sup' (restrictConceptClass C (Finset.univ.image xs)) ...`
- **Critical subtlety**: The existing `restrictConceptClass` in Bridge.lean operates on `Finset (X -> Bool)`, but our C is `Set (X -> Bool)`. Need either:
  (a) Assume C is finite (add `Finset` hypothesis) -- restrictive.
  (b) Show the sSup over the set equals the sSup over the finite image -- works for any C.
  (c) Work directly with the bounded set -- the sSup is well-defined and bounded by 1.

### UK: Pressures from Type Mismatches / Universe Issues

| # | Pressure | Impact | Mitigation |
|---|----------|--------|------------|
| UK_8 | EmpRad uses `sSup` over `Set R` but Massart needs finite `max` | CRITICAL for B1 | Show sSup equals max over finite restriction patterns |
| UK_9 | `HasSubgaussianMGF` uses `NNReal` parameter but our bounds use `R` | MEDIUM | Cast via `NNReal.toReal` or work with NNReal throughout |
| UK_10 | Our EmpRad is a finite sum but SubGaussian API needs `Measure.pi` integral | MEDIUM | Show finite average = integral under counting measure |
| UK_11 | `iIndepFun_pi` works with `Measure.pi` but our sign vectors use counting measure | LOW | Counting measure on `Fin m -> Bool` = `Measure.pi` of counting on Bool |
| UK_12 | `growth_function_le_sauer_shelah` requires `Fintype X, DecidableEq X` | MEDIUM | The sorry is in a general theorem without Fintype. Need to work with the finite restriction set `(Fin m -> X)` locally. |

### UU: Boundary

- Whether a single standalone Massart lemma (~100 LOC) or the full SubGaussian pipeline (~250 LOC) is worth the investment given the remaining sorry count.
- The exact measure-theoretic relationship between our finite-sum EmpRad and the integral form needed for SubGaussian API.
- Whether Zhang's `expected_max_subGaussian` can be imported as a lakefile dependency without breaking our v4.29 build.

---

## 2. Measurement (Pl/Coh/Inv/Comp) for Each Bridge Lemma

### B1: Restriction Collapse

**EmpRad with sSup over C = EmpRad with max over <= GrowthFunction(C,m) patterns**

- **Pl (Plausibility)**: HIGH. Mathematically standard. The correlation `corr(h,sigma,xs)` depends on h only through `(h(xs 0), ..., h(xs (m-1)))`. The number of distinct restriction patterns is at most `GrowthFunction(C,m)`.
- **Coh (Coherence at joints)**: The joint with B3 requires the sSup to be expressed as a finite maximum. The joint with KK_11 (`growth_function_le_sauer_shelah`) requires the finite set to have cardinality bounded by the growth function. Both joints are clean IF we work with the restriction set from Bridge.lean.
  - **HC at B1-B3 joint**: B3 (Massart) needs `E[max_{j<=N} Z_j]`. B1 must produce a `Finset` of patterns with explicit cardinality bound. The output of B1 must be: a `Finset` of functions `Fin m -> Bool` (restriction patterns) with card <= GrowthFunction, and a proof that the sSup equals the Finset.sup' of the corresponding correlation values.
  - **HC at B1-KK_11 joint**: `growth_function_le_sauer_shelah` outputs a bound on `GrowthFunction X C m`. B1 needs `GrowthFunction` or its bound as input for the cardinality of the restriction set. The bridge is clean.
- **Inv (Alternatives)**:
  - Skip B1 entirely: work with sSup directly, bounding it by Massart applied to an INFINITE set. NOT viable -- Massart is for finite sets.
  - Use `restrictConceptClass` from Bridge.lean directly. VIABLE -- this gives the finite set of restriction patterns with cardinality bound.
  - Define a new quotienting map inline. VIABLE but duplicates Bridge.lean infrastructure.
- **Comp (What's proved)**: `restrictConceptClass` (Bridge.lean:278) gives the Finset of distinct restrictions. `card_restrict_le_sauer_shelah_bound` (Bridge.lean:393) bounds its cardinality. What's MISSING: the proof that `sSup { |corr(h,sigma,xs)| : h in C }` equals `Finset.sup'` over the restriction patterns.

### B2: Sub-Gaussianity of Rademacher Correlation

**Each correlation variable is (1/sqrt(m))-sub-Gaussian under uniform sign measure**

- **Pl**: HIGH. Each `corr_j(sigma) = (1/m) * sum_i a_{j,i} * boolToSign(sigma_i)` with `|a_{j,i}| <= 1`. Each summand lies in `[-1/m, 1/m]`. The sigma_i are independent under the product measure (by `iIndepFun_pi`). Hoeffding's lemma (`hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`) gives sub-Gaussianity for each summand. Sum of independent sub-Gaussians is sub-Gaussian (by `sum_of_iIndepFun` or similar).
- **Coh**:
  - **HC at B2-M_2 joint**: `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` requires `AEMeasurable X mu`, `ae mu (X in Icc a b)`, `integral X mu = 0`. For each summand `f_i(sigma) = a_i * boolToSign(sigma_i) / m`: AEMeasurable is trivial on discrete space; Icc bound is `[-1/m, 1/m]`; integral = 0 by `boolToSign_sum_zero`.
  - **HC at B2-M_4 joint**: `iIndepFun_pi` gives independence of coordinate projections under `Measure.pi`. We need: the summands `f_i(sigma) = g_i(sigma_i)` are functions of DIFFERENT coordinates, hence independent. This is the composition: `f_i = g_i . proj_i` where `proj_i` are independent by `iIndepFun_pi`.
  - **HC at B2-UK_10 joint**: Our EmpRad is a FINITE sum, not an integral. The sub-Gaussian bound gives `E[max Z_j]` under `Measure.pi`. We need to show this equals our `(1/2^m) * sum_sigma max_j |Z_j(sigma)|`. This is the counting-measure-to-Measure.pi bridge.
- **Inv**:
  - Direct Hoeffding without SubGaussian: use `exp(t * sum_i f_i)` directly, factor by independence, bound each `E[exp(t*f_i)]` by `exp(t^2/(8m^2))`. This avoids `HasSubgaussianMGF` entirely.
  - Use the variance bound (`rademacher_variance_eq`, KK_5) with Chebyshev. Only gives `E[max] <= sqrt(GF/m)` which is weaker than Massart's `sqrt(2*log(GF)/m)`.
- **Comp**: `iIndepFun_pi` is PROVED in Mathlib. `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` is PROVED. `boolToSign_sum_zero` is PROVED. The connection between counting measure and `Measure.pi` is NOT proved in our codebase.

### B3: Massart Finite Lemma

**E[max_{j<=N} Z_j] <= sigma * sqrt(2 * log(N)) for sigma-sub-Gaussian RVs**

- **Pl**: HIGH. Standard textbook result (Boucheron-Lugosi-Massart 2013, Lemma 2.6). The proof is the Chernoff method: optimize lambda in `E[max] <= (1/lambda) * log(sum_j E[exp(lambda*Z_j)])`.
- **Coh**:
  - **HC at B3-B1 joint**: B1 provides `N = (restrictConceptClass C S).card`. B3 needs `N >= 2` for `log(N) > 0`. If N = 0 or 1, the bound is trivially true (max of 0 or 1 variables). Handle as special cases.
  - **HC at B3-B2 joint**: B2 provides `HasSubgaussianMGF (Z_j) c mu` for each restriction pattern j. B3 needs the cgf bound `cgf Z_j mu t <= t^2 * sigma^2 / 2`. This follows from `HasSubgaussianMGF.mgf_le` by taking log.
  - **HC at B3-M_1 joint**: Mathlib's `HasSubgaussianMGF` uses `NNReal` parameter `c` where the sub-Gaussian variance proxy is `c`. Our sigma = 1/sqrt(m), so c = 1/m as `NNReal`. The conversion is clean: `(1/m : NNReal)`.
- **Inv**:
  - Import Zhang's `expected_max_subGaussian` directly. This theorem uses `cgf`-based bounds (not `HasSubgaussianMGF`), taking `(hX_sgb : forall i in s, forall t, cgf (X i) mu t <= t^2*sigma^2/2)`. This BYPASSES the entire `HasSubgaussianMGF` overhead.
  - Prove from scratch using exponential moments. ~80-100 LOC.
  - Use tail integration `E[max] = integral P[max >= t] dt`. Gives WEAKER bound `O(N*sigma)` instead of `sigma*sqrt(log N)`.
- **Comp**: Zhang has `expected_max_subGaussian` PROVED (SLT/MeasureInfrastructure.lean:181). Mathlib has NO Massart lemma. We have NO Massart lemma.

### B4: Assembly

**Chain B1 + B3 + Sauer-Shelah: EmpRad(xs) <= sqrt(2*d*log(2m/d)/m)**

- **Pl**: HIGH. Pure algebraic chaining of the three bounds.
- **Coh**: All joints already analyzed. The final algebra: `(1/sqrt(m)) * sqrt(2*log(N))` where `N <= (2m/d)^d` gives `sqrt(2*d*log(2m/d)/m)`. The `log((2m/d)^d) = d*log(2m/d)` step uses `Real.log_pow`.
- **Inv**: No alternative -- this is just the assembly.
- **Comp**: All components available once B1-B3 are proved. Algebra lemma `analytical_log_sqrt_bound` (KK_9) already handles the m-large-enough case.

---

## 3. Bridge Lemma Specifications

### B1: `restriction_collapse` (~50 LOC)

**Exact Lean4 Statement:**

```lean
/-- The sSup over C in EmpRad equals the Finset.sup' over restriction patterns. -/
private theorem restriction_collapse {X : Type u} {m : ℕ} (hm : 0 < m)
    (C : ConceptClass X Bool) (σ : SignVector m) (xs : Fin m → X) :
    sSup { r : ℝ | ∃ h ∈ C, r = |rademacherCorrelation h σ xs| } =
      if hne : { f : Fin m → Bool | ∃ h ∈ C, ∀ i, h (xs i) = f i }.Nonempty then
        sSup { r : ℝ | ∃ f ∈ { f : Fin m → Bool | ∃ h ∈ C, ∀ i, h (xs i) = f i },
          r = |(1 / (m : ℝ)) * ∑ i : Fin m, boolToSign (σ i) * boolToSign (f i)| }
      else 0
```

**Proof Sketch:**

```
-- Key insight: rademacherCorrelation h σ xs depends on h only through (h(xs 0), ..., h(xs (m-1)))
-- 1. Show: corr(h, σ, xs) = corr(h', σ, xs) whenever h(xs i) = h'(xs i) for all i
-- 2. The set of values { |corr(h,σ,xs)| : h ∈ C } = { |corr(f,σ,xs)| : f ∈ restrictions }
-- 3. So sSup of the original set = sSup of the restriction set
-- 4. The restriction set is finite (subset of Fin m → Bool) with card ≤ GrowthFunction
--
-- Tactic outline:
-- congr 1; ext r; constructor
-- · rintro ⟨h, hC, rfl⟩
--   exact ⟨fun i => h (xs i), ⟨h, hC, fun i => rfl⟩, by unfold rademacherCorrelation; congr 1; ...⟩
-- · rintro ⟨f, ⟨h, hC, hf⟩, rfl⟩
--   exact ⟨h, hC, by unfold rademacherCorrelation; congr 1; ...⟩
```

**Required Mathlib APIs:** None beyond basic `sSup` and `Set.ext`.

**LOC Estimate:** 40-50 lines.

**Blockers:** None. Pure set-theoretic reasoning.

**Risk:** LOW.

### B2: `rademacher_summand_subgaussian` (~70 LOC)

**Exact Lean4 Statement (Option A -- cgf-based, avoiding HasSubgaussianMGF):**

```lean
/-- Each restriction-pattern correlation is sub-Gaussian under counting measure.
    For fixed xs and restriction pattern f : Fin m → Bool:
    Z_f(σ) = (1/m) * Σ_i boolToSign(σ_i) * boolToSign(f i)
    satisfies cgf Z_f μ_count t ≤ t² / (2m) for all t,
    where μ_count = Measure.pi (fun _ => (1/2) • (Measure.dirac true + Measure.dirac false)). -/
private theorem rademacher_correlation_cgf_bound {m : ℕ} (hm : 0 < m)
    (f : Fin m → Bool) :
    let μ := MeasureTheory.Measure.pi (fun _ : Fin m => uniformMeasure Bool)
    ∀ t : ℝ, ProbabilityTheory.cgf
      (fun σ : SignVector m => (1 / (m : ℝ)) * ∑ i, boolToSign (σ i) * boolToSign (f i))
      μ t ≤ t ^ 2 / (2 * m)
```

**Proof Sketch:**

```
-- The function Z(σ) = (1/m) * Σ_i a_i * boolToSign(σ_i) where a_i = boolToSign(f i), |a_i| = 1.
-- Z = (1/m) * Σ_i Z_i where Z_i(σ) = a_i * boolToSign(σ_i).
-- Each Z_i is bounded in [-1/m, 1/m] and has E[Z_i] = 0 (by boolToSign_sum_zero).
-- The σ_i are iIndepFun under Measure.pi (by iIndepFun_pi).
-- By Hoeffding's lemma (hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero):
--   HasSubgaussianMGF Z_i ((‖1/m - (-1/m)‖₊/2)^2 = (1/m)^2) μ
-- By sum_of_iIndepFun: HasSubgaussianMGF (Σ Z_i) (Σ (1/m)^2 = 1/m) μ
-- The cgf bound follows: cgf Z μ t ≤ t^2 * (1/m) / 2 = t^2/(2m).
--
-- ALTERNATIVE (avoiding HasSubgaussianMGF, using direct finite computation):
-- Since SignVector m is finite, cgf = log(E[exp(t*Z)]) = log((1/2^m) * Σ_σ exp(t*Z(σ))).
-- Factor: Σ_σ exp(t/m * Σ_i a_i*bs(σ_i)) = Π_i (Σ_{b:Bool} exp(t*a_i*bs(b)/m))
-- because the sigma_i are independent coordinates.
-- Each factor = exp(t*a_i/m) + exp(-t*a_i/m) ≤ 2*exp(t²/(2m²)) by Hoeffding's lemma.
-- Product = 2^m * exp(t²·m/(2m²)) = 2^m * exp(t²/(2m)).
-- So E[exp(tZ)] = (1/2^m) * Σ = exp(t²/(2m)).
-- cgf = log(E[exp(tZ)]) ≤ t²/(2m).
```

**Required Mathlib APIs:**
- `iIndepFun_pi` for independence (or direct finite factoring)
- `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` for Hoeffding's lemma per summand
- `sum_of_iIndepFun` for sum of independent sub-Gaussians (if using HasSubgaussianMGF route)
- OR: `Finset.prod_sum` for direct computation (if using finite factoring)

**LOC Estimate:** 60-80 lines.

**Blockers:**
- UK_10: Connection between our finite sum and `Measure.pi` integral. Resolved by choosing the direct finite computation route.
- UK_11: Counting measure = Measure.pi. Resolved by `iIndepFun_pi`.

**Risk:** MEDIUM. The type-level machinery around `Measure.pi` on finite types may require ~20 LOC of boilerplate.

### B3: `massart_finite_lemma` (~100 LOC)

**Exact Lean4 Statement:**

```lean
/-- Massart's finite lemma: expected maximum of sub-Gaussian random variables.
    For random variables Z_1,...,Z_N each satisfying cgf Z_j μ t ≤ t²σ²/2:
    E[max_{j∈s} Z_j] ≤ σ * √(2 * log |s|).
    This is the key concentration result for Rademacher complexity. -/
theorem massart_finite_lemma {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {ι : Type*} {Z : ι → Ω → ℝ} {σ : ℝ} (hσ : 0 < σ)
    {s : Finset ι} (hs : s.Nonempty) (hs_card : 2 ≤ s.card)
    (hZ_meas : ∀ i ∈ s, Measurable (Z i))
    (hZ_int : ∀ i ∈ s, MeasureTheory.Integrable (Z i) μ)
    (hZ_cgf : ∀ i ∈ s, ∀ t : ℝ, ProbabilityTheory.cgf (Z i) μ t ≤ t ^ 2 * σ ^ 2 / 2)
    (hZ_int_exp : ∀ i ∈ s, ∀ t : ℝ,
      MeasureTheory.Integrable (fun ω => Real.exp (t * Z i ω)) μ) :
    ∫ ω, s.sup' hs (fun i => Z i ω) ∂μ ≤ σ * Real.sqrt (2 * Real.log s.card)
```

**Proof Sketch:**

```
-- Standard Chernoff + union bound + optimize lambda:
-- For any lambda > 0:
--   E[sup' s Z] <= (1/lambda) * log(E[exp(lambda * sup' s Z)])
--   <= (1/lambda) * log(Σ_{j∈s} E[exp(lambda * Z_j)])
--   <= (1/lambda) * log(|s| * exp(lambda² σ² / 2))
--   = (1/lambda) * (log|s| + lambda² σ² / 2)
-- Set lambda = sqrt(2 * log|s|) / σ:
--   = σ * sqrt(2 * log|s|)
--
-- Tactic outline:
-- set n := s.card
-- set lambda := sqrt(2 * log n) / σ
-- have h_lambda_pos : 0 < lambda := ...
-- -- Step 1: E[max] ≤ (1/lambda) * log(E[exp(lambda * max)])
-- have h1 := jensen_log_exp_bound ... -- from exp_mean_ge_mean_exp
-- -- Step 2: exp(lambda * max) ≤ Σ exp(lambda * Z_j)
-- have h2 : ∀ ω, exp(lambda * sup' s Z ω) ≤ Σ_{j∈s} exp(lambda * Z j ω) := ...
-- -- Step 3: E[Σ] = Σ E by linearity
-- -- Step 4: Each E[exp(lambda * Z_j)] ≤ exp(lambda² σ² / 2) by cgf bound
-- -- Step 5: Σ ≤ n * exp(lambda² σ² / 2)
-- -- Step 6: Algebra with lambda = sqrt(2*log n)/σ gives σ*sqrt(2*log n)
```

**Required Mathlib APIs:**
- `Real.log_le_log`, `Real.exp_le_exp` for monotonicity
- `MeasureTheory.integral_mono` for integral comparison
- `Finset.sup'_le`, `Finset.le_sup'` for max properties
- `Real.exp_add`, `Real.log_mul`, `Real.log_exp` for algebra
- `Real.sqrt_div`, `Real.sqrt_mul` for final simplification

**LOC Estimate:** 80-120 lines. This is the HARDEST bridge lemma.

**Blockers:**
- Step 1 (Jensen) requires either a direct proof that `x <= (1/t)*log(exp(t*x))` or a call to Jensen's inequality for concave log. The former is trivial: `x = log(exp(x)) = (1/t)*log(exp(t*x))` is an EQUALITY, not inequality. The bound comes from `max <= log_sum_exp`.
- Step 2 (exp-of-max <= sum-of-exp) is standard: `exp(max_j x_j) <= sum_j exp(x_j)`.
- The measurability/integrability of `sup'` may require work.

**Risk:** MEDIUM-HIGH. The main risk is Step 1 (bounding E[max] by log-sum-exp) and the measurability of `Finset.sup'`.

### B4: `assembly` (~30 LOC)

**Exact Lean4 Statement:**

(This is the sorry itself -- `vcdim_bounds_rademacher_quantitative`, B < 1 branch)

```lean
-- Inside the sorry at line 435:
-- Goal: EmpiricalRademacherComplexity X C xs ≤ B
-- where B = sqrt(2 * d * log(2 * m / d) / m)
--
-- Chain:
-- EmpRad(xs) = (1/2^m) * Σ_σ sSup_{h∈C} |corr(h,σ,xs)|      [definition]
--            = (1/2^m) * Σ_σ max_{f∈restrictions} |corr(f,σ)|  [B1: restriction_collapse]
--            = E_σ[max_{f∈R} |Z_f(σ)|]                          [notation]
--            ≤ (1/√m) * √(2 * log |R|)                          [B3: massart_finite_lemma]
--            ≤ (1/√m) * √(2 * d * log(2m/d))                    [Sauer-Shelah: |R| ≤ (2m/d)^d]
--            = √(2 * d * log(2m/d) / m)                          [algebra]
--            = B
```

**Required Mathlib APIs:**
- `Real.log_pow` for `log((2m/d)^d) = d*log(2m/d)`
- `Real.sqrt_div` for final rearrangement
- `Nat.choose_le` or direct Sauer-Shelah bound

**LOC Estimate:** 25-35 lines.

**Blockers:** None once B1-B3 are proved.

**Risk:** LOW.

---

## 4. Counterfactual Proof Pathways

### Route A: Full SubGaussian Chain (B1+B2+B3+B4)

- **Description**: Prove all four bridge lemmas as specified above. Use Mathlib's `HasSubgaussianMGF`, `iIndepFun_pi`, `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`, and prove Massart from scratch.
- **LOC**: ~250 total (B1:50 + B2:70 + B3:100 + B4:30)
- **Viability**: HIGH. All Mathlib APIs exist. No external dependencies.
- **Blockers**: Massart lemma is the hardest part (~100 LOC). The connection between finite sum EmpRad and Measure.pi integral needs ~15 LOC of boilerplate.
- **Risk**: MEDIUM. The SubGaussian pipeline is well-understood but verbose in Lean4.

### Route B: Direct Hoeffding + Tail Integration (Bypass Massart)

- **Description**: Skip the Chernoff-optimize-lambda approach. Instead use:
  1. B1 (restriction collapse) -- same as Route A
  2. Union bound: `P[max_j Z_j >= t] <= N * P[Z_1 >= t] <= N * exp(-m*t²/2)`
  3. Tail integration: `E[max_j Z_j] = integral_0^infty P[max >= t] dt`
  4. Evaluate: `integral_0^infty N*exp(-m*t²/2) dt = N*sqrt(pi/(2m))`
  5. This gives `E[max] <= N*sqrt(pi/(2m))` which is MUCH WORSE than Massart: linear in N vs sqrt(log N).
- **LOC**: ~200
- **Viability**: LOW. The bound is `O(N/sqrt(m))` instead of `O(sqrt(log(N)/m))`. This does NOT give the required `sqrt(2*d*log(2m/d)/m)` bound.
- **Blockers**: The tail integration in Lean requires `lintegral_rpow_eq_lintegral_meas_lt` or Gaussian integrals.
- **Risk**: HIGH. The bound is too weak for our theorem statement.

### Route C: Cauchy-Schwarz Generalization (from VCDim=0 Pattern)

- **Description**: Generalize `vcdim_zero_rademacher_le_inv_sqrt` (KK_8). For general VCDim=d:
  1. EmpRad = (1/N) * Σ_σ max_j |Z_j(σ)|
  2. By Cauchy-Schwarz: ((1/N) * Σ_σ max_j |Z_j|)² ≤ (1/N) * Σ_σ (max_j |Z_j|)²
  3. (max_j |Z_j|)² ≤ Σ_j Z_j² (since max² ≤ sum of squares for nonneg terms)
  4. Σ_σ Σ_j Z_j² = Σ_j Σ_σ Z_j² = number_of_patterns * (1/m) (by rademacher_variance_eq)
  5. So EmpRad² ≤ GrowthFunction(C,m) / m
  6. EmpRad ≤ sqrt(GrowthFunction/m) ≤ sqrt((2m/d)^d / m)
- **LOC**: ~100
- **Viability**: LOW. The bound `sqrt(GF/m)` is WEAKER than `sqrt(2*d*log(2m/d)/m)`. For `GF ~ (em/d)^d`, `sqrt(GF/m) ~ (em/d)^{d/2} / sqrt(m)` which is polynomial in m for fixed d. Our theorem requires a bound that goes to 0 as m -> infinity, which `sqrt(GF/m)` does NOT (it grows for d >= 2).
- **Blockers**: Cannot match the theorem statement without Massart.
- **Risk**: FATAL. The bound doesn't match the required form.

### Route D: Import Zhang's `expected_max_subGaussian`

- **Description**: Add Zhang's `lean-stat-learning-theory` as a lakefile dependency. Use `expected_max_subGaussian` directly for B3.
- **LOC**: ~150 (B1:50 + B2_bridge:50 + B4:30 + lakefile:20)
- **Viability**: MEDIUM. Zhang's theorem takes `cgf`-based bounds, matching our needs exactly. The type signature is:
  ```lean
  theorem expected_max_subGaussian {ι : Type*}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {σ : ℝ} (hσ : 0 < σ)
    {s : Finset ι} (hs : s.Nonempty) (hs_card : 2 ≤ s.card)
    (hX_meas : ∀ i ∈ s, Measurable (X i))
    (hX_int_basic : ∀ i ∈ s, Integrable (X i) μ)
    (hX_sgb : ∀ i ∈ s, ∀ t, cgf (X i) μ t ≤ t^2 * σ^2 / 2)
    (hX_int_exp : ∀ i ∈ s, ∀ t, Integrable (fun ω => exp (t * X i ω)) μ) :
    ∫ ω, s.sup' hs (fun i => X i ω) ∂μ ≤ σ * sqrt (2 * log s.card)
  ```
  This is EXACTLY what B3 needs. The cgf-based interface avoids `HasSubgaussianMGF` entirely.
- **Blockers**:
  - Zhang uses Lean v4.27.0-rc1, we use v4.29.0-rc6. Two minor version gap.
  - Mathlib version alignment unknown. Risk of `sorry` in Zhang's library or API changes.
  - The lakefile dependency adds build complexity.
- **Risk**: HIGH for build stability, LOW for mathematical content.

### Recommendation

**Route A is the PRIMARY recommendation.** Self-contained, no external dependencies, well-understood proof path. The 250 LOC investment is justified by closing the key sorry.

**Route D is the FALLBACK** if Route A's B3 (Massart) proves too verbose. The Zhang import saves ~100 LOC on B3 at the cost of a build dependency.

Routes B and C are NOT viable -- they produce bounds too weak for the theorem statement.

---

## 5. Prior Art Check

### Zhang's lean-stat-learning-theory

| Component | Available? | Type Signature | Compatible? | Notes |
|-----------|-----------|----------------|-------------|-------|
| `expected_max_subGaussian` | YES (PROVED) | cgf-based, Finset-indexed | YES | Exact match for B3. Uses `cgf` not `HasSubgaussianMGF`. |
| `IsSubGaussianProcess` | YES (PROVED) | PseudoMetricSpace-indexed | NO | Overkill. Our setting is finite RVs, not metric processes. |
| `subGaussian_tail_bound` | YES (PROVED) | Chernoff tail bound | NOT NEEDED | We don't need tail bounds, we need expected max. |
| `subGaussian_first_moment_bound` | YES (PROVED) | E[\|X_s - X_t\|] bound | NOT NEEDED | Wrong direction (first moment, not max). |
| Rademacher definition | NO | N/A | N/A | Zhang defines Gaussian complexity, not Rademacher. |
| Massart standalone | NO | N/A | N/A | Their Massart is embedded in `expected_max_subGaussian`. |
| **Overall**: `expected_max_subGaussian` is the only useful theorem. It's directly usable IF imported. |

### Sonoda's lean-rademacher (auto-res/lean-rademacher)

- NOT present in our `prior-art/` directory. Was referenced in v1 URS but not evaluated.
- From the v1 URS: does NOT prove Massart, has a different Rademacher definition.
- **Verdict**: NOT useful.

### Mathlib Lemmas We're Missing

| Lemma | Status | Impact |
|-------|--------|--------|
| Massart finite lemma | NOT IN MATHLIB | Must prove ourselves or import Zhang |
| `iIndepFun_pi` | IN MATHLIB (proved) | Resolves CKU_12 |
| `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` | IN MATHLIB (proved) | Hoeffding's lemma for B2 |
| `measure_sum_ge_le_of_iIndepFun` | IN MATHLIB (proved) | Hoeffding inequality (not directly needed, B3 is about max not sum) |
| Counting measure = Measure.pi for finite types | IN MATHLIB (implicit in Measure.pi construction) | Needed for UK_10/UK_11 bridge |
| exp-of-max <= sum-of-exp for Finset | NOT IN MATHLIB as standalone lemma | Easy to prove (~5 LOC) |
| Jensen for log (concave) | IN MATHLIB (various forms) | Needed for B3 Step 1 |

---

## 6. K/U Update (D6 Massart v2)

### KK (Verified -- net new since v2 URS)

- KK_19: `iIndepFun_pi` (Mathlib Independence/Basic.lean:784) provides exactly the independence structure needed for B2. Coordinate projections on `Measure.pi` are independent.
- KK_20: `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` (Mathlib SubGaussian.lean:842) provides Hoeffding's lemma with parameter `((b-a)/2)^2` as NNReal.
- KK_21: Zhang's `expected_max_subGaussian` (SLT/MeasureInfrastructure.lean:181) is PROVED and uses cgf-based interface. This is the only external theorem that would help.
- KK_22: The sorry target (`vcdim_bounds_rademacher_quantitative`, line 435) is ONLY the `B < 1` case. The `B >= 1` case is already handled by `empiricalRademacherComplexity_le_one`. The integral monotonicity step (Rad = integral EmpRad <= integral B = B) is already proved.

### KU (Articulated unknowns -- net new)

- CKU_12: RESOLVED. `iIndepFun_pi` gives independence of coordinate projections. See analysis above.
- CKU_16: RESOLVED. No Massart in Mathlib. Must prove or import.
- CKU_17: RESOLVED. EmpRad uses `sSup` over `Set R`. See analysis above.
- CKU_18: RESOLVED. The `sSup` collapses to a finite max over restriction patterns. See B1 specification.
- CKU_19 (NEW): The EXACT measure on `SignVector m` used in EmpRad. EmpRad uses `(1/2^m) * sum_sigma`, which equals `integral d(counting/2^m)`. Need to show this equals `integral d(Measure.pi (fun _ => uniform Bool))`. This is a ~15 LOC lemma.
- CKU_20 (NEW): Whether `Finset.sup' hs (fun i => Z i omega)` is measurable and integrable under `Measure.pi`. Since `SignVector m` is finite, this is trivial (all functions on finite types are measurable). But the Lean API may require explicit instances.

### UK (Pressures -- net new)

- UK_8: RESOLVED by B1 design: sSup collapses to finite max.
- UK_9: MEDIUM. The `NNReal` vs `R` conversion for sub-Gaussian parameter. Workaround: use cgf-based approach (Route A variant or Route D) which avoids `HasSubgaussianMGF` entirely.
- UK_10: RESOLVED by CKU_19 design: prove counting measure = Measure.pi bridge.
- UK_11: RESOLVED by `iIndepFun_pi`.
- UK_12: MEDIUM. `growth_function_le_sauer_shelah` requires `Fintype X`. The sorry is in a general theorem without Fintype. Resolution: the restriction set is finite regardless of X (it's a subset of `Fin m -> Bool`). Work with `card_restrict_le_sauer_shelah_bound` which operates on `Finset (X -> Bool)`. BUT our C is `Set (X -> Bool)`, not `Finset`. Resolution: the B1 lemma works at the sSup level, showing the sSup equals a finite max. The cardinality bound comes from the Sauer-Shelah bound on the finite restriction set.

---

## 7. Recommended Implementation Plan

### Phase 1: Standalone Massart Lemma (~100 LOC)

**Why first**: B3 is the hardest and highest-risk component. Proving it first de-risks the entire effort.

**Strategy**: Prove `massart_finite_lemma` as a standalone theorem in Rademacher.lean (or a new helper file). Use the cgf-based approach matching Zhang's interface:

1. For any `lambda > 0`: `E[sup' s Z] <= (1/lambda) * log(E[exp(lambda * sup' s Z)])` (~20 LOC)
2. `exp(lambda * sup' s Z) <= sum_{j in s} exp(lambda * Z_j)` (~10 LOC)
3. `E[sum] = sum E`, each `E[exp(lambda*Z_j)] <= exp(lambda^2*sigma^2/2)` (~15 LOC)
4. Algebra: `(1/lambda) * (log|s| + lambda^2*sigma^2/2)` with `lambda = sqrt(2*log|s|)/sigma` gives `sigma*sqrt(2*log|s|)` (~30 LOC)
5. Edge cases: `|s| = 0, 1` (~10 LOC)

### Phase 2: B1 Restriction Collapse (~50 LOC)

**Strategy**: Show the sSup in EmpRad collapses to a maximum over restriction patterns.

1. Prove `corr(h,sigma,xs) = corr(h',sigma,xs)` when `h|_xs = h'|_xs` (~10 LOC)
2. Show the set of values is a subset of a finite set (~15 LOC)
3. Conclude sSup = max over finite set (~15 LOC)
4. Connect to `card_restrict_le_sauer_shelah_bound` for cardinality bound (~10 LOC)

### Phase 3: B2 Sub-Gaussianity (~70 LOC)

**Strategy**: Use direct finite computation (avoid `HasSubgaussianMGF` overhead).

1. Show the counting measure on `SignVector m` = `Measure.pi (fun _ => uniform Bool)` (~15 LOC)
2. Factor the exponential moment: `E[exp(t*Z)] = product_i E_i[exp(t*g_i(sigma_i))]` (~20 LOC)
3. Bound each factor by Hoeffding's lemma (~15 LOC)
4. Conclude cgf bound (~10 LOC)

### Phase 4: B4 Assembly (~30 LOC)

**Strategy**: Chain B1 + B3 + Sauer-Shelah.

1. Apply B1 to rewrite sSup as finite max
2. Apply B3 with N = cardinality of restriction set
3. Apply Sauer-Shelah bound on N
4. Algebra to get sqrt(2*d*log(2m/d)/m)

### Total LOC: ~250. Total sorrys closed: 1 (the Massart sorry).

---

## 8. A4/A5 Compliance

### A4 (No trivially-true sorrys)

The sorry at line 435 is in the `B < 1` branch, which requires genuine Massart content. The `B >= 1` case is already handled. The proof chain B1-B4 is non-trivial mathematical content (sub-Gaussian concentration, Sauer-Shelah combinatorics). **A4 CLEAN.**

### A5 (No simplification under obstruction)

The proof route is the standard textbook chain (SSBD Ch.26, Mohri Ch.3, BLM 2013). No statement weakening is proposed. The theorem statement `RademacherComplexity X C D m <= sqrt(2*d*log(2*m/d)/m)` matches the standard bound. The bridge lemmas B1-B4 are the canonical proof components. **A5 CLEAN.**

---

## Literature References

1. Shalev-Shwartz & Ben-David (2014). Understanding Machine Learning. Ch.26.
2. Mohri, Rostamizadeh & Talwalkar (2018). Foundations of Machine Learning. 2nd ed. Ch.3.
3. Massart, P. (2000). Some applications of concentration inequalities to statistics.
4. Boucheron, Lugosi & Massart (2013). Concentration Inequalities. Ch.2, Lemma 2.6.
5. Zhang, Y. et al. (2026). Statistical Learning Theory in Lean 4. arXiv:2602.02285.
6. Degenne, R. (2025). SubGaussian module in Mathlib4.
7. Vershynin, R. (2018). High-Dimensional Probability. Ch.2.
