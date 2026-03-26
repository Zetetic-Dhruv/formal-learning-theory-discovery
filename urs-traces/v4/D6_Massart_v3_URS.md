# D6 Massart v3 URS -- Zhang Port Specification + Complete Counterfactual Proof Infrastructure

**Date**: 2026-03-20
**Target**: The single `sorry` at Rademacher.lean:435 (`vcdim_bounds_rademacher_quantitative`)
**Scope**: Complete closure via inline Massart finite lemma (ported from Zhang) + bridge lemmas B1-B4
**Supersedes**: D6_Massart_v2_URS.md (all content carried forward + Zhang source analysis + complete tactic sketches)

---

## 0. Zhang Source Code Analysis (PHASE 2 COMPLETE)

### What Was Read

1. **`SLT/MeasureInfrastructure.lean`** (Zhang, Lean 4.27.0-rc1): FULL content retrieved via WebFetch.
2. **`SLT/SubGaussian.lean`** (Zhang): FULL content retrieved. Contains `IsSubGaussianProcess` (PseudoMetricSpace-indexed, NOT needed).
3. **`lakefile.lean`** + **`lean-toolchain`** (Zhang): Lean 4.27.0-rc1, Mathlib master branch.

### Zhang's `expected_max_subGaussian` -- EXACT Type Signature

```lean
theorem expected_max_subGaussian {ι : Type*}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {σ : ℝ} (hσ : 0 < σ)
    {s : Finset ι} (hs : s.Nonempty) (hs_card : 2 ≤ s.card)
    (hX_meas : ∀ i ∈ s, Measurable (X i))
    (hX_int_basic : ∀ i ∈ s, Integrable (X i) μ)
    (hX_sgb : ∀ i ∈ s, ∀ t, ProbabilityTheory.cgf (X i) μ t ≤ t^2 * σ^2 / 2)
    (hX_int_exp : ∀ i ∈ s, ∀ t, Integrable (fun ω => exp (t * X i ω)) μ) :
    ∫ ω, s.sup' hs (fun i => X i ω) ∂μ ≤ σ * sqrt (2 * log s.card)
```

### Zhang's Proof Structure (6 Steps)

1. **Setup**: `n = s.card`, `t_opt = sqrt(2*log n) / σ`
2. **Algebraic identity**: `(1/t_opt) * (log n + t_opt^2*σ^2/2) = σ*sqrt(2*log n)`
3. **Step 1 (Integrability)**: `sup'` is integrable via bound by `∑|X_i|`
4. **Step 2 (MGF bound)**: `E[exp(t*X_i)] ≤ exp(t^2*σ^2/2)` from cgf hypothesis
5. **Step 3 (Soft-max)**: `E[exp(t*sup')] ≤ n * exp(t^2*σ^2/2)` via `exp_mul_sup'_le_sum`
6. **Step 4-6**: `E[sup'] ≤ (1/t)*log(E[exp(t*sup')]) ≤ (1/t)*(log n + t^2σ^2/2) = σ*sqrt(2*log n)`

### Zhang Helper Lemmas (ALL to port)

| Lemma | Lines | Role | Port Decision |
|-------|-------|------|---------------|
| `exp_sup'_le_sum` | ~8 | `exp(max_i f_i) ≤ Σ exp(f_i)` | PORT INLINE (~8 LOC) |
| `exp_mul_sup'_le_sum` | ~8 | Scaled version: `exp(t*max) ≤ Σ exp(t*f_i)` | PORT INLINE (~8 LOC) |
| `abs_sup'_le_sum` | ~6 | `|max_i f_i| ≤ Σ |f_i|` | PORT INLINE (~6 LOC) |
| `jensen_exp` | ~8 | `exp(E[X]) ≤ E[exp(X)]` (Jensen for convex exp) | PORT INLINE (~8 LOC) |
| `mean_le_log_mgf` | ~15 | `E[X] ≤ (1/t)*log E[exp(tX)]` for t > 0 | PORT INLINE (~15 LOC) |
| `measure_finset_sup_ge_le_sum` | ~12 | Union bound for sup' | NOT NEEDED (not used in main proof) |
| `chernoff_bound_cgf` | ~3 | P(X>=eps) ≤ exp(cgf-t*eps) | NOT NEEDED |
| `chernoff_bound_subGaussian` | ~15 | Optimized Chernoff for sub-Gaussian | NOT NEEDED |

**Total port LOC for helpers**: ~45 LOC
**Total port LOC for `expected_max_subGaussian`**: ~60 LOC
**Grand total inline Massart**: ~105 LOC

### Version Compatibility Analysis

| Feature | Zhang (4.27.0-rc1) | Ours (4.29.0-rc6) | Compatible? |
|---------|--------------------|--------------------|-------------|
| `ProbabilityTheory.cgf` | Used directly | Available in Mathlib | YES |
| `ProbabilityTheory.mgf` | Used via cgf | Available | YES |
| `Finset.sup'` | Standard | Standard | YES |
| `Finset.measurable_sup'` | Used in integrability | Need to verify | CHECK |
| `ConvexOn.map_integral_le` | Used for Jensen | Available | YES |
| `integral_exp_pos` | Helper | May need inline proof | CHECK |
| `exp_le_exp` | `exp_le_exp.mpr` | Same API | YES |
| `log_le_log` | Standard | Standard | YES |

**Potential breakages (4.27 -> 4.29)**:
1. `Finset.measurable_sup'` -- may have changed signature. Fallback: prove directly for finite type.
2. `integral_exp_pos` -- may not exist as named lemma. Inline: `integral_pos_of_nonneg_of_support`.
3. Minor name changes in Mathlib APIs between versions. Risk: LOW (2 minor versions).

---

## 1. Complete KK/UK/KU Universe

### KK: All Proved Infrastructure (v3 -- includes all v2 + new)

| # | Component | Location | Status | Exact Type/Role |
|---|-----------|----------|--------|-----------------|
| KK_1 | `EmpiricalRademacherComplexity` | Rademacher.lean:205 | DEFINED | `(1/2^m) * Σ_σ sSup { r : R \| ∃ h ∈ C, r = \|corr(h,σ,xs)\| }` |
| KK_2 | `RademacherComplexity` | Rademacher.lean:247 | DEFINED | `∫ xs, EmpRad(xs) ∂(Measure.pi D)` |
| KK_3 | `rademacherCorrelation` | Rademacher.lean:177 | DEFINED | `(1/m) * Σ_i boolToSign(σ i) * boolToSign(h(xs i))` |
| KK_4 | `empiricalRademacherComplexity_le_one` | Rademacher.lean:213 | PROVED | `EmpRad ≤ 1` |
| KK_5 | `rademacher_variance_eq` | Rademacher.lean:122 | PROVED | `Σ_σ (Σ_i bs(σ i)*a_i)² = m * \|SignVector m\|` when `\|a_i\|=1` |
| KK_6 | `empRad_eq_one_of_all_labelings` | Rademacher.lean:349 | PROVED | EmpRad = 1 when all labelings realized |
| KK_7 | `shatters_subset` | Rademacher.lean:324 | PROVED | Subset of shattered set is shattered |
| KK_8 | `vcdim_zero_rademacher_le_inv_sqrt` | Rademacher.lean:701 | PROVED | VCDim=0 => Rad ≤ 1/sqrt(m) |
| KK_9 | `analytical_log_sqrt_bound` | Rademacher.lean:838 | PROVED | For large m: 2d*log(2m/d)/m < eps^2 |
| KK_10 | `vcdim_finite_imp_rademacher_vanishing` | Rademacher.lean:910 | PROVED | VCDim < top => uniform Rad vanishing |
| KK_11 | `growth_function_le_sauer_shelah` | Bridge.lean:465 | PROVED | GrowthFunction ≤ Σ_{i≤d} C(m,i) |
| KK_12 | `card_restrict_le_sauer_shelah_bound` | Bridge.lean:393 | PROVED | restriction card ≤ Sauer-Shelah |
| KK_13 | `restrictConceptClass` | Bridge.lean:278 | DEFINED | `C.image (restrictToFinset · S)` |
| KK_14 | `restrictToFinset` | Bridge.lean:273 | DEFINED | `fun ⟨x, _⟩ => c x` |
| KK_15 | `funcToSubsetFamily` | Bridge.lean:299 | DEFINED | Finset (S -> Bool) -> Finset (Finset S) |
| KK_16 | `boolToSign_abs_eq_one` | Rademacher.lean:35 | PROVED | `\|boolToSign b\| = 1` |
| KK_17 | `boolToSign_sum_zero` | Rademacher.lean:44 | PROVED | `Σ_b boolToSign b = 0` |
| KK_18 | `sum_boolToSign_cancel` | Rademacher.lean:80 | PROVED | Rademacher cancellation |
| KK_19 | `iIndepFun_pi` | Mathlib Independence/Basic:784 | IN MATHLIB | Coordinate projections iIndepFun under Measure.pi |
| KK_20 | `hasSubgaussianMGF_of_mem_Icc` | Mathlib SubGaussian:860 | IN MATHLIB | Bounded -> sub-Gaussian (called `_of_mem_Icc` in our Mathlib version) |
| KK_21 | `ProbabilityTheory.cgf` | Mathlib Probability.Moments.Basic | IN MATHLIB | Cumulant generating function `log(E[exp(t*X)])` |
| KK_22 | `ConvexOn.map_integral_le` | Mathlib Analysis.Convex.Integral | IN MATHLIB | Jensen for convex functions on integrals |
| KK_23 | `corr_eq_one_of_agree` | Rademacher.lean:308 | PROVED | Agreement => correlation = 1 |
| KK_24 | `vcdim_zero_concepts_agree` | Rademacher.lean:668 | PROVED | VCDim=0 => all concepts in C agree |
| KK_25 | `empRad_eq_one_of_injective_in_shattered` | Rademacher.lean:440 | PROVED | Injective sample in shattered set => EmpRad=1 |
| KK_26 | `rademacher_lower_bound_on_shattered` | Rademacher.lean:472 | SORRY at 636 | Birthday bound sorry (separate from our target) |
| KK_27 | `rademacher_vanishing_imp_pac` | Rademacher.lean:640 | PROVED (depends on KK_26) | Uniform Rad vanishing => PAC |

**Zhang Infrastructure (to port inline -- NOT yet in codebase):**

| # | Component | Zhang Location | Port Status | Adapted Type |
|---|-----------|----------------|-------------|--------------|
| Z_1 | `exp_sup'_le_sum` | MeasureInfra:131 | TO PORT | `exp(s.sup' hs f) ≤ Σ_{i∈s} exp(f i)` |
| Z_2 | `exp_mul_sup'_le_sum` | MeasureInfra:139 | TO PORT | `exp(t * s.sup' hs f) ≤ Σ_{i∈s} exp(t * f i)` |
| Z_3 | `abs_sup'_le_sum` | MeasureInfra:146 | TO PORT | `\|s.sup' hs f\| ≤ Σ_{i∈s} \|f i\|` |
| Z_4 | `jensen_exp` | MeasureInfra:154 | TO PORT | `exp(E[X]) ≤ E[exp(X)]` |
| Z_5 | `mean_le_log_mgf` | MeasureInfra:164 | TO PORT | `E[X] ≤ (1/t)*log(E[exp(tX)])` for t > 0 |
| Z_6 | `expected_max_subGaussian` | MeasureInfra:181 | TO PORT | Full Massart lemma |

### UK: Remaining Pressures (reduced from v2)

| # | Pressure | Impact | Status |
|---|----------|--------|--------|
| UK_8 | sSup vs finite max in EmpRad | CRITICAL for B1 | RESOLVED by B1 design (see below) |
| UK_9 | NNReal vs R for sub-Gaussian parameter | MEDIUM | RESOLVED: cgf-based route avoids NNReal entirely |
| UK_10 | Counting measure vs Measure.pi | MEDIUM | RESOLVED: Route A-cgf works with cgf directly, bypassing measure bridge |
| UK_11 | iIndepFun_pi on SignVector | LOW | RESOLVED: KK_19 gives this |
| UK_12 | Fintype X in growth_function_le_sauer_shelah | MEDIUM | ADDRESSED: B1 works at the sSup level, B4 uses card_restrict |
| UK_13 (NEW) | `Finset.measurable_sup'` API stability | LOW | Fallback: finite type -> all functions measurable |
| UK_14 (NEW) | `integral_exp_pos` named lemma | LOW | Inline: `integral_pos_of_pos_of_nonneg` or `integral_pos_of_support_subset` |

**All UKs from v2 are now KK or resolved. No structural UKs remain.**

### KU: Key Questions -- All Resolved

| # | Question | Resolution |
|---|----------|------------|
| CKU_12 | iIndepFun for coordinate projections | RESOLVED: `iIndepFun_pi` (Mathlib) |
| CKU_13 | Massart without SubGaussian | RESOLVED: cgf-based approach (Zhang's route) avoids HasSubgaussianMGF entirely |
| CKU_16 | Massart in Mathlib? | RESOLVED: NO. Must prove or port. |
| CKU_17 | EmpRad exact type | RESOLVED: sSup over Set R |
| CKU_18 | EmpRad + finite restrictions | RESOLVED: sSup collapses to finite max via B1 |
| CKU_19 | Counting measure = Measure.pi | RESOLVED: Not needed for cgf-based Route A. The B2 lemma works directly with finite sums. |
| CKU_20 | Measurability of sup' | RESOLVED: On finite types (SignVector m), all functions are measurable by `measurable_of_finite` |

---

## 2. Complete Counterfactual Proof Pathways

### Route A: Port Zhang's `expected_max_subGaussian` Inline (RECOMMENDED)

**Description**: Port Zhang's 6 helper lemmas + main theorem inline into Rademacher.lean. Prove bridge lemmas B1-B4 using the ported Massart as B3.

**Total LOC**: ~260 (B1:50 + B2:55 + B3-port:105 + B4:30 + imports/boilerplate:20)

#### B1: Restriction Collapse (~50 LOC)

**Statement**:
```lean
private theorem restriction_collapse {X : Type u} {m : ℕ} (hm : 0 < m)
    (C : ConceptClass X Bool) (σ : SignVector m) (xs : Fin m → X)
    (hC : C.Nonempty) :
    sSup { r : ℝ | ∃ h ∈ C, r = |rademacherCorrelation h σ xs| } =
    sSup { r : ℝ | ∃ f : Fin m → Bool,
      (∃ h ∈ C, ∀ i, h (xs i) = f i) ∧
      r = |(1 / (m : ℝ)) * ∑ i, boolToSign (σ i) * boolToSign (f i)| } := by
```

**Complete tactic sketch**:
```
  -- Key: rademacherCorrelation h σ xs depends on h only through (h(xs 0), ..., h(xs (m-1)))
  congr 1; ext r; constructor
  -- (→) Given ⟨h, hC, rfl⟩, produce f = fun i => h (xs i)
  · rintro ⟨h, hhC, rfl⟩
    refine ⟨fun i => h (xs i), ⟨h, hhC, fun i => rfl⟩, ?_⟩
    -- Show: |rademacherCorrelation h σ xs| = |(1/m) * Σ bs(σ i)*bs(h(xs i))|
    unfold rademacherCorrelation; rw [dif_neg (by omega)]
    -- The sums are identical term-by-term
  -- (←) Given ⟨f, ⟨h, hhC, hf⟩, rfl⟩, produce h
  · rintro ⟨f, ⟨h, hhC, hf⟩, rfl⟩
    refine ⟨h, hhC, ?_⟩
    unfold rademacherCorrelation; rw [dif_neg (by omega)]
    -- Rewrite using hf : ∀ i, h (xs i) = f i
    congr 1; apply Finset.sum_congr rfl; intro i _
    rw [hf i]
```

**Pl**: 0.98. Pure set equality. No measure theory.
**Coh at B1-B3 joint**: The output is an sSup over a FINITE set (subset of `Fin m -> Bool`). B3 needs a `Finset` and `sup'`. Bridge: the finite set can be converted to a Finset via `Set.Finite.toFinset` since `Fin m -> Bool` is `Fintype`. HC: 0.95.
**Blockers**: None.
**Risk**: LOW.

#### B2: Sub-Gaussianity of Rademacher Correlation via cgf (~55 LOC)

**Statement**:
```lean
private theorem rademacher_correlation_cgf_bound {m : ℕ} (hm : 0 < m)
    (f : Fin m → Bool) (σ_fixed : SignVector m) :
    -- For the function Z(σ) = (1/m) * Σ_i boolToSign(σ i) * boolToSign(f i),
    -- the cgf under counting measure on SignVector m satisfies:
    -- cgf Z μ_count t ≤ t^2 / (2*m)
    -- SIMPLIFIED: work with finite sums directly, no Measure.pi needed.
    -- Statement: for any t, (1/2^m) * Σ_σ exp(t * Z(σ)) ≤ exp(t^2 / (2*m))
    let Z := fun σ : SignVector m =>
      (1 / (m : ℝ)) * ∑ i : Fin m, boolToSign (σ i) * boolToSign (f i)
    ∀ t : ℝ, (1 / (Fintype.card (SignVector m) : ℝ)) *
      ∑ σ : SignVector m, Real.exp (t * Z σ) ≤ Real.exp (t ^ 2 / (2 * m)) := by
```

**Complete tactic sketch**:
```
  intro t
  -- Z(σ) = (1/m) * Σ_i a_i * bs(σ i) where a_i = boolToSign(f i), |a_i| = 1
  -- exp(t * Z(σ)) = exp((t/m) * Σ_i a_i * bs(σ i)) = Π_i exp((t/m) * a_i * bs(σ i))
  -- The product factorization holds because exp converts sums to products.
  --
  -- (1/2^m) * Σ_σ Π_i exp((t/m)*a_i*bs(σ i))
  --   = Π_i (1/2) * Σ_{b:Bool} exp((t/m)*a_i*bs(b))     [product over independent coordinates]
  --   = Π_i ((exp(t*a_i/m) + exp(-t*a_i/m)) / 2)
  --   = Π_i cosh(t*a_i/m)
  --   ≤ Π_i exp((t*a_i/m)^2 / 2)                          [cosh(x) ≤ exp(x^2/2)]
  --   = exp(Σ_i (t/m)^2 * a_i^2 / 2)
  --   = exp(t^2/(2*m^2) * Σ_i a_i^2)
  --   = exp(t^2/(2*m^2) * m)                               [|a_i| = 1 so a_i^2 = 1, Σ = m]
  --   = exp(t^2/(2*m))
  --
  -- The key step is the PRODUCT FACTORIZATION over independent coordinates.
  -- On SignVector m = Fin m -> Bool, the sum over σ of a product of functions
  -- each depending on only one coordinate factors as the product of sums.
  --
  -- Lean formalization:
  -- 1. Rewrite Z(σ) to make the per-coordinate structure explicit
  -- 2. Use Fintype.sum_prod_type or Fintype.prod_sum for product factorization
  -- 3. Bound each factor using cosh_le_exp_sq (Hoeffding's lemma for ±1)
  -- 4. Multiply bounds
  --
  -- CRITICAL IDENTITY for step 2:
  --   Σ_{σ : Fin m -> Bool} Π_i g(i, σ i) = Π_i Σ_{b : Bool} g(i, b)
  -- This is `Fintype.sum_prod` applied to functions on (Fin m -> Bool).
  -- Mathlib: `Finset.prod_sum` or direct unfolding for Fin m -> Bool.
  --
  -- For step 3, the per-coordinate factor:
  --   (1/2) * (exp(t*a/m) + exp(-t*a/m)) = cosh(t*a/m)
  --   cosh(x) ≤ exp(x^2/2) is Hoeffding's lemma for the Rademacher case.
  --   This is proved by: cosh(x) = Σ x^(2k)/(2k)! ≤ Σ (x^2/2)^k/k! = exp(x^2/2)
  --   Mathlib has `Real.cosh_le_exp_sq` or we prove inline (~10 LOC).
  sorry -- PLACEHOLDER: ~55 LOC finite computation
```

**Pl**: 0.90. The product factorization and cosh bound are standard. The Lean encoding of "sum over Fin m -> Bool of product factors" is the main work.
**Coh at B2-B3 joint**: B3 (Zhang's Massart) needs cgf bound: `cgf Z μ t ≤ t^2*σ^2/2`. Our B2 gives `(1/2^m) * Σ exp(t*Z) ≤ exp(t^2/(2m))`. The cgf = log(mgf) where mgf = E[exp(tZ)] = (1/2^m)*Σ exp(tZ). So cgf ≤ t^2/(2m) follows by taking log. Need to bridge between our finite-sum formulation and Zhang's integral-over-Measure.pi formulation. HC: 0.85 (the measure bridge is the tightest joint).
**Blockers**: cosh_le_exp_sq may need inline proof (~10 LOC). Product factorization over `Fin m -> Bool` needs `Finset.prod_sum` or equivalent.
**Risk**: MEDIUM. The finite computation is conceptually clear but Lean encoding may be verbose.

#### B2-alt: Direct cgf Bound Without Product Factorization (~40 LOC)

**Alternative**: Instead of the product factorization route, use:
1. `hasSubgaussianMGF_of_mem_Icc` (Mathlib) gives sub-Gaussianity for each summand under Measure.pi
2. `measure_sum_ge_le_of_iIndepFun` (Mathlib) composes independent sub-Gaussians
3. This gives the mgf bound directly under Measure.pi

**This requires the counting-measure-to-Measure.pi bridge (UK_10)**. The bridge is ~15 LOC:
```lean
-- The uniform measure on (Fin m -> Bool) equals Measure.pi (fun _ => uniformMeasure Bool)
-- where uniformMeasure Bool = (1/2) * (dirac true + dirac false).
-- Proof: both are probability measures on a finite type with the same values on singletons.
-- By ext_of_generate_finite or similar.
```

**Risk**: MEDIUM. The bridge lemma is standard but may require ~20 LOC of boilerplate around `Measure.pi`.

#### B3: Massart Finite Lemma -- Port of Zhang's `expected_max_subGaussian` (~105 LOC)

**Port specification**: Copy Zhang's proof verbatim with these adaptations:

| Zhang Code | Our Adaptation | Reason |
|------------|---------------|--------|
| `import SLT.MeasureInfrastructure` | Inline all helpers | No external dependency |
| `ProbabilityTheory.cgf X μ t` | Same (available in our Mathlib) | API stable |
| `Finset.measurable_sup'` | `measurable_of_finite` if on finite type | Version safety |
| `integral_exp_pos` | Inline: `integral_pos_of_pos_of_nonneg exp_pos ae_of_all ...` | May not be named in our Mathlib |

**Exact code to port** (from Zhang, with modifications marked `-- PORTED:`):

```lean
-- HELPER 1: exp_mul_sup'_le_sum (~8 LOC)
private theorem exp_mul_sup'_le_sum {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    (f : ι → ℝ) (t : ℝ) :
    Real.exp (t * s.sup' hs f) ≤ ∑ i ∈ s, Real.exp (t * f i) := by
  obtain ⟨j, hj, hmax⟩ := Finset.exists_mem_eq_sup' hs f
  rw [hmax]
  exact Finset.single_le_sum (fun i _ => (Real.exp_pos _).le) hj

-- HELPER 2: abs_sup'_le_sum (~6 LOC)
private theorem abs_sup'_le_sum {ι : Type*} {s : Finset ι} (hs : s.Nonempty)
    (f : ι → ℝ) :
    |s.sup' hs f| ≤ ∑ i ∈ s, |f i| := by
  obtain ⟨j, hj, hmax⟩ := Finset.exists_mem_eq_sup' hs f
  rw [hmax]
  exact Finset.single_le_sum (fun j _ => abs_nonneg _) hj

-- HELPER 3: mean_le_log_mgf (~15 LOC)
-- PORTED: uses ConvexOn.map_integral_le (same API)
private theorem mean_le_log_mgf {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX_int : MeasureTheory.Integrable X μ)
    {t : ℝ} (ht : 0 < t)
    (hexpX_int : MeasureTheory.Integrable (fun ω => Real.exp (t * X ω)) μ) :
    ∫ ω, X ω ∂μ ≤ (1/t) * Real.log (∫ ω, Real.exp (t * X ω) ∂μ) := by
  -- Jensen: exp(E[tX]) ≤ E[exp(tX)]
  -- So E[tX] ≤ log(E[exp(tX)])
  -- So E[X] ≤ (1/t) * log(E[exp(tX)])
  have htX_int : MeasureTheory.Integrable (fun ω => t * X ω) μ := hX_int.const_mul t
  have h_jensen : Real.exp (∫ ω, t * X ω ∂μ) ≤ ∫ ω, Real.exp (t * X ω) ∂μ :=
    (convexOn_exp).map_integral_le continuous_exp.continuousOn isClosed_univ
      (by simp) htX_int hexpX_int
  have h1 : ∫ ω, t * X ω ∂μ = t * ∫ ω, X ω ∂μ := MeasureTheory.integral_const_mul t X
  have h2 : t * ∫ ω, X ω ∂μ ≤ Real.log (∫ ω, Real.exp (t * X ω) ∂μ) := by
    calc t * ∫ ω, X ω ∂μ
        = Real.log (Real.exp (t * ∫ ω, X ω ∂μ)) := (Real.log_exp _).symm
      _ ≤ Real.log (∫ ω, Real.exp (t * X ω) ∂μ) :=
          Real.log_le_log (Real.exp_pos _) (h1 ▸ h_jensen)
  linarith [div_le_iff ht |>.mpr (by linarith : (∫ ω, X ω ∂μ) * t ≤ _)]

-- MAIN: expected_max_subGaussian (~60 LOC)
-- PORTED: identical signature to Zhang, using our imports
private theorem expected_max_subGaussian {Ω : Type*} [MeasurableSpace Ω]
    {ι : Type*}
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} {σ : ℝ} (hσ : 0 < σ)
    {s : Finset ι} (hs : s.Nonempty) (hs_card : 2 ≤ s.card)
    (hX_meas : ∀ i ∈ s, Measurable (X i))
    (hX_int_basic : ∀ i ∈ s, MeasureTheory.Integrable (X i) μ)
    (hX_sgb : ∀ i ∈ s, ∀ t, ProbabilityTheory.cgf (X i) μ t ≤ t^2 * σ^2 / 2)
    (hX_int_exp : ∀ i ∈ s, ∀ t,
      MeasureTheory.Integrable (fun ω => Real.exp (t * X i ω)) μ) :
    ∫ ω, s.sup' hs (fun i => X i ω) ∂μ ≤ σ * Real.sqrt (2 * Real.log s.card) := by
  -- [Zhang's proof, verbatim with our namespacing]
  sorry -- PLACEHOLDER: ~60 LOC exact copy of Zhang's Steps 1-6
```

**Pl**: 0.95. Zhang's proof is COMPLETE and VERIFIED in Lean 4.27. The port is syntactic.
**Coh at B3-B2 joint**: B2 gives cgf bound `≤ t^2/(2m)` which means `σ^2 = 1/m`, so `σ = 1/sqrt(m)`. B3 takes `σ` as parameter. HC: 0.98 (clean type match).
**Coh at B3-B4 joint**: B3 gives `E[sup'] ≤ σ*sqrt(2*log n)`. B4 needs `EmpRad(xs) ≤ B` where `B = sqrt(2d*log(2m/d)/m)`. Need to show EmpRad = E_σ[sup'] and apply B3 with n = restriction cardinality, σ = 1/sqrt(m). HC: 0.90 (the EmpRad = integral bridge is the tightest point).
**Blockers**: `Finset.measurable_sup'` stability, `integral_exp_pos` naming.
**Risk**: LOW-MEDIUM. The port is syntactic but version differences may require ~10 LOC of fixes.

#### B4: Assembly (~30 LOC)

**Statement**: The sorry itself at Rademacher.lean:435.

**Complete tactic sketch**:
```
-- Inside the sorry at line 435:
-- Goal: EmpiricalRademacherComplexity X C xs ≤ B
-- where B = sqrt(2 * d * log(2 * m / d) / m)
-- Context: hB1 : B < 1, hm : 0 < m, hd_pos : 0 < d, hdm : d ≤ m
-- Available: hd : VCDim X C = ↑d

-- Step 1: Handle C empty case
by_cases hC : C.Nonempty
swap
· -- C empty: EmpRad = 0 ≤ B
  rw [Set.not_nonempty_iff_eq_empty] at hC
  unfold EmpiricalRademacherComplexity; rw [dif_neg (by omega)]
  simp [show {r : ℝ | ∃ h ∈ C, _} = ∅ from by ext; simp [hC]]
  exact Real.sqrt_nonneg _

-- Step 2: Apply restriction_collapse to rewrite sSup
-- EmpRad(xs) = (1/2^m) * Σ_σ sSup_{f ∈ restrictions} |corr_f(σ)|
-- This equals E_σ[max_{f ∈ R} |Z_f(σ)|] where the expectation is uniform over σ.

-- Step 3: Convert to Measure.pi integral form
-- The finite average (1/2^m) * Σ_σ g(σ) = ∫ σ, g(σ) d(Measure.pi (fun _ => uniform Bool))
-- This bridges our definition to the integral form needed for B3.

-- Step 4: Apply expected_max_subGaussian (B3) with:
--   Ω = SignVector m = Fin m -> Bool
--   μ = Measure.pi (fun _ : Fin m => uniformMeasure Bool)
--   ι = restriction patterns (a Fintype)
--   s = Finset of all restriction patterns
--   X_i(σ) = |rademacherCorrelation (pattern_i) σ xs|
--   σ_param = 1 / sqrt(m)

-- Step 5: Bound |s| ≤ growth_function_le_sauer_shelah
-- |s| = (restrictConceptClass C (Finset.univ.image xs)).card
--      ≤ Σ_{i≤d} C(m, i)  [by card_restrict_le_sauer_shelah_bound]
-- log |s| ≤ d * log(2m/d) [by standard bound on binomial sum]

-- Step 6: Algebra
-- (1/sqrt(m)) * sqrt(2 * log |s|) ≤ (1/sqrt(m)) * sqrt(2 * d * log(2m/d))
--   = sqrt(2 * d * log(2m/d) / m) = B

sorry -- PLACEHOLDER: ~30 LOC chaining B1 + B2 + B3 + Sauer-Shelah
```

**Pl**: 0.85. The main risk is the measure bridge in Step 3.
**Coh**: All joints analyzed in B1-B3. The final algebra is clean.
**Blockers**: The bridge between `(1/2^m) * Σ_σ` and `∫ d(Measure.pi)`. This is CKU_19.
**Risk**: MEDIUM. The bridge lemma is the weakest joint.

#### Route A Measurement Summary

| Metric | B1 | B2 | B3 | B4 | Total |
|--------|----|----|----|----|-------|
| LOC | 50 | 55 | 105 | 30 | 260 |
| Pl | 0.98 | 0.90 | 0.95 | 0.85 | 0.85 (min) |
| HC (worst joint) | 0.95 | 0.85 | 0.90 | 0.85 | 0.85 |
| Risk | LOW | MEDIUM | LOW-MEDIUM | MEDIUM | MEDIUM |
| Blockers | None | cosh_le_exp_sq, product factorization | Finset.measurable_sup' | Measure bridge | 3 addressable |

---

### Route B: Self-Contained Massart from Mathlib Primitives Only (NO Zhang port)

**Description**: Prove B3 (Massart) entirely from scratch using only Mathlib APIs, without porting Zhang's code. Use `HasSubgaussianMGF` structure.

**LOC**: ~320 (B1:50 + B2-Mathlib:80 + B3-scratch:150 + B4:30 + boilerplate:10)

**B2-Mathlib variant**: Use `hasSubgaussianMGF_of_mem_Icc` + `iIndepFun_pi` + the counting-measure-to-Measure.pi bridge. This gives `HasSubgaussianMGF Z ((1/m : NNReal)) (Measure.pi ...)` directly. But requires:
- UK_10 bridge (counting -> Measure.pi): ~15 LOC
- UK_9 NNReal casting: ~10 LOC
- `sum_of_iIndepFun` for composing independent sub-Gaussians: ~20 LOC

**B3-scratch**: Prove Massart from scratch using `HasSubgaussianMGF.mgf_le` to extract the cgf bound, then do the Chernoff-optimize-lambda chain. This duplicates Zhang's proof structure but uses `HasSubgaussianMGF` instead of raw cgf bounds.

**Why this is worse than Route A**: The `HasSubgaussianMGF` overhead adds ~70 LOC of NNReal/R casting, structure management, and API adapters. Zhang's cgf-based approach is cleaner and more direct.

**Measurement**:
| Metric | Value |
|--------|-------|
| LOC | 320 |
| Pl | 0.80 |
| HC (worst joint) | 0.75 (NNReal conversion) |
| Risk | MEDIUM-HIGH |
| Advantage | No external code dependency |
| Disadvantage | +60 LOC boilerplate, NNReal friction |

---

### Route C: Cauchy-Schwarz Generalization (Weak Bound)

**Description**: Generalize `vcdim_zero_rademacher_le_inv_sqrt` (KK_8) to general d.

**Bound achieved**: `EmpRad ≤ sqrt(GrowthFunction(C,m) / m)`

**Why this FAILS**: For VCDim = d, GrowthFunction ~ (em/d)^d. So:
- `sqrt(GF/m) ~ sqrt((em/d)^d / m) = (em/d)^{d/2} / sqrt(m)`
- For d >= 2: this GROWS as m -> infinity (polynomial in m).
- Our theorem statement requires `EmpRad ≤ sqrt(2d*log(2m/d)/m)` which DECREASES to 0.

**Verdict**: FATAL. Cannot match the theorem statement. Route C is non-viable for any d >= 2.

**LOC**: ~100
**Pl**: 0.95 (the proof itself is easy)
**Coh**: 0.00 (bound doesn't match statement)
**Risk**: FATAL

---

### Route D: Direct Hoeffding Tail Integration (Weak Bound)

**Description**: Skip Massart entirely. Use:
1. P[max_j Z_j >= t] <= N * exp(-mt^2/2) (union bound + Hoeffding tail)
2. E[max] = integral_0^infty P[max >= t] dt (tail integration)
3. Evaluate integral: N * sqrt(pi/(2m))

**Bound achieved**: `E[max] <= N * sqrt(pi/(2m)) = N / sqrt(m) * sqrt(pi/2)`

**Why this FAILS**: Linear in N (= GrowthFunction) instead of sqrt(log N). For N ~ (em/d)^d, this gives `(em/d)^d / sqrt(m)` which is even worse than Route C.

**LOC**: ~200
**Pl**: 0.85
**Coh**: 0.00
**Risk**: FATAL

---

### Route E: Import Zhang as Lakefile Dependency

**Description**: Add Zhang's `lean-stat-learning-theory` repo as a dependency in our lakefile.lean. Import `SLT.MeasureInfrastructure` directly.

**LOC**: ~160 (B1:50 + B2:55 + B4:30 + lakefile:5 + import:5 + bridge:15)
**Saves**: ~105 LOC (the B3 port)

**Why this is WORSE than Route A**:
1. **Version mismatch**: Zhang uses Lean 4.27.0-rc1, we use 4.29.0-rc6. Two minor version gap.
2. **Mathlib alignment**: Zhang uses Mathlib master at an unknown commit. Our Mathlib may be different.
3. **Build fragility**: External dependency adds a new failure mode to every `lake build`.
4. **Maintenance**: Zhang's repo may change or break. We'd need to pin a commit.
5. **A5 concern**: External dependency for ~105 LOC of well-understood proof code is not structurally justified.

**Measurement**:
| Metric | Value |
|--------|-------|
| LOC | 160 |
| Pl | 0.90 (math) |
| Build risk | HIGH |
| Maintenance risk | HIGH |

---

## 3. INVARIANT Route Identification

### Route A dominates all alternatives:

| Route | LOC | Pl | Coh | Build Risk | A4/A5 | Viable? |
|-------|-----|----|-----|------------|-------|---------|
| **A** | 260 | 0.85 | 0.85 | LOW | CLEAN | **YES** |
| B | 320 | 0.80 | 0.75 | LOW | CLEAN | YES but inferior |
| C | 100 | 0.95 | 0.00 | N/A | N/A | **NO** (bound too weak) |
| D | 200 | 0.85 | 0.00 | N/A | N/A | **NO** (bound too weak) |
| E | 160 | 0.90 | 0.85 | HIGH | CONCERN | YES but fragile |

**Route A is the INVARIANT route because**:
1. It survives ALL KU threats (no structural unknowns remain).
2. It has the highest Coh (0.85) among viable routes.
3. It is self-contained (no external dependencies).
4. It is A4/A5 clean.
5. It is robust to Mathlib/Lean version changes (cgf-based approach uses stable APIs).
6. Zhang's proof is VERIFIED in Lean 4.27 and the port is syntactic.

**The tightest joint is B4 (assembly)**: the measure bridge between `(1/2^m) * Σ_σ` and the integral form. This can be bypassed entirely if we reformulate B3 to work directly with finite sums (see Route A-finite variant below).

### Route A-finite: Finite Variant (STRONGEST)

**Key insight**: We can avoid the Measure.pi bridge entirely by formulating B3 for FINITE sums rather than integrals.

Instead of porting Zhang's `expected_max_subGaussian` (which uses `∫ ... ∂μ`), prove a FINITE MASSART LEMMA:

```lean
theorem finite_massart {ι : Type*} {m : ℕ} (hm : 0 < m)
    {Z : ι → SignVector m → ℝ} {σ : ℝ} (hσ : 0 < σ)
    {s : Finset ι} (hs : s.Nonempty) (hs_card : 2 ≤ s.card)
    (hZ_sgb : ∀ i ∈ s, ∀ t : ℝ,
      (1 / (Fintype.card (SignVector m) : ℝ)) *
        ∑ sv : SignVector m, Real.exp (t * Z i sv) ≤ Real.exp (t ^ 2 * σ ^ 2 / 2)) :
    (1 / (Fintype.card (SignVector m) : ℝ)) *
      ∑ sv : SignVector m, s.sup' hs (fun i => Z i sv) ≤
      σ * Real.sqrt (2 * Real.log s.card)
```

This is the SAME mathematical content as Zhang's theorem but formulated over finite sums instead of measure-theoretic integrals. The proof is identical (Jensen, soft-max, cgf bound, algebra) but all "integrals" are finite sums with `(1/2^m)` normalization.

**Advantage**: ELIMINATES the Measure.pi bridge entirely. Coh at B3-B4 joint rises from 0.85 to 0.98.
**Disadvantage**: Slightly more LOC (~10 LOC extra for finite-sum versions of Jensen and integral_mono).

**This is the true invariant**: Route A-finite has Coh >= 0.95 at ALL joints.

---

## 4. Meta-Programmatic Analysis

### Metaprogram Type of the Massart Sorry

The sorry at Rademacher.lean:435 is an **M-Pipeline** metaprogram:

```
sSup → B1 → finite max → B2 → cgf bound → B3 → E[max] bound → B4 → sqrt bound
```

This is a 4-stage pipeline where each stage transforms the problem across a paradigm boundary:
1. **B1 (Set Theory → Combinatorics)**: sSup over infinite C → max over finite restrictions
2. **B2 (Combinatorics → Probability)**: finite patterns → sub-Gaussian random variables
3. **B3 (Probability → Analysis)**: sub-Gaussian RVs → expected maximum bound (concentration)
4. **B4 (Analysis → Algebra)**: expected max → algebraic bound via Sauer-Shelah

### Paradigm Joints

The chain crosses **3 paradigm joints**:
1. **Set/Combinatorics**: B1 (sSup → Finset.sup')
2. **Combinatorics/Probability**: B2 (counting → sub-Gaussian)
3. **Probability/Analysis**: B3 (concentration → bound)

Each joint is a potential HC failure point. The Route A-finite variant ELIMINATES joint 2 (stays in finite counting throughout), reducing to 2 paradigm joints.

### Chain Collapse

**Can the chain be collapsed?** YES, partially:
- B1 + B2 can be merged: instead of first collapsing sSup to finite max and THEN proving sub-Gaussianity, directly show: `E_σ[sSup{|corr_h|: h ∈ C}] ≤ E_σ[max_{j} Z_j]` in one step, since the sSup equals the max. This saves ~20 LOC but doesn't change the paradigm count.
- B3 + B4 CANNOT be merged: the Massart lemma is a general tool (any sub-Gaussian RVs) while B4 is specific to our setting.

### VCDim=0 Pattern Lifting

The `vcdim_zero_rademacher_le_inv_sqrt` proof (KK_8) demonstrates:
1. All h ∈ C agree → sSup collapses to single value → Cauchy-Schwarz → 1/sqrt(m)

For general d, the key difference is: concepts DON'T all agree. Instead, there are at most GrowthFunction(C,m) distinct restriction patterns. The Cauchy-Schwarz approach gives `sqrt(GF/m)` which is too weak (Route C). The Massart approach gives `sqrt(2*log(GF)/m)` by using exponential moment methods instead of second moments.

**The lift from d=0 to general d REQUIRES Massart**. The second-moment (Cauchy-Schwarz) approach cannot achieve the required bound for d >= 2. This is because the maximum of N random variables has expected value O(sqrt(log N)) (by sub-Gaussianity), NOT O(sqrt(N)) (which is what second moments give).

### What d=0 Teaches About the General Case

The d=0 proof uses:
1. Agreement collapse: sSup → single value
2. Cauchy-Schwarz: E[|Z|] ≤ sqrt(E[Z^2])
3. Rademacher variance: E[Z^2] = 1/m

The general case REPLACES step 1 with:
1'. Restriction collapse: sSup → max over N patterns (N ≤ GrowthFunction)

And REPLACES step 2 with:
2'. Massart: E[max_j |Z_j|] ≤ σ*sqrt(2*log N)

Step 3 is reused: each Z_j has variance proxy 1/m (i.e., σ = 1/sqrt(m)).

The structural insight: **d=0 is Massart with N=1** (trivially: max of 1 variable = the variable itself, and sqrt(2*log 1) = 0, but the actual bound is the direct variance bound).

---

## 5. Implementation Specification

### Recommended Proof Order

1. **Port Zhang helpers** (Z_1 through Z_5): ~45 LOC. Standalone, no dependencies.
2. **Port `expected_max_subGaussian`** (Z_6): ~60 LOC. Depends on Z_1-Z_5.
3. **OR** (preferred): Write `finite_massart` instead: ~70 LOC. Depends on adapted Z_1-Z_5.
4. **Prove B2** (`rademacher_correlation_cgf_bound`): ~55 LOC. Standalone.
5. **Prove B1** (`restriction_collapse`): ~50 LOC. Standalone.
6. **Close the sorry** (B4 assembly): ~30 LOC. Depends on B1, B2, B3, and Sauer-Shelah.

### Where to Place Code

All new code goes in `Rademacher.lean`, inserted BEFORE the `vcdim_bounds_rademacher_quantitative` theorem (before line 390). Structure:

```
-- Line ~380: new section
/-! ## Massart Infrastructure (ported from Zhang, adapted for finite sums) -/

-- Z_1: exp_mul_sup'_le_sum
-- Z_2: abs_sup'_le_sum
-- Z_5: mean_le_log_mgf (or finite variant)
-- Z_6: expected_max_subGaussian (or finite_massart)
-- B1: restriction_collapse
-- B2: rademacher_correlation_cgf_bound

/-! ## VCDim → Rademacher bound -/
-- existing vcdim_bounds_rademacher_quantitative theorem
-- sorry REPLACED by B4 assembly code
```

### Required New Imports

```lean
-- Add to Rademacher.lean imports (line 8-11):
import Mathlib.Probability.Moments.Basic          -- ProbabilityTheory.cgf
-- Note: already have MeasureTheory.Constructions.Pi (for Measure.pi)
-- Note: already have Analysis.SpecialFunctions.Pow.Real (for sqrt, log)
```

Check if `Mathlib.Probability.Moments.Basic` is already transitively imported via existing imports. If so, no new import needed.

### A4/A5 Compliance

**A4**: The sorry at line 435 requires genuine sub-Gaussian concentration content. The proof chain B1-B4 is standard textbook mathematics. No trivially-true content. **CLEAN.**

**A5**: The proof route is the canonical chain from SSBD Ch.26, Mohri Ch.3, BLM 2013 Lemma 2.6. No statement weakening. The theorem statement matches the standard bound. **CLEAN.**

---

## 6. Risk Register

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| `Finset.measurable_sup'` API changed | LOW | LOW | Use `measurable_of_finite` for finite types |
| `integral_exp_pos` not named in our Mathlib | MEDIUM | LOW | Inline: 3 LOC |
| `cosh_le_exp_sq` not in Mathlib | MEDIUM | LOW | Inline: 10 LOC (Taylor comparison) |
| Product factorization encoding verbose | MEDIUM | MEDIUM | Alternative: use `Fintype.prod_sum` directly |
| Measure bridge EmpRad <-> integral | MEDIUM | HIGH | Use Route A-finite to eliminate entirely |
| B2 requires 20+ LOC boilerplate | HIGH | LOW | Accept the cost |
| Zhang proof has subtle version-specific API calls | LOW | MEDIUM | Test each ported lemma individually |

---

## 7. Literature References

1. Boucheron, Lugosi & Massart (2013). Concentration Inequalities. Ch.2, Lemma 2.6 (Massart finite lemma).
2. Shalev-Shwartz & Ben-David (2014). Understanding Machine Learning. Ch.26 (Rademacher complexity).
3. Mohri, Rostamizadeh & Talwalkar (2018). Foundations of Machine Learning. 2nd ed. Ch.3.
4. Zhang, Lee & Liu (2026). Statistical Learning Theory in Lean 4. arXiv:2602.02285. GitHub: `YuanheZ/lean-stat-learning-theory`.
5. Degenne, R. (2025). SubGaussian module in Mathlib4. `Mathlib.Probability.Moments.SubGaussian`.
6. Vershynin, R. (2018). High-Dimensional Probability. Ch.2 (sub-Gaussian random variables).
7. Massart, P. (2000). Some applications of concentration inequalities to statistics. Annales de la Faculte des Sciences de Toulouse.
