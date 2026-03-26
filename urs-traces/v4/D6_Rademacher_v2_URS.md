# D6 Rademacher v2 URS -- Uniform Route + Full Proof DAG (2026-03-20)

## Executive Summary

v1 URS discovered a critical circularity (CKU_7) in sorry #8: the hypothesis is pointwise-in-D
but the birthday-probability proof gives a lower bound that decays exponentially, failing to
contradict vanishing. v2 resolves this by:

1. **Sorry #8**: Strengthen hypothesis from pointwise to uniform Rademacher vanishing.
   The existing `vcdim_finite_imp_rademacher_vanishing` proof already computes m0 independent
   of D, so the forward direction survives verbatim. The backward direction becomes trivial.
2. **Sorry #7**: Unchanged from v1. Massart finite lemma + Sauer-Shelah chain.

**Net effect**: 2 sorrys -> 0 sorrys. ~350 LOC total. Both directions A4/A5 clean.

---

## CKU_7 Resolution: The Uniform Route

### Why Pointwise Fails

The pointwise hypothesis is: `forall D [IsProbabilityMeasure D], forall eps > 0, exists m0(D), forall m >= m0(D), Rad_m(C,D) < eps`.

To prove `VCDim < top` by contrapositive (VCDim = top -> NOT hrad), we must find a single D where Rad doesn't vanish. The birthday-probability approach gives:

- For D_n = uniform on shattered T_n (|T_n| = n):
  `Rad_m(C, D_n) >= P[injective sample] >= (m!/m^m)` for m = n.
- But hrad only constrains m >= m0(D_n), which could be >> n.
- For m = m0(D_n): we don't control which shattered set is relevant.

All known lower-bound constructions yield Rad >= c^m -> 0, consistent with pointwise vanishing.

### Why Uniform Works

The uniform hypothesis is: `forall eps > 0, exists m0, forall D [IsProbabilityMeasure D], forall m >= m0, Rad_m(C,D) < eps`.

Proof by contrapositive (VCDim = top -> NOT hrad_uniform):
1. hrad_uniform with eps = 1/2 gives a single m0.
2. VCDim = top -> exists shattered T with |T| = 2*m0.
3. D = uniform on T. For m = m0 draws from 2*m0 points:
   P[all distinct] = prod_{k<m0}(1 - k/(2*m0)) >= (1/2)^{m0}.
4. BUT (1/2)^{m0} can be < 1/2, so need tighter analysis.

**TIGHTER ARGUMENT**: For m = 1, D = uniform on T (|T| >= 2, shattered):
- 1 draw is always in T. xs = [x_0] with x_0 in T.
- {x_0} is shattered (subset of shattered set -- `shatters_subset` PROVED).
- By `empRad_eq_one_of_all_labelings`: EmpRad = 1 for ALL such 1-samples.
- So Rad_1(C, D) = integral of 1 = 1 >= 1/2.
- If m0 <= 1, this contradicts hrad_uniform.
- If m0 > 1, use m0 directly:

**CORRECT TIGHT ARGUMENT**:
1. hrad_uniform with eps = 1/2 gives m0.
2. VCDim = top -> exists shattered T with |T| >= 4*m0^2.
3. D = uniform on T. For m = m0:
   P[all distinct] = prod_{k<m0}(1 - k/|T|) >= prod_{k<m0}(1 - k/(4*m0^2))
   >= (1 - m0/(4*m0^2))^{m0} = (1 - 1/(4*m0))^{m0} >= 1/e > 1/4.
4. On distinct draws from T (which is shattered): EmpRad = 1 (by empRad_eq_one_of_all_labelings).
5. Rad_{m0}(C, D) >= (1/4) * 1 = 1/4.
6. But hrad says Rad_{m0}(C, D) < 1/2 since m0 >= m0. Not yet contradicted since 1/4 < 1/2.

**EVEN TIGHTER**: Use eps = 1/8 and show Rad >= 1/4 > 1/8.

Actually, the clean approach: fix ANY eps in (0, 1). hrad gives m0.
- Take |T| = (2*m0)^2 = 4*m0^2. D = uniform on T. m = m0.
- P[all distinct] >= 1 - m0*(m0-1)/(2*|T|) >= 1 - m0^2/(8*m0^2) = 7/8 (by union bound on collisions).
- On distinct draws: EmpRad = 1.
- On non-distinct draws: EmpRad >= 0.
- Rad_{m0}(C,D) >= (7/8) * 1 + (1/8) * 0 = 7/8 >= eps for eps < 7/8.

So for eps < 7/8, we get Rad_{m0}(C,D) >= 7/8 > eps, contradicting hrad.

For eps >= 7/8: use |T| even larger. With |T| = N * m0^2:
P[all distinct] >= 1 - m0^2/(2N*m0^2) = 1 - 1/(2N).
Choose N large enough that 1 - 1/(2N) > eps. Since eps < 1, this is always possible.

**FINAL CLEAN PROOF**:
1. Fix eps > 0. hrad_uniform gives m0.
2. Choose N such that 1 - 1/(2*N) > max(eps, 0), i.e., N > 1/(2*(1-eps)) (always finite since eps < 1 for probability). Actually for any eps > 0 we can just use N = m0^2 + 1 and compute.
3. |T| = 2*N*m0. D = uniform on T.
4. P[all m0 draws distinct] >= 1 - C(m0,2)/|T| >= 1 - m0^2/(2*2*N*m0) = 1 - m0/(4*N).
5. This approaches 1 as N grows. For N = m0 we get >= 1 - 1/4 = 3/4.
6. Rad_{m0} >= 3/4 > eps for eps < 3/4. For eps >= 3/4, use larger N.

**SIMPLEST APPROACH** (recommended for formalization):
1. Fix eps > 0 with eps < 1 (for eps >= 1, Rad <= 1 < eps is impossible since Rad >= 0, so hrad_uniform is trivially falsifiable... wait, no, Rad < eps for eps >= 1 is easy to satisfy).
2. Actually: for eps >= 1, hrad_uniform says Rad < eps, which Rad <= 1 satisfies. So we cannot derive contradiction for eps >= 1. We need to use a SPECIFIC eps.
3. Use eps = 1/2. hrad_uniform gives m0. VCDim = top gives shattered T with |T| >= 4*m0^2.
4. D = uniform on T. m = m0. Birthday bound (union over pairs):
   P[collision] <= C(m0,2)/|T| = m0*(m0-1)/(2*4*m0^2) < 1/8.
   So P[all distinct] > 7/8 > 1/2 = eps.
   Rad_{m0}(C,D) >= P[distinct] * 1 > 7/8 > 1/2 = eps. Contradiction.

THIS WORKS.

---

## Corrected Statement for rademacher_vanishing_imp_pac

### Current (v1 -- CIRCULAR):
```lean
theorem rademacher_vanishing_imp_pac (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool)
    (hrad : forall (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D ->
      forall eps > 0, exists m0, forall m >= m0, RademacherComplexity X C D m < eps) :
    PACLearnable X C
```

### Proposed (v2 -- UNIFORM):
```lean
theorem rademacher_vanishing_imp_pac (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool)
    (hrad : forall eps > 0, exists m0, forall (D : MeasureTheory.Measure X),
      MeasureTheory.IsProbabilityMeasure D ->
      forall m >= m0, RademacherComplexity X C D m < eps) :
    PACLearnable X C
```

The change: `forall D, ... exists m0 ...` becomes `exists m0, forall D, ...`.

### Cascade: Statements that must change

**1. `rademacher_vanishing_imp_pac` (Rademacher.lean:455)**: Hypothesis strengthened as above.

**2. `fundamental_rademacher` (PAC.lean:191)**: RHS of iff changes from pointwise to uniform.
```lean
-- CURRENT:
PACLearnable X C <->
  (forall D, IsProbabilityMeasure D -> forall eps > 0, exists m0, forall m >= m0, Rad < eps)

-- PROPOSED:
PACLearnable X C <->
  (forall eps > 0, exists m0, forall D, IsProbabilityMeasure D -> forall m >= m0, Rad < eps)
```

**3. `fundamental_theorem` conjunct 3 (PAC.lean:207-209)**: Same change.

**4. `vcdim_finite_imp_rademacher_vanishing` (Rademacher.lean:753)**: Conclusion changes to uniform.
BUT the existing proof already computes m0 = max(d+1, ceil(32*(d+1)/eps^4)+1) which does NOT depend on D.
The proof body is: `intro D hD eps heps ... use [formula not involving D] ...`
So we just reorder: `intro eps heps ... use [formula] ... intro D hD m hm ...`
**This is a pure quantifier reordering; the proof content is unchanged.**

### A5 Compliance

This is NOT simplification. The uniform statement is STRONGER than pointwise:
- Uniform vanishing implies pointwise vanishing (specialize the exists m0 for each D).
- Pointwise vanishing does NOT imply uniform vanishing.

So the hypothesis of `rademacher_vanishing_imp_pac` gets STRONGER (harder to satisfy),
making the theorem WEAKER (applies to fewer situations).

BUT the equivalence `fundamental_rademacher` changes its RHS to a STRONGER property,
and the forward direction still holds (since the proof of vanishing from VCDim < top
is already uniform). So the iff is between PAC and a STRONGER Rademacher condition.

This is A5-compliant: we are proving a richer mathematical structure (uniform rates),
not simplifying. The standard textbook (SSBD Theorem 26.2) uses uniform vanishing.

### A4 Compliance

No trivially-true sorrys introduced. The remaining sorry content is:
- Sorry #7: Massart finite lemma (genuine sub-Gaussian concentration content).
- Sorry #8 under uniform: VCDim = top -> exists D with Rad >= 1/2 (genuine adversarial construction).

---

## Full Proof DAG

```
VCDim X C = d (finite)
  |
  +--> [PROVED] growth_function_le_sauer_shelah
  |      GrowthFunction(C,m) <= sum_{i<=d} C(m,i) for m >= d
  |
  +--> [B1] restriction_to_finite_set
  |      For fixed xs, EmpRad with sSup over C = EmpRad with sSup over
  |      finite set of <= GrowthFunction(C,m) distinct restriction patterns.
  |      ~50 LOC. Quotients C by xs-equivalence.
  |
  +--> [B2] rademacher_summand_sub_gaussian
  |      For fixed restriction pattern j and fixed xs:
  |      Z_j(sigma) = (1/m) sum_i a_{j,i} * boolToSign(sigma_i)
  |      is (1/sqrt(m))-sub-Gaussian under uniform measure on SignVector m.
  |      ~70 LOC. Uses Mathlib hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero.
  |      Requires: SignVector m under counting measure = product of Bernoulli.
  |      CKU_12: iIndepFun for coordinate projections on product measure.
  |
  +--> [B3] massart_finite_lemma
  |      For N sub-Gaussian RVs Z_1,...,Z_N each with parameter c:
  |      E[max_j Z_j] <= c * sqrt(2 * log(N)).
  |      ~100 LOC. Standard Chernoff + union bound + optimize lambda.
  |      This is the hardest bridge lemma.
  |
  +--> [B4] assembly (Sorry #7 = vcdim_bounds_rademacher_quantitative)
  |      Chain B1 + B3 + Sauer-Shelah:
  |      EmpRad(xs) <= sqrt(2 * d * log(2*m/d) / m)
  |      ~30 LOC.
  |
  +--> [PROVED] analytical_log_sqrt_bound
  |      For large m: 2*d*log(2*m/d)/m < eps^2.
  |
  +--> [PROVED, needs quantifier reorder] vcdim_finite_imp_rademacher_vanishing
  |      VCDim < top -> forall eps > 0, exists m0, forall D, forall m >= m0, Rad < eps.
  |      (Currently proved with pointwise quantifiers but m0 doesn't depend on D.)
  |
  +--> [Sorry #8 = rademacher_vanishing_imp_pac, uniform version]
  |      Uniform Rad vanishing -> PACLearnable.
  |      Proof: contrapositive. VCDim = top ->
  |        (a) exists shattered T of any size [PROVED: h_large_shatter]
  |        (b) [NEW] birthday_lower_bound: for D = uniform on T (|T| = 4*m0^2),
  |            Rad_{m0}(C,D) >= 7/8 > 1/2 = eps.  ~60 LOC.
  |        (c) Contradiction with hrad.
  |      Total ~80 LOC.
  |
  +--> [PROVED] vcdim_finite_imp_pac_direct
         VCDim < top -> PACLearnable.
```

### Complete dependency chain:

```
Sorry #7 proof:
  Mathlib.HasSubgaussianMGF (imported)
  + Mathlib.iIndepFun (imported)
  + B1 (restriction collapse, ~50 LOC)
  + B2 (sub-Gaussianity, ~70 LOC, uses CKU_12)
  + B3 (Massart finite lemma, ~100 LOC)
  + B4 (assembly, ~30 LOC)
  + growth_function_le_sauer_shelah (PROVED)
  = vcdim_bounds_rademacher_quantitative (Sorry #7 closed)

Sorry #8 proof (uniform version):
  shatters_subset (PROVED)
  + empRad_eq_one_of_all_labelings (PROVED)
  + h_large_shatter (PROVED inline)
  + birthday_lower_bound (NEW, ~60 LOC)
  + vcdim_finite_imp_pac_direct (PROVED with its own sorry chain)
  = rademacher_vanishing_imp_pac (Sorry #8 closed)
```

---

## Sorry #7: Tactic Sequences for Bridge Lemmas

### B1: restriction_to_finite_set (~50 LOC)

```
-- Statement:
-- For fixed xs : Fin m -> X, the set of distinct restriction patterns
-- { fun i => h(xs i) | h in C } is a finite set of cardinality <= GrowthFunction(C, m).
-- EmpRad(xs) = EmpRad over this finite set.

-- Proof sketch:
-- 1. Define restriction: restrict(h, xs) = fun i => h(xs i)
-- 2. Show: rademacherCorrelation h sigma xs depends on h only through restrict(h, xs)
--    (by unfolding rademacherCorrelation, which sums boolToSign(sigma i) * boolToSign(h(xs i)))
-- 3. The set of restrictions is a subset of (Fin m -> Bool), hence finite (Fintype instance)
-- 4. sSup over C = sSup over the Finset of distinct restrictions
-- 5. Cardinality of this Finset <= GrowthFunction(C, m) by definition

-- Tactic outline:
-- intro xs
-- set patterns := (Finset.univ.image (fun h => restrict h xs)).filter (fun p => exists h in C, ...)
-- show EmpRad = avg_sigma sSup_{p in patterns} |corr_p(sigma, xs)|
-- congr; ext sigma
-- apply le_antisymm
-- . csSup_le ... (each r = |corr(h,sigma,xs)| = |corr(restrict(h,xs), sigma, xs)| in the new set)
-- . csSup_le ... (reverse inclusion)
```

### B2: rademacher_summand_sub_gaussian (~70 LOC)

```
-- Statement:
-- Under uniform measure on SignVector m (= Measure.pi (fun _ : Fin m => uniformMeasure Bool)),
-- the function Z(sigma) = (1/m) * sum_i a_i * boolToSign(sigma i) with |a_i| <= 1
-- has HasSubgaussianMGF with parameter 1/sqrt(m).

-- Proof sketch:
-- 1. Each summand f_i(sigma) = a_i * boolToSign(sigma i) / m satisfies:
--    f_i(sigma) in [-1/m, 1/m]  (since |a_i| <= 1)
-- 2. Under uniform measure on SignVector m = product of (uniform on Bool):
--    the sigma_i are independent (iIndepFun for coordinate projections)
-- 3. E[f_i] = a_i/m * E[boolToSign(sigma i)] = a_i/m * 0 = 0
--    (boolToSign_sum_zero: sum_b boolToSign b = 0)
-- 4. Apply hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero to each f_i
-- 5. Apply sum_of_iIndepFun to the sum
-- 6. Parameter: sum of (1/m)^2 * ... = 1/m total

-- KEY: CKU_12 resolution.
-- The uniform measure on (Fin m -> Bool) IS Measure.pi (fun _ => Measure.count / 2).
-- Coordinate projections are iIndepFun by Measure.iIndepFun_iff and pi_apply.
-- Mathlib has: MeasureTheory.iIndepFun_iff for product measures.
-- The proof that pi-projections are independent under product measure is in
-- Mathlib.Probability.Independence.Kernel (iIndepFun_of_measure_pi or similar).

-- Tactic outline:
-- intro a ha m hm mu h_pi
-- set f : Fin m -> (SignVector m -> R) := fun i sigma => a i * boolToSign (sigma i) / m
-- have h_bdd : forall i, ae mu (fun sigma => f i sigma in Set.Icc (-1/m) (1/m)) := by ...
-- have h_mean : forall i, integral mu (f i) = 0 := by ...
-- have h_indep : iIndepFun (fun _ => inferInstance) (fun i sigma => f i sigma) mu := by
--   -- This is the CKU_12 content
--   apply iIndepFun_of...
-- have h_sg : forall i, HasSubgaussianMGF (f i) (1/m) mu := by
--   intro i; apply hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero ...
-- exact sum_of_iIndepFun h_indep h_sg
```

### B3: massart_finite_lemma (~100 LOC)

```
-- Statement:
-- For Z_1, ..., Z_N : Omega -> R, each HasSubgaussianMGF with parameter c,
-- E[max_{j <= N} Z_j] <= c * sqrt(2 * log N).

-- Standard proof:
-- For any lambda > 0:
--   E[max Z_j]
--   <= (1/lambda) * log(E[exp(lambda * max Z_j)])     -- Jensen: max >= log-sum-exp / log(N)
--   <= (1/lambda) * log(sum_j E[exp(lambda * Z_j)])   -- exp monotone + max >= each
--   <= (1/lambda) * log(N * exp(c^2 * lambda^2 / 2))  -- sub-Gaussian MGF bound
--   = (1/lambda) * (log N + c^2 * lambda^2 / 2)       -- log of product

-- Optimize: lambda = sqrt(2 * log N) / c gives
--   E[max Z_j] <= c * sqrt(2 * log N)

-- Lean proof strategy:
-- 1. The "max" is over a Finset, so use Finset.sup or sSup over a finite set.
-- 2. Need: exp(lambda * max Z_j) <= sum_j exp(lambda * Z_j)
--    This is: exp(lambda * Finset.sup' ...) <= Finset.sum (fun j => exp(lambda * Z_j))
--    Standard via: exp monotone, max <= sum of exp.
-- 3. E[sum] = sum E by linearity of integral.
-- 4. E[exp(lambda * Z_j)] <= exp(c^2 * lambda^2 / 2) by HasSubgaussianMGF definition.
-- 5. Algebra: optimize lambda.

-- KEY DIFFICULTY: Working with sSup over a finite set, measurability of max,
-- and the integral of the exponential. May need to define max as Finset.sup'
-- and prove basic properties.

-- ALTERNATIVE (simpler, avoids optimize-lambda):
-- Use tail integration: E[max Z_j] = integral_0^infty P[max Z_j >= t] dt
-- P[max Z_j >= t] <= N * exp(-t^2 / (2*c^2))  (union bound + sub-Gaussian tail)
-- integral_0^infty N * exp(-t^2/(2c^2)) dt = N * c * sqrt(pi/2)
-- This gives E[max] <= N * c * sqrt(pi/2), which is WORSE (linear in N vs sqrt(log N)).
-- So the Chernoff approach is essential for the sqrt(log N) bound.

-- Tactic outline:
-- intro Omega mu N Z c hN h_sg
-- by_cases hN_zero : N = 0
-- . simp [hN_zero]
-- set lambda := Real.sqrt (2 * Real.log N) / c
-- have h_lambda_pos : 0 < lambda := by ...
-- calc E[max_{j in Finset.range N} Z_j]
--     <= (1/lambda) * Real.log (E[exp(lambda * max Z_j)]) := by
--         -- Jensen's inequality for log (concave) applied to exp(lambda * max)
--         sorry -- or use: x <= (1/t) * log(exp(t*x)) for t > 0
--     _ <= (1/lambda) * Real.log (sum_j E[exp(lambda * Z_j)]) := by
--         -- exp(lambda * max) <= sum exp(lambda * Z_j)
--         ...
--     _ <= (1/lambda) * Real.log (N * exp(c^2 * lambda^2 / 2)) := by
--         -- sub-Gaussian MGF bound on each term
--         ...
--     _ = c * Real.sqrt (2 * Real.log N) := by
--         -- algebra with lambda = sqrt(2 log N) / c
--         ...
```

### B4: assembly (~30 LOC)

```
-- Statement: EmpRad(xs) <= sqrt(2 * d * log(2*m/d) / m)
-- Given:
--   B1: EmpRad = sSup over <= GrowthFunction(C,m) patterns
--   B3: E_sigma[max_{j<=N} Z_j] <= (1/sqrt(m)) * sqrt(2 * log N)
--   Sauer-Shelah: GrowthFunction(C,m) <= sum_{i<=d} C(m,i) <= (2*m/d)^d
--   (or more precisely: log(GrowthFunction) <= d * log(2*m/d))

-- Proof:
-- EmpRad(xs) = (1/2^m) * sum_sigma sSup_j |corr_j|   [definition]
--            = E_sigma[max_j |Z_j|]                     [B1: finite max over patterns]
--            <= (1/sqrt(m)) * sqrt(2 * log(N))          [B3: Massart with N = GrowthFunction]
--            <= (1/sqrt(m)) * sqrt(2 * d * log(2*m/d))  [Sauer-Shelah log bound]
--            = sqrt(2 * d * log(2*m/d) / m)             [algebra]

-- Tactic outline:
-- intro xs
-- obtain <N, hN_card, hN_eq> := restriction_to_finite_set C xs
-- have h_sg := rademacher_summand_sub_gaussian ...
-- calc EmpRad(xs) = E_sigma[max_{j in patterns} |Z_j|] := hN_eq
--     _ <= ... := massart_finite_lemma ...
--     _ <= ... := by { apply ...; exact growth_function_le_sauer_shelah ... }
```

---

## Sorry #8: Tactic Sequence (Uniform Version)

```
-- REVISED STATEMENT:
theorem rademacher_vanishing_imp_pac (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool)
    (hrad : forall eps > 0, exists m0, forall (D : MeasureTheory.Measure X),
      MeasureTheory.IsProbabilityMeasure D ->
      forall m >= m0, RademacherComplexity X C D m < eps) :
    PACLearnable X C := by
  apply vcdim_finite_imp_pac_direct
  by_contra hvcdim_inf
  push_neg at hvcdim_inf
  have hvcdim_top : VCDim X C = top := le_antisymm le_top hvcdim_inf
  -- Step 1: hrad with eps = 1/2 gives m0.
  obtain <m0, hm0> := hrad (1/2) (by norm_num)
  -- Step 2: VCDim = top -> exists shattered T with |T| >= 4*m0^2 + 1.
  have h_large_shatter : forall n, exists T, Shatters X C T /\ n <= T.card := by
    intro n; by_contra h_neg; push_neg at h_neg
    have hle : VCDim X C <= n := by
      apply iSup2_le; intro T hT; exact_mod_cast le_of_lt (h_neg T hT)
    rw [hvcdim_top] at hle; exact absurd hle (by simp)
  obtain <T, hT_shat, hT_card> := h_large_shatter (4 * m0^2 + 1)
  -- Step 3: C nonempty.
  have hC_ne : C.Nonempty := by
    obtain <c, hc, _> := hT_shat (fun _ => true); exact <c, hc>
  -- Step 4: Construct D = uniform measure on T.
  -- D = (1/|T|) * sum_{x in T} dirac(x). This is a probability measure.
  -- In Lean: MeasureTheory.Measure.restrict MeasureTheory.Measure.count T normalized.
  -- Or: use Finset.uniformMeasure or similar.
  --
  -- Step 5: Show Rad_{m0}(C,D) >= 7/8.
  -- (a) P[m0 draws from T are all distinct] >= 1 - m0*(m0-1)/(2*|T|)
  --     >= 1 - m0^2/(2*(4*m0^2+1)) > 1 - 1/8 = 7/8.
  -- (b) On distinct draws: all draws land in T, the image is a subset of T
  --     with card = m0, hence shattered by shatters_subset.
  -- (c) By empRad_eq_one_of_all_labelings: EmpRad = 1 on such draws.
  -- (d) Rad_{m0}(C,D) = integral EmpRad >= integral_{distinct} 1 * (7/8) = 7/8.
  --
  -- Step 6: But hm0 says Rad_{m0}(C,D) < 1/2. And 7/8 > 1/2. Contradiction.
  --
  -- MEASURE-THEORETIC DETAILS:
  -- The probability that m0 draws are all distinct is computed under D^{m0}.
  -- D^{m0} = MeasureTheory.Measure.pi (fun _ : Fin m0 => D).
  -- The set of injective samples: { xs : Fin m0 -> X | Function.Injective xs }.
  -- For uniform D on T: P[injective] = prod_{k<m0}(1 - k/|T|) = |T|! / ((|T|-m0)! * |T|^m0).
  -- Lower bound: >= 1 - C(m0,2)/|T| by union bound on collision pairs.
  --
  -- FORMALIZATION NOTE: constructing the uniform measure on T and computing
  -- birthday probability requires Measure.pi and Finset.sum properties.
  -- ~60 LOC for this step.
  sorry -- PLACEHOLDER: the proof outlined above, ~80 LOC total
```

---

## Counterfactual Route Evaluation

### Sorry #7 Routes

| Route | Description | LOC | Risk | Composition |
|-------|-------------|-----|------|-------------|
| **A: Full SubGaussian chain** | B1+B2+B3+B4 as described above | ~250 | MEDIUM | Best: uses Mathlib SubGaussian directly |
| **B: Direct Hoeffding + union** | Skip SubGaussian, use Hoeffding tail bound directly | ~200 | MEDIUM | Avoids HasSubgaussianMGF, but needs integral-of-tail |
| **C: Bypass Massart (Cauchy-Schwarz)** | Generalize vcdim_zero pattern | ~150 | MEDIUM-HIGH | Gives WEAKER bound: Rad <= sqrt(GF/m) instead of sqrt(2*d*log(2m/d)/m) |
| **D: Import Zhang** | Bridge to zhang/subGaussian_finite_max_bound | ~150 | HIGH | Type mismatch: IsSubGaussianProcess vs finite RVs |

**Recommendation**: Route A is the standard textbook chain and composes best with existing infrastructure. Route C gives a weaker bound but is shorter; however, the current `vcdim_bounds_rademacher_quantitative` statement requires the sqrt(2d*log(2m/d)/m) bound specifically, so Route C would require changing the statement (A5 concern). Route A is preferred.

**Route B detail**: Instead of the Massart lemma's Chernoff-optimize-lambda approach, directly use:
1. P[max_j Z_j >= t] <= N * P[Z_1 >= t] <= N * exp(-t^2*m/2) (union bound + Hoeffding)
2. E[max_j Z_j] = integral_0^infty P[max >= t] dt
3. This gives E[max] <= sqrt(2*log(N)/m) + error term

The issue is that tail integration in Lean requires `MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt` or similar, which is available but technically involved. Route A (Chernoff) is more algebraic and avoids integrals.

### Sorry #8 Routes (under uniform hypothesis)

| Route | Description | LOC | Risk |
|-------|-------------|-----|------|
| **A: Birthday + shatters_subset** | As described above | ~80 | LOW-MEDIUM |
| **B: Factor through Sorry #7** | VCDim < top => Rad <= sqrt(2d*log(2m/d)/m) -> 0, plus contrapositive | ~20 | LOW (but depends on Sorry #7) |
| **C: Direct PAC from vc_characterization** | Skip Rademacher entirely | ~5 | LOW |

**Route C detail**: If `rademacher_vanishing_imp_pac` is only used in `fundamental_rademacher` to prove the iff, and we have `vc_characterization : PACLearnable X C <-> VCDim X C < top` proved independently, then we could prove `rademacher_vanishing_imp_pac` by:
1. uniform Rad vanishing -> VCDim < top (by contrapositive + birthday, ~80 LOC)
2. VCDim < top -> PAC (by `vcdim_finite_imp_pac_direct`, PROVED)

This IS Route A. There's no shortcut that avoids the birthday argument.

**Route B detail**: If Sorry #7 is proved first, then:
- `vcdim_bounds_rademacher_quantitative` gives Rad <= f(d,m) for VCDim = d.
- `vcdim_finite_imp_rademacher_vanishing` gives uniform vanishing from VCDim < top.
- For the converse: NOT(VCDim < top) means VCDim = top.
  But sorry #7 only gives an UPPER bound on Rad, not a lower bound.
  We still need the birthday argument for the lower bound.

So Route A is necessary regardless.

---

## Risk Assessment (v2)

| Sorry | Route | LOC | Risk | A4 | A5 | Blockers |
|-------|-------|-----|------|----|----|----|
| #7 (quantitative) | A: SubGaussian chain | ~250 | MEDIUM | CLEAN | CLEAN | CKU_12 (iIndepFun on product measure) |
| #8 (vanishing->PAC) | A: Birthday (uniform hyp) | ~80 | LOW-MEDIUM | CLEAN | CLEAN | Uniform measure construction on Finset, birthday probability |

**Total**: ~330 LOC, 2 sorrys -> 0 sorrys.
**Statement changes**: 3 theorem statements (rademacher_vanishing_imp_pac, fundamental_rademacher, fundamental_theorem conjunct 3) change quantifier order.

---

## K/U Update (D6 v2)

### KK (Verified)
- v1 KK items all still hold.
- NEW KK_14: `vcdim_finite_imp_rademacher_vanishing` computes m0 = max(d+1, ceil(32*(d+1)/eps^4)+1) which does NOT depend on D. The forward direction already proves uniform vanishing in content.
- NEW KK_15: The downstream consumers of pointwise vanishing are exactly: `fundamental_rademacher` (PAC.lean:196-199) and `fundamental_theorem` conjunct 3 (PAC.lean:207-209). Both can be updated to uniform quantifiers.
- NEW KK_16: `shatters_subset` (Rademacher.lean:324) is PROVED and gives: any subset of a shattered set is shattered. This is essential for the birthday argument.
- NEW KK_17: `empRad_eq_one_of_all_labelings` (Rademacher.lean:349) is PROVED and gives EmpRad = 1 when every labeling of the sample is realized.

### KU (Articulated unknowns)
- CKU_6 RESOLVED (v1): Zhang not needed.
- CKU_7 RESOLVED (v2): Use uniform vanishing. The pointwise statement is likely true but requires a fundamentally harder proof (single adversarial D with infinite support via dependent choice, where Rad lower bound doesn't decay). The uniform version is textbook-standard and provable.
- CKU_12 OPEN: iIndepFun for coordinate projections under Measure.pi on (Fin m -> Bool). Mathlib likely has this but the exact API needs verification. Search: `iIndepFun_of_measure_pi`, `iIndepFun_pi`, or construct from `Measure.pi_apply` + `iIndep_iff`.
- CKU_13 RESOLVED: Massart CAN be proved without SubGaussian (direct Hoeffding tail + integration), but the Chernoff/SubGaussian route is cleaner and shorter in Lean.
- NEW CKU_14: Constructing uniform probability measure on a Finset T in Lean. Options: (a) `(T.card)^{-1} * sum_{x in T} Measure.dirac x`, (b) `Measure.count.restrict T` normalized, (c) `MeasureTheory.Measure.ofFinset`. Need to verify which API exists and prove IsProbabilityMeasure.
- NEW CKU_15: Birthday probability lower bound in Lean. Need: for m draws from uniform on n points, P[all distinct] >= 1 - C(m,2)/n. This is a standard combinatorial inequality but may require explicit formalization (~20 LOC).

### UK (Pressures)
- UK_5 RESOLVED: The pointwise-in-D statement is likely true but we BYPASS the question by strengthening to uniform. The uniform version is textbook-standard and provable.
- UK_6 RESOLVED: No longer needed (uniform route avoids single adversarial D construction).
- NEW UK_7: The exact Mathlib API for Measure.pi and iIndepFun composition. If Mathlib doesn't expose `iIndepFun` for pi-projections directly, building the bridge (~30 LOC) is the main unknown for B2.

---

## Proof Order Recommendation

### Phase 1: Statement changes (0 LOC new proofs, ~20 LOC edits)
1. Change `rademacher_vanishing_imp_pac` hypothesis to uniform.
2. Reorder quantifiers in `vcdim_finite_imp_rademacher_vanishing` proof (intro eps before D).
3. Update `fundamental_rademacher` and `fundamental_theorem` conjunct 3 RHS.
4. Build to verify 0 errors, 2 sorrys unchanged.

### Phase 2: Sorry #8 (uniform version, ~80 LOC)
1. Construct uniform measure on Finset.
2. Prove birthday lower bound.
3. Assemble contradiction.
4. Build: 0 errors, 1 sorry remaining.

### Phase 3: Sorry #7 (~250 LOC)
1. B1: restriction_to_finite_set (~50 LOC)
2. B2: rademacher_summand_sub_gaussian (~70 LOC, resolves CKU_12)
3. B3: massart_finite_lemma (~100 LOC, hardest lemma)
4. B4: assembly (~30 LOC)
5. Build: 0 errors, 0 sorrys in Rademacher.lean.

### Why this order?
- Phase 1 is risk-free and validates the design.
- Phase 2 is lower risk than Phase 3 and produces immediate value (sorry count drops).
- Phase 3 is self-contained within Rademacher.lean.

---

## Literature References

(Same as v1, plus:)

8. Boucheron, Lugosi & Massart (2013). Concentration Inequalities. Oxford University Press. Ch.2 (sub-Gaussian variables), Lemma 2.6 (Massart finite lemma). [DOI: 10.1093/acprof:oso/9780199535255.001.0001]

9. Ledoux & Talagrand (1991). Probability in Banach Spaces. Springer. Ch.4 (Rademacher processes).
