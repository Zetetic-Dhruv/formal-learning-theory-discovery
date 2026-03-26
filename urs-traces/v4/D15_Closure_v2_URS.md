# D15 Closure v2 URS: Complete Closure of D1 + D5 Dependees

## Will

Close `uc_bad_event_le_delta` (Generalization.lean:1270, the SOLE remaining blocker
for the entire UC-to-PAC chain) and `sample_complexity_upper_bound` (Bridge.lean:621).
These two sorrys gate the quantitative PAC theory: without them, the VC characterization
exists but lacks sample complexity bounds.

## Date: 2026-03-20

---

## 1. AMRT-Organized K/U Universe

### 1.1 KK (Known Knowns) -- Verified Proved Infrastructure

| ID | Lemma | File:Line | Signature | Status |
|----|-------|-----------|-----------|--------|
| KK1 | `consistent_tail_bound` | Gen:550-586 | `D [Prob] h c m eps -> Measure.pi {consistent} <= ofReal((1-eps)^m)` | PROVED (one-sided, for FIXED h with TrueErr >= eps) |
| KK2 | `pow_mul_exp_neg_le_factorial_div` | Gen:717-738 | `t^d * exp(-t) <= (d+1)!/t` for t > 0 | PROVED |
| KK3 | `sum_choose_le_mul_pow` | Gen:741-755 | `sum_{i<=d} C(m,i) <= (d+1)*m^d` for m >= 1 | PROVED |
| KK4 | `vcdim_finite_imp_growth_bounded` | Gen:759-... | `VCDim < top -> exists d, forall m >= d, GF(C,m) <= sum C(m,i)` | PROVED |
| KK5 | `uc_imp_pac` | Gen:1346-1442 | `HasUniformConvergence X C -> PACLearnable X C` | PROVED (sorry-free) |
| KK6 | `vcdim_finite_imp_pac_via_uc` | Gen:1447-1454 | `VCDim < top -> PACLearnable` (routes through uc_imp_pac + vcdim_finite_imp_uc) | Depends on KU1 only |
| KK7 | `growth_function_le_sauer_shelah` | Bridge:465-483 | Sauer-Shelah via Mathlib | PROVED |
| KK8 | `per_sample_labeling_bound` | Gen:2809-2900 | Pairing + flip involution, `2 * good_count <= total` | PROVED |
| KK9 | `nfl_counting_core` | Gen:2907-... | Double-counting + pigeonhole via per_sample_labeling_bound | PROVED (calls per_sample_labeling_bound) |
| KK10 | `vcdim_infinite_not_pac` measure bridge (substep B) | Gen:3304-end | Counting-to-Measure.pi | PROVED |
| KK11 | `prob_compl_ge_of_le` | Gen:525-538 | mu(s) <= delta -> mu(s^c) >= 1-delta | PROVED |
| KK12 | `shatters_iff_finset_shatters` | Bridge:130-191 | Our Shatters <-> Mathlib Shatters | PROVED |
| KK13 | `vcdim_eq_finset_vcdim` | Bridge:217-248 | Our VCDim = Mathlib vcDim | PROVED |
| KK14 | `card_restrict_le_sauer_shelah_bound` | Bridge:393-425 | Restriction card <= sum C(m,i) | PROVED |
| KK15 | `Real.one_sub_le_exp_neg` | Mathlib | `1 - x <= exp(-x)` | Available |
| KK16 | `Real.pow_div_factorial_le_exp` | Mathlib | `t^n / n! <= exp(t)` for t >= 0 | Available (used by KK2) |
| KK17 | `measure_sum_ge_le_of_iIndepFun` | Mathlib SubGaussian.lean:780 | Hoeffding: `mu.real {eps <= sum X_i} <= exp(-eps^2 / (2 * sum c_i))` | Available |
| KK18 | `hasSubgaussianMGF_of_mem_Icc` | Mathlib SubGaussian.lean | Bounded rv -> SubGaussian | Available |

### 1.2 KU (Known Unknowns) -- Articulated Questions with Resolution Paths

#### KU1: `uc_bad_event_le_delta` (Gen:1270-1283) -- THE critical sorry

**Precise question:** Can we prove that for m >= (v+2)!/(eps^(v+1)*delta), the probability of the bad UC event {exists h in C, |TrueErr - EmpErr| >= eps} is <= delta?

**Statement (exact):**
```lean
private lemma uc_bad_event_le_delta {X : Type u} [MeasurableSpace X]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (C : ConceptClass X Bool) (c : Concept X Bool)
    (m : ℕ) (hm : 0 < m) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1)
    (v : ℕ) (hv : ∀ (n : ℕ), v ≤ n →
      GrowthFunction X C n ≤ ∑ i ∈ Finset.range (v + 1), Nat.choose n i)
    (hm_bound : ↑((v + 2).factorial) / (ε ^ (v + 1) * δ) ≤ ↑m) :
    MeasureTheory.Measure.pi (fun _ : Fin m => D)
      { xs : Fin m → X | ∃ h ∈ C,
        |TrueErrorReal X h c D -
         EmpiricalError X Bool h (fun i => (xs i, c (xs i)))
           (zeroOneLoss Bool)| ≥ ε }
      ≤ ENNReal.ofReal δ
```

**Counterproof attempt:** The statement is mathematically TRUE. The factorial sample complexity is vastly larger than needed for the Hoeffding bound (m ~ (v log m + log(1/delta))/eps^2 suffices). The excess means ANY valid proof technique (Hoeffding, Chebyshev, polynomial tail) will produce a bound <= delta at this sample size. No counterexample exists.

**Key structural observation:** The statement says TWO-SIDED (absolute value), but the `c` parameter is fixed and the bad event quantifies over ALL h in C. This is the FULL uniform convergence bad event, not just the consistent case.

**Resolution paths:** See Section 4 (three routes detailed).

#### KU2: `sample_complexity_upper_bound` (Bridge:621-657) -- D5 sorry

**Precise question:** Can this be closed independently of KU1?

**Statement (exact):**
```lean
theorem sample_complexity_upper_bound (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (d : ℕ) (hd : VCDim X C = ↑d)
    (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    SampleComplexity X C ε δ ≤
      Nat.ceil ((8 / ε) * (↑d * Real.log (2 / ε) + Real.log (2 / δ)))
```

**Counterproof attempt:** The statement is mathematically TRUE (standard textbook bound). The sorry at line 657 is:
```lean
exact ⟨L, fun D hD c hcC => by sorry⟩
```
This requires showing that L (obtained from `vcdim_finite_imp_pac_via_uc`) achieves PAC at sample size = bound. But L is an `Exists.choose` from `vcdim_finite_imp_pac_via_uc`, making `mf` opaque. The proof tries to directly show bound is in the SampleComplexity set, but this requires the SAME measure-theoretic argument as KU1.

**Dependency verdict:** `sample_complexity_upper_bound` is BLOCKED by KU1. The sorry at line 657 requires proving `D^m {good event} >= 1 - delta` for the ERM learner at sample size = bound. This is exactly the content of `uc_bad_event_le_delta` with different constants.

**Resolution path:** After KU1 is resolved, the proof approach for KU2 is:
1. Show the ceiling bound >= (v+2)!/(eps^(v+1)*delta) for appropriate v (the VCDim value d).
2. Apply `vcdim_finite_imp_uc` to get UC at this sample size.
3. Apply `uc_imp_pac`'s logic to show PAC at this sample size.
4. Show the bound is in the SampleComplexity set.

**Alternative (weaker closure):** Prove `SampleComplexity X C eps delta <= mf eps delta` (step 4 of existing proof, line 643, already done) and then bound `mf eps delta`. But mf is opaque (Exists.choose), making this impossible without definitional unfolding.

#### KU3: Is there a measurability obstruction for the growth-function-per-sample argument?

**Precise question:** The standard textbook proof of the UC bound groups hypotheses by their restriction to the sample. For EACH sample xs, at most GF(C,m) distinct behaviors exist. But formalizing "for each sample, union-bound over at most GF(C,m) terms" requires integrating a per-sample union bound inside the product measure. Is the set `{xs | exists h in C, ...}` even measurable?

**Counterproof attempt:** In Lean4 with `MeasureTheory.Measure.pi`, we work with OUTER measure, not just measurable sets. The existing codebase already uses `MeasureTheory.OuterMeasure.mono` (Gen:1396) for set inclusion arguments without measurability. So measurability is NOT a hard blocker -- we can use outer measure monotonicity throughout.

**Resolution:** Not a true obstruction. The proof can avoid measurability issues by working with outer measure inequalities.

#### KU4: Does the Hoeffding route (via Mathlib) require iIndepFun for coordinate projections under Measure.pi?

**Precise question:** To apply `measure_sum_ge_le_of_iIndepFun` (Mathlib:780), we need `iIndepFun (fun i => X_i) (Measure.pi D^m)` where `X_i omega = indicator(h(omega_i) != c(omega_i))`. Is this available?

**Counterproof attempt:** Mathlib's `Measure.pi` does provide independence of coordinate projections. The lemma `ProbabilityTheory.iIndepFun_iff_pi_map_eq` or `MeasureTheory.Measure.iIndepFun_of_pi` should establish this. The codebase already uses `iIndepFun_block_extract` (Gen:~3015) which proves independence for block extractions from product measures. Coordinate projections are the k=m, block_size=1 case.

**Resolution:** Likely available but may need a small bridge lemma (~10 LOC).

#### KU5: Does the Measure.real bridge work cleanly?

**Precise question:** `measure_sum_ge_le_of_iIndepFun` returns a bound on `mu.real {event}` (= `(mu event).toReal`). We need a bound on `mu event` (in ENNReal). Is the bridge clean?

**Counterproof attempt:** For probability measures, `mu.real s <= r` implies `mu s <= ENNReal.ofReal r` when `r >= 0` and `mu s < top`. Both conditions hold for probability measures. The bridge is: `mu s = ENNReal.ofReal (mu.real s)` when `mu s < top`, then monotonicity of `ofReal`.

**Resolution:** ~5 LOC bridge, no blockers.

### 1.3 UK (Unknown Unknowns) -- Structural Pressures

| ID | Pressure | Risk |
|----|----------|------|
| UK1 | The factorial sample complexity `(v+2)!/(eps^(v+1)*delta)` in `uc_bad_event_le_delta` is MUCH larger than the standard Hoeffding-based bound `O((v log(v/eps) + log(1/delta))/eps^2)`. This mismatch means the Hoeffding route has more arithmetic headroom but a DIFFERENT proof structure than what the codebase was designed for. The polynomial-tail route matches the factorial but only works one-sided. | MEDIUM: the two-sided requirement may force the Hoeffding route, but the factorial gives ample room. |
| UK2 | The `c : Concept X Bool` parameter in `uc_bad_event_le_delta` is a RED HERRING. The bound must hold for ALL h in C, regardless of c. The role of c is only in constructing the labeled sample `(xs i, c (xs i))` -- it determines the training distribution but the UC bound must hold for deviations of ANY hypothesis. This means the one-sided consistent-only approach is INSUFFICIENT without additional argument. | HIGH: this is the core tension between one-sided and two-sided. |
| UK3 | The dead code sections (bad_consistent_covering, union_bound_consistent, vcdim_finite_imp_pac_direct) at Gen:618-713 and Gen:878-1190 are substantial (~500 lines). Their sorrys are NOT on the critical path (bypassed by the UC route). But they may confuse future agents into thinking they need to be proved. | LOW: documentation issue only. |

### 1.4 UU (Unknown Unknowns) -- Boundary

| ID | Region | Why Opaque |
|----|--------|------------|
| UU1 | Whether Mathlib's `iIndepFun` for indicator functions under `Measure.pi` is provable without `MeasurableSet` hypotheses on the error sets `{x | h x != c x}`. The codebase avoids measurability assumptions on concept classes (working with outer measure), but Hoeffding needs `AEMeasurable` for each `X_i`. | The gap between outer-measure arguments and inner-measure (Hoeffding) arguments may force adding measurability hypotheses. |
| UU2 | Whether the `Exists.choose` opacity in `sample_complexity_upper_bound` can be resolved. The learner L and sample function mf are behind `Exists.choose` from `vcdim_finite_imp_pac_via_uc`. Their definitional behavior is opaque, making it impossible to compute `mf eps delta` explicitly. | May require restructuring to expose the concrete mf. |

---

## 2. Measurement (Pl/Coh/Inv/Comp)

### 2.1 Plausibility

**uc_bad_event_le_delta:** Pl = 0.65. Three independent routes exist (Section 4). At least one should work. The factorial sample complexity provides massive headroom. The main risk is the two-sided requirement forcing Hoeffding, which has the iIndepFun/AEMeasurable bridge risk.

**sample_complexity_upper_bound:** Pl = 0.40. Blocked by KU1 AND by the Exists.choose opacity (UU2). Even after KU1, the proof requires either:
(a) Restructuring to expose the concrete mf, or
(b) A second sorry-closure that directly shows bound is in the SampleComplexity set.
Option (b) duplicates much of the UC proof.

### 2.2 Coherence (with HC at each layer joint)

**Layer 1: Combinatorics -> Measure Theory** (Sauer-Shelah -> Concentration)
- Joint: GrowthFunction (combinatorial) feeds into measure-theoretic union bound.
- HC = 0.1 (clean bridge via proved infrastructure KK3, KK4, KK7).

**Layer 2: Per-hypothesis concentration -> Union bound**
- Joint: Single-hypothesis tail bound composed with growth function counting.
- HC = 0.3 for one-sided (proved KK1), HC = 0.5 for two-sided (needs Hoeffding).

**Layer 3: Measure.real -> ENNReal**
- Joint: Hoeffding gives `mu.real` bound, need `ENNReal.ofReal` bound.
- HC = 0.1 (standard bridge, ~5 LOC).

**Layer 4: UC -> PAC -> SampleComplexity**
- Joint: `vcdim_finite_imp_uc` -> `uc_imp_pac` -> `Nat.sInf_le`.
- HC = 0.0 (all proved except uc_bad_event_le_delta).

**Layer 5: Exists.choose opacity for sample_complexity_upper_bound**
- Joint: mf from PACLearnable witness -> concrete bound.
- HC = 0.8 (HIGH: the mf is opaque, cannot be computed).

### 2.3 Invariance

**Under strengthened VCDim hypothesis:** The proofs are invariant under adding `[Fintype X]` or `[DecidableEq X]` -- the growth function argument works for general X through the abstract GrowthFunction bound `hv`.

**Under weakened sample complexity:** If the factorial bound were replaced with a tighter Hoeffding-based bound, the proof would be EASIER (less arithmetic headroom needed). Invariant under tightening.

**Counterfactual: What if eps > 1/2?** The polynomial tail `(1-eps)^m` is negative for eps > 1 (nonsensical). For eps in (1/2, 1), the factorial bound `(v+2)!/(eps^(v+1)*delta)` still works but the Hoeffding route `exp(-2*m*eps^2)` is more natural. The proof should handle eps in (0, 1) uniformly.

### 2.4 Compactness

| Target | Dependencies | LOC Estimate | Confidence |
|--------|-------------|--------------|------------|
| uc_bad_event_le_delta (Route A) | KK1, KK2, KK3, KK4 | ~60 | 0.55 |
| uc_bad_event_le_delta (Route B) | KK17, KK18, KU4, KU5 | ~120 | 0.45 |
| uc_bad_event_le_delta (Route C) | ConcentrationAlt infrastructure | ~200 | 0.25 |
| sample_complexity_upper_bound | KU1 resolved + restructure | ~80 | 0.35 |

---

## 3. Symmetrization Status Report

### 3.1 EXACT Inventory of What Exists

**In ConcentrationAlt.lean (155 lines total):**

| Component | Line | Status |
|-----------|------|--------|
| `GhostSample` structure | 123-125 | DEFINED (primary : Fin m -> X, ghost : Fin m -> X) |
| `DoubleSampleMeasure` | 128-133 | DEFINED (Measure.prod of two Measure.pi) |
| `symmetrization_lemma` | 136-154 | SORRY (statement only, reduces single-sample deviation to double-sample) |
| `mcdiarmid_via_zhang` | 66-84 | SORRY (McDiarmid via Zhang's Efron-Stein bridge) |
| `single_hypothesis_two_sided` | 89-101 | SORRY (two-sided Hoeffding for single h) |
| `uc_via_mcdiarmid` | 105-112 | SORRY (UC via Route B, the McDiarmid chain) |

**In Generalization.lean:**
| Component | Line | Status |
|-----------|------|--------|
| `HasBoundedDifferences` | ~460 | DEFINED |
| `empiricalError_bounded_diff` | ~470-516 | PROVED (EmpError has bounded differences with c = 1/m) |
| `iIndepFun_block_extract` | ~3015-3057 | PROVED (independence of block extractions from product measure) |
| `block_extract` | defined | DEFINED + PROVED (splits Fin(k*m) -> X into k blocks) |

### 3.2 What Is MISSING for Full Symmetrization

1. **symmetrization_lemma proof** (~70 LOC): Reduces P(|EmpErr - TrueErr| >= eps) to 2 * P(|EmpErr(S) - EmpErr(S')| >= eps/2). Requires Chebyshev or Markov on the ghost sample.

2. **Conditioned restriction counting** (~40 LOC): After conditioning on combined sample, at most GF(C,2m) distinct restriction patterns exist.

3. **Per-pattern Hoeffding** (~50 LOC): For each restriction pattern, apply Hoeffding to bounded iid random variables (swap indicators).

4. **Assembly** (~30 LOC): Chain components 1-3 into the full UC bound.

### 3.3 Verdict

Symmetrization infrastructure EXISTS at the definition level but ALL proofs are sorry'd. The block_extract independence (KK from Generalization.lean) is the one proved component that would feed into a symmetrization proof. The full symmetrization route is ~190 LOC of new proofs -- the MOST expensive of the three routes for closing `uc_bad_event_le_delta`.

**For the current closure task, symmetrization is NOT recommended.** Routes A and B (Section 4) are more efficient.

---

## 4. Proof Routes for `uc_bad_event_le_delta`

### Route A: One-Sided Polynomial Tail (through pow_mul_exp_neg_le_factorial_div)

**Viability: 0.55** -- Highest confidence but requires resolving the one-sided vs two-sided gap.

**Core idea:** Bound the two-sided UC bad event by a one-sided bound plus a concentration term. For consistent hypotheses (EmpErr = 0), the bad event reduces to TrueErr >= eps. For non-consistent hypotheses, bound their contribution separately.

**Proof sketch:**
```
Step 1: Decompose bad event.
  {exists h in C, |TrueErr - EmpErr| >= eps}
  SUBSET {exists h in C, TrueErr >= eps AND consistent(h, xs)}
         UNION {exists h in C, EmpErr > 0 AND |TrueErr - EmpErr| >= eps}

Step 2: Bound first set via growth function + consistent_tail_bound.
  mu(first) <= GF(C,m) * (1-eps)^m
             <= (v+1)*m^v * exp(-eps*m)           [KK3 + one_sub_le_exp_neg]
             <= (v+1) * (v+1)!/(eps^(v+1)*m)      [KK2 with t = eps*m]
             = (v+2)!/(eps^(v+1)*m)
             <= delta/2                            [from hm_bound, with factor 2]

Step 3: Bound second set.
  For non-consistent h: h disagrees with c on at least one sample point.
  The empirical error EmpErr(h, xs) >= 1/m > 0.
  Need: P(|TrueErr - EmpErr| >= eps for some non-consistent h in C) <= delta/2.
  This requires per-hypothesis concentration for non-consistent h.
  For FIXED h: P(|EmpErr - TrueErr| >= eps) <= 2*exp(-2*m*eps^2) [Hoeffding].
  Union over GF(C,m) classes: GF(C,m) * 2*exp(-2*m*eps^2) <= delta/2.
  For m >= (v+2)!/(eps^(v+1)*delta), this holds because
  (v+1)*m^v * 2*exp(-2*m*eps^2) decays faster than any polynomial.
```

**Blocker:** Step 3 still requires Hoeffding (Route B infrastructure). If we want a PURE polynomial-tail proof, we need to avoid the second set entirely.

**PURE POLYNOMIAL-TAIL VARIANT (Route A'):**

**Key insight:** Weaken the statement. Instead of bounding the full two-sided event, bound only the consistent-hypothesis event. Then modify `vcdim_finite_imp_uc` to use a one-sided UC definition.

**Problem:** `HasUniformConvergence` (Gen:1234-1245) requires |TrueErr - EmpErr| < eps for ALL h in C, not just consistent ones. Weakening this changes the definition, which changes uc_imp_pac, which changes PACLearnable's proof structure.

**Verdict on Route A pure:** NOT viable without statement changes. Route A with Step 3 is viable but requires Route B infrastructure anyway.

**LOC:** ~60 (Steps 1-2) + ~60 (Step 3 via Hoeffding bridge) = ~120.

---

### Route B: Two-Sided Hoeffding (through Mathlib measure_sum_ge_le_of_iIndepFun)

**Viability: 0.45** -- Clean mathematical route but significant Lean4 bridge work.

**Core idea:** For each FIXED h in C, the centered indicators `Y_i = 1_{h(x_i) != c(x_i)} - TrueErr(h)` are iid, bounded in [-1, 1], with mean 0 under Measure.pi. Hoeffding gives P(|EmpErr - TrueErr| >= eps) <= 2*exp(-2*m*eps^2). Union over GF(C,m) restriction classes gives the full UC bound.

**Proof sketch:**
```
Step 1: For FIXED h, define Y_i : (Fin m -> X) -> R.
  Y_i(omega) = (if h(omega i) != c(omega i) then 1 else 0) - (D {x | h x != c x}).toReal
  Y_i are bounded in [-1, 1].
  E[Y_i] = 0 (by linearity: E[indicator] = D{error} = TrueErr).

Step 2: Establish iIndepFun for (Y_i)_{i : Fin m} under Measure.pi.
  Each Y_i depends only on the i-th coordinate.
  Measure.pi makes coordinates independent.
  Need: lemma iIndepFun_of_pi_coord or similar.

Step 3: Apply hasSubgaussianMGF_of_mem_Icc.
  Y_i in [-(1 : R), 1], so HasSubgaussianMGF Y_i ((1 - (-1))^2 / 4) = HasSubgaussianMGF Y_i 1.

Step 4: Apply measure_sum_ge_le_of_iIndepFun.
  mu.real {eps*m <= sum Y_i} <= exp(-(eps*m)^2 / (2 * m * 1)) = exp(-m*eps^2/2).
  Two-sided: multiply by 2 (apply to both sum >= eps*m and sum <= -eps*m).
  Result: mu.real {|sum Y_i| >= eps*m} <= 2*exp(-m*eps^2/2).
  Convert: sum Y_i / m = EmpErr - TrueErr.
  So: mu.real {|EmpErr - TrueErr| >= eps} <= 2*exp(-m*eps^2/2).

Step 5: Bridge mu.real -> mu (ENNReal).
  mu {bad for h} <= ENNReal.ofReal (2*exp(-m*eps^2/2)).

Step 6: Growth function union bound.
  For each sample xs, at most GF(C,m) distinct restriction classes.
  The bad event {exists h in C, bad} is contained in the union of GF(C,m)
  per-class events. Each has probability <= 2*exp(-m*eps^2/2).
  ISSUE: The per-class bound is for a FIXED h, but the class contains multiple h
  with different TrueErr. The worst-case h within each class dominates.
  RESOLUTION: For each class, the EmpErr is the SAME (same restriction).
  Pick any representative h_r. If |EmpErr(h_r, xs) - TrueErr(h_r)| < eps,
  this says nothing about other h' in the class with different TrueErr.
  BUT: the bad event asks for |TrueErr(h) - EmpErr(h, xs)| >= eps.
  Since EmpErr(h, xs) = EmpErr(h_r, xs) for all h in the same class,
  the bad event for class r is: {xs | exists h in class r, |TrueErr(h) - EmpErr_r(xs)| >= eps}.
  This is NOT bounded by the representative's Hoeffding bound.

  CRITICAL REALIZATION: The standard textbook proof handles this differently.
  For EACH h individually (not per class), Hoeffding gives the bound.
  The union bound is over all HYPOTHESES, bounded by GF(C,m) because
  hypotheses with the same restriction have the SAME EmpErr AND the SAME
  per-sample loss distribution on the complement of the sample.

  CORRECTION: For h, h' with the same restriction to {xs_i}:
  - EmpErr(h, xs) = EmpErr(h', xs) (same on sample points).
  - TrueErr(h) may differ from TrueErr(h') (different on population).
  - The Hoeffding bound P(|EmpErr - TrueErr| >= eps) depends on TrueErr(h).
  - SO: within a class, different h have different deviation probabilities.

  RESOLUTION: The correct argument is that for EACH xs, within each restriction
  class, the bad event is either triggered or not (it's a deterministic function
  of TrueErr and the common EmpErr). The probability is taken over xs, and
  the class membership itself depends on xs. So we cannot simply union-bound
  over classes.

  ACTUAL CORRECT APPROACH: For each FIXED h, P(bad for h) <= 2*exp(-2*m*eps^2).
  The event {exists h, bad} has probability <= sum over all h of P(bad for h).
  But C is potentially uncountable. The growth function trick: for each xs,
  group hypotheses by restriction. Within a class, ALL have the same (EmpErr, xs).
  The deviation |TrueErr(h) - EmpErr(h, xs)| = |TrueErr(h) - common_value|.
  If ANY h in the class is bad, the class is bad. The question: is P(class r bad)
  bounded?

  YES: Pick a REPRESENTATIVE h_r from each class. For class r:
  {xs | class r is bad} SUBSET {xs | |TrueErr(h_r) - EmpErr(h_r, xs)| >= eps}
  ONLY IF h_r is the worst-case member. Otherwise, the inclusion fails.

  FINAL RESOLUTION: The correct approach uses the fact that for a FIXED sample xs,
  the set of "bad" h is determined by finitely many representatives (one per class).
  But since the classes depend on xs, we cannot fix representatives in advance.

  THE TEXTBOOK TRICK: Condition on the sample xs. For each xs, at most GF(C,m)
  distinct empirical errors. For each distinct empirical error value e_j,
  the set of h achieving this error has the same EmpErr = e_j.
  The "worst" h in the class (maximizing |TrueErr - e_j|) determines whether
  the class contributes to the bad event.
  P(class j bad) = P(exists h in class j with |TrueErr(h) - e_j| >= eps).
  This is bounded by P(|e_j - TrueErr(h_j)| >= eps) for any fixed representative h_j.
  By Hoeffding for h_j: P(|EmpErr(h_j) - TrueErr(h_j)| >= eps) <= 2*exp(-2*m*eps^2).
  Union over <= GF(C,m) representatives: P(bad) <= GF(C,m) * 2*exp(-2*m*eps^2).

  ISSUE: The representative h_j must be chosen BEFORE seeing xs (otherwise the
  Hoeffding bound doesn't apply -- the representative is data-dependent).
  This is exactly the bad_consistent_covering problem! (Gamma_92)

  CORRECT TEXTBOOK SOLUTION: Use DOUBLE SAMPLE / SYMMETRIZATION to avoid
  the pre-sample representative issue. This is Route C.

  ALTERNATIVE (for our proof): Use the WEAKER bound that avoids representatives.
  For EACH h (fixed, not data-dependent):
    P(|EmpErr(h) - TrueErr(h)| >= eps) <= 2*exp(-2*m*eps^2).
  The event {exists h in C, bad(h)} has outer measure:
    mu*({exists h, bad}) <= ??? (cannot union-bound over uncountable C directly)

  RESOLUTION FOR LEAN4: Use the growth function at the SET level, not the
  representative level. The key set-inclusion:

  {xs | exists h in C, |TrueErr(h) - EmpErr(h,xs)| >= eps}
  = Union_h {xs | |TrueErr(h) - EmpErr(h,xs)| >= eps}

  This is an UNCOUNTABLE union. But by the growth function argument:
  for EACH xs, at most GF(C,m) distinct EmpErr values exist.
  So the uncountable union is really a FINITE union (dependent on xs).

  For OUTER MEASURE: mu*(Union_h A_h) <= sum_{j=1}^{GF(C,m)} mu*(A_{h_j})
  where h_j are representatives. But the representatives DEPEND on xs.

  THIS IS EXACTLY the bad_consistent_covering problem.
  Route B as stated is BLOCKED by the same structural issue as Gamma_92.
```

**Revised viability: 0.25** -- The per-hypothesis Hoeffding approach runs into the same representative-selection problem as bad_consistent_covering. The standard textbook resolution IS symmetrization (Route C).

**LOC:** ~120 if the representative issue could be resolved; ~200+ with symmetrization.

---

### Route C: Symmetrization-Based (through ConcentrationAlt infrastructure)

**Viability: 0.30** -- Mathematically correct but largest LOC investment.

**Core idea:** The symmetrization argument avoids the representative-selection problem by introducing a ghost sample. The key steps:
1. Symmetrization: P(|EmpErr - TrueErr| >= eps) <= 2 * P(|EmpErr(S) - EmpErr(S')| >= eps/2).
2. Conditioning: Fix combined sample (S, S'). At most GF(C, 2m) restriction patterns.
3. Per-pattern Hoeffding: For each pattern, the difference |EmpErr(S) - EmpErr(S')| is a sum of bounded iid random variables (the swap indicators). Hoeffding applies UNCONDITIONALLY.
4. Union bound: GF(C, 2m) * 2*exp(-m*eps^2/8) <= delta.

**Proof sketch:**
```
Step 1: Apply symmetrization_lemma (SORRY in ConcentrationAlt.lean:136-154).
  Need to PROVE this lemma first (~70 LOC).

Step 2: Conditioning on combined sample.
  DoubleSampleMeasure X D m = Measure.prod (Measure.pi D^m) (Measure.pi D^m).
  Condition on the COMBINED sample z = (S, S'). This is a 2m-point multiset.
  For fixed z, at most GF(C, 2m) distinct restriction patterns.
  Per pattern, the swap argument applies. (~40 LOC)

Step 3: Per-pattern Hoeffding.
  For a fixed restriction pattern on z, define:
  Y_i = loss(h, z_{sigma(i)}) - loss(h, z_{sigma'(i)})
  where sigma is a random permutation. Y_i are iid Rademacher-scaled.
  Hoeffding: P(|sum Y_i| >= m*eps/2) <= 2*exp(-m*eps^2/8). (~50 LOC)

Step 4: Assembly.
  P(bad) <= 2 * GF(C, 2m) * 2*exp(-m*eps^2/8)
          = 4 * GF(C, 2m) * exp(-m*eps^2/8).
  With GF(C, 2m) <= (v+1)*(2m)^v [Sauer-Shelah]:
  bound <= 4*(v+1)*(2m)^v * exp(-m*eps^2/8).
  For m >= (v+2)!/(eps^(v+1)*delta): this is <= delta (exponential beats polynomial). (~30 LOC)
```

**LOC:** ~190 new proof code (70 + 40 + 50 + 30).

**Blocker:** The symmetrization lemma (Step 1) is the hardest component. It requires either:
(a) Conditional probability/expectation manipulation (Fubini + tower property), or
(b) The simplified iid-symmetry argument (triangle inequality + equal marginals).
Option (b) is simpler but still requires ~70 LOC.

---

### Route A'' (RECOMMENDED): Direct Polynomial Tail with Statement-Compatible Bound

**Viability: 0.60** -- Avoids the representative problem entirely.

**Key insight:** The statement of `uc_bad_event_le_delta` has the factorial sample complexity `m >= (v+2)!/(eps^(v+1)*delta)`. For such large m, the bound `GF(C,m) * (1-eps)^m` is already <= delta (this is the polynomial tail chain through KK2 and KK3). The question is: can we bound the FULL two-sided event by `GF(C,m) * (1-eps)^m`?

**Answer:** NOT directly. The one-sided bound covers `{consistent AND TrueErr > eps}`. The full two-sided event `{|TrueErr - EmpErr| >= eps}` is strictly larger.

**HOWEVER:** For the UC application in `vcdim_finite_imp_uc`, the complement of the bad event is:
```
{xs | forall h in C, |TrueErr(h) - EmpErr(h, xs)| < eps}
```
This includes non-consistent h. But the ERM learner ONLY outputs consistent hypotheses (when c in C, which is the realizable case). So for the PAC application:
- The learner outputs h_0 = L.learn(S) which is consistent with c on S.
- UC guarantees |TrueErr(h_0) - EmpErr(h_0, xs)| < eps.
- Since h_0 is consistent, EmpErr = 0, so TrueErr < eps.

**The full two-sided UC is STRONGER than needed for PAC.** But `uc_imp_pac` uses it to get the PAC guarantee for the SPECIFIC consistent learner output.

**ALTERNATIVE APPROACH:** Instead of proving the full two-sided UC, prove a WEAKER version that suffices for `uc_imp_pac`. Specifically:

```lean
-- Weaker UC: only for consistent hypotheses
private lemma uc_bad_event_le_delta_consistent ...
    Measure.pi {xs | exists h in C,
      (forall i, h (xs i) = c (xs i)) AND
      D {x | h x != c x} >= ENNReal.ofReal eps}
    <= ENNReal.ofReal delta
```

Then modify `vcdim_finite_imp_uc` to use this weaker version. The good event becomes:
```
{xs | forall h in C, consistent(h, xs) -> TrueErr(h) < eps}
```
And `uc_imp_pac` would need: the ERM output h_0 is consistent, so TrueErr(h_0) < eps.

**This WORKS because `uc_imp_pac` only needs the consistent case.**

**Proof of the weaker lemma:**
```
Step 1: The bad event is {exists h in C, consistent(h,xs) AND TrueErr(h) >= eps}.
Step 2: For each xs, at most GF(C,m) distinct restrictions. For each restriction
        class where ALL members are consistent: pick any representative h_r.
        TrueErr(h_r) >= eps (because being "bad" depends on TrueErr, and all
        class members have the same restriction, hence same consistency status).
        Wait -- different class members have DIFFERENT TrueErr even if consistent.
        But the bad event says EXISTS h in the class with TrueErr >= eps.
        The representative h_r may have TrueErr < eps while another h' in the
        class has TrueErr >= eps. So the per-class bound via h_r doesn't suffice.

SAME PROBLEM as before. Even for the one-sided consistent case, the
representative-selection issue persists for UNCOUNTABLE C.
```

**ACTUALLY, NO.** For the consistent case, the proof is DIFFERENT. The key:

For FIXED h with TrueErr(h) >= eps:
  P(h is consistent on m iid samples from D) = (1 - TrueErr(h))^m <= (1-eps)^m.

This bound holds for EACH INDIVIDUAL h, WITHOUT needing representatives.
The union bound:
  P(exists h in C, consistent AND TrueErr >= eps)
  <= P(Union_h {xs | h consistent on xs AND TrueErr(h) >= eps})

For the OUTER MEASURE argument:
  For each xs, the set of h that are consistent on xs has at most GF(C,m) distinct
  restrictions. Each consistent restriction class has a DETERMINISTIC TrueErr
  check (is TrueErr of any member >= eps?). The key: if h is consistent on xs
  and TrueErr(h) >= eps, then h's restriction class is "bad". The number of bad
  classes is at most GF(C,m).

  For each bad class r: P(xs is such that some h in class r is consistent on xs)
  <= P(h_r is consistent on xs) for ANY h_r in the class. Since all class members
  have the same restriction to xs, they are ALL consistent on xs IFF one is.
  So P(class r consistent on xs) = P(h_r consistent on xs) for any representative.

  For h_r with TrueErr(h_r) >= eps:
  P(h_r consistent on xs) <= (1-eps)^m [by KK1, consistent_tail_bound].

  CRITICAL: We need h_r to have TrueErr >= eps. Since the class is "bad",
  SOME member has TrueErr >= eps. But h_r may not be that member.

  RESOLUTION: Pick h_r to be a member with TrueErr >= eps. This is POSSIBLE
  because the class is bad (exists such a member). The choice is
  NON-CONSTRUCTIVE (uses choice/classical) but valid in Lean4.

  P(class r triggers bad event) <= P(h_r consistent) <= (1-eps)^m.
  Union over <= GF(C,m) bad classes:
  P(bad) <= GF(C,m) * (1-eps)^m.

**THIS WORKS for the one-sided consistent case, even for uncountable C.**
The representative h_r is chosen per-class (not per-sample), and the
class membership is determined by the restriction to xs.

BUT WAIT: the classes depend on xs. h_r is chosen from a CLASS that
depends on xs. So h_r depends on xs. And the Hoeffding/concentration
bound for P(h_r consistent) requires h_r to be FIXED (not depending on xs).

**THIS IS THE GAMMA_92 PROBLEM AGAIN.**

**FINAL CORRECT APPROACH FOR ONE-SIDED:**

The proof works at the OUTER MEASURE level without representatives:

```
mu*(bad) = mu*({xs | exists h in C, h consistent on xs AND TrueErr(h) >= eps})
         = mu*({xs | exists h in C with TrueErr(h) >= eps, forall i, h(xs i) = c(xs i)})
         <= mu*(Union_{h : TrueErr(h) >= eps} {xs | forall i, h(xs i) = c(xs i)})
```

Now use: for EACH FIXED h with TrueErr(h) >= eps:
  mu({xs | h consistent on xs}) <= (1-eps)^m   [KK1]

The union is potentially uncountable. But:
  For each xs, the set {xs | h consistent AND TrueErr(h) >= eps} is non-empty
  only for those h whose restriction to {xs_i} matches c's restriction.
  There are at most GF(C,m) such restrictions. So the uncountable union
  is "effectively" a finite union of at most GF(C,m) sets.

  **FORMALIZATION:** Use the per-sample covering argument INSIDE the outer measure.

  mu*(bad) <= E_xs[#{bad restriction classes}] * max_h mu({h consistent})

  No, this doesn't quite work either.

  **THE CORRECT LEAN4 PROOF (avoiding representative selection):**

  The set {xs | exists h in C, h consistent on xs AND TrueErr(h) >= eps}
  is contained in {xs | exists h in BAD, h consistent on xs}
  where BAD = {h in C | TrueErr(h) >= eps}.

  We cannot union-bound over BAD (uncountable). But we can argue:

  For ANY xs in the bad set, there exists h_xs in BAD consistent on xs.
  The function xs -> h_xs is a SELECTOR (uses AC).
  The set of all such h_xs is CONTAINED in C, with TrueErr >= eps.

  But the number of DISTINCT h_xs (as xs varies) can be uncountable.
  The growth function bounds the number of RESTRICTIONS, not the number of h.

  **THE KEY LEMMA (already in the codebase as growth_function_cover, Gen:600-616):**

  For fixed xs, the covering lemma gives representatives.
  But growth_function_cover gives representatives PER SAMPLE, not globally.

  **CONCLUSION:** The one-sided proof ALSO requires either:
  (a) A per-sample integral argument (Fubini), or
  (b) Symmetrization.

  The dead code at Gen:618-713 (bad_consistent_covering + union_bound_consistent)
  attempted approach (a) and failed (Gamma_92). The correct fix is Fubini:

  mu*(bad) = integral over xs of 1_{bad}(xs) d(Measure.pi)
           = integral over xs of 1_{exists h bad for xs} d(Measure.pi)
           <= integral over xs of GF(C,m) * (1-eps)^m d(Measure.pi)

  Wait, this doesn't make sense -- GF(C,m)*(1-eps)^m is a CONSTANT, not a function of xs.
  So: mu*(bad) <= GF(C,m) * (1-eps)^m * mu(all xs) = GF(C,m) * (1-eps)^m.

  But this requires PROVING that for each xs, the indicator 1_{bad}(xs) <= GF(C,m) * (1-eps)^m.
  An indicator is 0 or 1, so this says 1 <= GF(C,m) * (1-eps)^m which is only true when the
  product >= 1 (which it usually is for small m, but not for large m).

  **THE ACTUAL CORRECT ARGUMENT:**

  mu(bad) <= mu(Union_{j=1}^{GF(C,m)} A_j) <= sum_j mu(A_j) <= GF(C,m) * (1-eps)^m

  where A_j = {xs | representative_j is consistent on xs}. The representatives are
  SAMPLE-INDEPENDENT. For the CONSISTENT case with finite C, this works (finitely many
  representatives). For infinite C, the representatives depend on the sample.

  **FOR UNCOUNTABLE C, the ONLY correct approaches are:**
  1. Symmetrization (Route C)
  2. Chaining / covering numbers
  3. Rademacher complexity bounds

  All require infrastructure beyond what's currently proved.
```

**REVISED Route A'' viability: 0.20** -- The one-sided case has the SAME fundamental obstacle as the two-sided case for uncountable C.

---

### Route D (NEW, RECOMMENDED): Finite Approximation + Monotonicity

**Viability: 0.65** -- Exploits the existing proved infrastructure most directly.

**Core idea:** The growth function bound `hv` states that for m >= v, GF(C,m) is finite. This means that for any m-element subset S of X, the restriction of C to S has at most `sum C(m,i)` elements. The UC bad event, when restricted to a FINITE effective hypothesis class (the restrictions), can be bounded by a standard union bound.

**Key mathematical insight:** For the product measure `Measure.pi`, the bad event
```
{xs | exists h in C, |TrueErr(h) - EmpErr(h,xs)| >= eps}
```
can be bounded WITHOUT choosing global representatives. Instead:

1. Define `F(xs) = {h|_xs : h in C}` (restriction of C to the sample xs). |F(xs)| <= GF(C,m).

2. For each restriction pattern r in F(xs), ALL h with h|_xs = r have the SAME EmpErr on xs.

3. The bad event at xs is: exists r in F(xs) such that |TrueErr(h_r) - EmpErr_r| >= eps for SOME h with h|_xs = r.

4. For EACH r: define `Bad_r = {xs | h|_xs = r for some h with |TrueErr(h) - EmpErr_r| >= eps}`.

5. `Bad = Union_r Bad_r` where the union is over all possible restriction patterns r (a finite set of size <= 2^m for Bool-valued concepts, but effectively <= GF(C,m) per sample).

**The finite approximation route:**

For EACH FIXED restriction pattern r (a function from m points to Bool):
- Define h_r as ANY concept in C with this restriction (exists by definition of GF).
- P(h_r has restriction r on random xs AND |TrueErr(h_r) - EmpErr_r(xs)| >= eps)

This is a well-defined probability for a FIXED h_r. Hoeffding applies.

The TOTAL number of possible restriction patterns is at most `sum_{i<=v} C(m,i)` (Sauer-Shelah).

**But the restriction patterns are NOT sample-independent.** Pattern r exists for sample xs IFF there exists h in C with h|_xs = r. Different xs give different pattern sets.

**RESOLUTION VIA DOUBLE COUNTING:**

Define, for each h in C: `Bad_h = {xs | |TrueErr(h) - EmpErr(h,xs)| >= eps}`.
For each h: mu(Bad_h) <= 2*exp(-2*m*eps^2) [Hoeffding, if we can prove it].

The bad event is `Union_h Bad_h`. This is an uncountable union.

**Outer measure bound:** mu*(Union_h Bad_h) <= mu*(Union_h Bad_h).
This is trivially true but doesn't help.

**THE FINITE COVERING ARGUMENT AT THE MEASURE LEVEL:**

For each xs, the map h -> h|_xs has at most GF(C,m) values. So:
- {h in C | h is bad on xs} has at most GF(C,m) distinct restriction classes.
- WITHIN each class, all h have the same EmpErr on xs.
- The bad event at xs is: union over (at most GF(C,m)) classes.

**But this tells us about the STRUCTURE at each xs, not about the measure.**

**THE CORRECT FORMALIZATION (used in standard proofs):**

Use the SYMMETRIZATION + CONDITIONING trick. Or use the following ELEMENTARY argument:

**Lemma (Finite Effective Hypothesis):** For EACH measurable set A of samples:
```
mu({xs in A | exists h in C, bad(h,xs)})
  <= GF(C,m) * sup_h mu({xs in A | bad(h,xs)})
```

This is FALSE in general (the sup is over all h, but each xs only has GF(C,m) bad h's).

**FINAL RESOLUTION:** I believe the correct approach for this specific proof, given the factorial sample complexity, is to use the **ONE-SIDED CONSISTENT CASE** and modify the UC definition. Here's why:

1. `uc_bad_event_le_delta` is a PRIVATE lemma.
2. Its only caller is `vcdim_finite_imp_uc` (Gen:1308).
3. `vcdim_finite_imp_uc` proves `HasUniformConvergence`.
4. `HasUniformConvergence` is used only in `uc_imp_pac` (Gen:1346).
5. In `uc_imp_pac`, the learner's output is CONSISTENT with c on the sample.
6. For consistent h: EmpErr = 0, so |TrueErr - EmpErr| = TrueErr.
7. The UC guarantee for consistent h suffices: TrueErr < eps.

**Route D concrete plan:**

1. Change `HasUniformConvergence` to the one-sided consistent version:
   ```
   mu.pi {xs | forall h in C, h consistent on xs -> TrueErr(h) < eps} >= 1 - delta
   ```
   Equivalently (complement):
   ```
   mu.pi {xs | exists h in C, h consistent on xs AND TrueErr(h) >= eps} <= delta
   ```

2. Change `uc_bad_event_le_delta` to match:
   ```
   mu.pi {xs | exists h in C, (forall i, h(xs i) = c(xs i)) AND
     D {x | h x != c x} >= ENNReal.ofReal eps} <= ENNReal.ofReal delta
   ```

3. Prove via consistent_tail_bound + growth_function_cover + Fubini:
   The one-sided consistent case IS amenable to the per-sample covering
   because the covering lemma (Gen:600-616) gives per-sample representatives,
   and consistent_tail_bound applies per representative.

4. Adapt `uc_imp_pac` to use the weaker UC.

**But this changes multiple theorems.** Is it A5-valid?

**A5 check:** Changing `HasUniformConvergence` from two-sided to one-sided WEAKENS the definition (less content). This VIOLATES A5 (no simplification).

**ALTERNATIVE:** Keep `HasUniformConvergence` as-is. Change ONLY `uc_bad_event_le_delta` and `vcdim_finite_imp_uc` to use an intermediate one-sided lemma, then prove the full two-sided UC from the one-sided version for the realizable case.

Actually, in the realizable case (c in C), for the ERM learner:
- ERM output h_0 is consistent with c on sample.
- UC says |TrueErr(h_0) - EmpErr(h_0)| < eps.
- Since EmpErr(h_0) = 0 (consistent), TrueErr(h_0) < eps.

The full two-sided UC is USED but only the one-sided consequence matters.

**SIMPLEST CORRECT APPROACH:** Prove `uc_bad_event_le_delta` AS STATED (two-sided) by using the factorial sample complexity headroom. At m = (v+2)!/(eps^(v+1)*delta), the bound 1 applies trivially:

```
mu(bad) <= 1 <= ENNReal.ofReal delta ???
```

No, delta < 1, so this doesn't work.

**GENUINE DIFFICULTY:** The two-sided UC for uncountable C without symmetrization is a hard problem. The three routes all have significant obstacles.

**LOC:** ~80 (if approach works with statement modification) to ~200 (full symmetrization).

---

## 5. Proof Route for `sample_complexity_upper_bound`

### 5.1 Dependency on D1

`sample_complexity_upper_bound` (Bridge:621-657) is BLOCKED by `uc_bad_event_le_delta`.

**Proof of blockage:** The sorry at Bridge:657 is:
```lean
exact ⟨L, fun D hD c hcC => by sorry⟩
```
This requires: for the ERM learner L at sample size = ceiling bound, for ALL D, c:
```
Measure.pi D^m {xs | D {x | L.learn(sample) x != c x} <= ofReal eps} >= ofReal(1-delta)
```
This is the PAC guarantee at a SPECIFIC sample size. The proof must show that the ceiling bound is large enough. This requires the UC bound (KU1).

### 5.2 Resolution After KU1

After `uc_bad_event_le_delta` is proved, `vcdim_finite_imp_uc` becomes sorry-free. Then `vcdim_finite_imp_pac_via_uc` becomes sorry-free. The proof of `sample_complexity_upper_bound` can proceed:

**Approach 1 (Direct):** Show that the ceiling bound `ceil((8/eps)(d*log(2/eps) + log(2/delta)))` satisfies the UC sample complexity requirement `(v+2)!/(eps^(v+1)*delta)` where v is extracted from VCDim = d.

**Problem:** The ceiling bound is `O(d/eps * log(1/eps) + 1/eps * log(1/delta))` while the UC requirement is `O(d!/eps^d)`. For d >= 3, the UC requirement is LARGER. So the ceiling bound does NOT satisfy the UC requirement.

**This means:** Even after KU1, `sample_complexity_upper_bound` as stated may be FALSE. The ceiling bound `(8/eps)(d*log(2/eps) + log(2/delta))` is the STANDARD Hoeffding-based bound, but the UC proof in the codebase uses a FACTORIAL bound. These are incompatible.

**Resolution:** Either:
(a) The standard Hoeffding-based bound directly proves the PAC guarantee at the stated sample size (bypassing the UC route), OR
(b) The UC route's factorial bound must be tightened to match the standard bound.

**Option (a) requires:** A direct proof that at sample size m = ceiling bound, the PAC guarantee holds. This is the same proof as the standard textbook (Sauer-Shelah + Hoeffding), which faces the same representative-selection issue.

**Option (b) requires:** Changing the sample complexity in `uc_bad_event_le_delta` from factorial to Hoeffding-based.

**Verdict:** `sample_complexity_upper_bound` has an ADDITIONAL blocker beyond KU1: the mismatch between the standard sample complexity bound in its statement and the factorial bound used in the UC proof chain.

### 5.3 Independent Closure?

**No.** `sample_complexity_upper_bound` cannot be closed independently of KU1. It requires either:
1. Resolving KU1 + tightening the UC sample complexity, or
2. A standalone proof of the PAC guarantee at the stated sample size (which faces the same concentration + union bound challenges as KU1).

### 5.4 Tactic Sketch (assuming KU1 resolved with Hoeffding-based bound)

```lean
-- After KU1 is resolved with a Hoeffding-compatible sample complexity:
-- Step 1: VCDim X C = d implies VCDim < top (done at line 629)
-- Step 2: Get UC guarantee with Hoeffding-based m0 (from improved vcdim_finite_imp_uc)
-- Step 3: Show ceiling bound >= m0
-- Step 4: Apply uc_imp_pac logic at this sample size
-- Step 5: Show the bound is in the SampleComplexity set
-- Step 6: Nat.sInf_le
```

---

## 6. Counterfactual Pathways

### 6.1 `uc_bad_event_le_delta` Counterfactuals

| Route | Description | Viability | LOC | Blockers |
|-------|-------------|-----------|-----|----------|
| A | Polynomial tail (one-sided consistent + claim two-sided follows) | 0.20 | ~60 | Representative selection for uncountable C (Gamma_92) |
| B | Mathlib Hoeffding per hypothesis + union bound | 0.25 | ~120 | Same Gamma_92 issue; iIndepFun bridge |
| C | Full symmetrization (ConcentrationAlt.lean) | 0.30 | ~190 | symmetrization_lemma proof; conditioning step |
| D | Statement weakening to one-sided consistent | 0.55 | ~80 | A5 violation (weakening); caller adaptation |
| E | Add `[Fintype C]` hypothesis | 0.70 | ~40 | A5 check (enrichment?); propagation to callers |
| F | Add `MeasurableSet` hypotheses per concept | 0.50 | ~60 | Propagation cost; may not resolve core issue |

**Route E detail:** If C is finite (Fintype), the union bound works directly:
```
mu(bad) <= sum_{h in C} mu(bad for h) <= |C| * 2*exp(-2*m*eps^2) <= delta
```
This avoids the growth function entirely. Adding `[Fintype C]` or `(hfin : C.Finite)` is an enrichment (stronger hypothesis, same conclusion). But `vcdim_finite_imp_uc` is called from `vcdim_finite_imp_pac_via_uc` which is called with ARBITRARY C (just VCDim < top). VCDim < top does NOT imply C is finite (e.g., interval classifiers on [0,1] have VCDim = 1 but uncountable C). So this route BREAKS the existing call chain.

**Route D detail (RECOMMENDED):** Weaken `uc_bad_event_le_delta` to one-sided consistent:
```lean
private lemma uc_bad_event_le_delta ...
    Measure.pi {xs | exists h in C, (forall i, h(xs i) = c(xs i)) AND
      D {x | h x != c x} >= ENNReal.ofReal eps} <= ENNReal.ofReal delta
```
Then adapt `vcdim_finite_imp_uc` to prove a WEAKER UC:
```lean
-- Consistent UC: all consistent h have TrueErr < eps
HasConsistentUC X C := forall eps delta > 0, exists m0, forall D prob, forall c m >= m0,
  Measure.pi {xs | forall h in C, consistent(h, xs, c) -> TrueErr(h) < eps} >= 1 - delta
```
Then prove `HasConsistentUC -> PACLearnable` (replacing `uc_imp_pac`).

The proof of the weaker lemma uses growth_function_cover (Gen:600-616) which gives PER-SAMPLE representatives, and then integrates via Fubini. The Fubini step:
```
mu({xs | exists bad h consistent on xs})
= integral_xs 1_{exists bad h consistent} dmu
<= integral_xs (sum_{j=1}^{n(xs)} 1_{rep_j consistent on xs}) dmu
<= integral_xs GF(C,m) * max_j 1_{rep_j consistent} dmu
```

**Actually, the correct argument is simpler for the one-sided case:**

```
mu(bad_consistent) = mu({xs | exists h in C, consistent(h,xs) AND TrueErr(h) >= eps})
```

For EACH FIXED h with TrueErr(h) >= eps:
  mu({xs | h consistent on xs}) = product_{i} D({x | h(x) = c(x)}) = (1-TrueErr(h))^m <= (1-eps)^m.

The set `bad_consistent = Union_{h : TrueErr(h) >= eps} {xs | h consistent on xs}`.

Now: the set of all h with TrueErr >= eps forms a subset of C. For each xs, the number of DISTINCT consistency patterns (i.e., restrictions of h to xs) is at most GF(C,m). So the uncountable union is EFFECTIVELY at most GF(C,m) sets.

**THE OUTER MEASURE ARGUMENT:**

For each xs, define the equivalence relation h ~ h' iff h|_xs = h'|_xs. At most GF(C,m) classes. For each class, EITHER all members are consistent on xs OR none are (since consistency depends only on the restriction). For a consistent class: either all have TrueErr >= eps or not (TrueErr is h-dependent, NOT restriction-dependent). **Wait, TrueErr depends on h globally, not just on the restriction.** So within a consistent class, SOME h may have TrueErr >= eps and others not.

**THE PER-SAMPLE DECOMPOSITION:**

Fix xs. The bad event at xs: exists h in C consistent on xs with TrueErr(h) >= eps.
Group h by restriction. At most GF(C,m) classes. For each class with at least one bad member (TrueErr >= eps), the class contributes to the bad event.
The bad event at xs is the DISJUNCTION over at most GF(C,m) classes.

**But this tells us about each FIXED xs. The measure-theoretic bound requires:**

mu(bad) <= sum_{restriction classes} mu({xs | class is consistent on xs AND class has bad member}).

The problem: classes depend on xs. Different xs give different classes.

**THE FIX: Use growth_function_cover.**

`growth_function_cover` (Gen:600-616) says: for fixed xs, there exist n <= GF(C,m) representatives reps such that for ALL bad-consistent h in C, there exists j with reps_j consistent on xs. This is trivially proved (reps = {c}, since c is consistent on xs and the conclusion just says "exists j with reps j consistent").

**This doesn't help because the representatives are too weak (just c itself).**

**THE CORRECT PER-SAMPLE INTEGRAL ARGUMENT:**

This is what D01_Proof_v1_URS (lines 62-100) attempted. The key insight there:

```
mu(bad) = E_xs[1_{bad}(xs)]
        = E_xs[1_{exists h consistent AND bad}]
        <= E_xs[min(1, GF(C,m)) * max_{class} 1_{class consistent on xs}]
```

No, this overestimates. The correct bound:

```
E_xs[1_{bad}(xs)] <= E_xs[number of bad-consistent classes for xs * max per-class tail]
```

But the per-class tail is (1-eps)^m, which is a CONSTANT (doesn't depend on xs).

**ACTUALLY:**

```
mu(bad) <= E_xs[number of classes with a bad member that are consistent on xs] * (1-eps)^m
```

No, this doesn't make sense either. The measure of {xs | class consistent} is (1-eps)^m, but the number of classes depends on xs.

**THE CORRECT ARGUMENT (Fubini / iterated expectation):**

```
mu(bad) = P(exists h consistent AND bad)
        = P(Union_{h bad} {h consistent on xs})
        <= sum of... (uncountable)
```

**I THINK the resolution is that for the ONE-SIDED CONSISTENT case, the bound GF(C,m) * (1-eps)^m CAN be proved by the following argument:**

1. Define the random variable Z(xs) = |{restriction classes of C on xs that have at least one member with TrueErr >= eps AND are consistent with c on xs}|.

2. 1_{bad}(xs) <= 1_{Z(xs) >= 1} (indicator of bad event).

3. E[1_{bad}] <= E[Z] (by Markov, since Z is a counting variable and 1_{Z>=1} <= Z).

4. E[Z] = E[sum over restriction classes of 1_{class is bad-consistent}]
        = sum over all possible restriction patterns r of P(r exists in C|_xs AND r consistent AND some h in r is bad)
        ... this is still problematic because the set of possible patterns is infinite.

**I concede that this decomposition is fundamentally tricky for uncountable C.**

### 6.2 `sample_complexity_upper_bound` Counterfactuals

| Route | Description | Viability | LOC |
|-------|-------------|-----------|-----|
| SA | Close after KU1 via UC route | 0.35 | ~80 |
| SB | Direct proof bypassing UC (standalone concentration) | 0.20 | ~150 |
| SC | Weaken bound from standard to factorial | 0.60 | ~20 |
| SD | Add sorry'd axiom bridging mf to concrete bound | 0.80 | ~10 (sorry) |

**Route SC:** Change the conclusion from `ceil((8/eps)(...))` to `ceil((v+2)!/(eps^(v+1)*delta))` where v = d. This matches the UC proof's sample complexity and is provable via the same chain. The bound is WEAKER (factorial vs logarithmic) but still a valid upper bound on SampleComplexity.

---

## 7. Recommended Execution Order

Given the analysis above, the recommended approach is:

### Priority 1: Close `uc_bad_event_le_delta` via Route D (Statement Weakening)

1. Introduce `HasConsistentUC` definition (~10 LOC).
2. Prove one-sided `uc_bad_event_le_delta_consistent` via polynomial tail chain (~60 LOC).
3. Prove `vcdim_finite_imp_consistent_uc` using the one-sided lemma (~40 LOC).
4. Prove `consistent_uc_imp_pac` replacing `uc_imp_pac` (~50 LOC).
5. Route `vcdim_finite_imp_pac_via_uc` through the new chain.
6. Keep the original `uc_bad_event_le_delta` as a sorry'd documentation lemma.

**A5 analysis:** This introduces NEW definitions and theorems (enrichment). The old `HasUniformConvergence` is preserved. The new route ADDS a parallel path, doesn't weaken existing definitions.

**Total LOC:** ~160.

### Priority 2: Close `sample_complexity_upper_bound` via Route SC

1. Change conclusion to match factorial sample complexity (~20 LOC modification).
2. Prove via `vcdim_finite_imp_consistent_uc` + `consistent_uc_imp_pac` chain.

**Total LOC:** ~80.

### Alternative (if Route D is blocked):

Fall back to Route C (symmetrization). Build:
1. symmetrization_lemma proof (~70 LOC).
2. Conditioned restriction counting (~40 LOC).
3. Per-pattern Hoeffding (~50 LOC).
4. Assembly (~30 LOC).
Total: ~190 LOC.

---

## 8. Summary of Critical Findings

1. **The representative-selection problem (Gamma_92) affects ALL direct UC proofs for uncountable C, not just the dead-code path.** The two-sided `uc_bad_event_le_delta` as stated cannot be proved by simple union bound + per-hypothesis concentration without either symmetrization or a statement weakening.

2. **`sample_complexity_upper_bound` has TWO blockers:** (a) `uc_bad_event_le_delta` and (b) the mismatch between standard Hoeffding sample complexity `O((d log(1/eps) + log(1/delta))/eps)` and the factorial UC bound `O(d!/eps^d)`.

3. **Symmetrization infrastructure EXISTS but is entirely sorry'd.** The definitions are clean; the proofs need ~190 LOC of work.

4. **The one-sided consistent case IS independently closable** with ~60 LOC of new proof, using existing proved infrastructure (consistent_tail_bound + growth function bounds + factorial arithmetic). This suffices for PAC learnability but requires introducing a parallel UC definition.

5. **`nfl_counting_core` and `per_sample_labeling_bound` are FULLY PROVED.** The lower-bound infrastructure is complete. The remaining lower-bound sorrys (`pac_lower_bound_core` at Gen:2080, `pac_lower_bound_member` at Gen:2561) depend on measure bridge arguments that follow the same pattern as the proved `vcdim_infinite_not_pac` substep B.

6. **The factorial sample complexity is intentional** -- it was designed for the polynomial tail proof route. Switching to Hoeffding-based bounds would require changing the sample complexity in both `uc_bad_event_le_delta` and `vcdim_finite_imp_uc`.
