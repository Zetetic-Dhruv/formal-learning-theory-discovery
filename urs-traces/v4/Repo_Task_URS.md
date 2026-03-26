# Repo Task URS — FLT_Proofs Sorry Pipeline (v4, 2026-03-19)

## Task Identity
**Mission:** Close all actionable sorrys. Produce discovery-oriented FLT kernel.
**Current:** 0 errors, 15 sorry-using declarations (verified by lake build).
**Target:** 0 errors, 4 sorry-using declarations (Extended.lean only).

## Verified Sorry Inventory (15 declarations — from lake build)

| # | File:Line | Theorem | Direction | Difficulty |
|---|-----------|---------|-----------|------------|
| 1 | Generalization:616 | union_bound_consistent | D1 | Hard (symmetrization) |
| 2 | Generalization:1269 | vcdim_finite_imp_uc | D3 | Medium (ES+Chebyshev) |
| 3 | Generalization:1926 | pac_lower_bound_core | D2 | Medium (double-counting) |
| 4 | Generalization:2137 | vcdim_finite_imp_compression | D5-UU | Deep (Moran-Yehudayoff) |
| 5 | Generalization:2456 | pac_lower_bound_member | D2 | Medium (routes through #3) |
| 6 | Generalization:2896 | vcdim_infinite_not_pac | D2 | Medium (factored A+B) |
| 7 | Rademacher:390 | vcdim_bounds_rademacher_quantitative | D6 | Hard (Massart) |
| 8 | Rademacher:455 | rademacher_vanishing_imp_pac | D6 | Very Hard (circularity) |
| 9 | Bridge:621 | sample_complexity_upper_bound | D5 | Medium (upstream blocked?) |
| 10 | Bridge:670 | compression_bounds_vcdim | D5 | Medium (check statement) |
| 11 | Separation:152 | boost_two_thirds_to_pac | D4 | Medium (~100 LOC) |
| 12 | Separation:721 | universal_strictly_stronger_pac | PERM | FALSE (Gamma_68) |
| 13 | Separation:750 | natarajan_not_characterizes_pac | PERM | UU (topology) |
| 14 | Extended:57 | computational_hardness_pac | PERM | UU (crypto) |
| 15 | Extended:109 | unlabeled_not_implies_labeled | PERM | UU (dist-dependent) |

## Actionable: 11 sorrys across 5 directions

### D1: Concentration (2 sorrys — #1, #2)
**#1 union_bound_consistent** — The covering sorry. Sample-independent reps impossible
for infinite C (Gamma_65). Needs SYMMETRIZATION: double-sample ghost argument giving
2*GF(C,2m)*exp(-me^2/8). This is ~200 LOC of new infrastructure.

**#2 vcdim_finite_imp_uc** — Two-sided uniform convergence. Not on critical path
(factorial bypass proves PAC). Route: Efron-Stein + Chebyshev (~100 LOC) or full
McDiarmid (~600 LOC). Value: tighter sample complexity.

### D2: NFL / Lower Bound (3 sorrys — #3, #5, #6)
All share the double-counting + pigeonhole + measure bridge pattern.
**Shared infrastructure needed:** Measure.pi of uniformMeasure = counting/d^m.

**#3 pac_lower_bound_core** — For m < d/(64e), construct D = uniform on shattered T,
show Pr[error <= e] < 6/7. Uses nfl_core (proved) on subtype T.

**#5 pac_lower_bound_member** — Same core, different wrapper. Routes through #3.

**#6 vcdim_infinite_not_pac** — Explicitly factored into:
  - Substep A (combinatorial): exists f_0 with counting bound on good xs. SORRY.
  - Substep B (measure bridge): counting -> Measure.pi. SORRY.
  Both independently provable. ~120 LOC total.

### D4: Boosting (1 sorry — #11)
**#11 boost_two_thirds_to_pac** — Majority vote construction.
For delta >= 1/3: trivial (2/3 >= 1-delta).
For delta < 1/3: k = ceil(ln(1/delta) / (2*(2/3-1/2)^2)) copies, majority vote,
Chernoff/Chebyshev bound. Agent D4v2 confirmed ~100 LOC.
Closing this also closes universal_imp_pac (line 427 calls boost directly).

### D5: Compression + Bridge (2 sorrys — #9, #10)
**#10 compression_bounds_vcdim** — VCDim <= 2^k - 1 from compression of size k.
**CKU_3:** Check if 2^(2^k) > (k+1)*(2*2^k)^k for k>=1. If FALSE, weaken statement.
Proof: pigeonhole. 2^n distinct labelings of n points, each compresses to C(n,k)*2^k
subsets. If 2^n > C(n,k)*2^k then two labelings collide -> contradiction with
compress_injective_on_labelings (proved sorry-free).

**#9 sample_complexity_upper_bound** — Routes through concentration chain.
May be independently closable: show bound is in the set defining SampleComplexity
via Nat.sInf_le, using the same learner L from vcdim_finite_imp_pac_direct.

### D6: Rademacher (2 sorrys — #7, #8)
**#7 vcdim_bounds_rademacher_quantitative** — EmpRad(C,xs) <= sqrt(2d*log(2m/d)/m).
Massart finite lemma: E[max Z_j] <= sigma*sqrt(2*log N) for sub-Gaussian Z_j.
Chain: restrict to GF(C,m) patterns -> each corr_j is 1/sqrt(m)-sub-Gaussian ->
Massart -> Sauer-Shelah for log N. ~150-210 LOC.

**#8 rademacher_vanishing_imp_pac** — VCDim < inf from Rad vanishing.
Contrapositive: VCDim=inf -> exists D where Rad doesn't vanish.
Genuine difficulty: pointwise-in-D hypothesis (m_0 depends on D) creates circularity.
Resolution: construct single D with infinite support covering shattered sets at all
scales. Needs [Infinite X] + countable choice + birthday probability. ~130-190 LOC.

### Permanent (4 sorrys — #12, #13, #14, #15)
Do NOT attempt. Correctly classified.
- #12: FALSE statement (Gamma_68)
- #13: UU (hyperbolic pseudo-manifolds)
- #14: UU (crypto)
- #15: UU (distribution-dependent compression)

## Proved Infrastructure (sorry-free — available for composition)

### Concentration
consistent_tail_bound, prob_compl_ge_of_le, uniformMeasure_isProbability,
empiricalError_bounded_diff, union_bound_consistent calc chain (sorry only at covering)

### Sauer-Shelah
funcToSubset_injective, restrict_shatters_lift, vcDim_restrict_le,
card_restrict_le_sauer_shelah_bound, growth_function_le_sauer_shelah,
vcdim_finite_imp_growth_bounded, growth_bounded_imp_vcdim_finite

### NFL
nfl_core (full NFL for finite), disagreement_sum_eq, exists_many_disagreements,
shatters_realize, shatters_hard_labeling, per_sample adversarial

### PAC Assembly
uc_imp_pac, erm_consistent_realizable, trueError_eq_genError,
empiricalMeasureError_eq_empiricalError, vcdim_finite_imp_pac_direct (factorial)

### Separation Witnesses
pac_not_implies_online (~180 LOC), ex_not_implies_pac (~80 LOC),
online_imp_pac (adversary), universal_imp_pac (structural)

### Online + Gold
littlestone_characterization (694 LOC), gold_theorem, mind_change_characterization

## Gamma Ledger (cumulative)

| ID | Discovery | Session |
|----|-----------|---------|
| Gamma_65 | growth_function_cover impossible for infinite C | S3 |
| Gamma_66 | Sauer-Shelah C(m,d) was FALSE | S3 |
| Gamma_67 | pac_lower_bound 1/(2e) needs EHKV; weakened to 1/(64e) | S3 |
| Gamma_68 | universal_strictly_stronger conjunct 2 FALSE (Bousquet 2021) | S3 |
| Gamma_69 | ES+Chebyshev gives UC in ~100 LOC vs McDiarmid ~600 LOC | S3 |
| Gamma_70 | UniversalLearnable needed Measure.pi fix | S3 |
| Gamma_71 | online_imp_pac needs adversary_from_shatters | S3 |
| Gamma_72-75 | D2 chain assembly, Rademacher d=0, birthday bypass, compression pigeonhole | S3 |
| (S4 discoveries to be logged here) | | |
