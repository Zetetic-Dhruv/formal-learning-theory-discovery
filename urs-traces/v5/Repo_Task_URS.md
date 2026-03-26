# Repo Task URS — FLT_Proofs Sorry Pipeline (v5, 2026-03-20)

## Task Identity
**Mission:** Close all actionable sorrys. Produce discovery-oriented FLT kernel.
**Current:** 0 errors (base), ~20 sorry-using declarations (decomposed from 15).
**Target:** 0 errors, ≤6 sorry-using declarations (4 permanent + Moran-Yehudayoff + EHKV gap).

## Sorry Inventory (v5 — reorganized by Task)

### T1: EmpRad Definition Fix (0 sorrys to close, but UNBLOCKS T5)
| File:Line | Declaration | Issue |
|-----------|-------------|-------|
| Rademacher:206 | EmpiricalRademacherComplexity | Uses \|corr\| (symmetric), should be corr (one-sided). Gamma_103. |

### T2: Symmetrization Chain (3 sorrys)
| File:Line | Declaration | Status |
|-----------|-------------|--------|
| Generalization:~1270 | symmetrization_reduction | sorry — ghost sample + triangle |
| Generalization:~1320 | double_sample_uc_bound | sorry — GF(C,2m) + Hoeffding. RESOLVES GAMMA_92 |
| Generalization:~1380 | arithmetic assembly (in calc) | sorry — factorial threading |

### T3: EHKV Wiring (0 new sorrys, strengthens existing)
| File:Line | Declaration | Issue |
|-----------|-------------|-------|
| PAC:172 | pac_lower_bound | Constant is ceil((d-1)/2), should be ceil((d-1)/(64ε)) |

### T4: NFL Lower Bound (3 sorrys)
| File:Line | Declaration | Status |
|-----------|-------------|--------|
| Generalization:~2008 | pac_lower_bound_core | sorry — double-counting + measure bridge |
| Generalization:~2539 | pac_lower_bound_member | sorry — routes through pac_lower_bound_core |
| Generalization:~2896 | vcdim_infinite_not_pac | sorry — substep A (combinatorial) + B (measure) |

### T5: Massart Assembly (2 sorrys, blocked by T1)
| File:Line | Declaration | Status |
|-----------|-------------|--------|
| Rademacher:~456 | empRad_le_of_restriction_count | sorry — sSup→Finset.sup' bridge |
| Rademacher:~483 | empRad_le_sqrt_vc_log | sorry — Sauer-Shelah constant + assembly |

Helpers PROVED (sorry-free):
- exp_mul_sup'_le_sum, cosh_le_exp_sq_half, rademacher_mgf_bound, finite_massart_lemma

### T6: Boosting (1 sorry, enabled by T2)
| File:Line | Declaration | Status |
|-----------|-------------|--------|
| Separation:152 | boost_two_thirds_to_pac | sorry — majority vote + Chebyshev |

### T7: Advice Elimination (TBD, enabled by T2)
| File:Line | Declaration | Status |
|-----------|-------------|--------|
| Extended:TBD | advice_elimination | not yet decomposed |

### T8: Moran-Yehudayoff (1 sorry, DEFERRED)
| File:Line | Declaration | Status |
|-----------|-------------|--------|
| Generalization:2137 | vcdim_finite_imp_compression | sorry — minimax on VC lattices. 60+ proof-days. |

### Other Open Sorrys
| File:Line | Declaration | Direction | Status |
|-----------|-------------|-----------|--------|
| Generalization:1269 | vcdim_finite_imp_uc | T2-adjacent | ES+Chebyshev, not critical path |
| Rademacher:390 | vcdim_bounds_rademacher_quantitative | T5 | Massart assembly target |
| Rademacher:455 | rademacher_vanishing_imp_pac | D6-deep | Circularity (pointwise-in-D) |
| Bridge:621 | sample_complexity_upper_bound | T2-dependent | Routes through concentration |
| Bridge:670 | compression_bounds_vcdim | T4-adjacent | Pigeonhole, check CKU_3 |

### Permanent (4 sorrys — DO NOT ATTEMPT)
| File:Line | Declaration | Why Permanent |
|-----------|-------------|---------------|
| Separation:721 | universal_strictly_stronger_pac | FALSE statement (Gamma_68) |
| Separation:750 | natarajan_not_characterizes_pac | UU (hyperbolic topology) |
| Extended:57 | computational_hardness_pac | UU (crypto assumptions) |
| Extended:109 | unlabeled_not_implies_labeled | UU (distribution-dependent) |

## Proved Infrastructure (sorry-free — available for composition)

### Concentration
consistent_tail_bound, prob_compl_ge_of_le, uniformMeasure_isProbability,
empiricalError_bounded_diff, uc_bad_event_le_delta calc structure (sorry only at 3 components)

### Sauer-Shelah
funcToSubset_injective, restrict_shatters_lift, vcDim_restrict_le,
card_restrict_le_sauer_shelah_bound, growth_function_le_sauer_shelah,
vcdim_finite_imp_growth_bounded, growth_bounded_imp_vcdim_finite

### NFL
nfl_core (full NFL for finite), disagreement_sum_eq, exists_many_disagreements,
shatters_realize, shatters_hard_labeling, per_sample_labeling_bound (PROVED session 5)

### Massart (NEW v5)
exp_mul_sup'_le_sum, cosh_le_exp_sq_half, rademacher_mgf_bound, finite_massart_lemma

### PAC Assembly
uc_imp_pac, erm_consistent_realizable, trueError_eq_genError,
empiricalMeasureError_eq_empiricalError, vcdim_finite_imp_pac_direct (factorial)

### Separation Witnesses
pac_not_implies_online (~180 LOC), ex_not_implies_pac (~80 LOC),
online_imp_pac (adversary), universal_imp_pac (structural)

### Online + Gold
littlestone_characterization (694 LOC), gold_theorem, mind_change_characterization

## Gamma Ledger (cumulative through Session 6)

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
| Gamma_92 | Representative-selection impossible for uncountable C | S6 |
| Gamma_98 | One-sided consistent case ALSO faces Gamma_92 | S6 |
| Gamma_99 | sample_complexity_upper_bound has Hoeffding/factorial mismatch | S6 |
| Gamma_100 | Route C (symmetrization) is ONLY viable route for UC | S6 |
| Gamma_101 | Cauchy-Schwarz CANNOT achieve sqrt(log N); exponential-moment NECESSARY | S6 |
| Gamma_102 | Factorial sample complexity vs Hoeffding: (16/ε²)^v absorption | S6 |
| Gamma_103 | Symmetric Rademacher (\|corr\|) creates factor-of-2 Massart incompatibility | S6 |
| Gamma_104 | Sauer-Shelah constant em/d vs 2m/d insufficient | S6 |
| Gamma_105 | Mathlib has Fubini for Measure.prod but NOT Measure.pi | S6 |
| Gamma_106 | All ESChebyshev sorrys trace to Gamma_92 | S6 |
