# Program State — Post Session 7

## Sorry Inventory (Critical Path Only)

### Sorry-Free Files ✅
| File | Lines | Theorems | Status |
|------|-------|----------|--------|
| Rademacher.lean | 1925 | 15 theorems | ✅ 0 sorry |
| VCDimension.lean | ~800 | GrowthFunction, VCDim, Shatters | ✅ 0 sorry |
| PAC.lean | ~600 | fundamental_theorem, vc_characterization | ✅ 0 sorry (modulo downstream) |
| Bridge.lean | ~300 | sample_complexity_upper_bound | ✅ 0 sorry (modulo downstream) |

### Files with Sorrys
| File | Sorrys | Critical? | Content |
|------|--------|-----------|---------|
| Symmetrization.lean | 3 | YES | SL3 (2) + T4 lower tail (1) |
| Generalization.lean | 2 | YES (1) | uc_bad_event_le_delta (1, critical) + compression (1, deep/deferred) |
| Extended.lean | 2 | NO | BHMZ + advice elimination (deferred) |
| Separation.lean | 1 | NO | boost_two_thirds_to_pac (separate chain) |

### The Critical Path (4 sorrys to PAC ↔ VCDim)
```
SL3 Sorry A (swap→signed avg) ──┐
SL3 Sorry B (Tonelli/measurability) ──┤──→ T3 done ──→ T4 done ──→ S6 done ──→ FUNDAMENTAL THEOREM
T4 lower tail (agent running) ─────────┘
```

## Proof Method Inventory (Verified Action Space)

### For sub-Gaussian concentration on product measures:
1. `measurePreserving_arrowProdEquivProdArrow` for (D^m)⊗(D^m) ≅ (D⊗D)^m
2. `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` for Hoeffding's lemma
3. `iIndepFun_pi` for independence of coordinate projections
4. `HasSubgaussianMGF.of_map` + `measurePreserving_eval` for per-coordinate sub-Gaussianity
5. `measure_sum_ge_le_of_iIndepFun` for the concentration bound

### For restriction collapse (sSup bounds):
1. `Infinite.exists_superset_card_eq` to pad Finsets to target cardinality
2. XOR bijection (`Bool.xor` involutive) to relate disagreement patterns to raw patterns
3. `le_csSup` with BddAbove for GrowthFunction sSup
4. `Set.ncard_le_card` → `Nat.card_fun` → `Nat.card_eq_fintype_card` for counting
5. `Finset.fintypeCoeSort` for Fintype instance on Finset subtypes

### For Rademacher/Massart bounds:
1. `rademacher_mgf_bound` with `Finset.sum_prod_piFinset` for product factorization
2. `cosh_le_exp_sq_half` for the cosh → exp bound
3. `finite_massart_lemma` via Jensen (`ConvexOn.map_sum_le`) + softmax + MGF optimization
4. Chernoff/Markov from rademacher_mgf_bound: `#{σ | avg ≥ t} ≤ |SV| · exp(-mt²/2)`

### For measure-theoretic plumbing:
1. `Measure.prod_swap` / `Measure.prod_comm` for symmetric product measures
2. `Measure.pi_map_pi` for coordinate-wise maps on product measures
3. `lintegral_finset_sum'` for Tonelli on finite sums (requires AEMeasurable)
4. `lintegral_indicator_one` for `μ(A) = ∫⁻ 𝟙_A` (requires MeasurableSet)
5. `prob_compl_eq_one_sub` for complement probability
6. `ENNReal.toReal_mono` / `ENNReal.ofReal_le_ofReal` for ℝ ↔ ℝ≥0∞ bridges

### For ENNReal arithmetic:
1. `ENNReal.mul_inv_cancel` for division
2. `ENNReal.natCast_ne_top` for finiteness
3. `ENNReal.ofReal_mul` + `ENNReal.ofReal_natCast` for factoring
4. `div_eq_mul_inv` (UNQUALIFIED, not ENNReal-qualified)

## Open Questions (KU for next session)

1. **SL3 measurability**: User has resolution. Implementation pending.
2. **SL3 swap→signed average**: Mathematical content clear, Lean4 implementation needed (~40 LOC)
3. **T4 lower tail**: Agent running. Uses `hoeffding_one_sided_upper` (complement concept) + mirror of symmetrization_step
4. **Conjunct 2 (compression)**: Moran-Yehudayoff 2016. Deep/deferred. Months of work.
5. **Conjunct 4 (quantitative sample complexity)**: Currently trivially proved (`mf = fun _ _ => 1`). Needs enrichment with actual ERM sample complexity bound.
