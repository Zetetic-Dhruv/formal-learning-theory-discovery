# Ignorance Profile — 8 Sorry Decomposition (v7.0, 2026-03-22 — Session 6 Recovery)

**Build-verified: 0 errors, 8 sorry-using declarations.**

## False Statement Alert

**Gamma_107**: `uc_bad_event_le_delta` (Generalization.lean:1270) has a **mathematically false** statement.
- Sample complexity `(v+2)!/(ε^(v+1)·δ)` is insufficient for two-sided UC bound
- Counterexample: VCDim=1, ε=10⁻¹⁰, δ=0.5 → UC bad event probability ≈ 0.83 > 0.5 = δ
- Root cause: formula was designed for one-sided consistent-hypothesis bound (exp(-ε·m) decay), not two-sided symmetrization (exp(-ε²·m/8) decay)
- Correct formula: `m ≥ C·(v/ε²)·(v·log(1/ε) + log(1/δ))` per SSBD Theorem 6.11
- **Must fix statement before attempting proof closure**

## Sorry Inventory (8 declarations, build-verified 2026-03-22)

| # | File:Line | Declaration | Task | Direction | Status | Blocker |
|---|-----------|-------------|------|-----------|--------|---------|
| 1 | Gen:1270 | uc_bad_event_le_delta | T2 | D1-D5 | **FALSE STMT** | Gamma_107: fix formula first |
| 2 | Gen:2729 | vcdim_finite_imp_compression | T8 | D2-Comp | Deferred | Moran-Yehudayoff (60+ proof-days) |
| 3 | Rad:390 | vcdim_bounds_rademacher_quantitative | T5 | D6-Massart | Blocked by T1 | Remove |·| first (Gamma_103) |
| 4 | Rad:472 | rademacher_lower_bound_on_shattered | — | D6-Birthday | **RECOVERABLE** | Proof in transcript (Gamma_110) |
| 5 | Sep:326 | boost_two_thirds_to_pac | T6 | D4-Boost | Open | Block independence (~100 LOC) |
| 6 | Ext:32 | bhmz_middle_branch | — | Extended | Open | BHMZ deep construction |
| 7 | Ext:89 | advice_elimination | T7 | D7-Advice | Open | Sample split + Hoeffding (~150 LOC) |
| 8 | Bridge:621 | sample_complexity_upper_bound | — | Bridge | Blocked by T2 | Follows from uc_bad_event_le_delta |

## Closed Since Session 5 Start (preserved in current build)

| Declaration | Task | How | Status |
|------------|------|-----|--------|
| pac_lower_bound_core | T4 | NFL counting → measure bridge | ✅ In Generalization.lean (stash 1f0c04c) |
| pac_lower_bound_member | T4 | Routes through pac_lower_bound_core | ✅ In Generalization.lean (stash 1f0c04c) |

## Closed Then Lost (recoverable from transcript/stash)

| Declaration | Task | How | Recovery Source |
|------------|------|-----|-----------------|
| rademacher_lower_bound_on_shattered (birthday) | — | Collision bound + ENNReal arithmetic | Transcript L776/L2238 (7591-char proof) |
| EmpRad |·| removal (T1 definition fix) | T1 | 3 helpers + symmetry rewrite | Subagent agent-a9f251b32105f8f11.jsonl (13 edits) |
| 4 Massart helpers (~240 LOC) | T5-prep | Product factorization + finite Jensen | Stash 64cdbbc lines 421-665 |
| sauer_shelah_exp_bound | T5-prep | Exponential Sauer-Shelah | Stash 64cdbbc lines 667-721 (may have typeclass error) |

## Proved Infrastructure (sorry-free, cumulative through Session 6)

### Concentration
- consistent_tail_bound, prob_compl_ge_of_le, uniformMeasure_isProbability
- empiricalError_bounded_diff, union_bound_consistent calc chain (sorry at covering only)

### Sauer-Shelah (full chain)
- funcToSubset_injective → restrict_shatters_lift → vcDim_restrict_le
- card_restrict_le_sauer_shelah_bound → growth_function_le_sauer_shelah
- vcdim_finite_imp_growth_bounded (BP_4 bridge), growth_bounded_imp_vcdim_finite
- shatters_mono, exp_beats_poly_at

### NFL + PAC Lower Bound (Session 5 — T4 CLOSED)
- nfl_counting_core (double-counting + pigeonhole)
- per_sample_labeling_bound (flip-unseen pairing)
- pac_lower_bound_core (NFL counting → Measure.pi bridge → probability bound)
- pac_lower_bound_member (routes through pac_lower_bound_core)
- vcdim_infinite_not_pac (NFL + measure bridge)
- sample_complexity_lower_bound (wiring)

### PAC Assembly
- uc_imp_pac, erm_consistent_realizable, trueError_eq_genError
- empiricalMeasureError_eq_empiricalError, vcdim_finite_imp_pac_direct (factorial)

### Rademacher (Session 5 — proved then lost, recoverable)
- rademacherCorrelation_le_one (one-sided bound, T1 helper)
- sum_boolToSign_eq_zero (sign-flip symmetry, T1 helper)
- sum_rademacherCorrelation_eq_zero (Rademacher symmetry, T1 helper)
- exp_mul_sup'_le_sum (soft-max bound)
- cosh_le_exp_sq_half (via Mathlib Real.cosh_le_exp_half_sq)
- rademacher_mgf_bound (~80 LOC, product factorization)
- finite_massart_lemma (~140 LOC, finite Jensen)

### Separation Witnesses
- pac_not_implies_online (~180 LOC), ex_not_implies_pac (~80 LOC)
- online_imp_pac (adversary), universal_imp_pac (via boost)
- chebyshev_majority_bound (~150 LOC, full Chebyshev chain)

### Online (694 LOC) + Gold
- littlestone_characterization, optimal_mistake_bound_eq_ldim, SOA
- gold_theorem, mind_change_characterization

### Bridge + Compression
- compression_bounds_vcdim (pigeonhole + exp_beats_poly)
- compression_imp_vcdim_finite (converse, sorry-free)

## Execution Priority (Session 6 Recovery)

| Priority | Action | Impact | LOC |
|----------|--------|--------|-----|
| 1st | Recover Rademacher.lean (T1 + birthday + Massart helpers) | 8 → 7 sorrys, preserves ~300 LOC infrastructure | ~0 (splice from stash/transcript) |
| 2nd | Fix uc_bad_event_le_delta statement (Gamma_107) | Unblocks T2 | ~5 (formula change) |
| 3rd | Close T2 symmetrization chain | 7 → 5 sorrys (closes #1 + unblocks #8) | ~200 |
| 4th | Close T5 Massart assembly (after T1 recovery) | 5 → 4 sorrys | ~100 |
| 5th | Close T6 boosting | 4 → 3 sorrys | ~100 |
| 6th | Close T7 advice elimination | 3 → 2 sorrys | ~150 |
| 7th | T8 Moran-Yehudayoff | 2 → 1 sorrys | 60+ proof-days |
| 8th | bhmz_middle_branch | 1 → 0 sorrys | Deep construction |

## Git Recovery Assets

| Asset | Hash | Contents | Verified? |
|-------|------|----------|-----------|
| Stash 1 | 1f0c04c | Generalization.lean (T4 closures) + PAC.lean | ✅ Currently in working tree |
| Stash 2 | 64cdbbc | Rademacher.lean (T1 + 5 Massart helpers, birthday NOT closed) | ❌ Has build errors |
| T1 subagent | agent-a9f251b32105f8f11.jsonl | 13 Edit calls, full T1 fix | Verified by forensic agent |
| Birthday proof | Transcript L2238 | 7591-char replacement for birthday sorry | Verified by forensic agent |
| T5 subagent | agent-a4eeaf55874775318.jsonl | Massart expansion edits | Partial — has build errors |
