# Proof Methods — M_noological (v6.0, 2026-03-22 — Session 5-6 Integration)

The MetaKernel maintains world models (traces) ON these methods. Each method is a substrate on which proof-traces are generated, compared, and validated. Methods are not tactics — they are CLASSES of reasoning that may be realized by multiple tactic strategies.

## Method Inventory

### Primary Methods (M_1-M_8)
- **M_1:** Diagonalization (Gold's theorem, separation theorems)
- **M_2:** Probabilistic (PAC bounds, concentration inequalities)
- **M_3:** Combinatorial (Sauer-Shelah, growth function bounds)
- **M_4:** Game-Theoretic (online learning, mistake bounds)
- **M_5:** Convergence (identification in the limit, Bayesian consistency)
- **M_6:** Construction (witness building for existentials)
- **M_7:** Reduction (reducing one learning problem to another)
- **M_8:** Category-Theoretic (structure-preserving maps between paradigms)

### Extended Methods (M_9-M_12, discovered session 3)
- **M_9:** Bounded Average — average of bounded values is bounded (empiricalRademacherComplexity_le_one)
- **M_10:** Paradigm-Joint Asymmetry — two directions of iff cross different paradigm joints (fundamental_rademacher)
- **M_11:** Per-Sample Adversarial — for EACH fixed sample, construct adversarial concept (nfl_core, pac_lower_bound_core per_sample lemma)
- **M_12:** Subtype Restriction — restrict from general X to Fintype T via shattered set (vcdim_finite_imp_growth_bounded BP_4 bridge)

### Session 5 Methods (M_13-M_16, discovered session 5)
- **M_13:** Rademacher Symmetry — Σ_σ corr(h,σ,xs) = 0 for any fixed h,xs by sign-flip involution. Used in empRad_nonneg: EmpRad = E_σ[sup_h corr] ≥ E_σ[corr(h₀)] = 0.
- **M_14:** Product Factorization — MGF of sum of independent bounded RVs = product of individual MGFs. Used in rademacher_mgf_bound (~80 LOC) via Fintype.prod_sum + cosh bound.
- **M_15:** Finite Jensen via Soft-Max — exp(E[max]) ≤ E[exp(max)] ≤ Σ E[exp] via convexOn_exp.map_sum_le. Used in finite_massart_lemma (~140 LOC).
- **M_16:** Birthday Collision Bound — P[injective m draws from n points] ≥ 1 - m²/(2n) via union bound over C(m,2) collision pairs. Used in rademacher_lower_bound_on_shattered.

### Session 6 Methods (M_17-M_19, discovered session 6)
- **M_17:** Forensic State Recovery — reconstruct codebase from multiple stash commits + agent subagent transcripts when working tree is fractured. Pattern: identify all dangling git objects, map each to a buildable/non-buildable state, splice verified sections.
- **M_18:** Stash Forensics — `git show <stash-commit>:<file>` to inspect files inside popped stashes. Stash merge commits survive garbage collection and can be addressed directly even after `git stash drop`.
- **M_19:** Agent Transcript Replay — extract exact Edit/Write tool calls from subagent JSONL files to recover lost proof code. Pattern: identify subagent file, read all tool calls, extract old_string/new_string pairs, replay on clean base.

### Metaprogram Types (14)
M-Bridge, M-BridgeLift, M-Contrapositive, M-Pipeline, M-Conjunction,
M-Construction, M-DefinitionRepair, M-CaseElimination,
M-Potential, M-InfSup, M-VersionSpaceCollapse, M-InfrastructureGap,
M-Splice (compose verified subsections from heterogeneous sources — Session 6),
M-ForensicRecovery (reconstruct buildable state from fractured git history — Session 6)

## Cross-Direction Discovery (Session 4)

### Shared Axis (Gamma_78)
All 11 actionable sorrys sit on ONE mathematical axis:
"How does finite combinatorial structure control infinite measure-theoretic objects?"

This is the deepest structural insight from Session 4. Every sorry requires converting
between a finite counting argument (on Fin m -> T, or on shattered sets, or on block
indices) and a measure-theoretic statement (on Measure.pi, or on ENNReal probabilities).

### Two Bottleneck Skills (Gamma_77 — reusable across D1, D2, D4, D6)

1. **Uniform-measure-to-Measure.pi bridge:** counting on Fin m -> T  <->  Measure.pi.
   Needed: `Measure.pi (fun _ : Fin m => uniformMeasure T) = (1/|T|^m) * Measure.count`
   Status: NOT BUILT. D0-Bridge research completed (9 UKs resolved). Proof agent launched
   but results not yet in codebase. Key lemmas identified:
   - `uniformMeasure_singleton` (from `sum_measure_singleton`)
   - `pi_uniformMeasure_singleton` (from `pi_singleton` + `Fin.prod_const`)
   - `pi_uniformMeasure_finset` (from product of singleton measures)

2. **Fin arithmetic toolkit:** splitting, cardinality, block indexing on Fin types.
   Status: PARTIALLY BUILT. In codebase (uncommitted):
   - `block_extract` (Generalization:2983, sorry-free) -- extracts block j from Fin(k*m) sample
   - `majority_vote` (Generalization:2987, sorry-free) -- majority over k Boolean votes
   - `block_extract_disjoint` (Generalization:2991, sorry-free) -- index sets are disjoint
   - `iIndepFun_block_extract` (Generalization:3004, SORRY) -- block extractions are independent

### D0 Infrastructure Approach -- Method Pattern
Session 4 discovered that BUILDING INFRASTRUCTURE FIRST is the highest-leverage action.
Instead of attacking individual sorrys, Session 4 identified the shared bottlenecks and
launched infrastructure agents. Pattern:
1. Map all sorrys to their shared dependencies (cross-direction analysis)
2. Identify the minimal set of reusable lemmas (bottleneck skills)
3. Build those lemmas as sorry-free infrastructure
4. Close individual sorrys by composing infrastructure

This is M-InfrastructureGap elevated from a metaprogram type to a strategic pattern.

### Symmetrization as Cross-Direction Infrastructure
Symmetrization (double-sample ghost argument) appears in D1 (union_bound_consistent)
AND D6 (Rademacher complexity). Building it once (~200 LOC) serves both directions.
Status: NOT BUILT. Route confirmed by D1v5 and D1v6 agents.

## Proved Infrastructure (sorry-free, cumulative)

### Concentration
- consistent_tail_bound, prob_compl_ge_of_le, uniformMeasure_isProbability
- empiricalError_bounded_diff, union_bound_consistent calc chain (sorry at covering only)

### Sauer-Shelah (full chain)
- funcToSubset_injective -> restrict_shatters_lift -> vcDim_restrict_le
- card_restrict_le_sauer_shelah_bound -> growth_function_le_sauer_shelah
- vcdim_finite_imp_growth_bounded (BP_4 bridge), growth_bounded_imp_vcdim_finite
- shatters_mono (made public, Session 4)
- exp_beats_poly_at (private, Session 4 -- used in compression_bounds_vcdim proof attempt)

### NFL
- nfl_core (finite domains), disagreement_sum_eq, exists_many_disagreements
- shatters_realize, shatters_hard_labeling, per-sample adversarial

### PAC Assembly
- uc_imp_pac, erm_consistent_realizable, trueError_eq_genError
- empiricalMeasureError_eq_empiricalError, vcdim_finite_imp_pac_direct (factorial)

### Separation Witnesses
- pac_not_implies_online (~180 LOC), ex_not_implies_pac (~80 LOC)
- online_imp_pac (adversary), universal_imp_pac (via boost)

### Online (694 LOC) + Gold
- littlestone_characterization, optimal_mistake_bound_eq_ldim, SOA
- gold_theorem, mind_change_characterization

### Session 4 New Infrastructure (uncommitted working copy)
- `block_extract` -- Fin(k*m) block splitting via finProdFinEquiv (sorry-free)
- `majority_vote` -- Boolean majority (sorry-free)
- `block_extract_disjoint` -- disjointness of block index sets (sorry-free)
- `boost_majority_vote` -- private duplicate in Separation.lean (sorry-free)
- `boost_block_extract` -- private duplicate in Separation.lean (sorry-free)
- `growth_bounded_at_vcdim` -- non-existential Sauer-Shelah at known VCDim (SORRY, Generalization:867)

## 6 Attack Directions (Session 4 Final State)

### D1: Concentration (2 sorrys) -- union_bound_consistent, vcdim_finite_imp_uc
Needs symmetrization (~200 LOC). D1v5+D1v6 confirmed structurally necessary.
No progress on proof in Session 4; cross-direction analysis only.

### D2: NFL (3 sorrys) -- pac_lower_bound_core, _member, vcdim_infinite_not_pac
Needs Measure.pi-of-uniform bridge (bottleneck #1). 3-for-1 opportunity.
D0-Bridge research completed: 9 UKs resolved, proof strategy identified.
Key: `sum_measure_singleton`, `pi_singleton`, `Fin.prod_const`.

### D3: UC (1 sorry) -- vcdim_finite_imp_uc (same as D1 #2)
ES+Chebyshev ~100 LOC. Not critical path. Overlaps with D1 sorry #2.

### D4: Boosting (1 sorry) -- boost_two_thirds_to_pac
Majority vote + Chebyshev. Needs Fin arithmetic (bottleneck #2). ~200 LOC (revised up
from ~100 based on D0-Fin-v2 research). Session 4 progress: learner construction written
in Separation.lean (uncommitted), event containment proved, probability chain set up.
Remaining: Chebyshev composition with block independence.
Key insights from D0-Fin-v2:
- `iIndepFun_pi` dissolves block independence without nested pi (KK-8)
- `Set.univ` for hypotheses, `output_in_H` trivial (NEW-UK-1)
- `IsProbabilityMeasure` implies `SigmaFinite` (NEW-UK-2)

### D5: Compression + Bridge (2 sorrys) -- compression_bounds_vcdim, sample_complexity_upper_bound
compression_bounds_vcdim (Bridge:669): Statement corrected from false 2^k-1 bound to
2^(cs.size)-1 (still has sorry in committed code). Session 4 identified Route A proof via
pigeonhole + exp_beats_poly_at. The SESSION_END_NOTES claimed closure but build confirms
sorry remains at Bridge:669.
sample_complexity_upper_bound (Bridge:621): Restructured by BridgeAgent-v1. All measure
theory scaffolded; remaining sorry is pure arithmetic connecting ERM bound to the
ceil(8/eps * (d*log(2/eps) + log(2/delta))) formula.

### D6: Rademacher (2 sorrys) -- Massart, NFL Rademacher lower bound
Hardest. Benefits from D1 symmetrization and Sauer-Shelah (proved).
No direct progress in Session 4; research only.

## Gamma Ledger (cumulative, Sessions 3-4)

| ID | Discovery | Session | Method |
|----|-----------|---------|--------|
| Gamma_65 | growth_function_cover impossible for infinite C | S3 | M-DefinitionRepair |
| Gamma_66 | Sauer-Shelah C(m,d) was FALSE | S3 | M-DefinitionRepair |
| Gamma_67 | pac_lower_bound 1/(2e) needs EHKV; weakened to 1/(64e) | S3 | M_2 |
| Gamma_68 | universal_strictly_stronger conjunct 2 FALSE (Bousquet 2021) | S3 | A4 alarm |
| Gamma_69 | ES+Chebyshev gives UC in ~100 LOC vs McDiarmid ~600 LOC | S3 | M_2 |
| Gamma_70 | UniversalLearnable needed Measure.pi fix | S3 | M-DefinitionRepair |
| Gamma_71 | online_imp_pac needs adversary_from_shatters | S3 | M_4+M_6 |
| Gamma_72 | D2 chain 6-step ~205 LOC | S3 | M-Pipeline |
| Gamma_73 | CompressionScheme uninhabitable -- realizability guard added | S3 | M-DefinitionRepair |
| Gamma_74 | Rademacher d=0 edge case | S3 | M-CaseElimination |
| Gamma_75 | Birthday bypass for combinatorial step | S3 | M_3 |
| Gamma_76 | vcdim_finite_imp_compression is Moran-Yehudayoff (deep/open) -- reclassified PERMANENT | S4 | Reclassification |
| Gamma_77 | Two bottleneck skills (Measure.pi bridge + Fin toolkit) shared across D1/D2/D4/D6 | S4 | Cross-direction |
| Gamma_78 | All 11 actionable sorrys on single axis: finite combinatorics -> measure lift | S4 | Cross-direction |
| Gamma_79 | compression_bounds_vcdim bound 2^k-1 FALSE for k=1; correct bound: 2*(k+1)^2 | S4 | A4 alarm |
| Gamma_80 | sample_complexity_upper_bound NOT one-line -- needs (em/d)^d form + log splitting | S4 | M-InfrastructureGap |
| Gamma_81 | compression_bounds_vcdim proof strategy: pigeonhole + exp_beats_poly_at (NOT yet closed) | S4 | M_3 |
| Gamma_82 | Route E is Littlestone-Warmuth conjecture (1986, $600 bounty, OPEN 40yr) NOT Moran-Yehudayoff | S4 | Literature |
| Gamma_84 | exp_dominates_poly_log PROVED: s/2 >= 1+log(s)+a for s >= 8(log2+a) | S4 | Sorry closure |
| Gamma_91 | Non-measurability blocking D2: goodX not MeasurableSet without MeasurableSingletonClass | S4 | Obstruction |
| Gamma_92 | iIndepFun_block_extract PROVED via currying equiv + infinitePi_map_curry | S4 | Sorry closure (infra) |
| Gamma_93 | compression_bounds_vcdim CLOSED: statement 2(k+1)^2, proof pigeonhole + exp_beats_poly_at | S4 | Sorry closure |
| Gamma_94 | chebyshev_majority_bound signature missing independence + measurability hypotheses | S4 | Statement repair |
| Gamma_95 | UU_1 (pure combinatorial D2 route) -> KU: NOT practical, conversion needs MeasurableSingletonClass | S4 | UU->KU |
| Gamma_96 | Route C ([MeasurableSingletonClass X]) is ONLY viable D2 route -- genuinely needed | S4 | Route selection |
| Gamma_97 | [MeasurableSingletonClass X] APPROVED for D2 chain: vacuous for all standard types, A5-valid | S4 | Decision (approved by Dhruv) |
| Gamma_98 | Routes A (direct cover), B (ε-net) blocked by Gamma_92 for uncountable C | S5 | Route elimination |
| Gamma_99 | Route D (consistent UC) blocked — sample-independent reps impossible for uncountable C | S5 | Route elimination |
| Gamma_100 | Route E (Dudley chaining) blocked — requires metric entropy absent from Mathlib | S5 | Route elimination |
| Gamma_101 | Symmetrization is THE ONLY viable route for UC bounds (all others blocked by Gamma_92) | S5 | Route selection |
| Gamma_102 | 3 Meta-Problems convergence: ALL open sorrys blocked by MP1 (Gamma_92), MP2 (definition coherence), or MP3 (Mathlib gaps) | S5 | Cross-direction |
| Gamma_103 | \|corr\| in EmpRad is LOAD-BEARING BLOCKER: E[sup\|Z\|] ≤ 2σ√(2 log N) but theorem states bound without factor 2 | S5 | A4 intersection |
| Gamma_104 | Sauer-Shelah constant: standard gives (em/d)^d but theorem states (2m/d)^d. Since e > 2, standard is too loose | S5 | Constant mismatch |
| Gamma_105 | Mathlib has Fubini for Measure.prod but NOT Measure.pi. Workaround: coordinate-wise decomposition | S5 | Mathlib gap |
| Gamma_106 | Symmetrization infrastructure also unblocks ESChebyshev.lean sorrys | S5 | Cross-direction |
| Gamma_107 | **uc_bad_event_le_delta STATEMENT IS MATHEMATICALLY FALSE.** Sample complexity (v+2)!/(ε^(v+1)·δ) insufficient for two-sided UC. Counterexample: VCDim=1, ε=10⁻¹⁰, δ=0.5 → P[bad] ≈ 0.83 > δ. Correct formula: C·(v/ε²)·(v·log(1/ε) + log(1/δ)) | S5 | **FALSE STATEMENT** |
| Gamma_108 | T1 fix (remove \|·\|) requires 3 new helpers + symmetry argument for empRad_nonneg. Completed by agent, lost in revert, recoverable from subagent transcript | S5 | Proof method |
| Gamma_109 | Massart helpers (4/6) proved sorry-free: exp_mul_sup'_le_sum, cosh_le_exp_sq_half, rademacher_mgf_bound (~80 LOC), finite_massart_lemma (~140 LOC) | S5 | Sorry closure |
| Gamma_110 | Birthday proof closed: 3-phase (measure transfer → collision bound → ENNReal→ℝ). Lost in revert, recoverable from transcript | S5 | Sorry closure |
| Gamma_111 | T4 (pac_lower_bound_core + pac_lower_bound_member) CLOSED sorry-free. Preserved in stash 1f0c04c, currently in working tree | S5 | Sorry closure |
| Gamma_112 | Concurrent agent writes to same file cause race conditions. T5 agent overwrote T1's \|·\| removal. Mitigation: worktree isolation per agent | S6 | **PROCESS FAILURE** |
| Gamma_113 | Context compaction destroys epistemic calibration. Successor sessions operate on beliefs not facts. Mitigation: state manifest file, URS log entries before every edit | S6 | **PROCESS FAILURE** |
| Gamma_114 | git stash commits survive drop/pop and can be addressed by hash. Key recovery mechanism for lost work | S6 | Recovery method |
| Gamma_115 | Subagent JSONL files preserve full edit history of dead/completed agents. Can replay exact code changes | S6 | Recovery method |

Note on Gamma_81: The SESSION_END_NOTES claimed this sorry was CLOSED, but the build
at session end still shows Bridge:669 as sorry-using. The proof strategy was identified
and partially written but not completed in the committed code.

## Counterfactual Proof Routes (Session 4)

### D5: compression_bounds_vcdim -- 5 routes through CompressionScheme -> VCDim <= bound

| Route | Bound | File | Status | Discovery Value |
|-------|-------|------|--------|-----------------|
| A | 2*(k+1)^2 = O(k^2) | Bridge.lean (main) | Sorry remains (proof strategy identified, Gamma_81) | Low -- reuses existing |
| B | Explicit threshold solve | (not created) | Available | Medium -- computable |
| C | O(k*log k) | CompressionBoundAlt.lean (109 LOC) | COUNTERFACTUAL (not in build) | **HIGH** -- connects to sample complexity |
| D | 2^k - 1 | (was in Bridge.lean) | FALSE (Gamma_79) | N/A |
| E | O(k) | CompressionBoundOptimal.lean (682 LOC) | BENCHMARK (Littlestone-Warmuth 1986, OPEN 40yr, $600 bounty) | Highest -- open conjecture |

**Gamma_82:** Route E is NOT Moran-Yehudayoff (who proved the forward direction).
The converse (compression k -> VCDim O(k)) IS the Littlestone-Warmuth conjecture.
Chase 2022 claimed resolution but withdrew within 24 hours. Chase et al. COLT 2024
showed the embedding approach has fundamental exponential barriers.

**Route E counterfactual file:** `FLT_Proofs/Complexity/CompressionBoundOptimal.lean`
- NOT in build (excluded from imports), 682 LOC
- 12 sorry'd lemmas, 6 parts, difficulty 1-5 stars
- `compression_deficiency_bound` (5 stars) IS the open conjecture
- Partial results (O(k*sqrt(log k)), maximum classes) ARE provable benchmarks
- ~950-1300 LOC missing Mathlib infrastructure catalogued
- Full citations: Moran-Yehudayoff 2016, Chase et al. COLT 2024, Floyd-Warmuth 1995

**Route C counterfactual file:** `FLT_Proofs/Complexity/CompressionBoundAlt.lean`
- NOT in build (excluded from imports), 109 LOC
- Contains skeleton + full proof sketch + inquiry axes
- Estimated ~60-80 LOC to close

### D5: sample_complexity_upper_bound -- 3 routes through arithmetic sorry

The sorry at Bridge.lean:657 is PURE ARITHMETIC after BridgeAgent-v1 restructured:
`GrowthFunction X C bound * (1-eps)^bound <= delta` for `bound = ceil((8/eps)(d*log(2/eps)+log(2/delta)))`.

| Route | Method | Status | Discovery Value |
|-------|--------|--------|-----------------|
| A | Direct log splitting: exp(-4d*log(2/eps)) = (eps/2)^(4d) dominates polynomial | PROVING (BridgeAgent-v2 launched, not completed) | HIGH -- standard textbook bound |
| B | Weaken to larger bound with cleaner arithmetic | Fallback | LOW -- trades tightness for simplicity |
| C | Factor as standalone `sample_bound_arithmetic` lemma | Last resort | MEDIUM -- clean interface for future |

**Gamma_80:** BridgeAgent-v1 discovered this is NOT a one-line sorry. The tight bound formula
(8/eps)(d*log+log) requires different arithmetic from the factorial bound in
vcdim_finite_imp_pac_direct. Restructured: all measure theory done, only arithmetic remains.

### D4: boost_two_thirds_to_pac -- 2 proof strategies

| Strategy | Method | Status | LOC Est |
|----------|--------|--------|---------|
| Direct Chebyshev | k = ceil(9/delta) blocks, Chebyshev on indicator sum | IN PROGRESS (Separation.lean, uncommitted) | ~200 |
| Recursive median-of-3 | Well-founded recursion on m, p_{d+1} = 3p_d^2 - 2p_d^3 | RESEARCHED (D0-Fin-v2) | ~200 |

Direct Chebyshev is further along. The learner construction is written. The probability
chain (event containment) is proved. Remaining: connecting Chebyshev bound to block
independence under Measure.pi, which requires `iIndepFun_block_extract` (sorry).

### D2: NFL chain -- shared infrastructure approach

All 3 sorrys (pac_lower_bound_core, pac_lower_bound_member, vcdim_infinite_not_pac)
need the same Measure.pi-of-uniformMeasure bridge. D0-Bridge research resolved 9 UKs:
- UK-1: MeasurableEquiv for finProdFinEquiv NOT NEEDED (Fin has top MeasurableSpace)
- UK-2: pi_map_piCongrLeft takes plain Equiv (no MeasurableEquiv needed)
- UK-3: iIndepFun_pi + indepFun_finset gives block independence directly
- UK-4: finProdFinEquiv ordering confirmed (column-major)
- UK-5: Fin.blockSplit not needed (block_extract suffices)
- UK-6: Both Fin(k*m) and Fin k x Fin m valid for Measure.pi

## D0 Research Documents (Session 4)

### D0-Bridge (v3/D0_Fin_v2_RESOLVED.md + v4/D0_IndepFun_RESOLVED.md)
Resolved 9 UKs for Measure.pi bridge and Fin arithmetic. Key findings:
- `iIndepFun_pi` (Mathlib) directly gives coordinate independence under Measure.pi
- `iIndepFun.indepFun_finset` extends to disjoint coordinate blocks
- `infinitePi_map_curry` provides the measure currying identity
- Route A (via iIndepFun_iff_map_fun_eq_pi_map) recommended for iIndepFun_block_extract
- Route B (direct product formula) available as fallback
- Import `Mathlib.Probability.ProductMeasure` needed for infinitePi_eq_pi

### D0-Fin (v3/D0_Fin_v2_RESOLVED.md)
Resolved 6 UKs for Fin arithmetic. Key findings:
- `finProdFinEquiv` is column-major: (i,j) -> j + n*i
- `Fin.instMeasurableSpace` is top: ALL functions from/to Fin n are measurable
- `isProbabilityMeasure_pi` exists in Mathlib
- `IsProbabilityMeasure` implies `SigmaFinite` (standard instance)
- `variance_sum_pi` exists for variance of sum under product measure
- `hasSubgaussianMGF_of_mem_Icc` gives sub-Gaussian from boundedness (for boosting)

### Mathlib API Inventory (verified in Session 4)
| API | File | Use |
|-----|------|-----|
| finProdFinEquiv | Logic/Equiv/Fin/Basic:329 | Block splitting Fin k x Fin m <-> Fin(k*m) |
| MeasurableEquiv.piCongrLeft | MeasurableSpace/Embedding:469 | Reindexing product measures |
| pi_map_piCongrLeft | Constructions/Pi:453 | Map + piCongrLeft = pi (for reindexing) |
| measurePreserving_piCongrLeft | Constructions/Pi:744 | Measure-preserving reindexing |
| measurePreserving_piFinsetUnion | Constructions/Pi:899 | Disjoint union of sub-products |
| iIndepFun_pi | Independence/Basic:784 | Coordinate projections are iIndepFun under Measure.pi |
| iIndepFun.indepFun_finset | Independence/Kernel/IndepFun:331 | Disjoint coordinate sets are independent |
| meas_ge_le_variance_div_sq | Moments/Variance:378 | Chebyshev's inequality |
| IndepFun.variance_sum | Moments/Variance:403 | Variance of sum of independent RVs |
| variance_sum_pi | Moments/Variance:428 | Variance under product measure |
| measure_sum_ge_le_of_iIndepFun | Moments/SubGaussian:779 | Hoeffding inequality |
| hasSubgaussianMGF_of_mem_Icc | Moments/SubGaussian:860 | Bounded -> sub-Gaussian |
| infinitePi_eq_pi | ProductMeasure:509 | infinitePi = Measure.pi for Fintype |
| infinitePi_map_curry | ProductMeasure:557 | Currying for product measures |
