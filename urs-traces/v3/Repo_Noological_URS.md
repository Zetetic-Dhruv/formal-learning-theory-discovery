# Repo Noological URS — FLT_Proofs Agent Ontology (v3, 2026-03-19)

## Identity
FLT_Proofs: 7,000+ lines Lean4, 28+ files, 310+ declarations. 0 errors, ~19 sorry-using declarations (agents reducing).
Multi-paradigm formal learning theory: PAC + Online + Gold + Universal + Bayesian + Rademacher + Compression.

## A — Axioms (A₁-A₆ + NA₁-NA₁₄ unchanged from v2, plus:)

### NA₁₅ (NEW): Finite partition > measurable selection for PAC union bound
The PAC union bound does NOT need measurable selection. The bad event decomposes into a FINITE union over restriction patterns p : Fin m → Bool. This is Γ₆₅-resolution.

### NA₁₆ (NEW): NFL constant hierarchy
(d-1)/(64ε) is provable via standard averaging. (d-1)/(2ε) requires EHKV/Fano (information theory). Both give Ω(d/ε) sample complexity. The gap is in the constant, not the rate.

### NA₁₇ (NEW): Universal ↔ PAC equivalence (Bousquet 2021)
Every concept class is universally learnable at some rate (exponential, linear, or arbitrarily slow). PAC-learnable iff finite VCDim iff universally learnable at exponential rate. The existence separation (PAC ∧ ¬Universal) is FALSE.

### NA₁₈ (NEW): online_imp_pac via adversary argument
OnlineLearnable implies LDim < infinity implies VCDim < infinity implies PAC. The VCDim ≤ LDim step uses adversary_from_shatters: given d-shattered set, construct adversary strategy forcing d mistakes. Novel in Lean4.

### NA₁₉ (NEW): UniversalLearnable requires Measure.pi (not Gamma48)
The universal_imp_pac proof required fixing UniversalLearnable to use Measure.pi for product measures. Gamma48 was an incorrect placeholder that silently broke the quantifier structure.

## M — Mechanism Space (v3 additions)

### M₉-M₁₂ (discovered session 3)
- **M₉:** Bounded Average (empiricalRademacherComplexity_le_one)
- **M₁₀:** Paradigm-Joint Asymmetry (fundamental_rademacher ↔ directions)
- **M₁₁:** Per-Sample Adversarial (nfl_core, pac_lower_bound_core)
- **M₁₂:** Subtype Restriction (BP₄ bridge via Set.Finite.toFinset + Sauer-Shelah on ↥S)

## R — Representations (v3 sorry distribution)

### Layer completeness
- L0-L4: ✅ COMPLETE (0 sorry in Computation, Basic, Data, Learner, Criterion)
- L5 definitions: ✅ COMPLETE (VCDim, LittlestoneDim, MindChange, Ordinal, Structures)
- L5 proofs: 10 sorrys (all in Generalization.lean)
- L6 Online: ✅ COMPLETE (littlestone_characterization, SOA, 694 lines sorry-free)
- L6 Gold: ✅ COMPLETE (gold_theorem, mind_change_characterization)
- L6 PAC: routes through Generalization sorrys but PAC.lean itself is sorry-free
- L7: ✅ COMPLETE

### Proved infrastructure (sorry-free, session 3)
consistent_tail_bound, prob_compl_ge_of_le, uniformMeasure_isProbability, empiricalError_bounded_diff, nfl_core (full NFL for finite domains), uc_imp_pac, erm_consistent_realizable, trueError_eq_genError, empiricalMeasureError_eq_empiricalError, growth_bounded_imp_vcdim_finite, vcdim_finite_imp_growth_bounded (BP₄ bridge), pac_not_implies_online (threshold ~180 lines), ex_not_implies_pac (~80 lines), Sauer-Shelah bridge chain (4 lemmas in Bridge.lean), disagreement_sum_eq, exists_many_disagreements, shatters_hard_labeling, per_sample adversarial, union_bound_consistent calc chain

### Session 3 late additions (sorry-free)
online_imp_pac (adversary argument, VCDim ≤ LittlestoneDim), universal_imp_pac (structural contrapositive), UniversalLearnable fix (Gamma48 → Measure.pi), adversary_from_shatters, analytical_log_sqrt_bound, fundamental_rademacher assembly from proved components

## T — Traces

### HC at Paradigm Joints (v3 → v3.1)
| Joint | HC (v2) | HC (v3) | HC (v3.1) | Change |
|-------|---------|---------|-----------|--------|
| Finite/Ordinal | 0.2 | 0.0 | 0.0 | RESOLVED (Gamma27) |
| ENNReal/Real | 0.5 | 0.2 | 0.1 | prob_compl_ge_of_le + ENNReal arithmetic proved |
| Combinatorial/Measure | 0.7 | 0.3 | 0.1 | consistent_tail_bound + uniformMeasure proved |
| Set/Finset (BP4) | 0.5 | 0.1 | 0.0 | Sauer-Shelah bridge + first-principles growth bound proved |
| PAC/Online | 1.0 | 0.8 | 0.0 | online_imp_pac PROVED via adversary argument |
| CompressionScheme | — | 0.8 | 0.6 | Agent running, pigeonhole from compress_injective |

### Prior Art Status
| Library | Relevance | Bridge Status |
|---------|-----------|---------------|
| Zhang lean-stat-learning-theory | SubGaussian, EfronStein, Dudley | Types IDENTICAL to ours. NOT imported as dependency. |
| Google formal-ml | PAC for finite H (Lean3) | Proof patterns used, not imported |
| Mathlib Sauer-Shelah | card_shatterer_le_sum_vcDim | BRIDGED via Bridge.lean (sorry-free) |
| Mathlib Measure.pi | IsProbabilityMeasure instance | USED directly (consistent_tail_bound) |
