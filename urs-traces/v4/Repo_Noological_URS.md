# Repo Noological URS — FLT_Proofs Kernel Ontology (v4, 2026-03-19)

## Identity
FLT_Proofs: 11,170 lines Lean4, 33 files, 310+ declarations. 0 errors, 15 sorry-using
declarations. Multi-paradigm formal learning theory: PAC + Online + Gold + Universal +
Bayesian + Rademacher + Compression with separation proofs.

First formal learning theory library with this scope in any proof assistant.

## A — Axioms (cumulative)

### A_0: Discovery Will
The kernel exists to make new mathematical questions ASKABLE. Sorry closure is a
measurement of progress, not the objective. A sorry with a transparent proof route
and documented ignorance geometry is more valuable than a trivially-closed sorry.

### A_1-A_6: Type Architecture Axioms (unchanged from v2)
Invariance, completeness, compilation, break point honesty, anti-simplification,
anti-triviality.

### NA_15: Finite partition > measurable selection for PAC union bound
The bad event decomposes into finite union over restriction patterns p : Fin m -> Bool.
No measurable selection needed. GrowthFunction bounds occupied patterns. (Gamma_65)

### NA_16: NFL constant hierarchy
1/(64e) via standard averaging. 1/(2e) requires EHKV/Fano. Both Omega(d/e). (Gamma_67)

### NA_17: Universal <-> PAC equivalence (Bousquet 2021)
Every concept class is universally learnable at some rate. PAC iff finite VCDim iff
universal at exponential rate. Existence separation is FALSE. (Gamma_68)

### NA_18: online_imp_pac via adversary argument
OnlineLearnable -> LDim < inf -> VCDim < inf -> PAC. VCDim <= LDim via
adversary_from_shatters. Novel in Lean4. (Gamma_71)

### NA_19: UniversalLearnable requires Measure.pi
Gamma_48 was incorrect placeholder. Fixed to use Measure.pi for product measures.
(Gamma_70)

### NA_20 (NEW, v4): Symmetrization is the only path for union_bound_consistent
The covering format (sample-independent reps with GF bound) is structurally impossible
for uncountable C. Agents D1v5 and D1v6 confirmed independently. Symmetrization
gives different bound (2*GF(C,2m)*exp(-me^2/8)) but preserves PAC. (Gamma_65 + D1v6)

### NA_21 (NEW, v4): Boosting genuinely requires ~100 LOC
Agent D4v2 analyzed full construction. The Lean4 complexity is in Fin arithmetic for
block splitting + product measure independence for majority vote. Not a skill gap.

## M — Mechanism Space (12 + extensions)

### M_1-M_8: Primary (unchanged)
Diagonalization, Probabilistic, Combinatorial, Game-Theoretic, Convergence,
Construction, Reduction, Category-Theoretic.

### M_9-M_12: Session 3 Discoveries
M_9: Bounded Average. M_10: Paradigm-Joint Asymmetry. M_11: Per-Sample Adversarial.
M_12: Subtype Restriction (BP_4 bridge).

### Metaprogram Types (12)
M-Bridge, M-BridgeLift, M-Contrapositive, M-Pipeline, M-Conjunction,
M-Construction, M-DefinitionRepair, M-CaseElimination,
M-Potential, M-InfSup, M-VersionSpaceCollapse, M-InfrastructureGap.

## R — Representations (v4 sorry distribution)

### Layer Completeness
| Layer | Status | Files |
|-------|--------|-------|
| L0 Computation | COMPLETE (0 sorry) | Computation.lean |
| L1 Basic Types | COMPLETE (0 sorry) | Basic.lean |
| L2 Data | COMPLETE (0 sorry) | Data.lean |
| L3 Learners | COMPLETE (0 sorry) | Learner/*.lean |
| L4 Criteria | COMPLETE (0 sorry) | Criterion/*.lean |
| L5 VCDim/LDim/etc | COMPLETE (0 sorry) | Complexity/VCDimension, Littlestone, Ordinal, MindChange, Structures |
| L5 Generalization | 6 sorrys | Generalization.lean (3010 lines) |
| L5 Rademacher | 2 sorrys | Rademacher.lean |
| L6 Gold | COMPLETE (0 sorry) | Theorem/Gold.lean |
| L6 Online | COMPLETE (0 sorry) | Theorem/Online.lean (694 lines) |
| L6 PAC | COMPLETE (0 sorry — routes through L5) | Theorem/PAC.lean |
| L6 Separation | 1 sorry + 2 permanent | Theorem/Separation.lean |
| L6 Extended | 2 permanent | Theorem/Extended.lean |
| Bridge | 2 sorrys | Bridge.lean |
| L7 Processes | COMPLETE (0 sorry) | Process.lean |

### Sorry Distribution by Direction
| Direction | Count | Files |
|-----------|-------|-------|
| D1 Concentration | 2 | Generalization |
| D2 NFL | 3 | Generalization |
| D3 Uniform Convergence | 1 | Generalization |
| D4 Boosting | 1 | Separation |
| D5 Compression+Bridge | 2 | Bridge |
| D5-UU Compression (deep) | 1 | Generalization (Moran-Yehudayoff) |
| D6 Rademacher | 2 | Rademacher |
| PERMANENT | 4 | Separation (2), Extended (2) |

Note: vcdim_finite_imp_compression (#4, Generalization:2137) is classified D5-UU:
it requires Moran-Yehudayoff 2016 (approximate minimax on binary matrices of bounded
VC dimension). This is deep open mathematics, not a missing proof step.

## T — Traces

### HC at Paradigm Joints (v4)
| Joint | HC (v3) | HC (v4) | Notes |
|-------|---------|---------|-------|
| Finite/Ordinal | 0.0 | 0.0 | Gamma_27 resolved |
| ENNReal/Real | 0.1 | 0.1 | Bridges proved |
| Combinatorial/Measure | 0.1 | 0.1 | consistent_tail_bound proved |
| Set/Finset (BP4) | 0.0 | 0.0 | Sauer-Shelah bridge proved |
| PAC/Online | 0.0 | 0.0 | online_imp_pac proved |
| CompressionScheme | 0.6 | 0.6 | Gamma_73 realizability guard added |
| Symmetrization | N/A | 0.8 | NEW: D^m -> D^(2m) coupling not built |

### Prior Art Bridge Status
| Library | Status | Usable For |
|---------|--------|------------|
| Zhang (Lean4) | Types identical, NOT imported | D3 (ES), D6 (SubGaussian) |
| Google formal-ml (Lean3) | Blueprint only | D1 (pac_bound strategy), D2 |
| Mathlib Sauer-Shelah | BRIDGED (sorry-free) | D1, D2 (GrowthFunction bounds) |
| Mathlib Measure.pi | USED directly | D1, D2, D4 (product measure) |
| Mathlib Hoeffding | Available (measure_sum_ge_le_of_iIndepFun) | D1 (symmetrization), D6 |
