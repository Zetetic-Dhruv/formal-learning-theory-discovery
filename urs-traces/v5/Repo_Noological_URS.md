# Repo Noological URS — FLT_Proofs Kernel Ontology (v5, 2026-03-20)

## Identity
FLT_Proofs: ~12,000 lines Lean4, 33+ files, 310+ declarations. 0 errors (base),
~20 sorry-using declarations. Multi-paradigm formal learning theory: PAC + Online +
Gold + Universal + Bayesian + Rademacher + Compression with separation proofs.

First formal learning theory library with this scope in any proof assistant.

## A — Axioms (cumulative)

### A_0: Discovery Will
The kernel exists to make new mathematical questions ASKABLE. Sorry closure is a
measurement of progress, not the objective.

### A_1-A_6: Type Architecture Axioms (unchanged from v2)
Invariance, completeness, compilation, break point honesty, anti-simplification,
anti-triviality.

### NA_15-NA_19: (unchanged from v4)
Finite partition > measurable selection (NA_15), NFL constant hierarchy (NA_16),
Universal<->PAC equivalence Bousquet 2021 (NA_17), online_imp_pac via adversary (NA_18),
UniversalLearnable requires Measure.pi (NA_19).

### NA_20: Symmetrization is the only path for union_bound_consistent
Covering format structurally impossible for uncountable C. Symmetrization gives
different bound (2·GF(C,2m)·exp(-mε²/8)) but preserves PAC. (Gamma_92 + Gamma_100)

### NA_21: Boosting genuinely requires ~100 LOC
Fin arithmetic for block splitting + product measure independence for majority vote.

### NA_22 (NEW v5): 3 Meta-Problems convergence
All open sorrys blocked by exactly 3 meta-infrastructure issues:
MP1 (uncountable C → symmetrization), MP2 (definition coherence), MP3 (Mathlib gaps).
This is structurally simpler than the 6-direction model.

### NA_23 (NEW v5): Symmetric Rademacher is a load-bearing blocker
|corr| in EmpRad creates factor-of-2 incompatibility with Massart bound.
This is NOT cosmetic — it blocks the entire D6 assembly. (Gamma_103)

### NA_24 (NEW v5): Massart finite lemma proved in-house
~140 LOC via finite Jensen (convexOn_exp.map_sum_le). Does not require Zhang import.
Chain: rademacher_mgf_bound → finite_massart_lemma → empRad_le_sqrt_vc_log.

## M — Mechanism Space (16 + extensions)

### M_1-M_12: (unchanged from v4)

### M_13 (NEW v5): Coherence Audit
Systematic comparison of formal definitions against textbook references.
Pl: high (found 2 load-bearing blockers). Coh: composes with A4/A5 checks.

### M_14 (NEW v5): Meta-Problem Convergence
Cross-direction analysis revealing shared infrastructure blockers.
Pl: very high (collapsed 6 directions to 3 problems). Coh: organizes all future work.

### M_15 (NEW v5): Agent Decomposition
Multi-agent proof search with URS handoff protocol.
Pl: medium (1/8 agents fully closed). Coh: scales with file isolation.

### M_16 (NEW v5): Route Elimination
Exhaustive enumeration of proof routes, proving all but one blocked.
Pl: very high (Gamma_100 proved symmetrization is ONLY route). Coh: prevents wasted effort.

## R — Representations (v5 sorry distribution)

### Layer Completeness
| Layer | Status | Files |
|-------|--------|-------|
| L0 Computation | COMPLETE (0 sorry) | Computation.lean |
| L1 Basic Types | COMPLETE (0 sorry) | Basic.lean |
| L2 Data | COMPLETE (0 sorry) | Data.lean |
| L3 Learners | COMPLETE (0 sorry) | Learner/*.lean |
| L4 Criteria | COMPLETE (0 sorry) | Criterion/*.lean |
| L5 VCDim/LDim/etc | COMPLETE (0 sorry) | Complexity/VCDimension, Littlestone, Ordinal, MindChange, Structures |
| L5 Generalization | ~8 sorrys | Generalization.lean (~3400 lines) |
| L5 Rademacher | ~4 sorrys | Rademacher.lean |
| L6 Gold | COMPLETE (0 sorry) | Theorem/Gold.lean |
| L6 Online | COMPLETE (0 sorry) | Theorem/Online.lean (694 lines) |
| L6 PAC | COMPLETE (0 sorry) | Theorem/PAC.lean |
| L6 Separation | 1 sorry + 2 permanent | Theorem/Separation.lean |
| L6 Extended | 2 permanent | Theorem/Extended.lean |
| Bridge | 2 sorrys | Bridge.lean |
| L7 Processes | COMPLETE (0 sorry) | Process.lean |

### Sorry Distribution by Task
| Task | Count | Meta-Problem |
|------|-------|-------------|
| T1 (EmpRad fix) | 0 (definition) | MP2 |
| T2 (Symmetrization) | 3 | MP1 |
| T4 (NFL) | 3 | MP2 |
| T5 (Massart) | 2 | MP2+MP3 |
| T6 (Boosting) | 1 | MP1 |
| T8 (Compression) | 1 | Deep/Open |
| Other (adjacent) | ~4 | Various |
| PERMANENT | 4 | Correctly classified |

## T — Traces

### HC at Paradigm Joints (v5)
| Joint | HC (v4) | HC (v5) | Notes |
|-------|---------|---------|-------|
| Finite/Ordinal | 0.0 | 0.0 | Gamma_27 resolved |
| ENNReal/Real | 0.1 | 0.1 | Bridges proved |
| Combinatorial/Measure | 0.1 | 0.1 | consistent_tail_bound proved |
| Set/Finset (BP4) | 0.0 | 0.0 | Sauer-Shelah bridge proved |
| PAC/Online | 0.0 | 0.0 | online_imp_pac proved |
| CompressionScheme | 0.6 | 0.6 | Gamma_73 realizability guard added |
| Symmetrization | 0.8 | 0.5 | IMPROVED: structured calc chain, 3 independent sorrys |
| sSup/Finset.sup' | N/A | 0.7 | NEW: bridge needed for Massart (Gamma_103) |

### Prior Art Bridge Status
| Library | Status | Usable For |
|---------|--------|------------|
| Zhang (Lean4) | Types identical, NOT imported | SubGaussian, EfronStein |
| Google formal-ml (Lean3) | Blueprint only | Strategy reference |
| Mathlib Sauer-Shelah | BRIDGED (sorry-free) | Growth function bounds |
| Mathlib Measure.pi | USED directly | Product measure |
| Mathlib Hoeffding | Available | Symmetrization (T2), Rademacher (T5) |
| Mathlib convexOn_exp | USED (v5) | finite_massart_lemma proof |
