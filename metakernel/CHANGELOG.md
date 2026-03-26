# Changelog

## [0.1.1] - 2026-03-16

### Semantic Strengthening (69 sorry, 0 errors, CI-enforced)

- Eliminated all sorry-in-Prop definitions (IsOptimalTeacher, IsAdversarial, IsRandomTeacher, EXUnderDrift)
- Eliminated all True-placeholder theorem conclusions (computational_hardness_pac, meta_pac_bound, unlabeled_not_implies_labeled, fundamental_theorem conjunct 4)
- Fixed substrate compromises: BayesianInference.posterior now computes Bayes' rule, AlgorithmicStability.stable uses leave-one-out, InductiveBias.supported has correct predicate
- Added Lean4 CI to GitHub Actions (lake build, Mathlib cache, sorry count reporting)
- Reduced sorry count from 78 to 69

## [0.1.0] - 2026-03-16

### Type Architecture Complete (78 sorry, 0 errors)

First stable release of the LimitsOfLearning type architecture for formal learning theory.

**What this version provides:**
- Complete type skeleton covering PAC, Online, Gold, Universal, and Bayesian learning paradigms
- 78 theorem/definition stubs (`sorry`) with fully specified type signatures
- Deeply nested submodule structure for parallel proof development
- Mathlib4-coherent types (universe polymorphism, MeasurableSpace, WithTop ℕ, Ordinal)
- 7 documented break points (BP1-BP7) at paradigm boundaries

**Module structure:**
- `Basic` — foundational types (Concept, ConceptClass, HypothesisSpace, LossFunction)
- `Data` — data presentations (DataStream, TextPresentation, IIDSample, oracles)
- `Computation` — computability substrate (DFA, MDL, SRM)
- `Learner/{Core,Properties,Active,Bayesian}` — learner types (BP1: no common learner)
- `Criterion/{Gold,PAC,Online,Extended}` — success criteria (paradigm-separated)
- `Complexity/{VCDimension,Littlestone,Ordinal,MindChange,Generalization,Rademacher,Structures}` — complexity measures (BP2: ℕ∞ vs Ordinal)
- `Theorem/{Gold,PAC,Online,Separation,Extended}` — theorem statements
- `Bridge` — Mathlib bridges and cross-paradigm coercions
- `Process` — applications (GrammarInduction, LStar, CEGIS, ConceptDrift)

**Next:** Fill proofs per-submodule. Each `sorry` is independently replaceable.
