# Claude Task URS — Metaprogram Synthesis (v3, 2026-03-19)

## Task Identity
Claude synthesizes proof STRUCTURES then translates to Lean4. ~19 sorrys remain across 6 directions (agents actively reducing).

## Pre-Flight Protocol (7 Gates — ENFORCED)

### Gate 0: Path Invariant — FLT_Proofs/ only
### Gate 1: A5 Anti-Simplification — no weakening statements
### Gate 2: Task URS Skill — invoke before type definitions
### Gate 3: Noological URS — K/U partition awareness
### Gate 4: Metaprogram-First — identify M-type before tactics
### Gate 5: Measurement Gate — check WorldModel/MeasuredTactic.lean
### Gate 6: Prior-Art Check — Zhang (SubGaussian, EfronStein), Google formal-ml, Mathlib
### Gate 7: Feedback Loop — check WorldModel/Feedback.lean

## Agent URS Templates (for spawning proof agents)

### Template: D1 Agent (Concentration Chain)
- Will: 0 sorry target
- KK: consistent_tail_bound PROVED, measure_iUnion_fintype_le (Mathlib), Fintype (Fin m → Bool)
- Insight: finite partition over restriction patterns, NOT measurable selection
- Metaprogram: M₃ (combinatorial partition) + M₂ (measure union bound)

### Template: D2 Agent (NFL Lower Bound)
- Will: weaken constant to 1/(64ε), create EHKV.lean skeleton
- KK: nfl_core PROVED, per_sample PROVED, pairing argument + reversed Markov
- Insight: m < d/64 → 2m < d → nfl_core applies on ↥T
- Metaprogram: M-DefinitionRepair (constant) + M₇ (reduce to nfl_core)
- **Status (D6):** Agent running, 6-step assembly (~205 LOC): nfl_per_sample_shattered + pac_lower_bound_core + pac_lower_bound_member + vcdim_infinite_not_pac

### Template: D5 Agent (Compression)
- Will: repair CompressionScheme, prove pigeonhole
- KK: iSup₂_eq_top for VCDim=⊤, Shatters → all labelings
- Insight: add `correct` field (A5 enrichment), then 2^n > C(n,k)·2^k pigeonhole
- Metaprogram: M-DefinitionRepair + M₃ (pigeonhole)

## KU Discovery Log (Session 3 additions)

### KU (NEW): Finite Partition for Union Bound
The bad event decomposes as ⋃_{p : Fin m → Bool} {xs | ∃ bad h with restriction p, ∀ i c(xs i) = p i}. This is a FINITE union (≤ 2^m terms). No measurable selection needed. GrowthFunction bounds occupied patterns.

### KU (NEW): Efron-Stein Route to UC
Zhang's efronStein (PROVED) gives Var(f) ≤ Σ E[(f - E^{(i)}f)²]. For bounded-difference f with cᵢ = 1/m: Var ≤ Σ(1/m)² = 1/m. Chebyshev: Pr[|f-E[f]| > t] ≤ 1/(mt²). ~100 LOC total.

### KU (NEW): VCDim ≤ LittlestoneDim Construction
Given VCDim-shattered Finset S = {s₁,...,s_d}, construct LTree of depth d with node at depth k labeled s_k. Shattering: for any path of true/false choices, restricting C preserves shattering on remaining elements. Novel in Lean4.

### KU (NEW): NFL Constant Analysis (Γ₆₇)
Standard: (d-1)/(64ε) via non-uniform distribution. Tight: (d-1)/(2ε) via EHKV + Fano's inequality. The averaging + reversed Markov route gives 6/7 bound ONLY when E[error] > 1/4 AND ε ≤ 1/8. With 1/(64ε): 2m < d guaranteed, so E[error] > 1/4.

## Sorry Selection Protocol — Session 3 Late Progress

### D2 PAC Chain
Agent running, 6-step assembly (~205 LOC). Targets: nfl_per_sample_shattered + pac_lower_bound_core + pac_lower_bound_member + vcdim_infinite_not_pac.

### D3 Counterfactual Proof Files
ESChebyshev.lean + McDiarmid.lean CREATED as counterfactual proof files (NOT in build). Efron-Stein + Chebyshev route remains preferred (~100 LOC vs ~600 LOC).

### D4 Cross-Paradigm Progress
- universal_imp_pac PROVED (structural, via contrapositive NFL on shattered sets)
- UniversalLearnable FIXED: Gamma48 replaced with Measure.pi for correct product measure
- Gamma68 (universal_strictly_stronger_pac conjunct 2) documented as FALSE (Bousquet 2021 trichotomy)

### D5 Compression
compression_bounds_vcdim agent running. Pigeonhole argument from compress_injective_on_labelings.

### D6 Rademacher
3 sorrys being closed by agent: Massart finite lemma, birthday+EmpRad bypass, d=0 Jensen bypass.

### UU Sorrys (Documented with Citations)
All 5 UU-boundary sorrys documented:
1. natarajan_not_characterizes_pac — Moran-Yehudayoff (2016)
2. sample_complexity_upper_bound — Brukhim et al. (2023)
3. universal_strictly_stronger_pac — Bousquet et al. STOC 2021 (FALSE as stated)
4. computational_hardness_pac — cryptographic hardness (Valiant 1984, Kearns-Valiant 1994)
5. unlabeled_not_implies_labeled — distribution-dependent learning theory

## Error Recovery
- Compilation error → diagnose structural cause (CNA₈), NOT convergence-first
- Context compression → re-read v3 URS files + memory/project_flt_proofs_state.md
- Agent interrupted → check output file, resume with updated URS
