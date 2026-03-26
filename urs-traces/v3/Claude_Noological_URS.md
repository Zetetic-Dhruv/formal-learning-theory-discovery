# Claude Noological URS — Self-Model (v3, 2026-03-19)

## Identity
Claude operates the MetaKernel agent for FLT_Proofs. Session 3: 33 → ~19 sorrys (14+ closed, agents reducing further). 6 directions fully researched with NL proofs, Lean4 skeletons, and ignorance maps.

## CNA Violations Observed (Session 3)

### CNA₄ (proof-first): 40% → 20% (improved)
Gate 4 enforcement via URS-driven method reduced premature tactic writing. But empiricalError_bounded_diff still triggered CNA₄ (went in circles on Finset.sum manipulation before diagnosing the structural issue).

### CNA₈ (convergence-first): 20% → 15% (improved)
A5 enforcement caught the growth_function_cover false statement (Γ₆₅) instead of patching around it. But the ENNReal arithmetic in nfl_core still triggered CNA₈ (tried to fix by changing proof rather than diagnosing the type mismatch).

### CNA₉ (sorry-count worship): PARTIALLY RESOLVED
The Will (Axiom 0) and URS-driven method shifted focus from sorry-count to kernel health. But the counting issue (21 vs 10 vs 22 confusion due to transitive warnings) shows CNA₉ is still active — the NUMBER matters less than the STRUCTURE of remaining sorrys.

### CNA₁₂ (infrastructure-gap): ACTIVE
Multiple instances: McDiarmid chain was wrong abstraction (Γ₅₆), growth_function_cover was wrong statement (Γ₆₅), pac_lower_bound constant was too tight (Γ₆₇). Each time, the obstruction was in the STATEMENT/DEFINITION, not in the proof technique.

### CNA₁₃ (partial-build-confusion): CRITICAL — NEW
Partial build sorry count is UNRELIABLE when errors exist. Multiple times during session 3, sorry counts from `lake build` with errors present were misleading. Only trust sorry counts from clean (0 error) builds.

### CNA₁₄ (agent-file-conflict): NEW
Agents can conflict on same file — check file ownership before launching parallel agents. Two agents editing the same .lean file simultaneously causes merge conflicts and wasted work.

## K/U Universe (v3)

### KK (Verified — 213+ entries)
All v2 KK preserved plus:
- Finite partition for union bound (NOT measurable selection)
- Efron-Stein + Chebyshev gives UC in ~100 LOC
- VCDim ≤ LittlestoneDim via LTree construction (NL proof complete)
- NFL constant 1/(64ε) is provable; 1/(2ε) needs EHKV
- Zhang types IDENTICAL to ours (Measure.pi, IsProbabilityMeasure)
- Bousquet 2021: every class IS universally learnable (trichotomy)
- All 3 Rademacher NL proofs complete with Lean4 skeletons
- Mathlib has log_le_rpow_div (key for Rademacher sorry 3)
- **Session 3 late additions (13+):**
  - online_imp_pac PROVED (adversary argument, LTree construction)
  - universal_imp_pac PROVED (structural contrapositive)
  - uc_does_not_imply_online via threshold class (VCDim=1, LDim=infinity)
  - adversary_from_shatters construction for online_imp_pac
  - Sauer-Shelah bridge chain (4 lemmas, sorry-free)
  - consistent_tail_bound (finite partition + union bound)
  - nfl_core (full NFL for finite domains)
  - analytical_log_sqrt_bound (log x <= sqrt x for all x)
  - prob_compl_ge_of_le (complement probability lemma)
  - uniformMeasure_isProbability (product measure instance)
  - UniversalLearnable correct definition uses Measure.pi (not Gamma48)
  - Fin n measurability trick for product events
  - Birthday paradox bypass via direct combinatorial argument

### KU (Articulated — 15+ entries)
- CKU₁: Measurability of EmpiricalRademacherComplexity as function of xs (for sorry 2)
- ~~CKU₂: Birthday paradox for collision-free samples~~ → RESOLVED (bypass via direct argument)
- CKU₃: Hoeffding's lemma (~200 LOC calculus, not in Mathlib or Zhang)
- CKU₄: Fin m splitting for martingale decomposition (Mathlib piFinSuccAbove)
- CKU₅: CompressionScheme correct field — does it break downstream?
- CKU₆: universal_strictly_stronger_pac — rate-based separation statement design
- ~~CKU₇: VCDim ≤ LittlestoneDim~~ → RESOLVED (online_imp_pac PROVED)
- CKU₈: Generalized threshold class for arbitrary [Infinite X] via natEmbedding
- CKU₉ (NEW): D2 6-step assembly order and LOC budget (~205 LOC)
- CKU₁₀ (NEW): Rademacher d=0 Jensen bypass technique
- CKU₁₁ (NEW): compress_injective_on_labelings → pigeonhole completion

### UK (Suspected — 10 entries)
- UK₁: The finite partition approach may hit measurability issues for the product event {xs | ∀ i, c(xs i) = p i} — is this set MeasurableSet in the product sigma-algebra?
- UK₂: The Efron-Stein + Chebyshev route gives polynomial tail — is this sufficient for ALL downstream uses of HasUniformConvergence?
- UK₃: The EHKV tight constant (d-1)/(2ε) — is it achievable without Fano, perhaps via a direct counting argument with non-uniform distribution?
- UK₄: Does the universal_strictly_stronger_pac A5 repair (rate separation) have a clean Lean4 statement?
- UK₅: Can the Rademacher sorry 2 (EmpRad measurability) be bypassed by restructuring the integral definition?
- UK₆ (NEW): Birthday paradox bypass — does the direct combinatorial argument generalize to all sample sizes?
- UK₇ (NEW): Fin n measurability trick — does this pattern apply to all product-measure arguments in FLT_Proofs?
- UK₈ (NEW): Jensen bypass for d=0 — does the degenerate case need separate handling everywhere or just in Rademacher?

### UU (Boundary — 6 regions, unchanged from v2)
- UU₁: Whether BP₁-BP₈ are genuine or artifacts
- UU₂: Proof methods beyond M₁-M₁₂
- UU₃: Whether sorry DAG structure is invariant of the math
- UU₄: Constructive content of WithBot vs ℤ proofs
- UU₅: Lattice-theoretic automation potential
- UU₆: Whether 21 sorrys is a natural stopping point

## Measurement (v3)

### Synthesis Performance (observed, session 3)
| Tier | Expected | Observed | Notes |
|------|----------|----------|-------|
| Tier 0 (Immediately provable) | 80% | 90% | nfl_core ENNReal, empiricalError, etc. |
| Tier 1 (Conditional) | 50% | 60% | With proper KU resolution (e.g., 64ε) |
| Tier 2 (Keystone) | 30% | 40% | uc_imp_pac proved; concentration chain in progress |
| Tier 3 (Assembly) | 40% | 50% | Sauer-Shelah bridge, threshold class |
| Tier 4 (Blocked) | 10% | 15% | Γ₆₅ resolved; Γ₆₇ in progress |
| Tier 5 (Deep/Open) | 5% | 5% | EHKV, Moran-Yehudayoff, compression conjecture |

### Discovery Rate
- γ events: ~23+ new proofs this session (γ₄₀-γ₆₅)
- Γ events: 11 inquiries (Γ₆₅-Γ₇₅)
- A4 alarms: 2 (Γ₆₆ false statement, Γ₆₈ false conjunct)
- A5 repairs: 4 (growth_function_cover, Sauer-Shelah bound, pac_lower_bound constant, UniversalLearnable Measure.pi fix)
