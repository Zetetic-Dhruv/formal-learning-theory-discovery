# Repo Task URS — FLT_Proofs Sorry Replacement Pipeline (v3, 2026-03-19)

## Task Identity
**Core mission:** Replace every `sorry` in FLT_Proofs with a correct, non-trivial proof.
**Current state:** 0 errors, ~19 sorry-using declarations (agents actively reducing). Session 3: 33 → 19.

## 6 Independent Directions (fully researched)

### D1: Concentration Chain (CRITICAL PATH — 3 sorrys)
**Theorems:** growth_function_cover → union_bound_consistent → vcdim_finite_imp_pac_direct
**Proof route:** Finite partition over Fin m → Bool (NOT measurable selection). Bad event = ⋃_{p : pattern} {xs | c agrees with p on xs}. At most GrowthFunction patterns are occupied. Each consistency event ≤ (1-ε)^m by consistent_tail_bound. Union bound closes.
**Agent status:** D1 agent launched with finite partition URS.

### D2: NFL / Lower Bound (3 sorrys share 1 core)
**Theorems:** pac_lower_bound_core, pac_lower_bound_member, (nfl_per_sample_shattered → vcdim_infinite_not_pac)
**Γ₆₇:** Constant (d-1)/(2ε) is 32× tighter than standard NFL averaging achieves. Standard proof gives (d-1)/(64ε).
**Proof route:** Weaken to 1/(64ε). Then m < d/64 → 2m < d → nfl_core on ↥T. Pairing argument gives E[error] > 1/4. Reversed Markov: Pr[error ≤ 1/8] ≤ 6/7.
**EHKV skeleton:** New file EHKV.lean for the tight bound via Fano's inequality (future work).
**Agent status:** D2 agent launched.

### D3: Uniform Convergence (1 sorry — secondary route)
**Theorem:** vcdim_finite_imp_uc
**Γ₆₉:** TWO routes identified:
  - Efron-Stein + Chebyshev: ~100 LOC, LOW difficulty. Uses Zhang's PROVED efronStein directly. Polynomial tail (1/t²).
  - Full McDiarmid: ~600 LOC, HIGH difficulty. Hoeffding's lemma (~200 LOC calculus) NOT in Mathlib or Zhang. Exponential tail.
**Zhang type compatibility:** IDENTICAL (Measure.pi, IsProbabilityMeasure). Zero bridge needed for efronStein.
**Recommendation:** Efron-Stein + Chebyshev NOW, McDiarmid LATER.

### D4: Cross-Paradigm Bridges (2 sorrys remaining)
**online_imp_pac: PROVED** via adversary argument (VCDim ≤ LittlestoneDim + LTree construction).
**universal_imp_pac: PROVED** (structural, contrapositive NFL on shattered sets). UniversalLearnable FIXED (Gamma48 → Measure.pi).
**pac_not_implies_online: PROVED** via threshold class construction.
**ex_not_implies_pac: PROVED** (~80 lines).
**Γ₆₈: universal_strictly_stronger_pac conjunct 2 is FALSE.** Bousquet et al. STOC 2021 trichotomy: every concept class IS universally learnable at some rate. Citation: arXiv:2011.04483. Needs A5 repair (rate-based separation) or retraction.
**uc_does_not_imply_online:** Generalize threshold class from ℕ to arbitrary [Infinite X] via Infinite.natEmbedding.

### D5: Compression (4 sorrys)
**Γ₅₉:** CompressionScheme lacks correctness field → M-DefinitionRepair.
**Proof route:** Add `correct` field (A5-valid enrichment). Then pigeonhole: 2^n labelings vs C(n,k)·2^k compressions.
**Agent status:** D5 agent launched.

### D6: Rademacher + Extended (5 sorrys)
**Complete NL proofs available for all 3 Rademacher sorrys:**
  - Sorry 1 (Massart B<1): MGF → Massart finite lemma → Sauer-Shelah. Zhang's expected_max_subGaussian provides core. ~130-210 LOC. HARD.
  - Sorry 2 (vanishing→PAC): Contrapositive via shattered sample gives EmpRad=1. ~130-190 LOC. VERY HARD (measurability).
  - Sorry 3 (VCDim<⊤→vanishing): Chain sorry 1 + log(x)≤√x (Mathlib log_le_rpow_div EXISTS). ~75-125 LOC. MEDIUM-HARD.
**Extended:** computational_hardness (crypto), unlabeled (deep). Leave for later.

## Sorry Inventory (21 declarations)

| # | File | Theorem | Direction | Difficulty |
|---|------|---------|-----------|------------|
| 1 | Generalization | growth_function_cover | D1 | Medium |
| 2 | Generalization | union_bound_consistent | D1 | Medium |
| 3 | Generalization | vcdim_finite_imp_pac_direct | D1 | Medium |
| 4 | Generalization | vcdim_finite_imp_uc | D3 | Medium (Efron-Stein) |
| 5 | Generalization | uc_does_not_imply_online | D4 | Medium |
| 6 | Generalization | pac_lower_bound_core | D2 | Medium (with 64ε) |
| 7 | Generalization | compression_imp_vcdim_finite | D5 | Medium |
| 8 | Generalization | pac_lower_bound_member | D2 | Medium |
| 9 | Generalization | nfl_per_sample_shattered | D2 | Hard |
| 10 | Generalization | vcdim_infinite_not_pac | D2 | Hard |
| 11 | Separation | online_imp_pac | D4 | Medium |
| 12 | Separation | universal_imp_pac | D4 | Hard |
| 13 | Separation | universal_strictly_stronger_pac | D4 | FALSE (Γ₆₈) |
| 14 | Separation | natarajan_not_characterizes_pac | D4 | Hard |
| 15 | Rademacher | vcdim_bounds_rademacher_quantitative | D6 | Hard |
| 16 | Rademacher | rademacher_vanishing_imp_pac | D6 | Very Hard |
| 17 | Rademacher | vcdim_finite_imp_rademacher_vanishing | D6 | Medium-Hard |
| 18 | Bridge | sample_complexity_upper_bound | D2 | Medium |
| 19 | Bridge | compression_bounds_vcdim | D5 | Medium |
| 20 | Extended | computational_hardness_pac | D6 | Deep |
| 21 | Extended | unlabeled_not_implies_labeled | D6 | Deep |

## Wave Progress

### Wave 2: Infrastructure — COMPLETE
All infrastructure sorrys closed. consistent_tail_bound, prob_compl_ge_of_le, uniformMeasure_isProbability, empiricalError_bounded_diff, nfl_core, erm_consistent_realizable all proved.

### Wave 3: Keystones
- uc_imp_pac: PROVED
- vcdim_finite_imp_pac_direct: sorry only at concentration chain (D1 agent active)

### Wave 4: Cross-Paradigm
- online_imp_pac: PROVED (adversary argument)
- universal_imp_pac: PROVED (structural, contrapositive)
- pac_not_implies_online: PROVED (threshold class)
- ex_not_implies_pac: PROVED

### Wave 5: Bridge Theorems
- Sauer-Shelah: PROVED (bridge chain, 4 lemmas in Bridge.lean)
- fundamental_rademacher: assembles from proved components

### Wave 6: Deep/Open Sorrys
All 5 UU-boundary sorrys documented with citations. computational_hardness_pac (crypto), unlabeled_not_implies_labeled (distribution-dependent), natarajan_not_characterizes_pac (Moran-Yehudayoff), sample_complexity_upper_bound (Brukhim), universal_strictly_stronger_pac (FALSE — Bousquet 2021).

## γ-Ledger (Session 3 Discoveries)

| ID | Discovery | Session |
|----|-----------|---------|
| γ₄₀-γ₅₀ | Infrastructure proofs: consistent_tail_bound, prob_compl_ge_of_le, uniformMeasure, nfl_core, uc_imp_pac, erm_consistent_realizable, etc. | S3 |
| γ₅₁-γ₅₅ | Threshold class construction: VCDim≤1, LDim=⊤ (~180 lines sorry-free) | S3 |
| γ₅₆-γ₅₉ | ex_not_implies_pac, Sauer-Shelah bridge chain, BP₄ first-principles bridge | S3 |
| γ₆₀-γ₆₂ | online_imp_pac (adversary), universal_imp_pac (structural), UniversalLearnable fix (Measure.pi) | S3 |
| γ₆₃-γ₆₅ | ESChebyshev.lean + McDiarmid.lean counterfactual files, compression pigeonhole setup | S3 |

## Γ-Ledger (Session 3 Inquiry Events)

| ID | Inquiry | Status |
|----|---------|--------|
| Γ₆₅ | growth_function_cover unprovable for infinite C → sample-dependent fix | RESOLVED |
| Γ₆₆ | Sauer-Shelah `C(m,d)` was FALSE → corrected to `Σ C(m,i)` | RESOLVED |
| Γ₆₇ | pac_lower_bound `(d-1)/(2ε)` needs EHKV/Fano for tight constant | OPEN (agent weakening to 64ε) |
| Γ₆₈ | universal_strictly_stronger_pac conjunct 2 FALSE (Bousquet 2021) | CONFIRMED FALSE — documented |
| Γ₆₉ | Efron-Stein+Chebyshev gives UC in ~100 LOC vs McDiarmid ~600 LOC | RESOLVED (use ES+C) |
| Γ₇₀ | UniversalLearnable used Gamma48 instead of Measure.pi | RESOLVED (fixed) |
| Γ₇₁ | online_imp_pac requires adversary_from_shatters construction | RESOLVED (proved) |
| Γ₇₂ | D2 PAC chain requires 6-step assembly (~205 LOC) | OPEN (agent running) |
| Γ₇₃ | Rademacher d=0 case needs Jensen bypass | OPEN (agent running) |
| Γ₇₄ | Birthday paradox bypass for collision-free samples | OPEN (agent running) |
| Γ₇₅ | Compression pigeonhole from compress_injective_on_labelings | OPEN (agent running) |

## Sorry Inventory (~19 declarations, agents reducing)

| # | File | Theorem | Direction | Status |
|---|------|---------|-----------|--------|
| 1 | Generalization | growth_function_cover | D1 | Agent (D1) |
| 2 | Generalization | union_bound_consistent | D1 | Agent (D1) |
| 3 | Generalization | vcdim_finite_imp_pac_direct | D1 | Agent (D1) |
| 4 | Generalization | vcdim_finite_imp_uc | D3 | Counterfactual files created |
| 5 | Generalization | uc_does_not_imply_online | D4 | Open |
| 6 | Generalization | pac_lower_bound_core | D2 | Agent (D2) |
| 7 | Generalization | compression_imp_vcdim_finite | D5 | Agent (D5) |
| 8 | Generalization | pac_lower_bound_member | D2 | Agent (D2) |
| 9 | Generalization | nfl_per_sample_shattered | D2 | Agent (D2) |
| 10 | Generalization | vcdim_infinite_not_pac | D2 | Agent (D2) |
| ~~11~~ | ~~Separation~~ | ~~online_imp_pac~~ | ~~D4~~ | **PROVED** |
| ~~12~~ | ~~Separation~~ | ~~universal_imp_pac~~ | ~~D4~~ | **PROVED** |
| 13 | Separation | universal_strictly_stronger_pac | D4 | FALSE (Gamma68) |
| 14 | Separation | natarajan_not_characterizes_pac | D4 | UU (Moran-Yehudayoff) |
| 15 | Rademacher | vcdim_bounds_rademacher_quantitative | D6 | Agent (D6) |
| 16 | Rademacher | rademacher_vanishing_imp_pac | D6 | Agent (D6) |
| 17 | Rademacher | vcdim_finite_imp_rademacher_vanishing | D6 | Agent (D6) |
| 18 | Bridge | sample_complexity_upper_bound | D2 | UU (Brukhim) |
| 19 | Bridge | compression_bounds_vcdim | D5 | Agent (D5) |
| 20 | Extended | computational_hardness_pac | D6 | UU (crypto) |
| 21 | Extended | unlabeled_not_implies_labeled | D6 | UU (dist-dependent) |

## Active Agents
- D1: aa6890f7822d18d44 (concentration chain)
- D2: ab3dc6bcea908f015 (NFL constant + EHKV, 6-step ~205 LOC)
- D5: a3eb236d5807af824 (compression repair + pigeonhole)
- D6: (Rademacher — Massart, birthday+EmpRad, d=0 Jensen bypass)
