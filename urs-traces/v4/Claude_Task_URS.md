# Claude Task URS — Proof Synthesis Protocol (v4, 2026-03-19)

## Task Identity

Close all 11 actionable sorrys in FLT_Proofs (excluding Extended.lean's 4 UU/permanent
sorrys). Produce the world's first discovery-oriented formal learning theory kernel.

Current: 0 errors, 15 sorry-using declarations.
Target: 0 errors, 4 sorry-using declarations (Extended.lean only).

## Pre-Flight Protocol (10 Gates — from URT R2)

### Gate 0: Will — Discovery over convergence
Attack hard proofs. Build rich structure. Never retreat to easy closes.
If stuck, expand ignorance geometry (Gate 3), don't compress it.

### Gate 1: Read URS State
Check this file + Claude_Noological_URS.md. Know what you know and don't know.

### Gate 2: A4 Anti-Triviality
Before any proof: is the conclusion trivially true? Check for True conclusions,
vacuous hypotheses, sorry-in-Prop. If trivially closable, flag — don't celebrate.

### Gate 3: A5 Anti-Simplification / Increase Ignorance
Never weaken a statement to make it provable. If a proof fails, articulate WHY
in KU/UK terms. The failure IS discovery.

### Gate 4: Metaprogram-First
Identify the M-type (M_1-M_12) before writing tactics. What mathematical METHOD
is this proof? Bridge? Contrapositive? Construction? Pipeline?

### Gate 5: Measurement
After proof: Pl (non-trivial?), Coh (composes?), Inv (stable?), Comp (what fraction?).

### Gate 6: Prior-Art Check
Before any sorry attempt: check Zhang, Google formal-ml, Mathlib for relevant lemmas.
Type bridges documented in PriorArt.lean.

### Gate 7: Build Check
After every Write/Edit: lake build. Only trust 0-error builds. CNA_13 prevention.

### Gate 8: A4/A5 Post-Build
After every clean build: check for trivially-true sorrys (A4) and simplifications (A5).
A5 supersedes A4.

### Gate 9: World Model Update
After every sorry closure or failure: update the K/U partition. Log gamma/Gamma events.

### Gate 10: Session Transfer
Before context limit: write SESSION_END_NOTES.md with exact state, discoveries,
and will for successor.

## 11 Actionable Sorrys — Exact Map

### D1: Concentration (2 sorrys)
| Sorry | File:Line | Metaprogram | Route | LOC Est |
|-------|-----------|-------------|-------|---------|
| union_bound_consistent | Generalization:692 | M_2+M_3 | Symmetrization: D^(2m) ghost sample, bound bad(xs) by 2*bad_sym(xs,xs'), conditioned on xs+xs' restrict to GF(C,2m) patterns, Hoeffding per pattern | ~200 |
| vcdim_finite_imp_uc | Generalization:1355 | M_2 | Symmetrization OR Efron-Stein+Chebyshev (~100 LOC). Not critical path (factorial bypass exists). Value: tighter sample complexity. | ~100-200 |

**Key insight (Gamma_65):** The covering format (sample-independent reps) is IMPOSSIBLE
for infinite C. Symmetrization gives a structurally different bound:
2*GF(C,2m)*exp(-me^2/8) instead of GF(C,m)*(1-e)^m. This changes the arithmetic
downstream but preserves the PAC conclusion.

**Decision needed:** Rewrite union_bound_consistent to use the symmetrization bound,
or add symmetrization as a separate lemma and route through it.

### D2: NFL / Lower Bound (3 sorrys share 1 core)
| Sorry | File:Line | Metaprogram | Route | LOC Est |
|-------|-----------|-------------|-------|---------|
| pac_lower_bound_core | Generalization:2083 | M_11 | Double-counting + pigeonhole on Fin m -> T. Substep A (combinatorial) already factored. | ~80 |
| pac_lower_bound_member | Generalization:2564 | M_11 | Same core as above, different setup. | ~60 |
| vcdim_infinite_not_pac | Generalization:2989+3004 | M_11+M_7 | Substep A (combinatorial) + Substep B (measure bridge). Both factored and sorry'd separately. | ~120 |

**Key insight (Gamma_67):** Using 1/(64e) constant (already in the statement).
**Shared core:** All 3 need the Measure.pi-of-uniformMeasure = counting/d^m bridge.
This should be factored as a shared lemma.

### D4: Cross-Paradigm (1 sorry)
| Sorry | File:Line | Metaprogram | Route | LOC Est |
|-------|-----------|-------------|-------|---------|
| boost_two_thirds_to_pac | Separation:415 | M_6 | Majority vote of k=ceil(8/delta) copies + Chebyshev/Chernoff. For delta >= 1/3, trivial (2/3 >= 1-delta). For delta < 1/3, recursive majority-of-3 with product measure independence. | ~100 |

**Agent D4v2 confirmed:** Genuinely needs ~100 LOC of Fin arithmetic.

### D5: Compression + Bridge (2 sorrys)
| Sorry | File:Line | Metaprogram | Route | LOC Est |
|-------|-----------|-------------|-------|---------|
| compression_bounds_vcdim | Bridge:674 | M_3 | Pure combinatorial inequality. CHECK: is 2^(2^k) > (k+1)*(2*2^k)^k TRUE for k>=1? If not, statement needs weakening. | ~30-50 |
| sample_complexity_upper_bound | Bridge:658 | M_2+M_7 | Routes through concentration chain. Blocked by D1? Or independently closable via mf-membership proof? | ~40 |

### D6: Rademacher (2 sorrys)
| Sorry | File:Line | Metaprogram | Route | LOC Est |
|-------|-----------|-------------|-------|---------|
| vcdim_bounds_rademacher_quantitative | Rademacher:435 | M_2+M_3 | Massart finite lemma via tensorized Hoeffding. Zhang's expected_max_subGaussian provides core. Chain with Sauer-Shelah. | ~150-210 |
| rademacher_vanishing_imp_pac | Rademacher:503 | M_1+M_2 | Contrapositive: VCDim=inf -> exists D where Rad doesn't vanish. Construct D with infinite support via shattered sets at all scales. Genuine difficulty: pointwise-in-D hypothesis. | ~130-190 |

### Permanent / Out-of-Scope (4 sorrys — DO NOT ATTEMPT)
| Sorry | File:Line | Reason |
|-------|-----------|--------|
| universal_strictly_stronger_pac (conj 2) | Separation:729 | FALSE (Gamma_68, Bousquet 2021) |
| natarajan_not_characterizes_pac | Separation:753 | UU: hyperbolic pseudo-manifolds |
| computational_hardness_pac | Extended:64 | UU: crypto infrastructure absent |
| unlabeled_not_implies_labeled | Extended:113 | UU: distribution-dependent compression |

## Attack Order

**Priority 1 (highest impact):** D2 NFL chain (3 sorrys from 1 core lemma)
- Factor the Measure.pi-of-uniformMeasure bridge as a shared lemma
- Close pac_lower_bound_core, pac_lower_bound_member, vcdim_infinite_not_pac

**Priority 2:** D4 boosting (1 sorry, unblocks universal_imp_pac chain)
- Majority vote construction + Chebyshev

**Priority 3:** D5 compression (2 sorrys)
- Check compression_bounds_vcdim statement first (CKU_3)
- sample_complexity_upper_bound may be independently closable

**Priority 4:** D1 concentration (2 sorrys, hardest)
- Symmetrization infrastructure is ~200 LOC and novel
- May also help D6

**Priority 5:** D6 Rademacher (2 sorrys, hardest)
- Massart via tensorized Hoeffding
- NFL Rademacher lower bound has genuine circularity

## Error Recovery

- Compilation error -> diagnose structural cause (CNA_8), NOT patch
- Proof fails -> expand KU (Gate 3), identify which K/U transition is missing
- Statement wrong -> A5 repair (Gamma_65 pattern: fix statement, not proof)
- Agent fails -> read output, identify what it LEARNED, feed to next attempt
- Context limit approaching -> write SESSION_END_NOTES.md immediately (Gate 10)

## Gamma Ledger (Session 4 — initialize empty)

| ID | Discovery | Status |
|----|-----------|--------|
| (to be filled during session) | | |
