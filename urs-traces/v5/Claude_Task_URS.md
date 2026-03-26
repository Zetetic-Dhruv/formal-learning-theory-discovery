# Claude Task URS — Proof Synthesis Protocol (v5, 2026-03-20)

## Task Identity

Close all actionable sorrys in FLT_Proofs. Produce the world's first discovery-oriented
formal learning theory kernel.

Current: 0 errors (when agents not mid-edit), ~20 sorry-using declarations (increased
from 15 due to decomposition of monolithic sorrys into structured proof chains).
Target: 0 errors, ≤6 sorry-using declarations (4 permanent + Moran-Yehudayoff + EHKV gap).

## Session 6 State Delta (v4 → v5)

### What changed
- **D_n narrative RETIRED.** Proof directions D1-D6 are replaced by task decomposition
  T1-T8, organized by the 3 meta-infrastructure problems they resolve.
- **6 research agents + 8 proof agents** ran this session. 1 full closure (Birthday),
  4 decompositions, 3 Gamma discoveries.
- **Coherence audit** confirmed 14/17 definitions correct. 2 definition-level issues
  (symmetric Rademacher, pac_lower_bound constant) discovered to be LOAD-BEARING BLOCKERS,
  not cosmetic.
- **Sorry count went UP** (15 → ~20) but proof DEPTH went DOWN: monolithic sorrys replaced
  by structured chains with independently-closable components.

### Key discovery: The 3 Meta-Problems
All open sorrys are blocked by exactly 3 meta-infrastructure problems:
- **MP1 (Gamma_92):** Uncountable C wall. Resolved by symmetrization ONLY.
- **MP2 (Definition coherence):** |corr| in EmpRad + weakened constant in pac_lower_bound.
  These A4 findings ARE the active blockers.
- **MP3 (Mathlib gaps):** No Fubini for Measure.pi. Massart lemma now PROVED by us.

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
Identify the M-type (M_1-M_16) before writing tactics. What mathematical METHOD
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

## Task Decomposition (T1-T8)

### T1: Fix EmpiricalRademacherComplexity definition (remove |·|)
**Meta-Problem:** MP2 (Definition coherence)
**File:** Rademacher.lean:206
**What:** Remove absolute value from inside sSup in EmpiricalRademacherComplexity.
  Current: `sSup { r | ∃ h ∈ C, r = |rademacherCorrelation h σ xs| }`
  Target: `sSup { r | ∃ h ∈ C, r = rademacherCorrelation h σ xs }`
**Why:** The |·| makes EmpRad the symmetric (two-sided) Rademacher complexity.
  Massart gives E[sup Z] ≤ σ√(2 log N), but E[sup |Z|] ≤ 2σ√(2 log N).
  The factor of 2 makes the stated bound in vcdim_bounds_rademacher_quantitative
  unprovable. This is Gamma_103.
**Downstream:** Propagates through RademacherComplexity, empRad_nonneg,
  empiricalRademacherComplexity_le_one, empRad_eq_one_of_all_labelings,
  vcdim_bounds_rademacher_quantitative, rademacher_lower_bound_on_shattered.
  Each needs signature/proof adjustment.
**LOC:** ~30 (definition change + downstream fixups)
**Unlocks:** T5 (Massart assembly)

### T2: Close symmetrization chain (3 sorrys)
**Meta-Problem:** MP1 (Gamma_92 — uncountable C wall)
**File:** Generalization.lean:1267-1400
**What:** Close 3 sorry'd components in the symmetrization proof of uc_bad_event_le_delta:
  - T2a: `symmetrization_reduction` (~70 LOC) — ghost sample + E[EmpErr(S')] = TrueErr + triangle
  - T2b: `double_sample_uc_bound` (~90 LOC) — condition on combined sample, GF(C,2m) patterns,
    Hoeffding per pattern. THIS IS WHERE GAMMA_92 IS RESOLVED.
  - T2c: Arithmetic assembly (~40 LOC) — thread factorial sample complexity through Hoeffding
**Why:** This is the ONLY viable route for uc_bad_event_le_delta (Routes A,B,D,E all blocked
  by Gamma_92/Gamma_98/Gamma_100). Proved by exhaustive route analysis.
**Unlocks:** VCDim→UC→PAC (fundamental theorem conjuncts 1,3), T6, T7, ESChebyshev

### T3: Wire EHKV infrastructure into pac_lower_bound (restore Ω(d/ε))
**Meta-Problem:** MP2 (Definition coherence)
**File:** PAC.lean:172 (statement), Generalization.lean (EHKV infrastructure)
**What:** Restore pac_lower_bound constant from ceil((d-1)/2) to ceil((d-1)/(64ε)).
  The EHKV/Fano machinery exists in counterfactual files (D3). Wire it in.
  Alternatively: keep Ω(d) bound, document as intentional (combinatorial bound only),
  add EHKV as future work.
**Why:** Current Ω(d) bound is eps-independent — dramatically weaker than textbook Ω(d/ε).
  A reviewer would flag this immediately.
**LOC:** ~50-100 depending on how much EHKV infrastructure needs porting

### T4: Close pac_lower_bound_core + pac_lower_bound_member
**Meta-Problem:** MP2 (constant) + visibility (`private nfl_counting_core`)
**File:** Generalization.lean:2000-2700
**What:** Two obstacles:
  - `nfl_counting_core` is `private` at line 3128, needs to be called from line 2086.
    Fix: remove `private` keyword (1-word edit).
  - Arithmetic: m < ceil((d-1)/2) → 2m < d. Straightforward Nat reasoning.
**LOC:** ~80 (mostly measure bridge, reusing vcdim_infinite_not_pac pattern)

### T5: Massart assembly (after T1)
**Meta-Problem:** MP2 (|corr|) + MP3 (sSup→Finset.sup' bridge)
**File:** Rademacher.lean:379-546
**What:** After T1 removes |·|, assemble the proved helpers into vcdim_bounds_rademacher_quantitative:
  - exp_mul_sup'_le_sum (PROVED)
  - cosh_le_exp_sq_half (PROVED)
  - rademacher_mgf_bound (PROVED)
  - finite_massart_lemma (PROVED)
  - empRad_le_sqrt_vc_log (sorry — needs sSup→Finset.sup' bridge + Sauer-Shelah constant fix)
**Remaining Gammas:**
  - Gamma_103: sSup→Finset.sup' bridge for uncountable C → finite restrictions (~60 LOC)
  - Gamma_104: Sauer-Shelah constant em/d vs 2m/d (need tighter bound or constant change)
**LOC:** ~100 after T1

### T6: Boosting proof (enabled by T2)
**Meta-Problem:** MP1 (concentration over C, resolved by T2 infrastructure)
**File:** Separation.lean:326
**What:** boost_two_thirds_to_pac. Majority vote of k copies + Chebyshev.
  The concentration infrastructure from T2 enables the per-block independence argument.
  Also blocked by measurability of L.learn (KU, not UU — resolvable by adding
  MeasurableSingletonClass or working with outer measure).
**LOC:** ~100

### T7: Advice elimination proof (enabled by T2)
**Meta-Problem:** MP1 (same concentration infrastructure as T6)
**File:** Extended.lean
**What:** advice_elimination. Sample split + run all advice values + validation selection.
  Shares infrastructure with T6 (BatchLearner construction, block_extract).
**LOC:** ~150

### T8: Moran-Yehudayoff compression (DEEP — deferred)
**File:** Generalization.lean:2295
**What:** VCDim finite → compression scheme exists. Requires minimax theorem on
  VC-dimension lattices. Estimated 60+ proof-days. Not on critical path for
  fundamental theorem publication (4/5 conjuncts close without it).
**Status:** Deferred. Correctly classified as deep/open.

## Priority Order

```
T1 (30 LOC, definition fix) ──→ T5 (100 LOC, Massart assembly)
                                     ↓
T2 (200 LOC, symmetrization) ──→ T6 (100 LOC, boosting)
                                ──→ T7 (150 LOC, advice)
                                ──→ Fund. Thm conjuncts 1,3
T4 (80 LOC, NFL, agent running)
T3 (50-100 LOC, EHKV wiring)
T8 (deferred)
```

**Critical path:** T1 → T5 and T2 → {T6, T7, Fund. Thm}. Both can proceed in parallel.
T1 is the highest-leverage single action (30 LOC unlocks Massart assembly).

## Error Recovery

- Compilation error → diagnose structural cause (CNA_8), NOT patch
- Proof fails → expand KU (Gate 3), identify which K/U transition is missing
- Statement wrong → A5 repair (the obstruction is often upstream)
- Agent fails → read output, identify what it LEARNED, feed to next attempt
- Context limit approaching → write SESSION_END_NOTES.md immediately (Gate 10)

## Gamma Ledger (Session 6)

| ID | Discovery | Source |
|----|-----------|--------|
| Gamma_92 | Representative-selection impossible for uncountable C. ALL direct union bound routes blocked. | D1-D5 research |
| Gamma_98 | One-sided consistent case ALSO faces Gamma_92. Route D (HasConsistentUC) blocked. | D1-D5 deep research |
| Gamma_99 | sample_complexity_upper_bound has Hoeffding/factorial bound mismatch | D1-D5 deep research |
| Gamma_100 | Route C (symmetrization) is the ONLY viable route for UC. A/B/D/E all blocked. | D1-D5 deep research |
| Gamma_101 | Cauchy-Schwarz CANNOT achieve sqrt(log N). Exponential-moment method NECESSARY for d≥2. | D6-Massart deep research |
| Gamma_102 | Factorial sample complexity vs Hoeffding concentration: (16/ε²)^v factor must be absorbed by factorial growth | D1-D5 symmetrization |
| Gamma_103 | Symmetric Rademacher (|corr|) creates factor-of-2 incompatibility with Massart bound. DEFINITION BLOCKER. | D6-Massart closure |
| Gamma_104 | Sauer-Shelah constant em/d vs 2m/d: standard bound insufficient for stated theorem | D6-Massart closure |
| Gamma_105 | Mathlib has Fubini for Measure.prod but NOT Measure.pi. Blocks E[EmpError]=TrueErrorReal. | ESChebyshev closure |
| Gamma_106 | All ESChebyshev remaining sorrys trace to Gamma_92 | ESChebyshev closure |
