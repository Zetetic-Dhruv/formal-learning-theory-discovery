# Recovery URS v2: Rademacher.lean Restoration (Route R5)

## Identity
- **File**: `FLT_Proofs/Complexity/Rademacher.lean`
- **Meta-Problem**: Recovery from fractured working tree — 2 surgical fixes on an otherwise mature file
- **M-type**: M-Splice (reinsert missing theorem + insert birthday proof)
- **LOC estimate**: ~60 lines inserted (56 for HEAD theorem + ~160 for birthday proof)
- **Starting point**: Current working tree (stash `64cdbbc`, 1208 lines, 1 sorry, 2 build errors)

## Route Selection

### Route R5 (SELECTED): Fix current working tree in-place (2 surgical insertions)

The current working tree already contains:
- ✅ T1 fix (|·| removed from definition)
- ✅ 3 T1 helper lemmas (rademacherCorrelation_le_one, sum_boolToSign_eq_zero, sum_rademacherCorrelation_eq_zero)
- ✅ T1-adapted consumers (empRad_nonneg, empiricalRademacherComplexity_le_one, empRad_eq_one_of_all_labelings)
- ✅ T1-adapted VCDim=0 proof (uses Rademacher symmetry instead of Cauchy-Schwarz)
- ✅ 5 proved Massart/Sauer-Shelah helpers (~240 LOC sorry-free infrastructure)
- ❌ `vcdim_bounds_rademacher_quantitative` MISSING (T5 deleted it during restructure)
- ❌ Birthday sorry still at line 922

**Only 2 operations needed.** This preserves ALL proved infrastructure.

### Route R1 (SUPERSEDED): Replay T1 edits on HEAD
Would lose 240 LOC of proved Massart helpers. Requires 13 sequential edits. Higher risk, lower payoff.

### Route R2 (SUPERSEDED): Splice sections
No longer needed — the working tree IS the splice target, just with 2 holes.

## Source Inventory

### Source A: Current working tree (stash `64cdbbc`) — 1208 lines, 1 sorry, BROKEN
```
Lines 1-420:     T1-fixed definitions + 3 new helpers (CORRECT, PROVED)
Lines 421-721:   T5 Massart expansion: 5 proved helpers (CORRECT, PROVED)
Lines 722:       MISSING: vcdim_bounds_rademacher_quantitative (BUILD ERROR)
Lines 723-922:   Birthday section (sorry at 922)
Lines 923-1208:  VCDim=0 + vanishing (T1-adapted, CORRECT)
  Line 1190:     References vcdim_bounds_rademacher_quantitative (BUILD ERROR)
```

### Source B: HEAD (`24fadb5`) theorem to reinsert — 56 lines
```
Lines 379-435:   /-! ## VCDim → Rademacher bound -/ + vcdim_bounds_rademacher_quantitative (sorry)
```

### Source C: Birthday proof from agent transcripts — ~160 lines
```
3-phase proof: measure transfer → collision bound → ENNReal→ℝ transfer
```

## AMRT K/U Decomposition

### KK (Verified known)
- **KK₁**: All 5 Massart helpers are T1-compatible — NONE reference `rademacherCorrelation`. They work with abstract `boolToSign` sums, `Finset.sup'`, and sub-Gaussian bounds. Verified by research agent.
- **KK₂**: HEAD's `vcdim_bounds_rademacher_quantitative` (lines 379-435) has a section header + theorem declaration + sorry. The theorem's TYPE references `RademacherComplexity`, `VCDim`, `Real.sqrt`, `Real.log` — all unchanged between HEAD and working tree.
- **KK₃**: The splice point for reinserting the theorem is CLEAN. Working tree line 721 ends `sauer_shelah_exp_bound`, line 723 begins `/-! ## Rademacher ↔ PAC -/`. HEAD's theorem goes between them. No name conflicts.
- **KK₄**: Birthday proof does NOT reference `rademacherCorrelation` or `EmpiricalRademacherComplexity`. It works with `μ`, `μ_sub`, `D_sub`, ENNReal arithmetic. Fully T1-agnostic.
- **KK₅**: Birthday proof variables (φ, μ_sub, D_sub, hT_large, etc.) are defined in `rademacher_lower_bound_on_shattered` (working tree lines 758-921), which is UNCHANGED between HEAD, stash, and all agent versions.
- **KK₆**: The reference at line 1190 (`vcdim_bounds_rademacher_quantitative`) will resolve once the theorem is reinserted. The theorem signature in HEAD matches what line 1190 expects (same argument order: X C D m hm d hd hd_pos hdm).
- **KK₇**: After both fixes, expected sorry count = 2 (vcdim_bounds_rademacher_quantitative + birthday). Wait — the birthday fix would make it 1. Let me re-check: current working tree has 1 sorry (line 922 = birthday). Reinserting the theorem adds 1 sorry. Birthday fix removes 1 sorry. Net: 1 sorry (vcdim_bounds_rademacher_quantitative only).

### KU (Articulated unknowns)
- **KU₁**: Does HEAD's `vcdim_bounds_rademacher_quantitative` statement need T1-adaptation? The HEAD version references `RademacherComplexity X C D m` — which is defined as `∫ EmpiricalRademacherComplexity X C xs ∂pi`. After T1, EmpRad uses `corr` not `|corr|`, so the MEANING of RademacherComplexity changed. But the LEAN TYPE is unchanged. The sorry absorbs the semantic change.
  **Resolution**: No adaptation needed. The theorem statement is type-correct. The sorry makes the proof obligation reflect the new (correct) definition.
- **KU₂**: Does HEAD's theorem have comments that reference `|corr|`? Yes — HEAD line 386 says "EmpRad(xs) ≤ B for all xs [Massart + Sauer-Shelah]" and lines around it discuss the proof structure. These comments are outdated after T1 but harmless. We can update them or leave them.
  **Resolution**: Leave comments as-is for now. They don't affect compilation.
- **KU₃**: The birthday proof from agents a3af + a199 was composed across MULTIPLE edits. Does the composite proof match the 7591-char version extracted at transcript L2238?
  **Resolution**: The L2238 extraction IS the composite. Use that exact version.

### UK (Pressures)
- **UK₁**: The import `import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series` was added by T5 for `cosh_le_exp_sq_half`. HEAD doesn't have it. The working tree does. If this import causes issues (version mismatch, slow elaboration), it could surface later.
  **Mitigation**: The import was present in a building state at L1282. It works with current Mathlib.

### UU (Boundary)
- None. This is pure engineering.

## Measurements

| Metric | Value | Justification |
|--------|-------|---------------|
| Pl | 0.98 | Both insertions are exact replays of verified content. The working tree was at L1282 build state. |
| Coh | 0.95 | Theorem reinsertion fills the exact hole causing the build error. Birthday proof is self-contained. |
| Inv | 0.95 | Standard textbook definitions + proved infrastructure. |
| Comp | Working tree: 0.85 → after Step 1: 0.90 → after Step 2: 0.95 | Incremental, each step independently valuable. |
| HC | 0.05 | No paradigm joint crossing. 2 copy-paste operations. Lowest possible hardness. |

## File Outline: Recovery Target (1264 lines, 1 sorry)

```
SECTION 1: Infrastructure (Lines 1-420) [SOURCE: Working tree, UNCHANGED]
  Lines 1-5:       Copyright header
  Lines 6-13:      Imports (includes Trigonometric.Series for T5)
  Lines 14-55:     boolToSign + SignVector infrastructure (PROVED)
  Lines 56-177:    flipAt + rademacher_variance infrastructure (PROVED)
  Lines 179-205:   rademacherCorrelation + rademacherCorrelation_abs_le_one (PROVED)
  Lines 207-213:   EmpiricalRademacherComplexity (T1: |·| REMOVED)
  Lines 215-219:   rademacherCorrelation_le_one (T1: NEW, PROVED)
  Lines 221-253:   empiricalRademacherComplexity_le_one (T1: adapted, PROVED)
  Lines 255-259:   RademacherComplexity def
  Lines 261-284:   sum_boolToSign_eq_zero + sum_rademacherCorrelation_eq_zero (T1: NEW, PROVED)
  Lines 286-314:   empRad_nonneg (T1: REWRITTEN with symmetry, PROVED)
  Lines 316-347:   rademacherComplexity_le_one + nonneg + gen_bound (PROVED)
  Lines 349-380:   corr_eq_one_of_agree + shatters_subset (PROVED)
  Lines 382-419:   empRad_eq_one_of_all_labelings (T1: adapted, PROVED)

SECTION 2: Massart Helpers (Lines 421-721) [SOURCE: Working tree, UNCHANGED]
  Lines 421:       /-! ## Helpers for VCDim → Rademacher bound -/
  Lines 423-429:   exp_mul_sup'_le_sum (PROVED)
  Lines 431-435:   cosh_le_exp_sq_half (PROVED)
  Lines 437-519:   rademacher_mgf_bound (~80 LOC, PROVED)
  Lines 521-665:   finite_massart_lemma (~140 LOC, PROVED)
  Lines 667:       /-! ## Sauer-Shelah exponential bound -/
  Lines 669-721:   sauer_shelah_exp_bound (PROVED)

SECTION 3: VCDim → Rademacher (Lines 722-778) [SOURCE: HEAD lines 379-435, INSERTED]
  Lines 722:       /-! ## VCDim → Rademacher bound -/
  Lines 724-778:   vcdim_bounds_rademacher_quantitative (sorry — T5 target)

SECTION 4: Rademacher ↔ PAC (Lines 779-~1000) [SOURCE: Working tree + birthday fix]
  Lines 779:       /-! ## Rademacher ↔ PAC -/
  Lines 781-804:   empRad_eq_one_of_injective_in_shattered (PROVED)
  Lines 806-~980:  rademacher_lower_bound_on_shattered (BIRTHDAY PROOF INSERTED, PROVED)
  Lines ~982-1002: rademacher_vanishing_imp_pac (PROVED)

SECTION 5: VCDim=0 + Vanishing (Lines ~1003-~1264) [SOURCE: Working tree, UNCHANGED]
  Lines ~1003-1033: vcdim_zero_concepts_agree (PROVED)
  Lines ~1035-1103: vcdim_zero_rademacher_le_inv_sqrt (T1: REWRITTEN with symmetry, PROVED)
  Lines ~1105-1178: analytical_log_sqrt_bound (PROVED)
  Lines ~1180-1264: vcdim_finite_imp_rademacher_vanishing (PROVED, references vcdim_bounds_rademacher_quantitative)
```

**Final state**: ~1264 lines, 1 sorry (vcdim_bounds_rademacher_quantitative), 0 errors.

## Action Space (2 operations)

### Step 1: Reinsert vcdim_bounds_rademacher_quantitative
**Source**: HEAD (`24fadb5`) lines 379-435
**Target**: Insert between working tree line 721 (sauer_shelah_exp_bound end) and line 723 (PAC section)
**Operation**: Edit tool — old_string = lines ending sauer_shelah + PAC header, new_string = same with theorem inserted between
**Verification**: `grep "vcdim_bounds_rademacher_quantitative"` matches, `grep -c sorry` = 2

### Step 2: Insert birthday proof
**Source**: Transcript L2238 extraction (7591-char proof)
**Target**: Replace sorry at the `suffices h_birthday` block
**Operation**: Edit tool — old_string = comment block + sorry, new_string = birthday proof
**Verification**: `grep -c sorry` = 1 (only vcdim_bounds_rademacher_quantitative)

### Step 3: Build check
**Command**: `lake build`
**Expected**: 0 errors, 1 sorry-using declaration (vcdim_bounds_rademacher_quantitative)

## Counterproof Analysis

### CP1: "HEAD theorem statement incompatible with working tree definitions"
**Disproof**: HEAD's theorem references `RademacherComplexity X C D m` (type: ℝ), `VCDim X C` (type: ℕ∞), `Real.sqrt`, `Real.log`. All exist unchanged in working tree. The theorem's Lean TYPE is identical. Only the MEANING of RademacherComplexity changed (now one-sided), which is absorbed by the sorry.

### CP2: "Reinsertion disrupts Massart helpers"
**Disproof**: The theorem is inserted AFTER all Massart helpers (after line 721, after sauer_shelah_exp_bound end). The helpers don't reference the theorem. No backward dependency.

### CP3: "Birthday proof won't work after Massart insertion shifts line numbers"
**Disproof**: We use string matching (Edit tool), not line numbers. The birthday `suffices h_birthday...sorry` block is unique in the file.

### CP4: "Import Trigonometric.Series breaks with current Mathlib"
**Mitigation**: This import was present in the L1282 golden build (8 sorrys, 0 errors). If Mathlib updated since then, we diagnose at Step 3.

### CP5: "sauer_shelah_exp_bound has typeclass error (Nat.choose_le_pow_div)"
**CRITICAL CHECK**: The research agent found this theorem at stash lines 675-721 as PROVED. But the build errors showed "line 696: typeclass instance problem is stuck" — which is INSIDE sauer_shelah_exp_bound. There is a contradiction.
**Resolution**: The build error at line 696 was from the CURRENT working tree state, which includes my manual T1 edits from earlier this session (the `replace_all` that changed `|rademacherCorrelation|` references inside comments and proofs). The stash `64cdbbc` version may be different from what's currently on disk. MUST verify by checking `git diff` of current working tree against stash.
**Mitigation**: If sauer_shelah_exp_bound breaks, we can drop it (it's the bridge to the main theorem, not the proved helpers). The 4 core helpers (exp_mul_sup'_le_sum, cosh_le_exp_sq_half, rademacher_mgf_bound, finite_massart_lemma) are the priority.

### CP6: "The working tree was modified by my earlier manual edits and no longer matches stash"
**CRITICAL**: Earlier in this session I ran `git checkout 64cdbbc -- lean4/FLT_Proofs/Complexity/Rademacher.lean` which restored the stash, but THEN I made manual edits (L2435-L2464: replace_all on |rademacherCorrelation|, empRad_nonneg rewrite, etc.). The current file may be stash + my broken manual edits.
**Resolution**: Check `git diff 64cdbbc -- lean4/FLT_Proofs/Complexity/Rademacher.lean`. If non-empty, restore the pure stash first.

## Verification Restriction

**Total action space**: 2-3 operations (restore clean stash if needed, reinsert theorem, insert birthday)
**Invariant**: Build after each step. Expected sorry progression: 1 → 2 → 1.
**Revert**: `git checkout 64cdbbc -- lean4/FLT_Proofs/Complexity/Rademacher.lean` (restores pure stash)
**Backup**: `cp Rademacher.lean Rademacher.lean.bak` before any edit

**No git commits until user says so.**
