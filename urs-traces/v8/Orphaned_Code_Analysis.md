# Orphaned Code Analysis — Post Fundamental Theorem

## Context

After proving the fundamental theorem (PAC ↔ VCDim) sorry-free, the critical path
was rerouted through PRIMED versions of key theorems in Symmetrization.lean. The
original (unprimed) versions in Generalization.lean retain sorrys but are no longer
on the critical path.

## Orphaned Sorrys (3 of 7 total)

### 1. `uc_bad_event_le_delta` (Generalization.lean:878)
- **Original purpose**: UC bad-event bound composing symmetrization + arithmetic
- **Why orphaned**: Bypassed by `uc_bad_event_le_delta_proved` in Symmetrization.lean
- **Still called by**: `vcdim_finite_imp_uc` (unprimed) → `vcdim_finite_imp_pac_via_uc` (unprimed)
  → `uc_does_not_imply_online`, `consistent_learner_pac`, `sample_complexity_lower_bound`
- **Cannot delete**: Would break 4 downstream theorems in Generalization.lean
- **Migration path**: Redirect those 4 callers to use primed versions (requires adding [Infinite X] + hE_nullmeas)

### 2-3. `exchangeability_chain_bound` sorrys (Symmetrization.lean:1441, 1465)
- **Original purpose**: The swap→signed-avg connection + Tonelli chain
- **Why orphaned**: Critical path bypassed via `vcdim_finite_imp_uc'` which uses
  `uc_bad_event_le_delta_proved` (which uses `symmetrization_uc_bound` directly,
  not through the old `exchangeability_chain_bound` → `double_sample_pattern_bound` chain)
- **Still called by**: `double_sample_pattern_bound` (unprimed) → `symmetrization_uc_bound` (unprimed)
  → `vcdim_finite_imp_uc` (unprimed)
- **Cannot delete**: Same chain as #1

## Discovery & Inquiry Findings from the Orphaned Code

### γ₁₈: Sorry A (swap → signed average, Symm:1441)
- **Type**: Mathematical content (not elaboration)
- **What was needed**: Show `swap_fun σ z ∈ S` iff ∃h∈C with (1/m)∑sign(σ_i)·a_i(h,z) ≥ ε/2
- **Key insight**: The gap under coordinate-wise swap equals a Rademacher-weighted sum
  of loss differences. The loss differences a_i = indicator((z_i).2) - indicator((z_i).1)
  have |a_i| ≤ 1, enabling our `rademacher_mgf_bound`.
- **What `h_markov_bound` (PROVED) gives**: Per-pattern Chernoff bound
  #{σ | signed_avg ≥ ε/2} ≤ |SV| · exp(-mε²/8) from `rademacher_mgf_bound`
- **Missing link**: Decomposition by restriction patterns (≤ GF(C,2m) via
  `restriction_pattern_count`) + union bound (`Finset.card_biUnion_le`)
- **Estimated LOC to close**: ~40

### γ₁₉: Sorry B (Tonelli chain, Symm:1465)
- **Type**: Measure-theoretic infrastructure (not mathematical content)
- **Root cause**: `lintegral_finset_sum'` and `lintegral_indicator_one₀` require
  `NullMeasurableSet`, not `MeasurableSet`. For uncountable C, the event E is
  an uncountable union of measurable sets — not automatically measurable.
- **Resolution**: `finite_exchangeability_bound` theorem (60 LOC) using
  `NullMeasurableSet` + `MeasurePreserving.measure_preimage` + `AEMeasurable.indicator₀`
- **Key Mathlib APIs**: `lintegral_indicator_one₀`, `lintegral_finset_sum'`,
  `NullMeasurableSet.preimage`, `MeasurePreserving.quasiMeasurePreserving`
- **Structural finding**: The measurability of `{∃h∈C, |gap|≥ε}` for uncountable C
  is a genuine mathematical assumption, not a formalization artifact. The recent
  measurability paper confirms this. Resolution: add `NullMeasurableSet` hypothesis.

### Γ₉: "Can the Tonelli chain work with MeasurableSet?"
- **Answer**: NO for uncountable C. YES with NullMeasurableSet.
- **Evidence**: 3 agent failures + mathematical analysis + user's private evidence
  (measurability paper, Lean4/Mathlib API verification)
- **Impact**: Led to the `finite_exchangeability_bound` architecture

### Γ₁₀: "Can Sorry A be closed without the full pattern decomposition?"
- **Answer**: NO. The GF(C,2m) factor requires decomposition by restriction patterns.
  A trivial |SV| bound gives 2^m, not GF.
- **Evidence**: 3 agent attempts at direct union bound all failed
- **Impact**: The proved version uses a DIFFERENT architecture (primed versions)
  that composes T4+T5 directly instead of going through the old SL3 chain

## Recommended Migration (Future Work)

To eliminate all orphaned sorrys:
1. Add `[Infinite X]` + `hE_nullmeas` to `vcdim_finite_imp_uc` (unprimed)
2. Redirect its body to call `uc_bad_event_le_delta_proved`
3. Or: redirect all 4 downstream callers to use primed versions
4. Then: delete `uc_bad_event_le_delta`, `exchangeability_chain_bound` (old),
   `double_sample_pattern_bound` (old), `symmetrization_uc_bound` (old)
5. Estimated effort: ~30 LOC of signature changes
