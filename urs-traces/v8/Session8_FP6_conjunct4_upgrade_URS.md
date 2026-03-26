---
session: 8
date: 2026-03-26
task_id: FP6
target: fundamental_theorem conjunct 4 upgrade (sample_complexity_upper_of_pac_witness + sandwich)
file: FLT_Proofs/Theorem/PAC.lean
status: closed
---

## URS: FP6 — Conjunct 4 Upgrade (trivial → quantitative sandwich)

**Date**: 2026-03-26 | **File**: `FLT_Proofs/Theorem/PAC.lean`
**Target**: Replace trivially-true conjunct 4 of `fundamental_theorem` with quantitative sample complexity sandwich
**Status**: OPEN — 0 sorrys to close, 3 new theorems to add, 1 type change

### 0. Will

Current conjunct 4 (lines 238–243) says `PACLearnable X C → ∀ loss, ∃ mf, mf ε δ ≥ 1`. This is trivially proved by `mf = fun _ _ => 1` (line 255). The A4 alarm at line 251 flags this explicitly. We replace it with a real statement that extracts a PAC witness, proves the witness is an upper bound on `SampleComplexity`, and proves the NFL/VC lower bound on both `SampleComplexity` and the witness.

### 1. KK — What exists

| Lemma | File | Status |
|-------|------|--------|
| `SampleComplexity X C ε δ := sInf {m \| ∃ L, PAC at m}` | Generalization.lean:35 | ✅ |
| `sample_complexity_lower_bound` : `⌈(d-1)/2⌉ ≤ SampleComplexity` | GeneralizationResults.lean:207 | ✅ sorry-free |
| `pac_lower_bound_member` : `⌈(d-1)/2⌉ ≤ m` for PAC-valid m | Generalization.lean:2299 | ✅ sorry-free |
| `Nat.sInf_le` : `m ∈ S → sInf S ≤ m` | Mathlib | ✅ |
| `fundamental_theorem` conjuncts 1,2,3,5 | PAC.lean | ✅ (conjunct 2 has compression sorry, not our target) |
| `WellBehavedVC` available on `fundamental_theorem` | PAC.lean:231 | ✅ in scope |

### 2. Action Plan

**All edits in `FLT_Proofs/Theorem/PAC.lean` only.**

#### Phase 1: Insert `sample_complexity_upper_of_pac_witness` (after line 181, before `fundamental_vc_compression`)

```lean
/-- Any PAC witness (L, mf) gives an upper bound on SampleComplexity:
    the infimum is at most the witness sample size. -/
theorem sample_complexity_upper_of_pac_witness (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool)
    (L : BatchLearner X Bool) (mf : ℝ → ℝ → ℕ)
    (hPAC :
      ∀ (ε δ : ℝ), 0 < ε → 0 < δ →
        ∀ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D →
          ∀ c ∈ C,
            MeasureTheory.Measure.pi (fun _ : Fin (mf ε δ) => D)
              { xs : Fin (mf ε δ) → X |
                D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
                  ≤ ENNReal.ofReal ε }
              ≥ ENNReal.ofReal (1 - δ)) :
    ∀ (ε δ : ℝ), 0 < ε → 0 < δ →
      SampleComplexity X C ε δ ≤ mf ε δ := by
  intro ε δ hε hδ
  unfold SampleComplexity
  apply Nat.sInf_le
  exact ⟨L, fun D hD c hcC => hPAC ε δ hε hδ D hD c hcC⟩
```

**HC**: 0.15. Pure `Nat.sInf_le` application. ~15 LOC.

#### Phase 2: Insert `pac_sample_complexity_sandwich` (after Phase 1)

```lean
/-- Quantitative sample-complexity sandwich attached to any PAC witness.
    Packages: (1) PAC guarantee, (2) SampleComplexity ≤ mf,
    (3) NFL/VC lower bound on both SampleComplexity and mf. -/
theorem pac_sample_complexity_sandwich (X : Type u) [MeasurableSpace X]
    [MeasurableSingletonClass X]
    (C : ConceptClass X Bool)
    (hmeas_C : ∀ h ∈ C, Measurable h) (hc_meas : ∀ c : Concept X Bool, Measurable c)
    (hWB : WellBehavedVC X C) :
    PACLearnable X C →
      ∃ (L : BatchLearner X Bool) (mf : ℝ → ℝ → ℕ),
        (∀ (ε δ : ℝ), 0 < ε → 0 < δ →
          ∀ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D →
            ∀ c ∈ C,
              MeasureTheory.Measure.pi (fun _ : Fin (mf ε δ) => D)
                { xs : Fin (mf ε δ) → X |
                  D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
                    ≤ ENNReal.ofReal ε }
                ≥ ENNReal.ofReal (1 - δ)) ∧
        (∀ (ε δ : ℝ), 0 < ε → 0 < δ →
          SampleComplexity X C ε δ ≤ mf ε δ) ∧
        (∀ (d : ℕ), VCDim X C = d →
          ∀ (ε δ : ℝ), 0 < ε → ε ≤ 1 / 4 →
            0 < δ → δ ≤ 1 → δ ≤ 1 / 7 → 1 ≤ d →
            Nat.ceil ((d - 1 : ℝ) / 2) ≤ SampleComplexity X C ε δ ∧
            Nat.ceil ((d - 1 : ℝ) / 2) ≤ mf ε δ) := by
  intro hPAC
  rcases hPAC with ⟨L, mf, hmf⟩
  refine ⟨L, mf, hmf, ?_, ?_⟩
  · intro ε δ hε hδ
    exact sample_complexity_upper_of_pac_witness X C L mf hmf ε δ hε hδ
  · intro d hd ε δ hε hε1 hδ hδ1 hδ2 hd_pos
    have hlower :=
      sample_complexity_lower_bound X C d hd ε δ hε hε1 hδ hδ1 hδ2 hd_pos hmeas_C hc_meas hWB
    have hupper :=
      sample_complexity_upper_of_pac_witness X C L mf hmf ε δ hε hδ
    exact ⟨hlower, le_trans hlower hupper⟩
```

**HC**: 0.25. Composition of Phase 1 + `sample_complexity_lower_bound`. ~40 LOC.
**Key fix**: `hWB : WellBehavedVC X C` in signature — required by `sample_complexity_lower_bound`.

#### Phase 3: Edit `fundamental_theorem` conjunct 4

**Replace lines 238–243** (old conjunct 4 type):
```lean
    (PACLearnable X C →
      ∀ (loss : LossFunction Bool) [DecidableEq Bool],
        ∃ (mf : ℝ → ℝ → ℕ),
          ∀ (ε δ : ℝ), 0 < ε → 0 < δ →
            ∀ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D →
              mf ε δ ≥ 1) ∧
```

**With** (new conjunct 4 type):
```lean
    (PACLearnable X C →
      ∃ (L : BatchLearner X Bool) (mf : ℝ → ℝ → ℕ),
        (∀ (ε δ : ℝ), 0 < ε → 0 < δ →
          ∀ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D →
            ∀ c ∈ C,
              MeasureTheory.Measure.pi (fun _ : Fin (mf ε δ) => D)
                { xs : Fin (mf ε δ) → X |
                  D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
                    ≤ ENNReal.ofReal ε }
                ≥ ENNReal.ofReal (1 - δ)) ∧
        (∀ (ε δ : ℝ), 0 < ε → 0 < δ →
          SampleComplexity X C ε δ ≤ mf ε δ) ∧
        (∀ (d : ℕ), VCDim X C = d →
          ∀ (ε δ : ℝ), 0 < ε → ε ≤ 1 / 4 →
            0 < δ → δ ≤ 1 → δ ≤ 1 / 7 → 1 ≤ d →
            Nat.ceil ((d - 1 : ℝ) / 2) ≤ SampleComplexity X C ε δ ∧
            Nat.ceil ((d - 1 : ℝ) / 2) ≤ mf ε δ)) ∧
```

**Replace lines 251–255** (old conjunct 4 proof):
```lean
   -- Conjunct 4: PAC → ∃ mf ≥ 1. A4 NOTE: this conjunct is trivially true
   -- (take mf = fun _ _ => 1). The REAL content should be: mf achieves PAC
   -- AND mf ε δ ≥ (d/ε)(log(1/ε) + log(1/δ)). Current statement is A4-weak.
   -- ABD-R: strengthen to quantitative sample complexity bound.
   fun _ _ => ⟨fun _ _ => 1, fun _ _ _ _ _ _ => le_refl 1⟩,
```

**With**:
```lean
   pac_sample_complexity_sandwich X C hmeas_C hc_meas hWB,
```

**HC**: 0.10. One-line proof swap. ~5 LOC net.

### 3. Exclusive File Access

**WRITE**: `FLT_Proofs/Theorem/PAC.lean` only
**READ**: Any file
**DO NOT TOUCH**: Any other `.lean` file

### 4. Termination

- `lake build` passes with 0 errors
- `grep -n sorry FLT_Proofs/Theorem/PAC.lean` shows no new sorrys (existing compression sorry in `fundamental_vc_compression` unchanged)
- A4: conjunct 4 is no longer trivially true — it requires real content from `sample_complexity_lower_bound`
- A5: `fundamental_theorem` name unchanged, 5-way conjunction shape unchanged, conjuncts 1/2/3/5 unchanged

### 5. Guardrails

- A4/A5 checks after every edit
- MUST NOT introduce any new sorry
- Do not simplify — follow the given structure exactly
- Edit only PAC.lean
- Do NOT touch conjuncts 1, 2, 3, 5 of `fundamental_theorem`