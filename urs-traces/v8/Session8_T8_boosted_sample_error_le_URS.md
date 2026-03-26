---
session: 8
date: 2026-03-26
task_id: T8
target: boosted_sample_error_le_of_good_blocks
file: FLT_Proofs/Theorem/Separation.lean
status: closed
---

## T8: `boosted_sample_error_le_of_good_blocks` (line 819)

**File**: `FLT_Proofs/Theorem/Separation.lean`, line 819
**Scope**: Replace the `sorry` at line 819. Do not touch any other line.
**Dependencies**: T1 (`learn_measurable_fixed`), T7 (`majority_error_le_seven_rate_of_good_fraction`) — both proved.

### Current state (lines 803–819):

```lean
private lemma boosted_sample_error_le_of_good_blocks
    {X : Type u} [MeasurableSpace X]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (c : Concept X Bool) (hc_meas : Measurable c)
    (L : BatchLearner X Bool) (hL_meas : LearnEvalMeasurable L)
    (rate : ℕ → ℝ) (k n : ℕ)
    (ω : Fin (k * n) → X)
    (hk_pos : 0 < k)
    (hgoodfrac :
      7 * k ≤ 12 * (Finset.univ.filter (fun j => ω ∈ goodBlockEvent L D c rate k n j)).card) :
    D {x : X |
        boosted_majority k
          (fun j => L.learn
            (fun i => (block_extract k n ω j i, c (block_extract k n ω j i))) x) ≠ c x}
      ≤ ENNReal.ofReal (7 * max (rate n) 0) := by
  sorry
```

### Route

This is a thin wrapper that instantiates T7 (`majority_error_le_seven_rate_of_good_fraction`) with concrete choices:

- `hs j := L.learn (fun i => (block_extract k n ω j i, c (block_extract k n ω j i)))` — the hypothesis from block j
- `good := Finset.univ.filter (fun j => ω ∈ goodBlockEvent L D c rate k n j)` — the good blocks
- `ρ := max (rate n) 0` — non-negative rate (handles possible negative `rate n`)

### Proof sketch

```lean
  classical
  let hs : Fin k → Concept X Bool := fun j =>
    L.learn (fun i => (block_extract k n ω j i, c (block_extract k n ω j i)))

  let good : Finset (Fin k) :=
    Finset.univ.filter (fun j => ω ∈ goodBlockEvent L D c rate k n j)

  have hhs_meas : ∀ j : Fin k, Measurable (hs j) := by
    intro j
    exact learn_measurable_fixed L hL_meas
      (fun i => (block_extract k n ω j i, c (block_extract k n ω j i)))

  have hgooderr :
      ∀ j ∈ good, D {x : X | hs j x ≠ c x} ≤ ENNReal.ofReal (max (rate n) 0) := by
    intro j hj
    have hj' :
        D {x : X |
            L.learn (fun i => (block_extract k n ω j i, c (block_extract k n ω j i))) x ≠ c x}
          ≤ ENNReal.ofReal (rate n) := by
      simpa [good, goodBlockEvent] using hj
    exact le_trans hj' (ENNReal.ofReal_le_ofReal (le_max_left _ _))

  simpa [hs, good] using
    majority_error_le_seven_rate_of_good_fraction
      (D := D) (k := k) hk_pos
      (c := c) (hc_meas := hc_meas)
      (hs := hs) (hhs_meas := hhs_meas)
      (good := good) (hgoodfrac := hgoodfrac)
      (ρ := max (rate n) 0) (hρ := le_max_right _ _)
      hgooderr
```

### Key details

1. **`hhs_meas`**: Each `hs j` is measurable via `learn_measurable_fixed` (T1) applied to the labeled block extraction.

2. **`hgooderr`**: For `j ∈ good`, membership in `goodBlockEvent` gives `D{error} ≤ ofReal(rate n)`. Then `ofReal(rate n) ≤ ofReal(max (rate n) 0)` via `ENNReal.ofReal_le_ofReal (le_max_left _ _)`.

3. **The final `simpa`**: May need adjustment if the `let` bindings don't unfold cleanly. Fallback: use `exact` with explicit arguments and `show` to rewrite the goal.

4. **If `simpa` doesn't close**: Try:
```lean
  have := majority_error_le_seven_rate_of_good_fraction
    (D := D) (k := k) hk_pos c hc_meas hs hhs_meas good hgoodfrac
    (max (rate n) 0) (le_max_right _ _) hgooderr
  convert this using 2
  ext x; simp [hs]
```

### Estimated LOC: ~20

### Guardrails
- A4/A5 checks
- No new sorry
- Edit only line 819 (may expand to ~20 lines)
- Do not touch any other lemma