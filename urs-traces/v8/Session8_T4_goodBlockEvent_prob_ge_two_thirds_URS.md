---
session: 8
date: 2026-03-26
task_id: T4
target: goodBlockEvent_prob_ge_two_thirds
file: FLT_Proofs/Theorem/Separation.lean
status: closed
---

## T4: `goodBlockEvent_prob_ge_two_thirds` (line 503)

**File**: `FLT_Proofs/Theorem/Separation.lean`, line 503
**Scope**: Replace the `sorry` at line 503. Do not touch any other line.
**Dependencies**: T3 (`map_block_extract_eq_pi`, just proved). Also uses `measurableSet_goodBlock_A` (T0, proved) and `block_extract_measurable` (Generalization.lean).

### Current state (lines 485–503):

```lean
private lemma goodBlockEvent_prob_ge_two_thirds
    {X : Type u} [MeasurableSpace X]
    (C : ConceptClass X Bool)
    (L : BatchLearner X Bool) (hL_meas : LearnEvalMeasurable L) (rate : ℕ → ℝ)
    (huniv : ∀ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D →
      ∀ (c : Concept X Bool), c ∈ C →
        ∀ (m : ℕ),
          MeasureTheory.Measure.pi (fun _ : Fin m => D)
            { xs : Fin m → X |
              D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
                ≤ ENNReal.ofReal (rate m) }
            ≥ ENNReal.ofReal (2/3))
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (c : Concept X Bool) (hcC : c ∈ C) (hc_meas : Measurable c)
    (k n : ℕ) (j : Fin k) :
    (MeasureTheory.Measure.pi (fun _ : Fin (k * n) => D))
      (goodBlockEvent L D c rate k n j)
      ≥ ENNReal.ofReal (2/3) := by
  sorry
```

### What we need to show

`D^{k*n}(goodBlockEvent j) ≥ 2/3`

### Route (3 steps)

**Step 1**: Show `goodBlockEvent j` is a preimage of `A` under `block_extract`:

```lean
  let A : Set (Fin n → X) :=
    { xs : Fin n → X |
        D { x : X | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
          ≤ ENNReal.ofReal (rate n) }

  have hpre : goodBlockEvent L D c rate k n j =
      (fun ω : Fin (k * n) → X => block_extract k n ω j) ⁻¹' A := by
    ext ω; rfl
```

**Step 2**: Push forward via `map_block_extract_eq_pi` (T3):

```lean
  have hA : MeasurableSet A := measurableSet_goodBlock_A L hL_meas D c hc_meas rate n

  rw [hpre, ← MeasureTheory.Measure.map_apply (block_extract_measurable k n j) hA,
      map_block_extract_eq_pi k n D j]
```

After these rewrites, the goal becomes `D^n A ≥ ofReal(2/3)`.

**Step 3**: Apply `huniv`:

```lean
  exact huniv D inferInstance c hcC n
```

If `A` doesn't unfold to match `huniv`'s set, use `simpa [A] using huniv D inferInstance c hcC n`.

### Key API

- `map_block_extract_eq_pi` (T3, proved): `D^{k*n}.map(block_j) = D^n`
- `measurableSet_goodBlock_A` (T0, proved): `MeasurableSet A`
- `block_extract_measurable` (Generalization.lean): `Measurable (fun ω => block_extract k n ω j)`
- `MeasureTheory.Measure.map_apply`: `μ(f⁻¹'S) = μ.map(f)(S)` for measurable `f`, `MeasurableSet S`

### Potential issues

1. If `MeasureTheory.Measure.map_apply` rewrites in the wrong direction, use `← MeasureTheory.Measure.map_apply` or `Measure.map_apply_of_aemeasurable`.
2. If `huniv D inferInstance c hcC n` doesn't unify because `A` hasn't been unfolded, try `show D^n A ≥ _` first or `change` the goal.
3. The `IsProbabilityMeasure D` instance should be found by `inferInstance` since it's in the context.

### Estimated LOC: ~10

### Guardrails
- A4/A5 checks
- No new sorry
- Edit only line 503
- Do not touch any other lemma
- NEVER run `git checkout`, `git restore`, or any working-tree discard command