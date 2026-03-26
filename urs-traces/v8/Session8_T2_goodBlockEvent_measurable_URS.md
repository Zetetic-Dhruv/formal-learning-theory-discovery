---
session: 8
date: 2026-03-26
task_id: T2
target: goodBlockEvent_measurable
file: FLT_Proofs/Theorem/Separation.lean
status: closed
---

## T2: `goodBlockEvent_measurable` (line 342)

**File**: `FLT_Proofs/Theorem/Separation.lean`, line 342
**Scope**: Replace the `sorry` at line 342. Do not touch any other line.
**Dependencies**: T0 (`measurableSet_goodBlock_A`, now proved at lines 345–383). Also uses `block_extract_measurable` from Generalization.lean.

### Current state (lines 335–342):

```lean
private lemma goodBlockEvent_measurable
    {X : Type u} [MeasurableSpace X]
    (L : BatchLearner X Bool) (hL_meas : LearnEvalMeasurable L)
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (c : Concept X Bool) (hc_meas : Measurable c)
    (rate : ℕ → ℝ) (k n : ℕ) :
    ∀ j : Fin k, MeasurableSet (goodBlockEvent L D c rate k n j) := by
  sorry
```

### What `goodBlockEvent` is (lines 318–324):

```lean
goodBlockEvent L D c rate k n j =
  { ω : Fin (k * n) → X |
      D { x : X |
          L.learn (fun i => (block_extract k n ω j i, c (block_extract k n ω j i))) x ≠ c x }
        ≤ ENNReal.ofReal (rate n) }
```

### Route

`goodBlockEvent j` is the preimage of the set `A` (from `measurableSet_goodBlock_A`) under `block_extract k n · j`:

```
goodBlockEvent j = (fun ω => block_extract k n ω j) ⁻¹' A
```

where `A = { xs : Fin n → X | D { x | L.learn(labeled(xs)) x ≠ c x } ≤ ofReal(rate n) }`.

Since `A` is `MeasurableSet` (by `measurableSet_goodBlock_A`, just proved) and `fun ω => block_extract k n ω j` is `Measurable` (by `block_extract_measurable`), the preimage is `MeasurableSet`.

### Proof

```lean
  intro j
  have hA : MeasurableSet
      { xs : Fin n → X |
          D { x : X | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
            ≤ ENNReal.ofReal (rate n) } :=
    measurableSet_goodBlock_A L hL_meas D c hc_meas rate n
  have hpre : goodBlockEvent L D c rate k n j =
      (fun ω : Fin (k * n) → X => block_extract k n ω j) ⁻¹'
        { xs : Fin n → X |
            D { x : X | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
              ≤ ENNReal.ofReal (rate n) } := by
    ext ω; rfl
  rw [hpre]
  exact (block_extract_measurable k n j).measurableSet_preimage hA
```

### Key API

- `measurableSet_goodBlock_A` (T0, just proved): `MeasurableSet A`
- `block_extract_measurable k n j` (Generalization.lean): `Measurable (fun ω => block_extract k n ω j)`
- `Measurable.measurableSet_preimage`: if `f` measurable and `s` measurable, then `f⁻¹'(s)` measurable

### Potential issue

If `Measurable.measurableSet_preimage` doesn't exist with that exact name, use `measurableSet_preimage` or `hA.preimage (block_extract_measurable k n j)` or `(block_extract_measurable k n j) hA`.

If the `ext ω; rfl` doesn't close `hpre` (definitional unfolding issue), try `ext ω; simp [goodBlockEvent, block_extract]` or just skip `hpre` and use `show` to rewrite the goal directly:

```lean
  intro j
  show MeasurableSet ((fun ω => block_extract k n ω j) ⁻¹' _)
  exact (block_extract_measurable k n j).measurableSet_preimage
    (measurableSet_goodBlock_A L hL_meas D c hc_meas rate n)
```

### Estimated LOC: ~10

### Guardrails
- A4/A5 checks
- No new sorry
- Edit only line 342
- Do not touch any other lemma
- NEVER run `git checkout`, `git restore`, or any working-tree discard command