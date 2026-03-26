---
session: 8
date: 2026-03-26
task_id: FP4-Phase1
target: Scaffolding + interface change for boosting (boost_two_thirds_to_pac)
file: FLT_Proofs/Theorem/Separation.lean
status: closed
---

## FP4-Phase1: Scaffolding + Interface Change

**File**: `FLT_Proofs/Theorem/Separation.lean` (+ `Extended.lean` for caller propagation)
**Target**: Add all declarations, change signatures, build passes with sorrys only in the new helpers + main theorem.

### What to do

**Step 1**: Insert `LearnEvalMeasurable` definition before `boost_two_thirds_to_pac` (before line 329):

```lean
/-- Joint measurability of a batch learner's evaluation map. -/
private def LearnEvalMeasurable
    {X : Type u} [MeasurableSpace X]
    (L : BatchLearner X Bool) : Prop :=
  ∀ m : ℕ,
    Measurable (fun p : (Fin m → X × Bool) × X => L.learn p.1 p.2)
```

**Step 2**: Insert `learn_measurable_fixed` after LearnEvalMeasurable:

```lean
private lemma learn_measurable_fixed
    {X : Type u} [MeasurableSpace X]
    (L : BatchLearner X Bool) (hL_meas : LearnEvalMeasurable L)
    {m : ℕ} (S : Fin m → X × Bool) :
    Measurable (L.learn S) := by
  exact (hL_meas m).comp (Measurable.prodMk measurable_const measurable_id)
```

(This is the same pattern as `learnWithAdvice_measurable_fixed` in Extended.lean — copy the proof.)

**Step 3**: Insert `goodBlockEvent` definition:

```lean
private def goodBlockEvent
    {X : Type u} [MeasurableSpace X]
    (L : BatchLearner X Bool) (D : MeasureTheory.Measure X)
    (c : Concept X Bool) (rate : ℕ → ℝ)
    (k n : ℕ) (j : Fin k) : Set (Fin (k * n) → X) :=
  { ω : Fin (k * n) → X |
      D { x : X |
          L.learn (fun i => (block_extract k n ω j i, c (block_extract k n ω j i))) x ≠ c x }
        ≤ ENNReal.ofReal (rate n) }
```

**Step 4**: Insert all 6 helper lemma declarations with `sorry` bodies:
- `goodBlockEvent_measurable`
- `map_block_extract_eq_pi`
- `iIndepSet_goodBlockEvents`
- `goodBlockEvent_prob_ge_two_thirds`
- `chebyshev_seven_twelfths_bound`
- `majority_error_le_seven_rate_of_good_fraction`
- `boosted_sample_error_le_of_good_blocks`

(Use exact signatures from the user's declarations above.)

**Step 5**: Change `boost_two_thirds_to_pac` signature — add `hc_meas` and `hL_meas`:

```lean
private theorem boost_two_thirds_to_pac (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool)
    (hc_meas : ∀ c ∈ C, Measurable c)
    (L : BatchLearner X Bool) (hL_meas : LearnEvalMeasurable L)
    (rate : ℕ → ℝ)
    (hrate : ∀ ε > 0, ∃ m₀, ∀ m ≥ m₀, rate m < ε)
    (huniv : ...) :
    PACLearnable X C := by
  sorry
```

**Step 6**: Update `mf` parameters inside the proof body:
- `kmin := ⌈36/δ⌉ + 2` (was `⌈9/δ⌉ + 2`)
- `ε' := ε / 7` (was `ε / kmin`)

**Step 7**: Update caller `universal_imp_pac` (Sep:427-431) to supply `hc_meas` and `hL_meas`. This may require adding these to `universal_imp_pac`'s signature or deriving them from `UniversalLearnable`. Check what `UniversalLearnable` provides and decide.

**Step 8**: Propagate to `universal_trichotomy` in Extended.lean if needed.

**Step 9**: `lake build` — should pass with sorrys only in the 7 helpers + main theorem.

### Guardrails
- A4/A5 checks
- No sorry except in the explicitly listed 8 locations
- Build must pass

---