---
session: 8
date: 2026-03-26
task_id: T0
target: measurableSet_goodBlock_A
file: FLT_Proofs/Theorem/Separation.lean
status: closed
---

## T0: `measurableSet_goodBlock_A` (line 355)

**File**: `FLT_Proofs/Theorem/Separation.lean`, line 355
**Scope**: Replace the `sorry` at line 355. Do not touch any other line.
**Dependencies**: None — standalone. Uses only `hL_meas`, `hc_meas`, Mathlib API.

### Current state (lines 345–355):

```lean
private lemma measurableSet_goodBlock_A
    {X : Type u} [MeasurableSpace X]
    (L : BatchLearner X Bool) (hL_meas : LearnEvalMeasurable L)
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (c : Concept X Bool) (hc_meas : Measurable c)
    (rate : ℕ → ℝ) (n : ℕ) :
    MeasurableSet
      { xs : Fin n → X |
          D { x : X | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
            ≤ ENNReal.ofReal (rate n) } := by
  sorry
```

### What the set is

```
A = { xs : Fin n → X | D { x | L.learn(labeled(xs)) x ≠ c x } ≤ ofReal(rate n) }
```

This is the preimage of `Set.Iic (ENNReal.ofReal (rate n))` under the function `xs ↦ D { x | L.learn(labeled(xs)) x ≠ c x }`. So `MeasurableSet A` follows if that function is `Measurable`.

### Route (3 steps)

**Step 1**: Show the disagreement set `{(xs, x) : (Fin n → X) × X | L.learn(labeled(xs)) x ≠ c x}` is `MeasurableSet` in the product space.

```lean
  -- The labeling map: (xs, x) ↦ (fun i => (xs i, c (xs i)))
  have h_label : Measurable (fun p : (Fin n → X) × X =>
      fun i : Fin n => (p.1 i, c (p.1 i))) :=
    measurable_pi_lambda _ (fun i =>
      ((measurable_pi_apply i).comp measurable_fst).prodMk
        (hc_meas.comp ((measurable_pi_apply i).comp measurable_fst)))
  -- Joint measurability: (xs, x) ↦ L.learn(labeled(xs)) x
  have h_joint : Measurable (fun p : (Fin n → X) × X =>
      L.learn (fun i => (p.1 i, c (p.1 i))) p.2) :=
    (hL_meas n).comp (h_label.prodMk measurable_snd)
  -- c ∘ snd: (xs, x) ↦ c x
  have h_c_snd : Measurable (fun p : (Fin n → X) × X => c p.2) :=
    hc_meas.comp measurable_snd
  -- Disagreement set: {(xs, x) | learn(xs)(x) ≠ c(x)}
  have h_disagree : MeasurableSet {p : (Fin n → X) × X |
      L.learn (fun i => (p.1 i, c (p.1 i))) p.2 ≠ c p.2} :=
    (measurableSet_eq_fun h_joint h_c_snd).compl
```

**Step 2**: Apply `MeasureTheory.measurable_measure_prod_mk_left` to get measurability of the section-measure function `xs ↦ D(section at xs)`.

```lean
  -- Section measure: xs ↦ D { x | learn(xs)(x) ≠ c x } is Measurable
  have h_sec : Measurable (fun xs : Fin n → X =>
      D { x : X | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }) :=
    MeasureTheory.measurable_measure_prod_mk_left h_disagree
```

Note: `measurable_measure_prod_mk_left` takes a `MeasurableSet` in the product and returns `Measurable (fun a => ν (Prod.mk a ⁻¹' s))`. The section `Prod.mk xs ⁻¹' {(xs', x) | learn(xs') x ≠ c x}` equals `{x | learn(xs) x ≠ c x}` — this should be definitional or provable by `ext; rfl`.

If Lean doesn't see the definitional equality, you may need:
```lean
  have h_sec_eq : ∀ xs, Prod.mk xs ⁻¹' {p : (Fin n → X) × X |
      L.learn (fun i => (p.1 i, c (p.1 i))) p.2 ≠ c p.2} =
      {x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x} := by
    intro xs; ext x; rfl
```
Then rewrite before applying `measurable_measure_prod_mk_left`.

**Step 3**: Preimage of `Iic` under measurable function.

```lean
  exact h_sec measurableSet_Iic
```

Or if Step 2 needed the `h_sec_eq` bridge:
```lean
  have h_meas_fn : Measurable (fun xs : Fin n → X =>
      D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }) := by
    have := MeasureTheory.measurable_measure_prod_mk_left h_disagree
    simpa [h_sec_eq] using this  -- or: convert this using 1; ext xs; exact h_sec_eq xs
  exact h_meas_fn measurableSet_Iic
```

### Key Mathlib API

- `MeasureTheory.measurable_measure_prod_mk_left` — for `MeasurableSet s` in `α × β`, `fun a => ν (Prod.mk a ⁻¹' s)` is `Measurable`
- `measurableSet_eq_fun` — `{p | f p = g p}` measurable from `Measurable f`, `Measurable g`
- `MeasurableSet.compl` — `{p | f p ≠ g p}` from `.compl` of the above
- `measurableSet_Iic` — `Set.Iic a` is measurable in any measurable ordered space
- `hL_meas n` — gives `Measurable (fun p : (Fin n → X × Bool) × X => L.learn p.1 p.2)`
- `measurable_pi_lambda` — for building measurable functions into `Π i, α i`
- `measurable_pi_apply i` — projection `(fun f => f i)` is measurable

### Estimated LOC: ~20

### Guardrails
- A4/A5 checks
- No new sorry
- Edit only line 355
- Do not touch any other lemma
- NEVER run `git checkout`, `git restore`, or any working-tree discard command