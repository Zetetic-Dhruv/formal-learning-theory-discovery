---
session: 8
date: 2026-03-25
task_id: S1
target: MeasurableSet GoodTrain (UK_5)
file: FLT_Proofs/Theorem/Extended.lean
status: closed
---

## S1: UK_5 — `MeasurableSet GoodTrain` (line 645)

**File**: `FLT_Proofs/Theorem/Extended.lean`, line 645
**Scope**: Edit ONLY the `sorry` at line 645. Do not touch any other line.

**Definition** (lines 565–568):
```lean
let GoodTrain : Set (Fin m₁ → X) :=
  {xs₁ | TrueError X
    (LA.learnWithAdvice aStar (fun i => (xs₁ i, c (xs₁ i)))) c D
    ≤ ENNReal.ofReal (ε / 2)}
```

Where `TrueError X h c D = D {x | h x ≠ c x}`.

**Route**:
1. The disagreement set `{(xs₁, x) | LA.learnWithAdvice aStar (labeled(xs₁)) x ≠ c x}` is `MeasurableSet` in `(Fin m₁ → X) × X`. Proof: compose `AdviceEvalMeasurable` (`h_eval`, gives measurability of `(S, x) ↦ LA.learnWithAdvice a S x`) with the labeling map `xs₁ ↦ fun i => (xs₁ i, c (xs₁ i))` (measurable from `measurable_pi_apply` + `hcm`). Then `measurableSet_eq_fun` gives the set measurability, take `.compl` for `≠`.
2. `MeasureTheory.measurable_measure_prod_mk_left`: for a `MeasurableSet S` in a product, `x₁ ↦ μ(section of S at x₁)` is `Measurable`. Apply to get `fun xs₁ => D {x | ... x ≠ c x}` measurable.
3. `GoodTrain` = preimage of `Set.Iic (ENNReal.ofReal (ε/2))` under this measurable function. `measurableSet_Iic` gives `MeasurableSet GoodTrain`.

**Available in scope**: `h_eval : AdviceEvalMeasurable LA`, `aStar : A`, `hcm : Measurable c`, `D : Measure X` with `IsProbabilityMeasure D` and `SigmaFinite D`.

**Guardrails**: A4/A5. No new sorry. No simplification. Edit only line 645.

---