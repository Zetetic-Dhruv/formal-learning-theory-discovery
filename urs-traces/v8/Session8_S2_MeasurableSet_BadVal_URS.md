---
session: 8
date: 2026-03-25
task_id: S2
target: MeasurableSet BadVal (UK_6)
file: FLT_Proofs/Theorem/Extended.lean
status: closed
---

## S2: UK_6 — `MeasurableSet BadVal` (line 647)

**File**: `FLT_Proofs/Theorem/Extended.lean`, line 647
**Scope**: Edit ONLY the `sorry` at line 647. Do not touch any other line.
**Dependency**: S1 must be closed first (but `hBadVal_meas` is independent of `hGoodTrain_meas`).

**Definition** (lines 631–635):
```lean
let BadVal : Set ((Fin m₁ → X) × (Fin m₂ → X)) :=
  {p | ∃ a : A,
    |TrueErrorReal X (LA.learnWithAdvice a (fun i => (p.1 i, c (p.1 i)))) c D -
      EmpiricalError X Bool (LA.learnWithAdvice a (fun i => (p.1 i, c (p.1 i))))
        (fun j => (p.2 j, c (p.2 j))) (zeroOneLoss Bool)| ≥ ε / 4}
```

**Route**:
1. `BadVal = ⋃ a : A, {p | |f_a(p)| ≥ ε/4}` — finite union over `[Fintype A]`.
2. For each fixed `a`:
   - `TrueErrorReal` part: same `measurable_measure_prod_mk_left` pattern as S1 but applied to `p.1` (compose with `measurable_fst`). Gives `fun p => TrueErrorReal X (cand_a(p.1)) c D` measurable.
   - `EmpiricalError` part: finite sum `(1/m₂) * Σⱼ 𝟙[cand_a(xs₂_j) ≠ c(xs₂_j)]`. Each indicator `fun p => 𝟙[LA.learnWithAdvice a (labeled(p.1)) (p.2 j) ≠ c(p.2 j)]` is measurable from `AdviceEvalMeasurable` + `hcm`. Finite sum of measurable → measurable.
   - Difference is measurable, absolute value is measurable, `{|·| ≥ ε/4}` is preimage of `Set.Ici` → measurable.
3. Finite union (`Finset.measurableSet_biUnion` or `MeasurableSet.iUnion` for `Fintype`) → `MeasurableSet BadVal`.

**Guardrails**: A4/A5. No new sorry. No simplification. Edit only line 647.

---