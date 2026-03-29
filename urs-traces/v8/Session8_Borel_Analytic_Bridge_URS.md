---
session: 8
date: 2026-03-29
title: "Borel-Analytic Bridge: NullMeasurableSet is the Right Level for Learning Theory"
type: formalization-urs
status: open
target_file: FLT_Proofs/Complexity/Measurability.lean
theorem_count: 3 (positive bridge + counterexample + closure principle)
---

# Borel-Analytic Bridge: Formalization URS

## 0. Will -- What We're Proving

Three theorems that together characterize NullMeasurableSet as the exactly right measurability level for the Fundamental Theorem of Statistical Learning with Borel-parameterized concept classes:

1. **Positive bridge**: Borel parameterization implies analytic bad event implies NullMeasurableSet bad event.
2. **Negative bridge (counterexample)**: Analytic bad event need not be Borel measurable.
3. **Closure principle**: Borel-parameterized patching preserves NullMeasurableSet well-behavedness.

Together with the separation corollary (Theorem 4), these establish that NullMeasurableSet is necessary and sufficient -- strictly weaker than Krapp-Wirth's MeasurableSet, yet strong enough for the FTSL.

---

## 1. Theorem 1: Positive Bridge

### 1.1 Statement

Let X be a Polish space, Theta a standard Borel space, and e : Theta x X -> Bool Borel (the evaluation map). Fix measurable c : X -> Bool, m : N, epsilon > 0. Define the ghost-gap:

```
Delta(theta, p) = EmpErr(h_theta, p.2, c) - EmpErr(h_theta, p.1, c)
```

where h_theta(x) = e(theta, x) and p = (x, x') in X^m x X^m.

Then the bad event `E_{m,epsilon} = {p | exists theta in Theta, Delta(theta, p) >= epsilon/2}` is:
- Analytic (Sigma_1^1) in X^m x X^m
- Universally measurable
- NullMeasurableSet under any Borel probability measure on X

### 1.2 Proof Route

1. B_{m,epsilon} = {(theta, p) | Delta(theta, p) >= epsilon/2} is Borel in Theta x (X^m x X^m) because Delta is a finite combination of evaluations of the Borel map e, composed with projections and the measurable target c.
2. E_{m,epsilon} = pi(B_{m,epsilon}) is the projection of a Borel set from a standard Borel space, hence analytic by Suslin's theorem.
3. Analytic -> universally measurable -> NullMeasurableSet under any probability measure.

### 1.3 Lean Formalization

```lean
/-- Positive bridge: Borel-parameterized concept classes have NullMeasurableSet bad events.
    This is strictly weaker than Krapp-Wirth's MeasurableSet condition and strictly weaker
    than Pollard's permissibility. It is the exactly right level for the FTSL. -/
theorem borel_param_nullMeasurableSet_bad_event
    {X : Type u} [MeasurableSpace X] [TopologicalSpace X] [PolishSpace X] [BorelSpace X]
    {Θ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
    (e : Θ → Concept X Bool) (he : Measurable (fun p : Θ × X => e p.1 p.2))
    (c : Concept X Bool) (hc : Measurable c)
    (m : ℕ) (ε : ℝ) :
    ∀ (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D],
      MeasureTheory.NullMeasurableSet
        {p : (Fin m → X) × (Fin m → X) | ∃ θ : Θ,
          EmpiricalError X Bool (e θ) (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
          EmpiricalError X Bool (e θ) (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2}
        ((MeasureTheory.Measure.pi (fun _ : Fin m => D)).prod
         (MeasureTheory.Measure.pi (fun _ : Fin m => D))) := by
  sorry
```

### 1.4 Key Mathlib API Needed

- `MeasureTheory.AnalyticSet` -- definition of analytic sets
- `AnalyticSet.nullMeasurableSet` or `AnalyticSet.measurableSet_of_universallyMeasurable` -- the chain analytic -> universally measurable -> NullMeasurableSet
- `AnalyticSet.image_of_continuous` or projection lemmas
- `PolishSpace`, `StandardBorelSpace`, `BorelSpace` -- Mathlib typeclasses for Polish/Borel structure
- **Search needed**: Does Mathlib have the full chain Borel projection -> analytic -> universally measurable -> NullMeasurableSet? Search for `AnalyticSet` in Mathlib.

### 1.5 Estimates

- **LOC**: ~40 (statement + proof)
- **HC**: 0.45 -- need to navigate Mathlib's AnalyticSet API which may be incomplete

---

## 2. Theorem 2: Negative Bridge (Counterexample)

### 2.1 Statement

There exists a concept class C over R with:
- VCDim(C) = 1
- C is trivially PAC learnable
- Each h in C is Borel measurable
- The ghost-gap bad event for m=1, c=0, epsilon=1 is analytic but NOT Borel

### 2.2 Construction

1. Let A in R be an analytic non-Borel set (exists by Suslin's theorem in any uncountable Polish space).
2. Let Theta = N^N (Baire space, standard Borel), g : Theta -> R Borel with range(g) = A.
3. Define h_theta(x) = 1_{x = g(theta)} (singleton indicator).
4. C = {0} union {h_theta | theta in Theta}.
5. The bad event E = {(x, x') | x' in A and x != x'} is analytic non-Borel.

### 2.3 Proof That E Is Not Borel

If E were Borel in R^2, then for any a not in A, the section E_a = {x' | (a, x') in E} = A \ {a}. Sections of Borel sets are Borel. A \ {a} Borel implies A Borel (A = (A \ {a}) union {a}, union of two Borel sets). Contradiction.

### 2.4 Lean Formalization

```lean
/-- Negative bridge: there exists a concept class where the ghost-gap bad event
    is analytic (hence NullMeasurableSet) but NOT Borel (hence not MeasurableSet).
    This separates WellBehavedVC from KrappWirthWellBehaved. -/
theorem exists_analytic_non_borel_bad_event :
    ∃ (C : ConceptClass ℝ Bool),
      (∀ h ∈ C, Measurable h) ∧
      VCDim ℝ C ≤ 1 ∧
      (∃ (c : Concept ℝ Bool) (hc : Measurable c),
        MeasureTheory.NullMeasurableSet
          {p : ℝ × ℝ | ∃ h ∈ C,
            ... ≥ 1/2}
          ... ∧
        ¬ MeasurableSet
          {p : ℝ × ℝ | ∃ h ∈ C,
            ... ≥ 1/2}) := by
  sorry
```

### 2.5 Key Mathlib API Needed

- Existence of analytic non-Borel sets in R: search for `AnalyticSet.not_borel` or `exists_analytic_not_borel`
- `N -> N` (Baire space) as a standard Borel space
- Borel surjection onto an analytic set
- Section lemma: sections of Borel sets in product spaces are Borel

### 2.6 Estimates

- **LOC**: ~80 (statement + construction + proof)
- **HC**: 0.60 -- depends heavily on what Mathlib has for analytic non-Borel existence

---

## 3. Theorem 3: Closure Principle

### 3.1 Statement

If C_1 and C_2 are Borel-parameterized concept classes and {R_theta | theta in Theta} is a Borel-parameterized family of regions, then the patched class

```
C_patch = {x -> c_1(x) * 1_{R_theta}(x) + c_2(x) * 1_{R_theta^c}(x) | c_1 in C_1, c_2 in C_2, theta in Theta}
```

has NullMeasurableSet bad events (but not necessarily MeasurableSet).

### 3.2 Proof Route

This follows from Theorem 1 applied to the combined parameter space Theta_1 x Theta_2 x Theta_region. The composed evaluation map is Borel because it is built from Borel evaluation maps via Borel operations (multiplication, addition, indicator composition).

### 3.3 Lean Formalization

Corollary of `borel_param_nullMeasurableSet_bad_event` with Theta := Theta_1 x Theta_2 x Theta_region.

### 3.4 Estimates

- **LOC**: ~20 (corollary of Theorem 1)
- **HC**: 0.20

---

## 4. The Separation Theorem (Corollary)

Combining Theorems 1 and 2:

```lean
/-- NullMeasurableSet is strictly more general than MeasurableSet for the FTSL.
    There exist PAC-learnable concept classes where the UC bad event satisfies
    WellBehavedVC (NullMeasurableSet) but NOT KrappWirthWellBehaved (MeasurableSet). -/
theorem wellBehavedVC_strictly_weaker_than_krappWirth :
    ∃ (X : Type) (_ : MeasurableSpace X) (C : ConceptClass X Bool),
      MeasurableHypotheses X C ∧ WellBehavedVC X C ∧ ¬ KrappWirthWellBehaved X C := by
  sorry
```

This closes `KrappWirth_separation` from the kernel's open questions.

### Estimates

- **LOC**: ~10 (assembles Theorems 1 and 2)
- **HC**: 0.15

---

## 5. UK Items

**UK_1**: Does Mathlib have `AnalyticSet` with the full chain to NullMeasurableSet? Search needed. If the chain is incomplete, we may need to add intermediate lemmas.

**UK_2**: Does Mathlib have the existence of analytic non-Borel subsets of R? This is `exists A : Set R, AnalyticSet A and not MeasurableSet A`. If not, this is a substantial prerequisite (~50 LOC).

**UK_3**: The counterexample needs R with Borel sigma-algebra as a `PolishSpace` + `BorelSpace` + `StandardBorelSpace`. Mathlib should have all of these for R. Verify.

**UK_4**: The counterexample's VC dimension claim (VCDim <= 1) needs a proof that the singleton class doesn't shatter any 2-element set. This should be straightforward but needs the VC machinery.

**UK_5**: The statement of `KrappWirth_separation` in the kernel uses `KrappWirthWellBehaved X C` which is defined with our `KrappWirthV` (one-sided ghost gap sup). The counterexample shows the sup map is non-Borel. Need to verify the exact match between what `KrappWirthV` asks (Measurable ghostGapSup) and what the counterexample refutes (the sup map is 1_E which is non-Borel).

---

## 6. Formalization Plan

| Phase | Task | LOC | HC | Dependency |
|-------|------|-----|-----|-----------|
| F1 | Search Mathlib for AnalyticSet API | 0 | -- | None |
| F2 | Theorem 1 (positive bridge) | 40 | 0.45 | F1 |
| F3 | Theorem 2 (counterexample) | 80 | 0.60 | F1, UK_2 |
| F4 | Theorem 3 (closure principle) | 20 | 0.20 | F2 |
| F5 | Separation theorem (corollary) | 10 | 0.15 | F2, F3 |
| F6 | Close KrappWirth_separation | 5 | 0.10 | F5 |

**Total**: ~155 LOC, HC 0.45 average

### Dependency Graph

```
F1 (Mathlib search)
├── F2 (positive bridge)
│   ├── F4 (closure principle)
│   └── F5 (separation theorem) ← also needs F3
└── F3 (counterexample)
    └── F5 (separation theorem)
        └── F6 (close KrappWirth_separation)
```

---

## 7. Guardrails

- A4/A5 checks after every `lake build`
- `sorry`s allowed ONLY during phased development
- Final target: 0 sorrys in Theorems 1, 3, 4. Theorem 2 may need sorry if Mathlib lacks analytic non-Borel existence.
- Do NOT modify any existing theorem
- NEVER run `git checkout`, `git restore`, or any working-tree discard command

---

## 8. Publication Value

**Paper title**: "NullMeasurableSet is the Right Level: A Descriptive Set-Theoretic Characterization of Measurability in Statistical Learning"

**Core result**: For Borel-parameterized concept classes over Polish spaces, the uniform convergence bad event is always analytic (hence NullMeasurableSet), but not always Borel (hence MeasurableSet can fail). The singleton class over an analytic non-Borel parameter image provides a concrete separation witness with VC dimension 1.

**Novel content**:
1. First learning-theoretic application of the analytic/Borel distinction
2. Characterizes NullMeasurableSet as necessary and sufficient for the FTSL
3. Separates WellBehavedVC (this kernel) from KrappWirthWellBehaved (Krapp-Wirth 2024)
4. Concrete counterexample with VC dim 1, trivially PAC learnable

**Venue targets**: Annals of Statistics, Journal of Machine Learning Research (measurability/foundations track), or Annals of Pure and Applied Logic (if the descriptive set theory content is foregrounded)
