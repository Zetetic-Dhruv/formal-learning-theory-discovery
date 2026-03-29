---
session: 8
date: 2026-03-29
title: "Borel-Analytic Bridge v2: Definitive Formalization Plan"
type: formalization-urs
status: ready-to-implement
target_file: FLT_Proofs/Complexity/BorelAnalyticBridge.lean
theorem_count: 12 (A-L)
sorry_budget: 1 (Theorem C — DST bridge lemma, provable but needs inner regularity chain)
---

# Borel-Analytic Bridge: Definitive Formalization Plan (v2)

## Correction from v1

v1 attempted to close `KrappWirth_separation` which quantifies over ALL targets c.
The Borel-analytic route only works for MEASURABLE targets. v2 introduces
`WellBehavedVCMeasTarget` and closes `KrappWirthSeparationMeasTarget` instead.

This is the mathematically correct endpoint: the symmetrization/UC chain already
uses measurable targets throughout.

## File: `FLT_Proofs/Complexity/BorelAnalyticBridge.lean` (NEW)

### Imports

```lean
import FLT_Proofs.Complexity.Measurability
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.NullMeasurable
```

### 0. Core Definitions

```lean
abbrev GhostPairs (X : Type u) (m : ℕ) := (Fin m → X) × (Fin m → X)

def paramWitnessSet
    {X : Type u} [MeasurableSpace X]
    {Θ : Type*} [MeasurableSpace Θ]
    (e : Θ → Concept X Bool) (c : Concept X Bool) (m : ℕ) (ε : ℝ) :
    Set (Θ × GhostPairs X m) :=
  {q | EmpiricalError X Bool (e q.1) (fun i => (q.2.2 i, c (q.2.2 i))) (zeroOneLoss Bool) -
       EmpiricalError X Bool (e q.1) (fun i => (q.2.1 i, c (q.2.1 i))) (zeroOneLoss Bool) ≥ ε / 2}

def paramBadEvent
    {X : Type u} [MeasurableSpace X]
    {Θ : Type*} [MeasurableSpace Θ]
    (e : Θ → Concept X Bool) (c : Concept X Bool) (m : ℕ) (ε : ℝ) :
    Set (GhostPairs X m) :=
  Prod.snd '' paramWitnessSet e c m ε
```

### 0b. Measurable-Target WellBehavedVC

```lean
def WellBehavedVCMeasTarget
    (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) : Prop :=
  ∀ (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (c : Concept X Bool), Measurable c →
    ∀ (m : ℕ) (ε : ℝ),
      MeasureTheory.NullMeasurableSet
        {p : (Fin m → X) × (Fin m → X) | ∃ h ∈ C,
          EmpiricalError X Bool h (fun i => (p.2 i, c (p.2 i))) (zeroOneLoss Bool) -
          EmpiricalError X Bool h (fun i => (p.1 i, c (p.1 i))) (zeroOneLoss Bool) ≥ ε / 2}
        ((MeasureTheory.Measure.pi (fun _ : Fin m => D)).prod
         (MeasureTheory.Measure.pi (fun _ : Fin m => D)))

def KrappWirthSeparationMeasTarget : Prop :=
  ∃ (C : ConceptClass ℝ Bool),
    MeasurableHypotheses ℝ C ∧
    WellBehavedVCMeasTarget ℝ C ∧
    ¬ KrappWirthWellBehaved ℝ C
```

### 0c. Counterexample Definitions

```lean
noncomputable def zeroConcept : Concept ℝ Bool := fun _ => false

noncomputable def singletonConcept (a : ℝ) : Concept ℝ Bool :=
  fun x => decide (x = a)

def singletonClassOn (A : Set ℝ) : ConceptClass ℝ Bool :=
  {h | h = zeroConcept ∨ ∃ a ∈ A, h = singletonConcept a}

def planarWitnessEvent (A : Set ℝ) : Set (ℝ × ℝ) :=
  {q | q.2 ∈ A ∧ q.1 ≠ q.2}

def samplePair1ToPlane : GhostPairs ℝ 1 → ℝ × ℝ :=
  fun p => (p.1 0, p.2 0)
```

## 1. Theorem Package (A through L)

### Theorem A: Measurable witness graph (~30 LOC, HC 0.35)

```lean
theorem paramWitnessSet_measurable
    {X : Type u} [MeasurableSpace X]
    {Θ : Type*} [MeasurableSpace Θ]
    (e : Θ → Concept X Bool)
    (he : Measurable (fun p : Θ × X => e p.1 p.2))
    (c : Concept X Bool) (hc : Measurable c)
    (m : ℕ) (ε : ℝ) :
    MeasurableSet (paramWitnessSet e c m ε) := by
  sorry
```

**Route**: Δ is a finite sum of evaluations of he and hc composed with projections.
Same EmpiricalError-as-finite-sum pattern from Extended.lean and Symmetrization.lean.
Finish with `Δ_meas measurableSet_Ici`.

### Theorem B: Bad event is analytic (~15 LOC, HC 0.25)

```lean
theorem borel_param_badEvent_analytic
    {X : Type u} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [PolishSpace X]
    {Θ : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
    (e : Θ → Concept X Bool)
    (he : Measurable (fun p : Θ × X => e p.1 p.2))
    (c : Concept X Bool) (hc : Measurable c)
    (m : ℕ) (ε : ℝ) :
    MeasureTheory.AnalyticSet (paramBadEvent e c m ε) := by
  sorry
```

**Route**: paramWitnessSet is MeasurableSet (Theorem A). Apply
`MeasurableSet.analyticSet_image` (confirmed in Mathlib) with `measurable_snd`.

### Theorem C: DST bridge lemma (~20 LOC, HC 0.55 — THE hard one)

```lean
theorem analyticSet_nullMeasurableSet_of_isProbabilityMeasure
    {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [PolishSpace α]
    {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    {s : Set α} (hs : MeasureTheory.AnalyticSet s) :
    MeasureTheory.NullMeasurableSet s μ := by
  sorry
```

**Route**: Analytic → universally measurable → NullMeasurableSet.
May need inner regularity (`InnerRegular`, confirmed in Mathlib).
This is the ONE theorem that may need sorry if the inner regularity → completion
chain is not in Mathlib. Factor as a single local DST lemma.

### Theorem D: Positive bridge to NullMeasurableSet (~10 LOC, HC 0.15)

```lean
theorem borel_param_nullMeasurableSet_bad_event
    ... :
    ∀ (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D],
      MeasureTheory.NullMeasurableSet
        (paramBadEvent e c m ε)
        ((MeasureTheory.Measure.pi (fun _ : Fin m => D)).prod
         (MeasureTheory.Measure.pi (fun _ : Fin m => D))) := by
  sorry
```

**Route**: Apply Theorem B then Theorem C. The product measure on GhostPairs
is a probability measure on a Polish space.

### Theorem E: Class-level corollary (~15 LOC, HC 0.20)

```lean
theorem borel_param_wellBehavedVCMeasTarget
    ... :
    WellBehavedVCMeasTarget X (Set.range e) := by
  sorry
```

**Route**: Rewrite `{p | ∃ h ∈ range e, ...}` as `paramBadEvent`, apply Theorem D.

### Theorem F: Closure principle for patching (~25 LOC, HC 0.25)

Defines `patchEval` (if-then-else on region membership), proves joint measurability,
applies Theorem E to the product parameter space Θ₁ × Θ₂ × Ρ.

### Theorem G: Singleton class measurability (~10 LOC, HC 0.10)

```lean
theorem singletonClassOn_measurable (A : Set ℝ) :
    ∀ h ∈ singletonClassOn A, Measurable h := by
  sorry
```

**Route**: zeroConcept is measurable_const. singletonConcept a uses
measurableSingleton_of_standardBorel (confirmed in Mathlib).

### Theorem H: Bad event = planar witness (~20 LOC, HC 0.30)

Set equality via simp/norm_num on m=1, c=0, threshold 1/2.

### Theorem I: Planar witness is analytic (~10 LOC, HC 0.15)

Intersection of `Prod.snd ⁻¹' A` (analytic) with `{q | q.1 ≠ q.2}` (Borel).

### Theorem J: Planar witness is NOT Borel (~15 LOC, HC 0.25)

Section argument: fix a ∉ A, section E_a = A \ {a}, if E Borel then A Borel, contradiction.
Uses continuous map v_a(y) = (a, y), measurable preimage.

### Theorem K: Sample-space bad event is NOT measurable (~10 LOC, HC 0.15)

Rewrite via Theorem H, apply surjectivity of samplePair1ToPlane,
use `Measurable.measurableSet_preimage_iff_of_surjective` (confirmed in Mathlib).

### Theorem L: Relative separation (~15 LOC, HC 0.20)

```lean
theorem analytic_nonborel_set_gives_measTarget_separation
    (A : Set ℝ)
    (hA_an  : MeasureTheory.AnalyticSet A)
    (hA_non : ¬ MeasurableSet A) :
    KrappWirthSeparationMeasTarget := by
  sorry
```

**Route**:
1. From hA_an, use `analyticSet_iff_exists_polishSpace_range` to get β, g with range g = A
2. Construct parameterized family e via singletonConcept ∘ g
3. WellBehavedVCMeasTarget from Theorem E
4. ¬ KrappWirthWellBehaved from Theorem K (bad event not Borel → sup map not measurable
   → KrappWirthV fails at m=1, c=0, ε=1)

### Optional: Absolute corollary

```lean
theorem exists_measTarget_separation
    (hex : ∃ A : Set ℝ, MeasureTheory.AnalyticSet A ∧ ¬ MeasurableSet A) :
    KrappWirthSeparationMeasTarget := by
  obtain ⟨A, hA_an, hA_non⟩ := hex
  exact analytic_nonborel_set_gives_measTarget_separation A hA_an hA_non
```

## 2. UK Resolution Summary

| UK | Resolution |
|----|-----------|
| UK_1 (AnalyticSet → NullMeasurableSet chain) | Factor as Theorem C, single local DST lemma. May need sorry. |
| UK_2 (Analytic non-Borel existence) | Make Theorem L RELATIVE to arbitrary A. Absolute corollary conditional on existence. |
| UK_3 (ℝ typeclass instances) | ✅ Confirmed: PolishSpace ℝ, StandardBorelSpace via standardBorel_of_polish |
| UK_4 (VC dim ≤ 1) | Not needed in bridge core. Optional standalone lemma. |
| UK_5 (KrappWirthV alignment) | ✅ Confirmed: one-sided ghostGapSup + wellBehaved_event_eq_preimage_gapSup matches |

## 3. Formalization Phases

| Phase | Theorems | LOC | HC | Dependencies |
|-------|----------|-----|-----|-------------|
| F1 | Definitions (0, 0b, 0c) | 40 | 0.05 | None |
| F2 | A (witness measurable) | 30 | 0.35 | F1 |
| F3 | B (analytic projection) | 15 | 0.25 | F2 |
| F4 | C (DST bridge) | 20 | 0.55 | None (standalone) |
| F5 | D, E (positive bridge + corollary) | 25 | 0.20 | F3, F4 |
| F6 | F (closure principle) | 25 | 0.25 | F5 |
| F7 | G, H, I, J, K (counterexample chain) | 65 | 0.30 | F1 |
| F8 | L (separation) | 15 | 0.20 | F5, F7 |

Total: ~235 LOC, 12 theorems, at most 1 sorry (Theorem C).

## 4. What This Proves

"For Borel-parameterized concept classes over Polish spaces with measurable targets,
NullMeasurableSet is necessary and sufficient for the uniform convergence step of the FTSL.
MeasurableSet (Krapp-Wirth's condition) is strictly stronger and fails for natural
PAC-learnable classes with VC dimension 1."
