---
session: 9
date: 2026-03-31
title: "Version Space Learner: Measurable Selection via Countable Enumeration"
type: formalization-urs
status: ready-to-implement
target_file: FLT_Proofs/Learner/VersionSpace.lean
theorem_count: 5 (A-E)
sorry_budget: 0
---

# Version Space Learner: Measurable Selection via Countable Enumeration

## Scientific Claim

Version space learners — learners that output any hypothesis consistent with
training data — satisfy `MeasurableBatchLearner` when the concept class has a
measurable enumeration. This makes them valid RL policy classes, a prediction
not present in the RL literature.

## Why Countable?

Kuratowski-Ryll-Nardzewski (measurable selection for uncountable standard Borel
multifunctions) is NOT in Mathlib. For countable concept classes with a measurable
enumeration `enum : ℕ → Concept X Bool`, the version space learner uses `Nat.find`
to select the first consistent hypothesis. This is constructive and sorry-free.

The countable restriction is NOT a weakness: it covers all finite hypothesis
classes (standard PAC), all recursively enumerable classes (Gold paradigm),
and infinite discrete families (e.g., threshold classifiers on ℚ). These are
the classes where version space methods are actually used.

## File: `FLT_Proofs/Learner/VersionSpace.lean` (NEW)

### Imports

```lean
import FLT_Proofs.Learner.Core
import Mathlib.MeasureTheory.Measure.MeasureSpace
```

### 0. Core Definitions

```lean
/-- Consistency predicate: hypothesis h is consistent with sample S. -/
def IsConsistent {X : Type u} (h : Concept X Bool) {m : ℕ} (S : Fin m → X × Bool) : Prop :=
  ∀ i, h (S i).1 = (S i).2

/-- Version space: the set of indices whose concepts are consistent with S. -/
def versionSpaceIndices (enum : ℕ → Concept X Bool) {m : ℕ} (S : Fin m → X × Bool) : Set ℕ :=
  {n | IsConsistent (enum n) S}
```

### Theorem A: Decidability of consistency (~5 LOC, HC 0.05)

```lean
instance isConsistent_decidable
    {X : Type u} (h : Concept X Bool) {m : ℕ} (S : Fin m → X × Bool) :
    Decidable (IsConsistent h S) := by
  ...
```

**Route**: `IsConsistent` is `∀ i : Fin m, h (S i).1 = (S i).2`. Each conjunct
is `DecidableEq Bool`. Finite conjunction (`Fintype.decidableForallFintype`).

### Theorem B: Version space learner construction (~20 LOC, HC 0.15)

```lean
noncomputable def versionSpaceLearner
    {X : Type u} [MeasurableSpace X]
    (enum : ℕ → Concept X Bool) : BatchLearner X Bool where
  hypotheses := Set.range enum ∪ {fun _ => false}
  learn S :=
    if h : ∃ n, IsConsistent (enum n) S
    then enum (Nat.find h)
    else fun _ => false
  output_in_H S := by ...
```

**Route**: `output_in_H` is trivial — either `enum (Nat.find h) ∈ Set.range enum`
(by `⟨_, rfl⟩`) or `fun _ => false ∈ {fun _ => false}`.

### Theorem C: Measurability of consistency indicator (~15 LOC, HC 0.20)

```lean
theorem measurableSet_consistent
    {X : Type u} [MeasurableSpace X]
    (enum : ℕ → Concept X Bool)
    (h_meas : ∀ n, Measurable (enum n))
    (m : ℕ) (n : ℕ) :
    MeasurableSet {S : Fin m → X × Bool | IsConsistent (enum n) S} := by
  ...
```

**Route**: `{S | IsConsistent (enum n) S}` = `⋂ i, {S | enum n (S i).1 = (S i).2}`.
Each `{S | enum n (S i).1 = (S i).2}` is measurable:
- `S ↦ (S i).1` is `measurable_pi_apply i |>.fst` (measurable)
- `S ↦ (S i).2` is `measurable_pi_apply i |>.snd` (measurable)
- `S ↦ enum n ((S i).1)` is composition of measurable functions
- `{S | f(S) = g(S)}` is measurable when f, g are measurable into a discrete space
Finite intersection (Fintype) of measurable sets is measurable.

### Theorem D: Measurability of "find = n" events (~15 LOC, HC 0.25)

```lean
theorem measurableSet_find_eq
    {X : Type u} [MeasurableSpace X]
    (enum : ℕ → Concept X Bool)
    (h_meas : ∀ n, Measurable (enum n))
    (m : ℕ) (n : ℕ) :
    MeasurableSet {S : Fin m → X × Bool |
      (∃ k, IsConsistent (enum k) S) ∧ Nat.find (⟨_, ‹_›⟩ : ∃ k, IsConsistent (enum k) S) = n} := by
  ...
```

**NOTE**: This is the trickiest definition to state. The `Nat.find` depends on the
proof term. The cleaner route may be: define the set directly as
`{S | IsConsistent (enum n) S ∧ ∀ k < n, ¬ IsConsistent (enum k) S}`.
This is `measurableSet_consistent ∩ ⋂ k < n, (measurableSet_consistent)ᶜ` — measurable.

Then prove `Nat.find ... = n ↔ IsConsistent (enum n) S ∧ ∀ k < n, ¬IsConsistent (enum k) S`
using `Nat.find_eq_iff`.

### Theorem E: MeasurableBatchLearner (~25 LOC, HC 0.35)

```lean
theorem versionSpaceLearner_measurableBatchLearner
    {X : Type u} [MeasurableSpace X] [MeasurableSingletonClass X]
    (enum : ℕ → Concept X Bool)
    (h_meas : ∀ n, Measurable (enum n)) :
    MeasurableBatchLearner X (versionSpaceLearner enum) := by
  ...
```

**Route — the key argument**:

We need: for each m, the map `(S, x) ↦ versionSpaceLearner.learn S x` is measurable
from `(Fin m → X × Bool) × X → Bool`.

For Y = Bool, measurability = the preimage of `{true}` is MeasurableSet.

```
{(S, x) | versionSpaceLearner.learn S x = true}
= {(S, x) | ∃ n, [IsConsistent (enum n) S ∧ (∀ k < n, ¬IsConsistent (enum k) S)]
              ∧ enum n x = true}
= ⋃ n, ({S | find_eq n} ×ˢ {x | enum n x = true})
```

This is a **countable union of measurable rectangles**:
- `{S | find_eq n}` is MeasurableSet by Theorem D
- `{x | enum n x = true}` is MeasurableSet since `enum n` is measurable
- Product of measurable sets is measurable in the product sigma-algebra
- Countable union of measurable sets is measurable

QED.

The `¬∃` branch (version space empty → output `false`) contributes ∅ to the
preimage of `{true}`, which is measurable.

## Formalization Phases

| Phase | Content | LOC | HC | Dependencies |
|-------|---------|-----|-----|-------------|
| P0 | Definitions (IsConsistent, versionSpaceIndices) | 15 | 0.05 | Core.lean |
| P1 | Theorem A (decidability) | 5 | 0.05 | P0 |
| P2 | Theorem B (learner construction) | 20 | 0.15 | P0, P1 |
| P3 | Theorem C (consistency measurability) | 15 | 0.20 | P0 |
| P4 | Theorem D (find_eq measurability) | 15 | 0.25 | P3 |
| P5 | Theorem E (MeasurableBatchLearner) | 25 | 0.35 | P2, P4 |

Total: ~95 LOC, 5 theorems, 0 sorrys.

## Critical Path Analysis

The ONLY hard step is Theorem E, specifically the rewrite:
```
{(S, x) | learn S x = true} = ⋃ n, (A_n ×ˢ B_n)
```
where `A_n = {S | first consistent = n}` and `B_n = {x | enum n x = true}`.

The set-equality proof needs `ext ⟨S, x⟩; simp` + case analysis on `dif_pos`/`dif_neg`
for the `if ∃ n, ...` branch. This is the same ext/simp pattern from
BorelAnalyticSeparation.lean Theorems H-K.

## What This Proves

"Countable version space learners satisfy MeasurableBatchLearner. They are valid
RL policy classes. This is a prediction from the measurability typeclass that is
not present in the RL or PAC learning literature."
