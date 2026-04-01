---
session: 10
date: 2026-03-31
title: "Pure Math Extraction: Typeclasses for Concentration, KL Divergence, Exchangeability"
type: refactoring-urs
status: awaiting-verification
target_files:
  - FLT_Proofs/MathLib/Concentration.lean (NEW, ~200 LOC)
  - FLT_Proofs/MathLib/KLDivergence.lean (NEW, ~120 LOC)
  - FLT_Proofs/MathLib/Exchangeability.lean (NEW, ~150 LOC)
  - FLT_Proofs/Complexity/Symmetrization.lean (MODIFIED — imports new files, removes moved code)
  - FLT_Proofs/Theorem/PACBayes.lean (MODIFIED — imports KLDivergence, removes moved code)
  - FLT_Proofs/Theorem/Separation.lean (MODIFIED — imports Concentration, removes moved code)
sorry_budget: 0
M-type: M-DefinitionRepair (type architecture extraction)
HC: 0.25
---

# Pure Math Extraction: Typeclasses for Concentration, KL Divergence, Exchangeability

## Architectural Goal

Expose the deep typing of every theorem by separating pure mathematics into
its own layer with appropriate typeclasses. Learning theory becomes a collection
of functions OVER abstract mathematical domains, not a monolith that reinvents
probability infrastructure inline.

```
MathLib/ (pure math, zero learning-theory types)
  ├── ChoquetCapacity.lean       (already done, 416 LOC)
  ├── AnalyticMeasurability.lean  (already done, 110 LOC)
  ├── Concentration.lean          (NEW: BoundedRandomVariable, Hoeffding, Chebyshev voting)
  ├── KLDivergence.lean           (NEW: FinitePMF, KL divergence, cross-entropy)
  └── Exchangeability.lean        (NEW: ExchangeableSample, DoubleSampleMeasure, ValidSplit)
        │
        ▼ imports
Learning Theory Types (Concept, ConceptClass, MeasurableConceptClass, ...)
        │
        ▼ imports
Theorems (PAC, Separation, PACBayes, Online, ...)
```

---

## FILE 1: `MathLib/Concentration.lean` (~200 LOC)

### What Moves Here

| # | Declaration | From | Lines | Pure Math? |
|---|-------------|------|-------|------------|
| 1 | `chebyshev_majority_bound` | Separation.lean | 155-165 + proof | Yes — iIndepSet, indicator RVs, variance |
| 2 | `hoeffding_one_sided` wrapper | Symmetrization.lean | 188-196 | Partially — uses EmpiricalError/TrueErrorReal |
| 3 | `hoeffding_one_sided_upper` wrapper | Symmetrization.lean | 1914-1922 | Same |

### Typeclass: `BoundedRandomVariable`

```lean
/-- A random variable taking values in [a, b] almost everywhere.
    This is the hypothesis that Hoeffding, McDiarmid, Efron-Stein,
    and Chebyshev-based concentration bounds all require. -/
class BoundedRandomVariable {Ω : Type*} [MeasurableSpace Ω]
    (f : Ω → ℝ) (μ : MeasureTheory.Measure Ω) (a b : ℝ) : Prop where
  ae_mem_Icc : ∀ᵐ ω ∂μ, f ω ∈ Set.Icc a b
  measurable : Measurable f
```

**Mathlib bridge:**
- `BoundedRandomVariable f μ a b → MemLp f ∞ μ` (ae-bounded → L∞)
- `BoundedRandomVariable f μ a b → Integrable f μ` (bounded → integrable)
- `BoundedRandomVariable f μ 0 1 → HasSubgaussianMGF` (Hoeffding's lemma, if we need it)

**Who uses it:**
- `chebyshev_majority_bound`: each indicator 1_{events j} is BoundedRandomVariable _ _ 0 1
- `hoeffding_one_sided`: the loss indicator is BoundedRandomVariable _ _ 0 1
- Future: McDiarmid, Efron-Stein (not yet in kernel but planned)

### What `chebyshev_majority_bound` Becomes

Currently (Separation.lean:155):
```lean
private lemma chebyshev_majority_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    {k : ℕ} {δ : ℝ} (h_delta_pos : 0 < δ)
    (hk : (9 : ℝ) / δ ≤ k)
    (events : Fin k → Set Ω)
    (hevents_meas : ∀ j, MeasurableSet (events j))
    (hindep : ProbabilityTheory.iIndepSet (fun j => events j) μ)
    (hprob : ∀ j, μ (events j) ≥ ENNReal.ofReal (2/3)) :
    μ {ω | k < 2 * (Finset.univ.filter (fun j => ω ∈ events j)).card} ≥
      ENNReal.ofReal (1 - δ)
```

After extraction — drops `private`, moves to Concentration.lean. No type change needed.
The theorem is ALREADY pure math (no learning-theory types). It just needs to be
in the right file.

### Hoeffding: Partial Extraction

`hoeffding_one_sided` uses `EmpiricalError`, `TrueErrorReal`, `zeroOneLoss` in its
statement. These are learning-theory types. So the theorem itself cannot move verbatim.

**Strategy**: Extract a PURE Hoeffding bound:

```lean
/-- Pure one-sided Hoeffding: for m iid [0,1]-bounded random variables with mean p,
    Pr[sample mean ≤ p - t] ≤ exp(-2mt²). -/
theorem hoeffding_iid_one_sided
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    {m : ℕ} (hm : 0 < m) (t : ℝ) (ht : 0 < t)
    (f : Fin m → Ω → ℝ)
    (hf_bounded : ∀ i, BoundedRandomVariable (f i) μ 0 1)
    (hf_indep : ProbabilityTheory.iIndepFun (fun _ => inferInstance) f μ)
    (p : ℝ) (hp : ∀ i, ∫ ω, f i ω ∂μ = p) :
    μ {ω | (∑ i, f i ω) / m ≤ p - t} ≤
      ENNReal.ofReal (Real.exp (-2 * m * t ^ 2)) := by
  sorry -- this is the actual Hoeffding proof, currently wired through Mathlib's SubGaussian
```

Then `hoeffding_one_sided` in Symmetrization.lean becomes a COROLLARY that
instantiates f i = indicator of loss, p = TrueErrorReal, and applies the pure version.

**DECISION POINT**: This refactoring of Hoeffding into pure + corollary is NONTRIVIAL.
The current proof in Symmetrization.lean is ~400 LOC and tightly woven with the
learning-theory types. Extracting it requires rewriting the proof to factor through
the pure statement.

**Recommendation**: For this session, move `chebyshev_majority_bound` (which IS pure)
and DEFINE the `BoundedRandomVariable` typeclass + Mathlib bridges. Leave the Hoeffding
factoring as a follow-up task — it's a proof rewrite, not a structural extraction.

### Concentration.lean Contents (Phase 1)

```
- BoundedRandomVariable class (5 LOC)
- BoundedRandomVariable → Integrable bridge (5 LOC)
- BoundedRandomVariable → MemLp ∞ bridge (5 LOC)
- chebyshev_majority_bound (moved from Separation.lean, ~50 LOC)
- Section header + docstrings (~20 LOC)
```

~85 LOC for Phase 1. The Hoeffding pure extraction is Phase 2.

### Imports

```lean
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
```

Zero learning-theory imports.

---

## FILE 2: `MathLib/KLDivergence.lean` (~120 LOC)

### What Moves Here

| # | Declaration | From | Lines | Pure Math? |
|---|-------------|------|-------|------------|
| 1 | `FinitePMF` structure | PACBayes.lean | 41-44 | Yes |
| 2 | `klDivFinPMF` | PACBayes.lean | 49-52 | Yes |
| 3 | `crossEntropyFinitePMF` | PACBayes.lean | 56-59 | Yes |
| 4 | `expectFinPMF` | PACBayes.lean | 62-64 | Yes |
| 5 | `jensen_sqrt_finpmf` | PACBayes.lean | ~350 | Yes — pure Jensen's inequality |

### Typeclass: `HasFiniteKL`

```lean
/-- A finite probability mass function over a Fintype. -/
structure FinitePMF (H : Type*) [Fintype H] where
  prob : H → ℝ
  prob_nonneg : ∀ h, 0 ≤ prob h
  prob_sum_one : ∑ h, prob h = 1

/-- KL divergence between two finite PMFs. -/
noncomputable def klDiv {H : Type*} [Fintype H]
    (Q P : FinitePMF H) : ℝ :=
  ∑ h, Q.prob h * Real.log (Q.prob h / P.prob h)

/-- Expected value under a finite PMF. -/
noncomputable def expectFinPMF {H : Type*} [Fintype H]
    (Q : FinitePMF H) (f : H → ℝ) : ℝ :=
  ∑ h, Q.prob h * f h

/-- Cross-entropy between two finite PMFs. -/
noncomputable def crossEntropy {H : Type*} [Fintype H]
    (Q P : FinitePMF H) : ℝ :=
  ∑ h, Q.prob h * Real.log (1 / P.prob h)

/-- Typeclass: the prior has full support (needed for KL to be well-defined). -/
class HasPositivePrior {H : Type*} [Fintype H] (P : FinitePMF H) : Prop where
  pos : ∀ h, 0 < P.prob h
```

### What Changes in PACBayes.lean

PACBayes.lean currently defines FinitePMF, klDivFinPMF, crossEntropyFinitePMF,
expectFinPMF at the top of the file. After extraction:

```lean
import FLT_Proofs.MathLib.KLDivergence
```

Remove the moved definitions. Keep:
- `gibbsError`, `gibbsEmpError` (these reference `TrueErrorReal`, `EmpiricalError` — learning types)
- `pac_bayes_per_hypothesis`, `pac_bayes_all_hypotheses`, `pac_bayes_finite` (theorems)

The `gibbsError` and `gibbsEmpError` are learning-theory definitions that USE
`expectFinPMF` but ADD learning-theory types. They stay in PACBayes.lean.

### Mathlib Bridge

```lean
/-- Bridge: FinitePMF → Mathlib's PMF. -/
noncomputable def FinitePMF.toPMF {H : Type*} [Fintype H]
    (P : FinitePMF H) : PMF H :=
  ⟨fun h => ENNReal.ofReal (P.prob h),
   by ... -- sum of ENNReal.ofReal of nonneg reals with sum 1 = 1⟩
```

This bridge is a nice-to-have, not blocking. Can be added later.

### KLDivergence.lean Contents

```
- FinitePMF structure (5 LOC)
- klDiv definition (5 LOC)
- crossEntropy definition (5 LOC)
- expectFinPMF definition (5 LOC)
- HasPositivePrior class (3 LOC)
- klDiv_nonneg lemma (Gibbs' inequality, ~20 LOC)
- jensen_sqrt_finpmf (moved from PACBayes, ~30 LOC)
- Section headers + docstrings (~25 LOC)
```

~100 LOC.

### Imports

```lean
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
```

Zero learning-theory imports.

---

## FILE 3: `MathLib/Exchangeability.lean` (~150 LOC)

### What Moves Here

| # | Declaration | From | Lines | Pure Math? |
|---|-------------|------|-------|------------|
| 1 | `DoubleSampleMeasure` | Symmetrization.lean | 60-63 | Yes |
| 2 | `MergedSample` | Symmetrization.lean | 69 | Yes |
| 3 | `mergeSamples` | Symmetrization.lean | 77-83 | Yes |
| 4 | `splitMergedSample` | Symmetrization.lean | 87-90 | Yes |
| 5 | `ValidSplit` | Symmetrization.lean | 97-102 | Yes |
| 6 | `SplitMeasure` | Symmetrization.lean | 123-126 | Yes |
| 7 | `splitFirst` | Symmetrization.lean | 129-133 | Yes |
| 8 | `splitSecond` | Symmetrization.lean | 136-138 | Yes |

### Typeclass: `ExchangeableSample`

```lean
/-- An exchangeable double sample: two independent copies of the same
    product measure, with infrastructure for merging, splitting, and
    uniformly sampling permutation splits.

    This is the measure-theoretic foundation of symmetrization arguments
    in learning theory, but the structure itself is pure probability:
    product measures + Fin combinatorics + uniform split distributions. -/
structure ExchangeableSample {X : Type*} [MeasurableSpace X] where
  /-- Sample size per copy -/
  m : ℕ
  /-- Base probability measure on X -/
  μ : MeasureTheory.Measure X
  /-- Base is a probability measure -/
  hμ : MeasureTheory.IsProbabilityMeasure μ
```

**Key question**: Is `ExchangeableSample` a typeclass (`class`) or a structure?

**Answer**: Structure. It bundles data (m, μ) not a property. You don't want
`[ExchangeableSample X]` globally — you want to construct a specific sample for
a specific proof. The structure provides the API; the learning-theory files
construct instances.

### What the Definitions Look Like After Extraction

Currently in Symmetrization.lean:
```lean
noncomputable def DoubleSampleMeasure
    {X : Type u} [MeasurableSpace X]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D] (m : ℕ) :
    MeasureTheory.Measure ((Fin m → X) × (Fin m → X)) :=
  (MeasureTheory.Measure.pi (fun _ : Fin m => D)).prod
    (MeasureTheory.Measure.pi (fun _ : Fin m => D))
```

This moves verbatim. Zero type changes. The function takes a generic
probability measure D and sample size m — no learning-theory types.

### Exchangeability.lean Contents

```
- ExchangeableSample structure (8 LOC)
- DoubleSampleMeasure def (5 LOC)
- MergedSample type alias (2 LOC)
- mergeSamples def (8 LOC)
- splitMergedSample def (5 LOC)
- ValidSplit structure (8 LOC)
- SplitMeasure def (5 LOC)
- splitFirst, splitSecond defs (8 LOC)
- merge/split inverse lemmas if any (~20 LOC)
- Section headers + docstrings (~30 LOC)
```

~100 LOC.

### Imports

```lean
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
```

Zero learning-theory imports. (Currently these are imported by Symmetrization.lean.)

---

## FILE 4: Symmetrization.lean MODIFICATIONS

### What Changes

1. **Add import**: `import FLT_Proofs.MathLib.Exchangeability`
2. **Remove**: Lines 45-138 (DoubleSampleMeasure through splitSecond)
3. **Keep**: Everything else (all theorems referencing EmpiricalError, TrueErrorReal, etc.)

The Hoeffding theorems stay in Symmetrization.lean for now (Phase 1). They use
learning-theory types in their statements. A future Phase 2 would factor them
into pure + corollary.

### Risk

Medium. Symmetrization.lean is 3000+ lines. Removing 90 lines of definitions and
adding an import SHOULD be safe, but any `private` helper that references the
moved definitions needs to be checked.

**Mitigation**: Build after every change. The moved definitions have the SAME names
and types — if Symmetrization.lean just imports Exchangeability.lean, all references
resolve to the same names.

---

## FILE 5: Separation.lean MODIFICATIONS

### What Changes

1. **Add import**: `import FLT_Proofs.MathLib.Concentration`
2. **Remove**: `chebyshev_majority_bound` (~50 LOC) — currently `private`
3. **Keep**: `boost_two_thirds_to_pac` which CALLS chebyshev_majority_bound

**Critical**: `chebyshev_majority_bound` is `private` in Separation.lean. Moving it
to Concentration.lean makes it public. The call site in `boost_two_thirds_to_pac`
must now reference `chebyshev_majority_bound` without the private qualifier.

---

## FILE 6: PACBayes.lean MODIFICATIONS

### What Changes

1. **Add import**: `import FLT_Proofs.MathLib.KLDivergence`
2. **Remove**: Lines 41-64 (FinitePMF, klDivFinPMF, crossEntropyFinitePMF, expectFinPMF)
3. **Keep**: gibbsError, gibbsEmpError, all pac_bayes_* theorems

---

## MeasurableConceptClass PROPAGATION (Bonus, Optional)

7 theorems in Symmetrization.lean pass `(hmeas_C : ∀ h ∈ C, Measurable h)` explicitly.
The `MeasurableConceptClass` typeclass (Measurability.lean:60) bundles this.
PAC.lean already migrated. Symmetrization.lean didn't.

**This is a separate refactoring** — it changes theorem signatures, which is riskier
than moving code. Recommend doing it in a follow-up session, not in this extraction.

---

## KK/KU/UK/UU Partition

| Quadrant | Content |
|----------|---------|
| **KK** | All moved declarations are self-contained pure math. Zero learning-theory types in DoubleSampleMeasure, ValidSplit, FinitePMF, chebyshev_majority_bound. Mathlib has `iIndepSet`, `Measure.pi`, `Measure.prod`, `Real.log`, `Finset.sum`. |
| **KU** | (1) Does `chebyshev_majority_bound` reference any learning-theory type transitively? Must verify. (2) Does removing `private` from `chebyshev_majority_bound` cause name collisions? (3) Do any `private` helpers in Symmetrization.lean between lines 45-138 get used by the moved code? (4) The `jensen_sqrt_finpmf` proof — does it reference any PACBayes-specific infrastructure? |
| **UK** | The import DAG must not create cycles. Currently: Symmetrization imports nothing from MathLib/. After: Symmetrization imports Exchangeability. PACBayes imports KLDivergence. Separation imports Concentration. All unidirectional — no cycles. |
| **UU** | Whether the `ExchangeableSample` structure is useful as-is, or whether the definitions should stay as standalone functions (as they are now) without a bundling structure. The structure adds no mathematical content — it's purely organizational. |

### KU Resolution

**KU1**: `chebyshev_majority_bound` uses: `MeasurableSpace`, `Measure`, `IsProbabilityMeasure`,
`iIndepSet`, `MeasurableSet`, `ENNReal.ofReal`, `Finset`. All pure Mathlib types. Confirmed: no
learning-theory types.

**KU2**: Making it non-private is safe. The name `chebyshev_majority_bound` is unique in the
kernel (grep confirms single definition).

**KU3**: Lines 45-138 in Symmetrization.lean: `DoubleSampleMeasure`, `MergedSample`,
`mergeSamples`, `splitMergedSample`, `ValidSplit`, `SplitMeasure`, `splitFirst`, `splitSecond`.
None of these are `private`. None reference private helpers. They're standalone definitions.

**KU4**: `jensen_sqrt_finpmf` proof: need to read it to confirm. If it uses `gibbsError`
or learning types, it stays in PACBayes.lean.

---

## Execution Plan

### Phase 1: KLDivergence.lean (lowest risk — PACBayes.lean is small)

1. Create MathLib/KLDivergence.lean with FinitePMF, klDiv, expectFinPMF, crossEntropy, HasPositivePrior
2. Build `lake build FLT_Proofs.MathLib.KLDivergence`
3. Modify PACBayes.lean: add import, remove moved definitions
4. Build `lake build FLT_Proofs.Theorem.PACBayes`

### Phase 2: Exchangeability.lean (medium risk — Symmetrization.lean is large)

5. Create MathLib/Exchangeability.lean with DoubleSampleMeasure, ValidSplit, merge/split
6. Build `lake build FLT_Proofs.MathLib.Exchangeability`
7. Modify Symmetrization.lean: add import, remove lines 45-138
8. Build `lake build FLT_Proofs.Complexity.Symmetrization`

### Phase 3: Concentration.lean (medium risk — Separation.lean has private lemma)

9. Create MathLib/Concentration.lean with BoundedRandomVariable + chebyshev_majority_bound
10. Build `lake build FLT_Proofs.MathLib.Concentration`
11. Modify Separation.lean: add import, remove chebyshev_majority_bound
12. Build `lake build FLT_Proofs.Theorem.Separation`

### Phase 4: Full build

13. `lake build` — 0 errors
14. Grep for sorry in all 6 modified/new files — must be 0
15. Verify line counts

---

## Agent Guardrails

1. NEVER run `git checkout`, `git restore`, or any working-tree discard command
2. Build after EVERY file creation and EVERY file modification
3. Zero sorrys in all files
4. Do NOT change any theorem statement or proof body — only MOVE code
5. Preserve exact content of moved declarations (except removing `private` where needed)
6. Do NOT attempt the MeasurableConceptClass propagation — that's a separate task
7. If a moved declaration references a `private` helper, move the helper too
8. If Phase N fails, do NOT proceed to Phase N+1 — fix Phase N first
9. Add `open` statements matching what the source file currently has

---

## Summary

| File | Action | LOC delta |
|------|--------|-----------|
| MathLib/Concentration.lean | NEW | +85 |
| MathLib/KLDivergence.lean | NEW | +100 |
| MathLib/Exchangeability.lean | NEW | +100 |
| Symmetrization.lean | MODIFIED | -90 |
| PACBayes.lean | MODIFIED | -25 |
| Separation.lean | MODIFIED | -50 |

**Net new LOC**: ~120 (headers/docstrings). Zero new theorems, zero new sorrys.
Three new typeclasses: `BoundedRandomVariable`, `HasPositivePrior`, `ExchangeableSample`.
Pure structural extraction exposing the deep typing of every theorem.
