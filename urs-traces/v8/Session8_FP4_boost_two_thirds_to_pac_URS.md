---
session: 8
date: 2026-03-26
task_id: FP4
target: boost_two_thirds_to_pac (full 7/12-fraction architecture)
file: FLT_Proofs/Theorem/Separation.lean
status: closed
---

## URS: FP4 — `boost_two_thirds_to_pac` (Separation.lean line 419)

**Date**: 2026-03-26 | **File**: `FLT_Proofs/Theorem/Separation.lean`
**Target**: Close the sorry at line 419 inside `boost_two_thirds_to_pac`
**HC**: 0.50 | **LOC**: ~150-200

### 0. Will — The Corrected Route

The current proof body (lines 342-419) already has:
- L' (boosted learner) constructed (lines 345-362)
- mf (sample complexity) constructed (lines 370-379)
- `intro ε δ hε hδ D hD c hcC` already done (line 381)
- sorry at line 419

The proof has 3 obstructions resolved by the following architecture:

**O1 (Measurability)**: Add `LearnEvalMeasurable L` and `hc_meas` hypotheses to the theorem. This is an interface change — the theorem becomes stronger (requires regularity) but the caller `universal_imp_pac` must also be updated.

**O2 (Mathematical gap)**: Replace the broken `k·rate(n) < ε` argument with the **7/12-fraction argument**:
- Demand ≥ 7k/12 good blocks (not just k/2)
- Majority error ≤ 7·rate(n) via Markov on good-block disagreements
- Choose `rate(n) < ε/7` so majority error < ε
- Chebyshev with threshold 7k/12 needs constant 36 (not 9)

**O3 (Majority formalization)**: For fixed ω with ≥ 7k/12 good blocks:
- If majority wrong at x, then ≥ g - k/2 good blocks also wrong
- Since g ≥ 7k/12, gap = g - k/2 ≥ k/12
- E_D[Y_ω] ≤ g·rate(n), Markov gives D(majority wrong) ≤ g·rate(n)/(g-k/2) ≤ 7·rate(n)

### 1. KK — What Exists

| Lemma | Location | Status |
|-------|----------|--------|
| `chebyshev_majority_bound` | Sep:152-310 | ✅ sorry-free, threshold k/2, constant 9 |
| `block_extract k m S j` | Gen:2620 | ✅ |
| `block_extract_measurable` | Gen:2641 | ✅ |
| `block_extract_disjoint` | Gen:2628 | ✅ |
| `iIndepFun_block_extract` | Gen:2648 | ✅ |
| `boosted_majority` | Sep:145 | ✅ |
| `Nat.sqrt_add_eq` | Mathlib | ✅ |
| `MeasureTheory.measurable_measure_prod_mk_left` | Mathlib | ✅ |

### 2. Interface Changes Required

**Step 0a**: Change `boost_two_thirds_to_pac` signature to add regularity:

```lean
private theorem boost_two_thirds_to_pac (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool)
    (L : BatchLearner X Bool) (rate : ℕ → ℝ)
    (hL_meas : ∀ m, Measurable (fun p : (Fin m → X × Bool) × X => L.learn p.1 p.2))
    (hc_meas : ∀ c ∈ C, Measurable c)
    (hrate : ∀ ε > 0, ∃ m₀, ∀ m ≥ m₀, rate m < ε)
    (huniv : ...) :
    PACLearnable X C
```

**Step 0b**: Update caller `universal_imp_pac` (Sep:427-431) to supply the new hypotheses. This requires either:
- Adding `hL_meas` and `hc_meas` to `universal_imp_pac`'s signature, OR
- Deriving them from `UniversalLearnable` (which may need strengthening)

**Decision**: Add them to `universal_imp_pac` and propagate to `universal_trichotomy` Branch 3 in Extended.lean. Check that `universal_trichotomy` callers don't break (kill check showed zero external callers).

### 3. New Helper Lemmas

**Helper 1**: `chebyshev_seven_twelfths_bound` (~modify existing or new)

The existing `chebyshev_majority_bound` uses threshold k/2 and constant 9/δ ≤ k. We need threshold 7k/12 and constant 36/δ ≤ k. Two options:
- (a) Generalize `chebyshev_majority_bound` to parameterize the threshold
- (b) Write a new lemma

Option (b) is safer — don't touch proved code:

```lean
private lemma chebyshev_seven_twelfths_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    {k : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (hk : (36 : ℝ) / δ ≤ k)
    (events : Fin k → Set Ω)
    (hevents_meas : ∀ j, MeasurableSet (events j))
    (hindep : ProbabilityTheory.iIndepSet events μ)
    (hprob : ∀ j, μ (events j) ≥ ENNReal.ofReal (2/3)) :
    μ {ω | 7 * k ≤ 12 * (Finset.univ.filter (fun j => ω ∈ events j)).card}
      ≥ ENNReal.ofReal (1 - δ)
```

Proof: Same structure as `chebyshev_majority_bound` but with gap = k·(2/3 - 7/12) = k/12, variance ≤ k/4, Chebyshev gives P(S < 7k/12) ≤ (k/4)/(k/12)² = 36/k ≤ δ.

**Helper 2**: `majority_error_le_seven_rate` (~30 LOC)

For fixed ω with ≥ 7k/12 good blocks:

```lean
private lemma majority_error_le_seven_rate
    {X : Type u} [MeasurableSpace X]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (k n : ℕ) (c : Concept X Bool) (hc : Measurable c)
    (hypotheses : Fin k → Concept X Bool)
    (h_hyp_meas : ∀ j, Measurable (hypotheses j))
    (r : ℝ) (hr : 0 ≤ r)
    (goodIdx : Finset (Fin k))
    (hgood : ∀ j ∈ goodIdx, D {x | hypotheses j x ≠ c x} ≤ ENNReal.ofReal r)
    (hfrac : 7 * k ≤ 12 * goodIdx.card) :
    D {x | boosted_majority k (fun j => hypotheses j x) ≠ c x}
      ≤ ENNReal.ofReal (7 * r)
```

Proof route:
1. If majority wrong at x, then > k/2 hypotheses wrong
2. At most k - goodIdx.card bad blocks can be wrong
3. So ≥ (k/2 + 1) - (k - goodIdx.card) = goodIdx.card - k/2 + 1 good blocks wrong
4. Since 7k ≤ 12·g, g ≥ 7k/12, so g - k/2 ≥ k/12
5. Define Y(x) = #{j ∈ goodIdx : hypotheses j x ≠ c x}
6. {majority wrong} ⊆ {Y ≥ g - k/2}
7. E_D[Y] = Σ_{j ∈ goodIdx} D(h_j ≠ c) ≤ g·r
8. Markov: D(Y ≥ g-k/2) ≤ g·r/(g-k/2) ≤ (7k/12)·r / (k/12) = 7r

### 4. Corrected Proof Parameters

Replace the current parameters (lines 373-377) with:

```
kmin := ⌈36/δ⌉ + 2
ε' := ε/7
m₀ := Nat.find(hrate ε' ...)
n := max m₀ (kmin - 1)
k := n + 1
m := (n+1) * n
```

This gives:
- k ≥ kmin ≥ 36/δ + 2 > 36/δ ✓
- rate(n) < ε/7 (from n ≥ m₀) ✓
- 7·rate(n) < ε ✓
- Chebyshev with 36/δ ≤ k gives P(≥ 7k/12 good) ≥ 1-δ ✓

### 5. Proof Skeleton (replacing sorry at line 419)

```
-- Step 3.1: Parameter extraction
simp only [L', ...] at *
set kmin := ⌈36/δ⌉ + 2
set ε' := ε/7
set m₀ := Nat.find(hrate ε' ...)
set n := max m₀ (kmin - 1)
set k := n + 1
-- Derive: hk_ge : 36/δ ≤ k, hrate_n : rate n < ε/7

-- Step 3.2: Learner unfolding
-- Show Nat.sqrt((n+1)*n) = n, so L' uses k blocks of size n
-- Show blk = n > 0, so majority branch entered

-- Step 3.3: Define block-good events
set events : Fin k → Set (Fin (k*n) → X) := fun j =>
  {ω | D {x | L.learn (fun i => (block_extract k n ω j i, c (block_extract k n ω j i))) x ≠ c x}
    ≤ ENNReal.ofReal (rate n)}

-- Step 3.4: Measurability (from hL_meas + hc_meas + measurable_measure_prod_mk_left)
have hevents_meas : ∀ j, MeasurableSet (events j) := ...

-- Step 3.5: Independence (from iIndepFun_block_extract → iIndepSet)
have hindep : iIndepSet events μ := ...

-- Step 3.6: Marginal probability (block marginal = D^n → huniv)
have hprob : ∀ j, μ (events j) ≥ ofReal(2/3) := ...

-- Step 3.7: Concentration (chebyshev_seven_twelfths_bound)
have hconc := chebyshev_seven_twelfths_bound hδ hk events hevents_meas hindep hprob

-- Step 3.8: Event containment (majority_error_le_seven_rate)
have hcontain : {ω | 7*k ≤ 12*(good count)} ⊆ {ω | D{majority wrong} ≤ ofReal ε} := ...

-- Step 3.9: Compose
exact le_trans hconc (μ.mono hcontain)
```

### 6. File Access

**WRITE**: `FLT_Proofs/Theorem/Separation.lean` (main edits)
**WRITE**: `FLT_Proofs/Theorem/Extended.lean` (propagate `universal_imp_pac` change if needed)
**READ**: Any file
**DO NOT TOUCH**: Proved infrastructure (chebyshev_majority_bound, block_extract lemmas, etc.)

### 7. Termination

- `lake build` passes with 0 errors
- `grep -n sorry FLT_Proofs/Theorem/Separation.lean` shows no sorry
- A4: boost_two_thirds_to_pac requires genuine concentration + majority analysis
- A5: conclusion `PACLearnable X C` unchanged

### 8. Guardrails

- A4/A5 checks after every edit
- MUST close the sorry. No new sorry acceptable.
- Do not simplify — follow the 7/12-fraction architecture
- The interface change (adding regularity hypotheses) must propagate cleanly

---

This is a big proof. My honest HC assessment: 0.50 for the full thing, but the agent may need guidance on O1 (interface propagation) and O3 (majority Markov formalization). The helpers (`chebyshev_seven_twelfths_bound`, `majority_error_le_seven_rate`) are each ~50-80 LOC.