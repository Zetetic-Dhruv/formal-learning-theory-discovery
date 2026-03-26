---
session: 8
date: 2026-03-25
task_id: FP5
target: advice_elimination
file: FLT_Proofs/Theorem/Extended.lean
status: closed
versions: 4
---

# URS: FP5 — advice_elimination (3 sorrys → 0)

**Date**: 2026-03-25 | **File**: `FLT_Proofs/Theorem/Extended.lean`
**Target**: Close lines 648, 906, 931 — all inside `advice_elimination`
**Route**: Replace SuccessProd transport with measurable GoodPair + monotonicity
**Status**: OPEN — 3 sorrys, 0 closed

---

## 0. Will — Discovery Axiom

The previous agent attempted to prove `MeasurableSet SuccessProd` and transport SuccessProd through the pullback chain. That route is **architecturally wrong**. `bestAdvice` uses `Classical.choose` making the selection function non-measurable as a function of the validation sample — but that is NOT the fundamental issue. The fundamental issue is: **you do not need the selected hypothesis to be measurable as a function of the pair sample. You only need a measurable good event that implies success.**

The corrected route:
1. Define `GoodPair` (measurable inner event on product space)
2. Prove `GoodPair ⊆ SuccessProd` (deterministic implication)
3. Lower-bound `(μ₁.prod μ₂)(GoodPair)` (from proved helpers)
4. Transport `GoodPair` (not SuccessProd) back through the pullback chain
5. Conclude by measure monotonicity

This eliminates all three sorrys simultaneously. The `MeasurableSet SuccessProd` sorry disappears (no longer needed). The transport sorry disappears (GoodPair is measurable, subset containment replaces set equality). The product-space bound sorry disappears (standard application of proved helpers on GoodPair).

**Termination condition**: `advice_elimination` sorry-free (excluding `bhmz_middle_branch` at line 38 which is a separate theorem).

---

## 1. KK Universe — What We Know

### Proved Helper Lemmas (all sorry-free, in Extended.lean)

| # | Lemma | Line | Signature Summary |
|---|-------|------|-------------------|
| KK_1 | `learnWithAdvice_measurable_fixed` | 130 | `AdviceEvalMeasurable LA → Measurable (LA.learnWithAdvice a S)` for fixed `a`, `S` |
| KK_2 | `trueErrorReal_le_of_bestAdvice` | 137 | `(∀ a, \|TrueErr - EmpErr\| ≤ η) → TrueErr(aStar) ≤ τ → TrueErr(bestAdvice) ≤ τ + 2η` |
| KK_3 | `finite_validation_family_bound` | 160 | `μ₂ {xs \| ∃ a, \|TrueErr - EmpErr\| ≥ η} ≤ ofReal(\|A\|·2·exp(-2mη²))` |
| KK_4 | `prob_ge_one_sub_compl` | 256 | `μ(Sᶜ) ≤ δ → μ(S) ≥ 1 - δ` |
| KK_5 | `product_complement_bound` | 272 | `μ(GoodTrainᶜ) ≤ δ₁, ∀ x₁ ν{bad} ≤ δ₂ → (μ×ν)(GT ∩ GV) ≥ 1-(δ₁+δ₂)` |
| KK_6 | `pi_cylinder_set_eq` | 313 | Marginalizes junk coordinates: `D^ι(cylinder S) = D^p(S)` — **requires MeasurableSet S** |
| KK_7 | `pi_uniform_conditional_bound` | 344 | Uniform conditional → marginal: **requires MeasurableSet S** |
| KK_8 | `nat_pair_sample_marginal` | 425 | `D^N(usedPrefix⁻¹' S) = D^{m₁+m₂}(S)` — **requires MeasurableSet S** |
| KK_9 | `used_sample_split_measure` | 471 | `D^{m₁+m₂}(splitUsedEquiv⁻¹' S) = (μ₁×μ₂)(S)` — **requires MeasurableSet S** |
| KK_10 | `usedPrefix` | 401 | `(Fin (Nat.pair m₁ m₂) → X) → (Fin (m₁+m₂) → X)` via `Fin.castLE` |
| KK_11 | `splitUsedEquiv` | 406 | `MeasurableEquiv`: `(Fin (m₁+m₂) → X) ≃ᵐ (Fin m₁ → X) × (Fin m₂ → X)` |

### Key Types

```lean
TrueError X h c D : ENNReal := D {x | h x ≠ c x}
TrueErrorReal X h c D : ℝ := (TrueError X h c D).toReal
EmpiricalError X Bool h S loss : ℝ  -- (1/m) * Σ loss(h(xᵢ), yᵢ)
bestAdvice cand Sval : A  -- Classical.choose of Finset.exists_min_image
```

### Proof Context (lines 553–572, already compiled)

After `case pac =>` and `simp only [Nat.unpair_pair]`, the goal is:
```
⊢ MeasureTheory.Measure.pi (fun _ : Fin (Nat.pair m₁ m₂) => D)
    {xs | D {x | (let train := fun i => (xs ⟨↑i, _⟩, c (xs ⟨↑i, _⟩))
                  let val := fun j => (xs ⟨m₁ + ↑j, _⟩, c (xs ⟨m₁ + ↑j, _⟩))
                  let cand := fun a => LA.learnWithAdvice a train
                  cand (bestAdvice cand val)) x ≠ c x} ≤ ENNReal.ofReal ε}
  ≥ ENNReal.ofReal (1 - δ)
```

with `aStar : A`, `haStar` giving the training bound, `m₁ = mf_adv (ε/2) (δ/2)`, `m₂ = ⌈(8/ε²) · log(4|A|/δ)⌉ + 1`.

---

## 2. KU Universe — The Restructured Proof

### KU_0: DELETE lines 560–931

Delete the entire `SuccessProd` definition and the `suffices h_prod` block (lines 560–931). Everything from `-- Product-space success event` through the final `sorry` goes. Replace with Steps 1–5 below.

### KU_1: Define GoodPair (measurable inner event)

```lean
let μ₁ := MeasureTheory.Measure.pi (fun _ : Fin m₁ => D)
let μ₂ := MeasureTheory.Measure.pi (fun _ : Fin m₂ => D)

-- GoodTrain: the distinguished advice aStar produces a hypothesis with TrueError ≤ ε/2
let GoodTrain : Set (Fin m₁ → X) :=
  {xs₁ | TrueError X
    (LA.learnWithAdvice aStar (fun i => (xs₁ i, c (xs₁ i)))) c D
    ≤ ENNReal.ofReal (ε / 2)}

-- BadVal: some candidate has empirical error far from true error
let BadVal : Set ((Fin m₁ → X) × (Fin m₂ → X)) :=
  {p | let train : Fin m₁ → X × Bool := fun i => (p.1 i, c (p.1 i))
       let val   : Fin m₂ → X × Bool := fun j => (p.2 j, c (p.2 j))
       let cand  : A → Concept X Bool := fun a => LA.learnWithAdvice a train
       ∃ a : A,
         |TrueErrorReal X (cand a) c D -
           EmpiricalError X Bool (cand a) val (zeroOneLoss Bool)| ≥ ε / 4}

-- GoodPair: training succeeds AND validation is accurate
let GoodPair : Set ((Fin m₁ → X) × (Fin m₂ → X)) :=
  {p | p.1 ∈ GoodTrain ∧ p ∉ BadVal}
```

**Measurability**: `GoodTrain` is measurable from `AdviceEvalMeasurable` (fixed `a = aStar`, compose with `measurable_measure_prod_mk_left`, preimage of `Iic`). `BadVal` is measurable as a finite union (over `A`) of measurable sets (each uses `AdviceEvalMeasurable` for the candidate, `hc_meas` for `c`, and `measurableSet_eq_fun` for the disagreement set). `GoodPair` is the intersection of complements of measurable sets → measurable.

### KU_2: Prove GoodPair ⊆ SuccessProd (deterministic core)

On `GoodPair`, for any `p`:
- `p.1 ∈ GoodTrain`: `TrueError(LA.learnWithAdvice aStar train, c, D) ≤ ofReal(ε/2)`
- `p ∉ BadVal`: `∀ a, |TrueErrorReal(cand a) - EmpErr(cand a, val)| < ε/4`

Convert the `< ε/4` to `≤ ε/4` (negate `≥ ε/4`, get `< ε/4`, then `le_of_lt`).

Apply `trueErrorReal_le_of_bestAdvice` (KK_2) with `τ = ε/2`, `η = ε/4`:
```
TrueErrorReal(cand(bestAdvice), c, D) ≤ ε/2 + 2·(ε/4) = ε
```

Convert `TrueErrorReal ≤ ε` back to `TrueError ≤ ENNReal.ofReal ε`:
- `TrueError ≤ 1` (probability measure, `D(set) ≤ D(univ) = 1`)
- `TrueError ≠ ⊤` (from above)
- `ENNReal.toReal_le_toReal` bridge: `TrueErrorReal ≤ ε → TrueError ≤ ofReal ε`

**Exact Lean bridge** for the `TrueErrorReal ↔ TrueError` conversion:
```lean
have hfinite : TrueError X (cand best) c D ≠ ⊤ := by
  exact ne_of_lt (lt_of_le_of_lt
    (MeasureTheory.measure_mono (Set.subset_univ _))
    (by simp [MeasureTheory.IsProbabilityMeasure.measure_univ]; exact ENNReal.one_lt_top))
-- Then: ENNReal.ofReal_toReal hfinite ▸ ENNReal.ofReal_le_ofReal hsel_real
```

### KU_3: Lower-bound (μ₁.prod μ₂)(GoodPair) ≥ 1 - δ

**Training bound**: From `haStar`:
```
μ₁ GoodTrain ≥ ENNReal.ofReal (1 - δ/2)
```
This is literally `haStar` after unfolding `GoodTrain` and `m₁`. Rename if Lean's definitional unfolding cooperates; use `convert haStar using 2` + `ext` otherwise.

Therefore: `μ₁ GoodTrainᶜ ≤ ENNReal.ofReal (δ/2)`.

**Validation bound**: For each fixed `xs₁ : Fin m₁ → X`:
```
μ₂ {xs₂ | (xs₁, xs₂) ∈ BadVal} ≤ ENNReal.ofReal (δ/2)
```

This instantiates `finite_validation_family_bound` (KK_3) at `η = ε/4`, `m = m₂`:
- `h_cand_meas : ∀ a, Measurable (cand a)` — from `learnWithAdvice_measurable_fixed` (KK_1)
- `hm : 0 < m₂` — from `m₂ = ⌈...⌉ + 1 ≥ 1`
- `hη : 0 < ε/4` — from `hε`
- `hη1 : ε/4 ≤ 1` — **early case split**: if `ε ≥ 4`, the goal is trivially true since `TrueError ≤ 1 ≤ ε`, so the goal set is `Set.univ` with measure 1 ≥ 1-δ. After case split, `ε < 4` gives `ε/4 < 1`.

The Hoeffding bound gives: `≤ ofReal(|A| · 2 · exp(-2 · m₂ · (ε/4)²))`. Need: `|A| · 2 · exp(-2 · m₂ · ε²/16) ≤ δ/2`.

From `m₂ = ⌈(8/ε²) · log(4|A|/δ)⌉ + 1`:
```
2 · m₂ · ε²/16 ≥ 2 · (8/ε²) · log(4|A|/δ) · ε²/16 = log(4|A|/δ)
```
So `exp(-2m₂ε²/16) ≤ δ/(4|A|)`, hence `|A|·2·exp(...) ≤ δ/2`. ✓

This arithmetic is ~30 LOC of `Real.log`/`Real.exp` manipulation. Key Mathlib lemmas:
- `Real.exp_le_exp`, `Real.log_le_log`
- `Nat.le_ceil`, `Nat.lt_add_one_iff`
- `Real.exp_neg_le_of_le` (or manual: `exp(-t) ≤ 1/exp(t)`)

**Product bound**: Manual complement + union bound:
```lean
have hGP_compl_sub : GoodPairᶜ ⊆ {p | p.1 ∉ GoodTrain} ∪ BadVal := by
  intro p hp; simp [GoodPair] at hp; by_cases h : p.1 ∈ GoodTrain
  · exact Or.inr (by tauto)
  · exact Or.inl h
calc (μ₁.prod μ₂) GoodPairᶜ
    ≤ (μ₁.prod μ₂) ({p | p.1 ∉ GoodTrain} ∪ BadVal) :=
        (μ₁.prod μ₂).mono hGP_compl_sub
  _ ≤ (μ₁.prod μ₂) {p | p.1 ∉ GoodTrain} + (μ₁.prod μ₂) BadVal :=
      MeasureTheory.measure_union_le _ _
  _ ≤ ENNReal.ofReal (δ/2) + ENNReal.ofReal (δ/2) :=
      add_le_add htrain_compl hval_compl
  _ = ENNReal.ofReal δ := by
      rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; ring_nf
```

Then `prob_ge_one_sub_compl` (KK_4) gives `(μ₁×μ₂)(GoodPair) ≥ 1 - δ`.

The cylinder set measure `(μ₁×μ₂){p | p.1 ∉ GoodTrain}` uses:
```lean
have : {p : _ × _ | p.1 ∉ GoodTrain} = GoodTrainᶜ ×ˢ Set.univ := by ext; simp
rw [this, MeasureTheory.Measure.prod_prod, MeasureTheory.IsProbabilityMeasure.measure_univ, mul_one]
```
This uses `Measure.prod_prod` which needs `MeasurableSet GoodTrainᶜ` — which IS provable since `GoodTrain` is measurable (KU_1). ✓

### KU_4: Transport GoodPair back to D^N

Define:
```lean
let GoodUsed : Set (Fin (m₁ + m₂) → X) :=
  (splitUsedEquiv (X := X) m₁ m₂) ⁻¹' GoodPair
let GoodFull : Set (Fin (Nat.pair m₁ m₂) → X) :=
  (usedPrefix (X := X) m₁ m₂) ⁻¹' GoodUsed
```

Measurability:
```lean
have hGoodPair_meas : MeasurableSet GoodPair := ...
have hGoodUsed_meas : MeasurableSet GoodUsed :=
  (splitUsedEquiv (X := X) m₁ m₂).measurable.measurableSet_preimage hGoodPair_meas
```

For `GoodFull` measurability:
```lean
have h_usedPrefix_meas : Measurable (usedPrefix (X := X) m₁ m₂) := by
  exact measurable_pi_lambda _ (fun i => measurable_pi_apply _)
```

Measure chain:
```lean
have h_transport :
    MeasureTheory.Measure.pi (fun _ : Fin (Nat.pair m₁ m₂) => D) GoodFull
    = (μ₁.prod μ₂) GoodPair := by
  calc _ = MeasureTheory.Measure.pi (fun _ : Fin (m₁ + m₂) => D) GoodUsed :=
          nat_pair_sample_marginal D m₁ m₂ GoodUsed hGoodUsed_meas
    _ = (μ₁.prod μ₂) GoodPair :=
          used_sample_split_measure D m₁ m₂ GoodPair hGoodPair_meas
```

### KU_5: Subset + monotonicity

Show `GoodFull ⊆ goal_set`. For each `xs : Fin (Nat.pair m₁ m₂) → X`:
- `xs ∈ GoodFull` means `splitUsedEquiv(usedPrefix(xs)) ∈ GoodPair`
- `GoodPair ⊆ SuccessProd` (KU_2) means the hypothesis selected by bestAdvice has `TrueError ≤ ε`
- The access pattern matches: `splitUsedEquiv(usedPrefix(xs)).1 i` has `.val = i.val`, and `splitUsedEquiv(usedPrefix(xs)).2 j` has `.val = m₁ + j.val`

The Fin `.val` matching uses the existing `h_split_fst`, `h_composed_fst` helpers (lines 709–756) or reproves inline with `simp [usedPrefix, splitUsedEquiv, ...]`.

Key: we need the **subset direction only** (not set equality). This is strictly easier than what the old proof attempted.

Conclude:
```lean
calc MeasureTheory.Measure.pi (fun _ : Fin (Nat.pair m₁ m₂) => D) goal_set
    ≥ MeasureTheory.Measure.pi (fun _ : Fin (Nat.pair m₁ m₂) => D) GoodFull :=
        (MeasureTheory.Measure.pi _).mono hGoodFull_sub_goal
  _ = (μ₁.prod μ₂) GoodPair := h_transport
  _ ≥ ENNReal.ofReal (1 - δ) := hGoodPair_prob
```

---

## 3. UK Universe — Known Unknowns

| # | Pressure | Impact | Status |
|---|----------|--------|--------|
| UK_1 | `hη1 : ε/4 ≤ 1` for `finite_validation_family_bound` | MEDIUM | Early case split on `4 ≤ ε`: if yes, goal trivial. After split, `ε < 4` gives `ε/4 < 1`. |
| UK_2 | Arithmetic for `\|A\|·2·exp(-2m₂(ε/4)²) ≤ δ/2` | MEDIUM | ~30 LOC. Use `Nat.le_ceil`, `Real.exp_neg`, `Real.log_le_log`. |
| UK_3 | `TrueErrorReal ↔ TrueError` bridge in KU_2 | MEDIUM | `ENNReal.toReal_le_toReal` needs `≠ ⊤`. Get from `D(set) ≤ D(univ) = 1 < ⊤`. |
| UK_4 | `Measurable (usedPrefix m₁ m₂)` | LOW | `measurable_pi_lambda _ (fun i => measurable_pi_apply _)`. |
| UK_5 | `MeasurableSet GoodTrain` | MEDIUM | Needs `Measurable (fun xs₁ => D {x \| ... })` composed from `AdviceEvalMeasurable`. |
| UK_6 | `MeasurableSet BadVal` — finite union of measurable sets | MEDIUM | Each per-advice set uses `AdviceEvalMeasurable` + finite sum measurability. |
| UK_7 | `Measure.prod_prod` needs `MeasurableSet GoodTrainᶜ` | LOW | Follows from UK_5 + `.compl`. |
| UK_8 | Whether `h_split_fst`/`h_split_snd` helpers survive the rewrite | LOW | Depends only on `splitUsedEquiv` definition, not on SuccessProd. |

---

## 4. UU Boundary

| # | Region |
|---|--------|
| UU_1 | Whether `MeasurableSet GoodTrain` requires `Measurable (fun xs₁ => D {x \| ...})` or can be done via `measurableSet_le` on simpler functions. |
| UU_2 | Whether the `simp` lemma set for `splitUsedEquiv`/`usedPrefix` Fin matching suffices, or manual `Fin.ext` rewrites are needed. |
| UU_3 | Whether `product_complement_bound` (KK_5) can be invoked directly or the manual route is more robust. |

---

## 5. Action Space

| Step | Target | LOC | Pl | Risk |
|------|--------|-----|-----|------|
| 0 | Delete lines 560–931 (SuccessProd + suffices block + sorry) | -371 | 1.0 | NONE |
| 1 | KU_1: Define `GoodTrain`, `BadVal`, `GoodPair`, `GoodUsed`, `GoodFull` + measurability | 40 | 0.85 | UK_5, UK_6 |
| 2 | KU_2: Prove `GoodPair ⊆ SuccessProd` (deterministic core) | 50 | 0.90 | UK_3 |
| 3 | KU_3: Lower-bound `(μ₁.prod μ₂)(GoodPair) ≥ 1-δ` | 70 | 0.80 | UK_1, UK_2 |
| 4 | KU_4: Transport chain `D^N(GoodFull) = (μ₁×μ₂)(GoodPair)` | 15 | 0.95 | LOW |
| 5 | KU_5: Subset `GoodFull ⊆ goal_set` + final `calc` | 30 | 0.85 | UK_8 |

**Total**: ~205 LOC replacing ~371 LOC. Net reduction ~166 lines.

---

## 6. Exclusive File Access

**WRITE**: `FLT_Proofs/Theorem/Extended.lean` lines 560–931 ONLY (inside `case pac`)
**READ**: Any file in the project
**DO NOT TOUCH**: Lines 1–559 (learner construction, helpers), lines 932+ (meta_pac_bound, etc.)
**DO NOT TOUCH**: Any other .lean file

---

## 7. Termination Protocol

**Comp** = (closed sorry sites) / 3
- Target: 3/3 (sorry-free advice_elimination)
- Minimum acceptable: 2/3 with ONE localized sorry documented with exact obstruction

**Inv** = 0.95 (mathematical content is standard; all helpers proved)

**Termination conditions**:
1. `lake build` passes with 0 errors in Extended.lean
2. `grep -n sorry FLT_Proofs/Theorem/Extended.lean` shows ONLY line 38 (`bhmz_middle_branch`)
3. A4 check: no trivially-true sorrys introduced
4. A5 check: no simplification — the theorem statement is UNCHANGED
5. K/U transitions logged for any UK items that resolve

**HARD CONSTRAINT**: Do NOT introduce any new `sorry`. Every intermediate lemma must compile.
**HARD CONSTRAINT**: Do NOT change the theorem statement of `advice_elimination`.
**HARD CONSTRAINT**: Do NOT change helper lemma signatures (lines 1–559).
**HARD CONSTRAINT**: Use **Edit** only — no full-file Write operations.

---

## 8. HC (Hardness Coefficient)

**HC = 0.50** (was 0.75 on the wrong route)

With the corrected architecture:
- Step 1 (definitions + measurability): HC 0.55 — measurability of GoodTrain/BadVal is the crux
- Step 2 (containment): HC 0.45 — deterministic, uses proved helper directly
- Step 3 (product bound): HC 0.60 — Hoeffding arithmetic + ENNReal plumbing
- Step 4 (transport): HC 0.20 — direct application of proved transport lemmas
- Step 5 (subset + monotonicity): HC 0.50 — Fin matching, but subset direction only

The proof is now a standard application of proved infrastructure on a well-chosen measurable event. No Gamma-class obstructions remain.

---

## URS v3: FP5 — advice_elimination (3 sorrys → 0)

**Date**: 2026-03-25 | **File**: `FLT_Proofs/Theorem/Extended.lean`  
**Target**: Close lines 634, 747, 752  
**Route**: Replace suffices-SuccessProd block with GoodPair transport + monotonicity  

### 0. What to preserve (lines 560–628)

Lines 560–628 are CORRECT and COMPILED. Do not touch them. They contain:
- `simp_rw [Nat.unpair_pair]` (line 561)
- `μ₁`, `μ₂`, `GoodTrain`, `SuccessProd`, `GoodPair` definitions (562–581)
- `hGP_sub_SP : GoodPair ⊆ SuccessProd` — **PROVED** (583–625)
- `hgt_ge : μ₁ GoodTrain ≥ ENNReal.ofReal (1 - δ / 2)` (627)
- `hm₂_pos : 0 < m₂` (628)

### 1. DELETE lines 630–752

Delete everything from `suffices h_prod` through the final `sorry`. This removes all 3 sorrys.

### 2. REPLACE with the following structure

**Step 2a: Define BadVal, GoodUsed, GoodFull**
```lean
let BadVal : Set ((Fin m₁ → X) × (Fin m₂ → X)) :=
  {p | ∃ a : A,
    |TrueErrorReal X (LA.learnWithAdvice a (fun i => (p.1 i, c (p.1 i)))) c D -
      EmpiricalError X Bool (LA.learnWithAdvice a (fun i => (p.1 i, c (p.1 i))))
        (fun j => (p.2 j, c (p.2 j))) (zeroOneLoss Bool)| ≥ ε / 4}
let GoodUsed : Set (Fin (m₁ + m₂) → X) :=
  (splitUsedEquiv (X := X) m₁ m₂) ⁻¹' GoodPair
let GoodFull : Set (Fin (Nat.pair m₁ m₂) → X) :=
  (usedPrefix (X := X) m₁ m₂) ⁻¹' GoodUsed
```

**Step 2b: GoodPair = {p | p.1 ∈ GoodTrain ∧ p ∉ BadVal} equivalence**
```lean
have hGP_eq : GoodPair = {p | p.1 ∈ GoodTrain ∧ p ∉ BadVal} := by
  ext p; simp [GoodPair, BadVal, not_exists, not_le]
```

**Step 2c: Measurability**
```lean
have hGoodTrain_meas : MeasurableSet GoodTrain := by sorry -- UK_5
have hBadVal_meas : MeasurableSet BadVal := by sorry -- UK_6
have hGoodPair_meas : MeasurableSet GoodPair := by
  rw [hGP_eq]
  exact (measurable_fst.measurableSet_preimage hGoodTrain_meas).inter hBadVal_meas.compl
have hGoodUsed_meas : MeasurableSet GoodUsed :=
  (splitUsedEquiv (X := X) m₁ m₂).measurable.measurableSet_preimage hGoodPair_meas
```

Note: `hGoodTrain_meas` and `hBadVal_meas` are the genuine UK obligations. Route:
- **GoodTrain**: `{xs₁ | D {x | LA.learnWithAdvice aStar (labeled xs₁) x ≠ c x} ≤ ofReal(ε/2)}`. Needs the map `xs₁ ↦ D {x | h(xs₁) x ≠ c x}` to be measurable, then take preimage of `Set.Iic`. Use `AdviceEvalMeasurable` (KK_1) + `measurable_measure_prod_mk_left` or `Kernel.measurable_kernel_prodMk_left_of_finite`.
- **BadVal**: Finite union (over A) of `{p | |TrueErrorReal ... - EmpiricalError ...| ≥ ε/4}`. Each is measurable from AdviceEvalMeasurable.

**Step 2d: Fin composition helpers (re-proved from deleted block)**
```lean
have h_split_fst : ∀ (ys : Fin (m₁ + m₂) → X) (i : Fin m₁),
    (splitUsedEquiv (X := X) m₁ m₂ ys).1 i = ys (Fin.castAdd m₂ i) := by
  intro ys i
  simp [splitUsedEquiv, MeasurableEquiv.trans_apply, MeasurableEquiv.sumPiEquivProdPi,
    MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, finSumFinEquiv,
    Equiv.sumPiEquivProdPi, Fin.castAdd]
have h_split_snd : ∀ (ys : Fin (m₁ + m₂) → X) (j : Fin m₂),
    (splitUsedEquiv (X := X) m₁ m₂ ys).2 j = ys (Fin.natAdd m₁ j) := by
  intro ys j
  simp [splitUsedEquiv, MeasurableEquiv.trans_apply, MeasurableEquiv.sumPiEquivProdPi,
    MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, finSumFinEquiv,
    Equiv.sumPiEquivProdPi, Fin.natAdd]
have h_composed_fst : ∀ (xs' : Fin (Nat.pair m₁ m₂) → X) (i : Fin m₁),
    (splitUsedEquiv (X := X) m₁ m₂ (usedPrefix (X := X) m₁ m₂ xs')).1 i =
    xs' ⟨i.1, by have := Nat.left_le_pair m₁ m₂; omega⟩ := by
  intro xs' i; rw [h_split_fst]; simp [usedPrefix, Fin.castLE, Fin.castAdd]
have h_composed_snd : ∀ (xs' : Fin (Nat.pair m₁ m₂) → X) (j : Fin m₂),
    (splitUsedEquiv (X := X) m₁ m₂ (usedPrefix (X := X) m₁ m₂ xs')).2 j =
    xs' ⟨m₁ + j.1, by have := Nat.add_le_pair m₁ m₂; omega⟩ := by
  intro xs' j; rw [h_split_snd]; simp [usedPrefix, Fin.castLE, Fin.natAdd]
```

**Step 2e: GoodFull ⊆ goal_set (subset, not equality)**
```lean
have hGoodFull_sub_goal : GoodFull ⊆ {xs | D {x |
    (let train : Fin m₁ → X × Bool := fun i => (xs ⟨↑i, _⟩, c (xs ⟨↑i, _⟩))
     let val : Fin m₂ → X × Bool := fun j => (xs ⟨m₁ + ↑j, _⟩, c (xs ⟨m₁ + ↑j, _⟩))
     let cand := fun a => LA.learnWithAdvice a train
     cand (bestAdvice cand val)) x ≠ c x} ≤ ENNReal.ofReal ε} := by
  intro xs hxs
  have hxGP : splitUsedEquiv (X := X) m₁ m₂ (usedPrefix (X := X) m₁ m₂ xs) ∈ GoodPair := hxs
  have hxSP := hGP_sub_SP hxGP
  -- hxSP says: on the product view, D{error} ≤ ε
  -- Goal says: on the direct-index view, D{error} ≤ ε
  -- Bridge via h_composed_fst/snd showing same training/validation data
  -- [Use h_composed_fst, h_composed_snd, funext, congr to rewrite]
  sorry -- UK_8: Fin matching (subset direction only)
```

This sorry is a Fin-matching proof, NOT a mathematical obstruction. The `h_composed_fst`/`h_composed_snd` give the pointwise equalities; the proof just needs to `congr` through the `LA.learnWithAdvice` and `bestAdvice` calls. The `h_full_hyp` pattern from the deleted block (lines 674–710) is the template.

**Step 2f: Training complement bound**
```lean
have htrain_compl : μ₁ GoodTrainᶜ ≤ ENNReal.ofReal (δ / 2) := by
  -- From hgt_ge : μ₁ GoodTrain ≥ ofReal(1 - δ/2)
  -- μ₁ GoodTrainᶜ = 1 - μ₁ GoodTrain ≤ 1 - ofReal(1 - δ/2)
  sorry -- ~10 LOC ENNReal subtraction
```

**Step 2g: Validation uniform bound**
```lean
have hval_uniform : ∀ xs₁ : Fin m₁ → X,
    μ₂ {xs₂ | (xs₁, xs₂) ∈ BadVal} ≤ ENNReal.ofReal (δ / 2) := by
  intro xs₁
  -- Case split: if ε ≥ 4, dispatch trivially
  by_cases hε4 : 4 ≤ ε
  · sorry -- trivial: TrueError ≤ 1 ≤ ε, goal set = univ
  · have hη1 : ε / 4 ≤ 1 := by linarith
    let cand := fun a => LA.learnWithAdvice a (fun i => (xs₁ i, c (xs₁ i)))
    have h_cand_meas : ∀ a : A, Measurable (cand a) :=
      fun a => learnWithAdvice_measurable_fixed LA h_eval a _
    -- finite_validation_family_bound gives: ≤ ofReal(|A|·2·exp(-2m₂(ε/4)²))
    -- Then show |A|·2·exp(-2m₂(ε/4)²) ≤ δ/2 from m₂ definition
    sorry -- ~30 LOC: instantiate finite_validation_family_bound + Hoeffding arithmetic
```

**Step 2h: Product complement bound**
```lean
have hBadTrain_prod : (μ₁.prod μ₂) {p | p.1 ∉ GoodTrain} ≤ ENNReal.ofReal (δ / 2) := by
  have hrect : {p : (Fin m₁ → X) × (Fin m₂ → X) | p.1 ∉ GoodTrain} = GoodTrainᶜ ×ˢ Set.univ := by
    ext p; simp
  rw [hrect, MeasureTheory.Measure.prod_prod, 
      MeasureTheory.IsProbabilityMeasure.measure_univ, mul_one]
  exact htrain_compl

have hBadVal_prod : (μ₁.prod μ₂) BadVal ≤ ENNReal.ofReal (δ / 2) := by
  rw [MeasureTheory.Measure.prod_apply hBadVal_meas]
  calc ∫⁻ xs₁, μ₂ (Prod.mk xs₁ ⁻¹' BadVal) ∂μ₁
      ≤ ∫⁻ _, ENNReal.ofReal (δ / 2) ∂μ₁ := MeasureTheory.lintegral_mono (fun xs₁ => hval_uniform xs₁)
    _ = ENNReal.ofReal (δ / 2) := by simp [MeasureTheory.lintegral_const, 
                                            MeasureTheory.IsProbabilityMeasure.measure_univ]
```

Note: `Measure.prod_prod` needs `MeasurableSet GoodTrainᶜ` — from `hGoodTrain_meas.compl`. ✓

**Step 2i: GoodPair probability bound**
```lean
have hGP_compl_sub : GoodPairᶜ ⊆ {p | p.1 ∉ GoodTrain} ∪ BadVal := by
  intro p hp
  rw [hGP_eq] at hp
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_and_or] at hp
  exact hp.imp id id

have hGoodPair_bound : (μ₁.prod μ₂) GoodPair ≥ ENNReal.ofReal (1 - δ) := by
  have hcompl : (μ₁.prod μ₂) GoodPairᶜ ≤ ENNReal.ofReal δ :=
    calc (μ₁.prod μ₂) GoodPairᶜ
        ≤ (μ₁.prod μ₂) ({p | p.1 ∉ GoodTrain} ∪ BadVal) := (μ₁.prod μ₂).mono hGP_compl_sub
      _ ≤ (μ₁.prod μ₂) {p | p.1 ∉ GoodTrain} + (μ₁.prod μ₂) BadVal :=
          MeasureTheory.measure_union_le _ _
      _ ≤ ENNReal.ofReal (δ/2) + ENNReal.ofReal (δ/2) := add_le_add hBadTrain_prod hBadVal_prod
      _ = ENNReal.ofReal δ := by rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; ring_nf
  exact prob_ge_one_sub_compl (μ₁.prod μ₂) GoodPair (ENNReal.ofReal δ) hcompl
```

**Step 2j: Transport chain**
```lean
have h_transport : MeasureTheory.Measure.pi (fun _ : Fin (Nat.pair m₁ m₂) => D) GoodFull
    = (μ₁.prod μ₂) GoodPair :=
  calc _ = MeasureTheory.Measure.pi (fun _ : Fin (m₁ + m₂) => D) GoodUsed :=
          nat_pair_sample_marginal D m₁ m₂ GoodUsed hGoodUsed_meas
    _ = (μ₁.prod μ₂) GoodPair :=
          used_sample_split_measure D m₁ m₂ GoodPair hGoodPair_meas
```

**Step 2k: Final calc (monotonicity)**
```lean
calc MeasureTheory.Measure.pi (fun _ : Fin (Nat.pair m₁ m₂) => D) {xs | ...goal...}
    ≥ MeasureTheory.Measure.pi (fun _ : Fin (Nat.pair m₁ m₂) => D) GoodFull :=
        (MeasureTheory.Measure.pi _).mono hGoodFull_sub_goal
  _ = (μ₁.prod μ₂) GoodPair := h_transport
  _ ≥ ENNReal.ofReal (1 - δ) := hGoodPair_bound
```

### 3. Sorry inventory after restructuring

| # | Location | Nature | LOC estimate |
|---|----------|--------|-------------|
| S1 | `hGoodTrain_meas` | Measurability of `{xs₁ \| D{error} ≤ ε/2}` | 15-25 |
| S2 | `hBadVal_meas` | Measurability of `{p \| ∃ a, \|...\| ≥ ε/4}` | 15-25 |
| S3 | `hGoodFull_sub_goal` | Fin matching (subset direction) | 20-30 |
| S4 | `htrain_compl` | ENNReal complement arithmetic | 10 |
| S5 | `hval_uniform` | Hoeffding arithmetic + finite_validation_family_bound | 30 |

Total: ~90-120 LOC of proofs remaining. All are closable from existing infrastructure.

### 4. Exclusive File Access

**WRITE**: `FLT_Proofs/Theorem/Extended.lean` lines 630–752 ONLY  
**DO NOT TOUCH**: Lines 1–628 (proved), lines 753+ (other theorems)  
**Edit only** — no full-file Write operations.

### 5. Termination

Target: 0 sorrys in `advice_elimination` (excluding bhmz_middle_branch line 38).  
`lake build` must pass with 0 errors.

---

## URS v4: FP5 — advice_elimination (1 sorry → 0)

**Date**: 2026-03-25 | **File**: `FLT_Proofs/Theorem/Extended.lean`
**Target**: Close line 1027 — the last FP5 sorry
**Status**: S1 (measurability GoodTrain), S2 (measurability BadVal), S3 (Hoeffding arithmetic) all CLOSED. One sorry remains.

### 0. Discovery State

**What is proved**: The full mathematical content is compiled and sorry-free:
- `hGoodFull_sub_goal : GoodFull ⊆ {xs | D{...} ≤ ε}` (line ~712) — subset with `Fin m₁` types
- `h_transport : π(D)(GoodFull) = (μ₁.prod μ₂)(GoodPair)` (line ~993)
- `hGoodPair_bound : (μ₁.prod μ₂)(GoodPair) ≥ ofReal(1-δ)` (line ~814)
- `h_gf_bound : π(D)(GoodFull) ≥ ofReal(1-δ)` (line ~1006, from transport + bound)
- `h_combined` (lines 1014–1026): the full bound with explicit `Fin m₁` types

**What remains**: A single `sorry` at line 1027. `h_combined` has the right type but with `Fin m₁`. The goal has `Fin (Nat.unpair (Nat.pair m₁ m₂)).1`.

### 1. Root Cause Analysis

The S4 agent ran for **1 hour, 63 edits, 87 builds** in a CNA₃ loop because it never diagnosed the root cause. Here it is:

**The learner definition** (lines 540–548) uses:
```lean
fun {m} S =>
  let m₁ := (Nat.unpair m).1    -- learner's m₁
  let m₂ := (Nat.unpair m).2    -- learner's m₂
  ...
```

**The proof** (lines 559–560) uses:
```lean
set m₁ := mf_adv (ε / 2) (δ / 2)     -- proof's m₁
set m₂ := Nat.ceil (...) + 1           -- proof's m₂
```

After `case pac`, Lean specializes the learner at `m := Nat.pair m₁ m₂` (from `case mf`). So in the goal, the learner's `let m₁` becomes `(Nat.unpair (Nat.pair (mf_adv ...) (Nat.ceil ... + 1))).1`.

`simp_rw [Nat.unpair_pair]` at line 562 **should** rewrite `Nat.unpair (Nat.pair a b)` to `(a, b)`. But `simp_rw` cannot rewrite inside **lambda binder types**. The goal's `Fin` types inside the learner's lambda are:
```
Fin (Nat.unpair (Nat.pair (mf_adv (ε/2) (δ/2)) (⌈...⌉ + 1))).1
```
These are propositionally equal to `Fin m₁` but not definitionally — and `simp_rw` can't penetrate the binder.

The proof's `set m₁` creates a **different** `m₁` that shadows but doesn't unify with the learner's `(Nat.unpair m).1`.

### 2. KU — Possible Routes

**Route A: `convert h_combined`**
Use `convert` to unify `h_combined` with the goal. `convert` tolerates propositional (not just definitional) equality. After `convert h_combined using N`, remaining goals should be `Fin (Nat.unpair (Nat.pair m₁ m₂)).1 = Fin m₁` which close by `simp [Nat.unpair_pair]` or `congr 1; simp [Nat.unpair_pair]`.

The S4 agent tried `convert` (edits 22–30) but failed because it used wrong `using N` depth and wrong closing tactics. The correct depth needs to be determined empirically.

**Route B: `show` with explicit type**
Write `show` with the goal type using `Fin m₁` instead of `Fin (Nat.unpair ...)`. If `simp_rw [Nat.unpair_pair]` already partially rewrote the goal, this might just work.

**Route C: Replace `simp_rw` with `simp only` + `change`**
At line 562, replace `simp_rw [Nat.unpair_pair]` with a more aggressive rewrite that penetrates binder types. Options:
- `change` the goal to an explicit form with `Fin m₁`, `Fin m₂`
- `conv` with `ext` to enter binder types
- `dsimp only [Nat.unpair_pair]` (dsimp can sometimes reduce where simp_rw can't)

**Route D: Restructure the learner definition**
Instead of `let m₁ := (Nat.unpair m).1`, define the learner to take `m₁ m₂` directly and use `Nat.pair` only in the sample complexity function. This would eliminate the `Nat.unpair` in the goal entirely.

This is a deeper change to lines 539–548 but would permanently fix the binder-type issue.

### 3. UK — What We Don't Know

| # | Question | Impact |
|---|----------|--------|
| UK_1 | Which `using N` depth makes `convert h_combined` leave only Fin-equality goals? | Route A viability |
| UK_2 | Does `dsimp only [Nat.unpair_pair]` at line 562 penetrate binder types? | Route C viability |
| UK_3 | Can `conv in Fin _ => rw [Nat.unpair_pair]` or similar target binder types? | Route C variant |
| UK_4 | Does changing the learner definition (Route D) break anything upstream? | Route D risk |

### 4. Recommended Action

**Try Route A first** (lowest risk, no code restructuring):
1. Replace `sorry` at line 1027 with `convert h_combined using 1` and check what goals remain
2. Close remaining goals with `simp [Nat.unpair_pair]` or `congr; simp [Nat.unpair_pair]`

**If Route A fails**, try Route C:
1. Replace `simp_rw [Nat.unpair_pair]` at line 562 with `dsimp only [Nat.unpair_pair]`
2. If that changes the goal shape, `exact h_combined` might work directly

**If Route C fails**, try Route D:
1. Restructure learner at lines 539–548 to avoid `Nat.unpair` in the lambda

### 5. Scope

**WRITE**: Line 1027 (and potentially line 562 if Route C needed, or lines 539–548 if Route D needed)
**DO NOT TOUCH**: Lines 1–538 (helpers), lines 563–1026 (proved infrastructure), lines 1028+ (other theorems)

### 6. Termination

- `grep -n sorry FLT_Proofs/Theorem/Extended.lean` shows ONLY line 39 (`bhmz_middle_branch`)
- `lake build` passes with 0 errors
- A4/A5 checks pass

### 7. Anti-Pattern Warning

The S4 agent's failure mode: **63 edits trying syntactic fixes without diagnosing the binding structure**. The next agent MUST:
1. First determine the exact goal type (use `set_option pp.all true` or substitute and read the error)
2. Identify which `Fin` types mismatch and WHY
3. Choose ONE route and execute it
4. If the route fails after 3 attempts, STOP and report the obstruction — do not loop

---

That's the full URS. The inquiry state is clear: one sorry, root cause diagnosed (learner `let` binder types vs proof `set` bindings), 4 routes identified. Your call on which route to try.