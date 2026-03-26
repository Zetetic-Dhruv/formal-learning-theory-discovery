# URS: FP5 — advice_elimination (3 sorrys → 0)

**Date**: 2026-03-25 | **File**: `FLT_Proofs/Theorem/Extended.lean`
**Target**: Close lines 648, 906, 931 — all inside `advice_elimination`
**Route**: Replace SuccessProd transport with measurable GoodPair + monotonicity
**Status**: OPEN — 3 sorrys, 0 closed

---

## 0. Will — Discovery Axiom

The previous agent attempted to prove `MeasurableSet SuccessProd` and transport
SuccessProd through the pullback chain. That route is **architecturally wrong**.
`bestAdvice` uses `Classical.choose` making the selection function non-measurable
as a function of the validation sample — but that is NOT the fundamental issue.
The fundamental issue is: **you do not need the selected hypothesis to be measurable
as a function of the pair sample. You only need a measurable good event that implies success.**

The corrected route:
1. Define `GoodPair` (measurable inner event on product space)
2. Prove `GoodPair ⊆ SuccessProd` (deterministic implication)
3. Lower-bound `(μ₁.prod μ₂)(GoodPair)` (from proved helpers)
4. Transport `GoodPair` (not SuccessProd) back through the pullback chain
5. Conclude by measure monotonicity

This eliminates all three sorrys simultaneously. The `MeasurableSet SuccessProd` sorry
disappears (no longer needed). The transport sorry disappears (GoodPair is measurable,
subset containment replaces set equality). The product-space bound sorry disappears
(standard application of proved helpers on GoodPair).

**Termination condition**: `advice_elimination` sorry-free (excluding `bhmz_middle_branch`
at line 38 which is a separate theorem).

---

## 1. KK Universe — What We Know

### Proved Helper Lemmas (all sorry-free, in Extended.lean)

| # | Lemma | Line | Signature Summary |
|---|-------|------|-------------------|
| KK_1 | `learnWithAdvice_measurable_fixed` | 130 | `AdviceEvalMeasurable LA → Measurable (LA.learnWithAdvice a S)` for fixed `a`, `S` |
| KK_2 | `trueErrorReal_le_of_bestAdvice` | 137 | `(∀ a, \|TrueErr - EmpErr\| ≤ η) → TrueErr(aStar) ≤ τ → TrueErr(bestAdvice) ≤ τ + 2η` |
| KK_3 | `finite_validation_family_bound` | 160 | `μ₂ {xs \| ∃ a, \|TrueErr - EmpErr\| ≥ η} ≤ ofReal(|A|·2·exp(-2mη²))` |
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

### Proof Context (lines 553-572, already compiled)

After `case pac =>` and `simp only [Nat.unpair_pair]`, the goal is:
```
⊢ MeasureTheory.Measure.pi (fun _ : Fin (Nat.pair m₁ m₂) => D)
    {xs | D {x | (let train := fun i => (xs ⟨↑i, _⟩, c (xs ⟨↑i, _⟩))
                  let val := fun j => (xs ⟨m₁ + ↑j, _⟩, c (xs ⟨m₁ + ↑j, _⟩))
                  let cand := fun a => LA.learnWithAdvice a train
                  cand (bestAdvice cand val)) x ≠ c x} ≤ ENNReal.ofReal ε}
  ≥ ENNReal.ofReal (1 - δ)
```

with `aStar : A`, `haStar` giving the training bound, `m₁ = mf_adv (ε/2) (δ/2)`,
`m₂ = ⌈(8/ε²) · log(4|A|/δ)⌉ + 1`.

---

## 2. KU Universe — The Restructured Proof

### KU_0: DELETE lines 560–931

Delete the entire `SuccessProd` definition and the `suffices h_prod` block (lines 560–931).
Everything from `-- Product-space success event` through the final `sorry` goes.
Replace with Steps 1–5 below.

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

**Measurability**: `GoodTrain` is measurable from `AdviceEvalMeasurable` (fixed `a = aStar`,
compose with `measurable_measure_prod_mk_left`, preimage of `Iic`). `BadVal` is measurable
as a finite union (over `A`) of measurable sets (each uses `AdviceEvalMeasurable` for the
candidate, `hc_meas` for `c`, and `measurableSet_eq_fun` for the disagreement set).
`GoodPair` is the intersection of complements of measurable sets → measurable.

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
This is literally `haStar` after unfolding `GoodTrain` and `m₁`. Rename if Lean's
definitional unfolding cooperates; use `convert haStar using 2` + `ext` otherwise.

Therefore: `μ₁ GoodTrainᶜ ≤ ENNReal.ofReal (δ/2)`.
Derive via: `prob_ge_one_sub_compl` gives `μ₁ GT ≥ 1 - δ/2`, then
`μ₁ GTᶜ = 1 - μ₁ GT ≤ 1 - (1 - δ/2) = δ/2` using `MeasureTheory.prob_compl_le_of_le`.
Or more directly: `μ₁ GTᶜ = 1 - μ₁ GT` (probability measure) + arithmetic.

**Validation bound**: For each fixed `xs₁ : Fin m₁ → X`:
```
μ₂ {xs₂ | (xs₁, xs₂) ∈ BadVal} ≤ ENNReal.ofReal (δ/2)
```

This instantiates `finite_validation_family_bound` (KK_3) at `η = ε/4`, `m = m₂`:
- `h_cand_meas : ∀ a, Measurable (cand a)` — from `learnWithAdvice_measurable_fixed` (KK_1)
- `hm : 0 < m₂` — from `m₂ = ⌈...⌉ + 1 ≥ 1`
- `hη : 0 < ε/4` — from `hε`
- `hη1 : ε/4 ≤ 1` — **early case split**: if `ε ≥ 4`, the goal is trivially true since
  `TrueError ≤ 1 ≤ ε`, so the goal set is `Set.univ` with measure 1 ≥ 1-δ.
  After case split, `ε < 4` gives `ε/4 < 1`.

The Hoeffding bound gives: `≤ ofReal(|A| · 2 · exp(-2 · m₂ · (ε/4)²))`.
Need: `|A| · 2 · exp(-2 · m₂ · ε²/16) ≤ δ/2`.

From `m₂ = ⌈(8/ε²) · log(4|A|/δ)⌉ + 1`:
```
2 · m₂ · ε²/16 ≥ 2 · (8/ε²) · log(4|A|/δ) · ε²/16
                = log(4|A|/δ)
```
So `exp(-2m₂ε²/16) ≤ δ/(4|A|)`, hence `|A|·2·exp(...) ≤ δ/2`. ✓

This arithmetic is ~30 LOC of `Real.log`/`Real.exp` manipulation. Key Mathlib lemmas:
- `Real.exp_le_exp`, `Real.log_le_log`
- `Nat.le_ceil`, `Nat.lt_add_one_iff`
- `Real.exp_neg_le_of_le` (or manual: `exp(-t) ≤ 1/exp(t)`)

**Product bound**: Use `product_complement_bound` (KK_5) directly:
```lean
have hGoodPair_prob : (μ₁.prod μ₂) GoodPair ≥ ENNReal.ofReal (1 - δ) := by
  -- GoodPair = {p | p.1 ∈ GoodTrain ∧ p ∉ BadVal}
  -- = {p | p.1 ∈ GoodTrain} ∩ BadValᶜ
  -- product_complement_bound with GoodTrain = GoodTrain, GoodVal = BadValᶜ
  -- gives (μ₁×μ₂)({p.1 ∈ GT ∧ p ∈ BVᶜ}) ≥ 1 - (δ/2 + δ/2) = 1 - δ
  ...
```

Or manually via complement + union bound (avoids fitting into `product_complement_bound`'s
exact interface):
```lean
have hGP_compl_sub : GoodPairᶜ ⊆ {p | p.1 ∉ GoodTrain} ∪ BadVal := by
  intro p hp; simp [GoodPair] at hp; by_cases h : p.1 ∈ GoodTrain
  · exact Or.inr (by tauto)
  · exact Or.inl h
calc (μ₁.prod μ₂) GoodPairᶜ
    ≤ (μ₁.prod μ₂) ({p | p.1 ∉ GoodTrain} ∪ BadVal) := by exact (μ₁.prod μ₂).mono hGP_compl_sub
  _ ≤ (μ₁.prod μ₂) {p | p.1 ∉ GoodTrain} + (μ₁.prod μ₂) BadVal :=
      MeasureTheory.measure_union_le _ _
  _ ≤ ENNReal.ofReal (δ/2) + ENNReal.ofReal (δ/2) := add_le_add htrain_compl hval_compl
  _ = ENNReal.ofReal δ := by rw [← ENNReal.ofReal_add (by linarith) (by linarith)]; ring_nf
```

Then `prob_ge_one_sub_compl` (KK_4) gives `(μ₁×μ₂)(GoodPair) ≥ 1 - δ`.

The cylinder set measure `(μ₁×μ₂){p | p.1 ∉ GoodTrain}` uses:
```lean
have : {p : _ × _ | p.1 ∉ GoodTrain} = GoodTrainᶜ ×ˢ Set.univ := by ext; simp
rw [this, MeasureTheory.Measure.prod_prod, MeasureTheory.IsProbabilityMeasure.measure_univ, mul_one]
```
This uses `Measure.prod_prod` which needs `MeasurableSet GoodTrainᶜ` — which IS
provable since `GoodTrain` is measurable (KU_1). ✓

The global validation bound `(μ₁×μ₂)(BadVal) ≤ δ/2` can be obtained by
`Measure.prod_apply` + `lintegral_mono` (same pattern as in `product_complement_bound`'s
proof at lines 286-291), or by observing that for each fixed `xs₁`, the conditional
bound holds uniformly.

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
have hGoodPair_meas : MeasurableSet GoodPair := ... -- from KU_1
have hGoodUsed_meas : MeasurableSet GoodUsed :=
  (splitUsedEquiv (X := X) m₁ m₂).measurable.measurableSet_preimage hGoodPair_meas
```

For `GoodFull` measurability, we need `Measurable (usedPrefix m₁ m₂)`. This is:
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

All transport lemmas (KK_8, KK_9) receive measurable sets. ✓

### KU_5: Subset + monotonicity

Show `GoodFull ⊆ goal_set`. For each `xs : Fin (Nat.pair m₁ m₂) → X`:
- `xs ∈ GoodFull` means `splitUsedEquiv(usedPrefix(xs)) ∈ GoodPair`
- `GoodPair ⊆ SuccessProd` (KU_2) means the hypothesis selected by bestAdvice has `TrueError ≤ ε`
- The access pattern matches: `splitUsedEquiv(usedPrefix(xs)).1 i` has `.val = i.val`,
  and `splitUsedEquiv(usedPrefix(xs)).2 j` has `.val = m₁ + j.val` — same as the goal's
  `xs⟨i.val, _⟩` and `xs⟨m₁ + j.val, _⟩`.

The Fin `.val` matching uses `congr` + `Fin.ext` (same arithmetic as the existing
`h_split_fst`, `h_composed_fst` helpers at lines 709–756, which ARE still useful —
keep them if they compile, or reprove inline with `simp [usedPrefix, splitUsedEquiv, ...]`).

Key: we need the **subset direction only** (not set equality). This is strictly easier
than what the old proof attempted. If the `simp` on `splitUsedEquiv`/`usedPrefix` doesn't
close the Fin matching, use:
```lean
have : (Fin.castLE (Nat.add_le_pair m₁ m₂) (Fin.castAdd m₂ i)).val = i.val := by
  simp [Fin.castLE, Fin.castAdd]
```
and `Fin.ext this` to bridge the proof-term gap.

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
| UK_1 | `hη1 : ε/4 ≤ 1` for `finite_validation_family_bound` | MEDIUM | Early case split on `4 ≤ ε`: if yes, goal trivial (TrueError ≤ 1 ≤ ε). After split, `ε < 4` gives `ε/4 < 1`. |
| UK_2 | Arithmetic for `|A|·2·exp(-2m₂(ε/4)²) ≤ δ/2` | MEDIUM | ~30 LOC. Use `Nat.le_ceil`, `Real.exp_neg`, `Real.log_le_log`. May need `have : (0:ℝ) < Fintype.card A` from `Nonempty A`. |
| UK_3 | `TrueErrorReal ↔ TrueError` bridge in KU_2 | MEDIUM | Standard but fiddly. `ENNReal.toReal_le_toReal` needs `≠ ⊤` witnesses. Get from `D(set) ≤ D(univ) = 1 < ⊤`. |
| UK_4 | `Measurable (usedPrefix m₁ m₂)` | LOW | `measurable_pi_lambda _ (fun i => measurable_pi_apply _)` should work — it's a projection. |
| UK_5 | `MeasurableSet GoodTrain` | MEDIUM | Needs `Measurable (fun xs₁ => D {x \| LA.learnWithAdvice aStar (fun i => (xs₁ i, c (xs₁ i))) x ≠ c x})`. This is: `measurable_measure_prod_mk_left` composed with `AdviceEvalMeasurable`. |
| UK_6 | `MeasurableSet BadVal` — finite union of measurable sets | MEDIUM | Each `{p \| \|TrueErr(cand a) - EmpErr(cand a, val)\| ≥ η}` needs measurability of EmpErr as a function of the validation sample. `EmpiricalError` is a finite sum of indicator functions → measurable. |
| UK_7 | `Measure.prod_prod` needs `MeasurableSet GoodTrainᶜ` | LOW | Follows from UK_5 + `.compl`. |
| UK_8 | Whether `h_split_fst`/`h_split_snd` helpers (lines 709–720) survive the rewrite | LOW | They can be kept or reproved. They depend only on `splitUsedEquiv` definition. |

---

## 4. UU Boundary

| # | Region |
|---|--------|
| UU_1 | Whether `MeasurableSet GoodTrain` requires `Measurable (fun xs₁ => D {x \| ...})` (measure-valued function measurability) or can be done via `measurableSet_le` on simpler functions. The exact Mathlib path may require experimentation. |
| UU_2 | Whether the `simp` lemma set for `splitUsedEquiv`/`usedPrefix` Fin matching suffices, or whether manual `Fin.ext` rewrites are needed. |
| UU_3 | Whether `product_complement_bound` (KK_5) can be invoked directly, or whether the manual complement + union bound route is more robust for fitting the exact types. |

---

## 5. Action Space

| Step | Target | LOC | Pl | Risk |
|------|--------|-----|-----|------|
| 0 | Delete lines 560–931 (SuccessProd + suffices block + sorry) | -371 | 1.0 | NONE |
| 1 | KU_1: Define `GoodTrain`, `BadVal`, `GoodPair`, `GoodUsed`, `GoodFull` + measurability | 40 | 0.85 | UK_5, UK_6 |
| 2 | KU_2: Prove `GoodPair ⊆ SuccessProd` (deterministic core) | 50 | 0.90 | UK_3 (TrueErrorReal bridge) |
| 3 | KU_3: Lower-bound `(μ₁.prod μ₂)(GoodPair) ≥ 1-δ` | 70 | 0.80 | UK_1 (ε/4≤1), UK_2 (arithmetic) |
| 4 | KU_4: Transport chain `D^N(GoodFull) = (μ₁×μ₂)(GoodPair)` | 15 | 0.95 | LOW |
| 5 | KU_5: Subset `GoodFull ⊆ goal_set` + final `calc` | 30 | 0.85 | UK_8 (Fin matching) |

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

The proof is now a standard application of proved infrastructure on a well-chosen
measurable event. No Gamma-class obstructions remain.
