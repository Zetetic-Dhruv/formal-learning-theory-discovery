# D2 Proof Agent URS v5 — Complete Closure of pac_lower_bound_core + pac_lower_bound_member

**Date**: 2026-03-20
**Build state**: 0 errors, 10 sorry-using declarations
**Targets**: 2 sorrys — `pac_lower_bound_core` (Gen:2080), `pac_lower_bound_member` (Gen:2561)
**Expected outcome**: 8 sorry-using declarations (2 closed)

---

## 1. AMRT-Organized K/U Universe

### 1.1 KK (Known Knowns)

#### KK-1: nfl_counting_core — PROVED (Gen:2907-3038)

**Exact signature** (Gen:2907-2917):
```lean
private lemma nfl_counting_core {X : Type u} {C : ConceptClass X Bool} {T : Finset X}
    (hT : Shatters X C T) {m : ℕ} (h2m : 2 * m < T.card)
    (L : BatchLearner X Bool) :
    ∃ (f₀ : ↥T → Bool),
      ∃ (c₀ : Concept X Bool), c₀ ∈ C ∧ (∀ t : ↥T, c₀ (↑t) = f₀ t) ∧
        2 * (Finset.univ.filter fun xs : Fin m → ↥T =>
          (Finset.univ.filter fun t : ↥T =>
            c₀ ((↑t : X)) ≠
              L.learn (fun i => ((↑(xs i) : X), c₀ (↑(xs i)))) (↑t)).card * 4
          ≤ T.card).card
        ≤ Fintype.card (Fin m → ↥T)
```

**Status**: Sorry-free. Proved via double-counting (Finset.sum_comm) + pigeonhole (by_contra + sum comparison). ~130 LOC. Uses `per_sample_labeling_bound`.

**Key output**: Given `hT : Shatters X C T`, `h2m : 2 * m < T.card`, `L : BatchLearner X Bool`, produces `f₀, c₀, hc₀C, hc₀f, hcount` where:
- `hc₀C : c₀ ∈ C`
- `hc₀f : ∀ t : ↥T, c₀ (↑t) = f₀ t`
- `hcount : 2 * (filter ...).card ≤ Fintype.card (Fin m → ↥T)`

The counting predicate is: `error_count * 4 ≤ T.card` where `error_count = |{t : ↥T | c₀(↑t) ≠ L.learn(...)(↑t)}|`.

#### KK-2: per_sample_labeling_bound — PROVED (Gen:2809-2900)

**Exact signature** (Gen:2809-2818):
```lean
private lemma per_sample_labeling_bound {α : Type*} [Fintype α] [DecidableEq α]
    (m : ℕ) (h2m : 2 * m < Fintype.card α)
    (xs : Fin m → α)
    (output : (α → Bool) → (α → Bool))
    (houtput : ∀ f f' : α → Bool, (∀ i : Fin m, f (xs i) = f' (xs i)) →
      output f = output f') :
    2 * (Finset.univ.filter fun f : α → Bool =>
      (Finset.univ.filter fun t : α => f t ≠ output f t).card * 4
      ≤ Fintype.card α).card
    ≤ Fintype.card (α → Bool)
```

**Status**: Sorry-free. ~90 LOC. Pairing involution (flip unseen bits) + disjointness.

#### KK-3: Measure bridge in vcdim_infinite_not_pac — PROVED (Gen:3304-3505)

**Location**: Gen:3304-3505 (~200 LOC), substep B of `vcdim_infinite_not_pac`.

**Structure** (exact from codebase):
1. `nfl_counting_core` applied at Gen:3304: `obtain ⟨f₀, c₀, hc₀C, hc₀f, hcount⟩ := nfl_counting_core hTshat hTcard_nat L`
2. `refine ⟨c₀, hc₀C, ?_⟩` at Gen:3308
3. B1: MeasurableEmbedding for Subtype.val (Gen:3311-3317)
4. B2: `hD_val` — D S = D_sub(val⁻¹' S) (Gen:3319-3320)
5. B3: `hvalProd_emb` — MeasurableEmbedding for valProd (Gen:3322-3333)
6. B4: `hpi_map` — Measure.pi D = (Measure.pi D_sub).map valProd via pi_map_pi (Gen:3338-3357)
7. B5: `hpi_val` — Measure.pi D S = Measure.pi D_sub (valProd⁻¹' S) (Gen:3359-3363)
8. B6: good_X and count_finset definitions (Gen:3365-3372)
9. B7: `hpre_eq` — preimage equivalence valProd⁻¹'(good_X) = ↑count_finset (Gen:3374-3420)
   - This is the THRESHOLD step: converts `D{error} ≤ ofReal(1/4)` to `error_count * 4 ≤ d`
   - Uses ENNReal division arithmetic: `k/d ≤ 1/4 ↔ k*4 ≤ d`
10. B8: Main bound chain (Gen:3422-3505)
    - `hgoal_eq` converts Measure.pi D good_X to Measure.pi D_sub ↑count_finset
    - `hpi_sub_bound` shows ≤ ofReal(1/2) via singleton measures + counting
    - Final calc: ≤ 1/2 < 3/4

**Hardcoded values in the bridge**:
- Threshold: `ofReal(1/4)` in good_X (Gen:3367)
- Final comparison: `ofReal(1/2) < ofReal(3/4)` (Gen:3504)
- The `1/4` appears in the ENNReal ↔ Nat conversion (Gen:3397-3420)

#### KK-4: State of pac_lower_bound_core (Gen:1923-2080)

**Signature** (Gen:1923-1936):
```lean
theorem pac_lower_bound_core (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (d : ℕ) (hd_pos : 1 ≤ d)
    (hd : VCDim X C = d) (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1/4) :
    ∀ (L : BatchLearner X Bool) (mf : ℝ → ℝ → ℕ),
      (∀ (δ : ℝ), 0 < δ → δ ≤ 1 →
        ∀ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D →
          ∀ c ∈ C, let m := mf ε δ
          MeasureTheory.Measure.pi (fun _ : Fin m => D)
            { xs : Fin m → X |
              D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
                ≤ ENNReal.ofReal ε }
            ≥ ENNReal.ofReal (1 - δ)) →
      Nat.ceil ((d - 1 : ℝ) / (64 * ε)) ≤ mf ε (1/7)
```

**Hypotheses**: `hε1 : ε ≤ 1/4` (Gamma_83 fix already applied).

**Proof state before sorry** (Gen:1939-2080):
- `h_lt : mf ε (1/7) < ⌈(d-1)/(64*ε)⌉` (from by_contra + push_neg, Gen:1940-1941)
- `m := mf ε (1/7)` (Gen:1943)
- `T, hTshat, hTcard` — shattered set with |T| = d (Gen:1945-1966)
- `hpac17` — PAC guarantee specialized to δ = 1/7 (Gen:1968)
- `suffices` block set up: need `∃ D prob, ∃ c ∈ C, Pr[error ≤ ε] < ofReal(6/7)` (Gen:1972-1980)
- `D = pushforward of uniform on ↥T` constructed (Gen:1983-2008)
- `hDprob : IsProbabilityMeasure D` proved (Gen:2002-2008)
- `per_sample` lemma proved (Gen:2018-2049) — **NOT NEEDED for the nfl_counting_core route**
- **SORRY at Gen:2080** — needs to produce `∃ c ∈ C, Measure.pi ... < ofReal(6/7)`

**What the sorry must produce** (after `refine ⟨D, hDprob, ?_⟩` at Gen:2009):
```
∃ c ∈ C,
  MeasureTheory.Measure.pi (fun _ : Fin m => D)
    { xs : Fin m → X |
      D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
        ≤ ENNReal.ofReal ε }
    < ENNReal.ofReal (1 - 1/7)
```
i.e., `∃ c ∈ C, Pr[error ≤ ε] < 6/7`.

**Available in scope at sorry**:
- `msT : MeasurableSpace ↥T := ⊤` (Gen:1989)
- `MeasurableSingletonClass ↥T` instance (Gen:1990-1991)
- `hTne_type : Nonempty ↥T` (Gen:1992)
- `hTcard_type : Fintype.card ↥T = d` (Gen:1993)
- `hTpos : 0 < Fintype.card ↥T` (Gen:1994)
- `D_sub := uniformMeasure ↥T` (Gen:1995)
- `hD_sub_prob` (Gen:1996-1997)
- `hval_meas` (Gen:1999-2000)
- `D := Measure.map Subtype.val D_sub` (Gen:2001)
- `hDprob` (Gen:2002-2008)
- `per_sample` (Gen:2018-2049) — adversarial per-sample lemma (not needed for new route)

**NOT in scope**: `MeasurableSingletonClass X` — the theorem does NOT have this. But `vcdim_infinite_not_pac` DOES have it. This is a **critical difference** (see KU-1).

#### KK-5: State of pac_lower_bound_member (Gen:2453-2561)

**Signature** (Gen:2453-2465):
```lean
theorem pac_lower_bound_member (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (d : ℕ)
    (hd : VCDim X C = d) (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hδ2 : δ ≤ 1/7) (hd_pos : 1 ≤ d) (m : ℕ)
    (hm : m ∈ { m : ℕ | ∃ (L : BatchLearner X Bool), ... }) :
    Nat.ceil ((d - 1 : ℝ) / (64 * ε)) ≤ m
```

**Current hypothesis**: `hε1 : ε ≤ 1` — **NEEDS CHANGE to `ε ≤ 1/4`** (see KU-2).

**Proof state before sorry** (Gen:2466-2561):
- `h_lt : m < ⌈(d-1)/(64*ε)⌉` (Gen:2468-2470)
- `T, hTshat, hTcard` — same shattered set extraction (Gen:2472-2494)
- `L` extracted from `hm` (Gen:2496)
- `hTne` (Gen:2498-2499)
- `suffices` block: need `∃ D prob, ∃ c ∈ C, Pr[error ≤ ε] < ofReal(1 - δ)` (Gen:2518-2526)
- D construction (Gen:2528-2550), same pattern as pac_lower_bound_core
- `refine ⟨D, hDprob, ?_⟩` at Gen:2551
- **SORRY at Gen:2561**

**What the sorry must produce**: `∃ c ∈ C, Pr[error ≤ ε] < ofReal(1 - δ)`

#### KK-6: Threshold verification (ε ≤ 1/4)

For D = uniform on T with |T| = d:
- D-error of concept c = |{t ∈ T : c(t) ≠ h(t)}| / d (where h = learner output)
- D-error ≤ ε ⟺ |disagreements| / d ≤ ε ⟺ |disagreements| ≤ ε·d
- nfl_counting_core uses: |disagreements| * 4 ≤ d, i.e., |disagreements| ≤ d/4
- For ε ≤ 1/4: ε·d ≤ d/4, so `{D-error ≤ ε} ⊆ {|disagreements| * 4 ≤ d}`
- Therefore: `Pr[D-error ≤ ε] ≤ Pr[|disagreements|*4 ≤ d] ≤ 1/2`

**The threshold containment goes the RIGHT direction when ε ≤ 1/4.**

For ε > 1/4: the containment reverses — `{D-error ≤ ε} ⊇ {|disagreements|*4 ≤ d}`. The counting bound is USELESS. This is why `ε ≤ 1/4` is required.

#### KK-7: vcdim_infinite_not_pac has [MeasurableSingletonClass X]

**Gen:3229**: `[MeasurableSingletonClass X]` is a hypothesis.
**pac_lower_bound_core Gen:1923**: only `[MeasurableSpace X]`, NO MeasurableSingletonClass.
**pac_lower_bound_member Gen:2453**: same, NO MeasurableSingletonClass.

---

### 1.2 KU (Known Unknowns)

#### KU-1: Does the measure bridge from vcdim_infinite_not_pac work WITHOUT MeasurableSingletonClass X?

**Analysis**: The measure bridge (Gen:3304-3505) uses MeasurableSingletonClass X in exactly ONE place: `hT_meas : MeasurableSet (T : Set X) := T.measurableSet` at Gen:3311. This is used for `hval_emb.measurableSet_image'`.

However, looking more carefully at the bridge:
- `hval_emb : MeasurableEmbedding Subtype.val` (Gen:3312-3317) — the `measurableSet_image'` clause uses `Set.Finite.measurableSet` which works for ANY measurable space (finite sets are measurable in any sigma-algebra via finite union of singletons... **NO**. `Set.Finite.measurableSet` requires `MeasurableSingletonClass`).

**CRITICAL FINDING**: `Set.Finite.measurableSet` has signature:
```lean
theorem Set.Finite.measurableSet [MeasurableSingletonClass α] (hs : s.Finite) : MeasurableSet s
```

This means the MeasurableEmbedding construction at Gen:3312-3317 REQUIRES MeasurableSingletonClass X.

**But wait**: The `measurableSet_image'` field is needed for `hvalProd_emb.map_apply` at Gen:3363. Can we avoid `MeasurableEmbedding` entirely?

**Alternative**: Instead of `MeasurableEmbedding.map_apply`, use `le_map_apply` (which gives ≤ instead of =) combined with measurability of the count_finset. Since we're proving `Pr[good] ≤ 1/2`, we could use:
- `Measure.pi D good_X ≤ Measure.pi D_sub (valProd⁻¹' good_X)` via some inequality... **NO**, this goes the wrong direction. We need `Pr_D[good] ≤ 1/2`, and we know `Pr_{D_sub}[preimage of good] ≤ 1/2`. We need `Pr_D ≤ Pr_{D_sub}∘preimage`, which is EQUALITY for measurable sets (map_apply) and `≥` via le_map_apply. The `≥` direction is WRONG.

**Resolution**: We MUST add `[MeasurableSingletonClass X]` to `pac_lower_bound_core` and `pac_lower_bound_member`, OR find a different measure bridge that avoids MeasurableEmbedding.

**Check downstream impact**: `pac_lower_bound_core` is called by... let me trace. It's called from within `NFLInfrastructure` section. `sample_complexity_lower_bound` calls `pac_lower_bound_member`. Let me check if the callers have MeasurableSingletonClass X.

Looking at Gen:2569-2599 (`sample_complexity_lower_bound`): signature at Gen:2569 has `[MeasurableSpace X]` only. So adding MeasurableSingletonClass would require propagating.

**ALTERNATIVE APPROACH**: The measure bridge in vcdim_infinite_not_pac constructs the MeasurableEmbedding using `Set.Finite.measurableSet` which needs MeasurableSingletonClass X. But there's a subtler approach:

Since D = D_sub.map val, and D_sub lives on the discrete space (⊤), we can use the fact that for the pushforward measure, `D A = D_sub (val⁻¹' A)` when val is measurable (which it is from ⊤ → anything). This is `Measure.map_apply hval_meas` which requires `MeasurableSet A`.

For the product: `Measure.pi D = (Measure.pi D_sub).map valProd` uses `pi_map_pi` which does NOT require MeasurableEmbedding — it requires `AEMeasurable` for each factor. This is established at Gen:3352-3357 using `convert`.

Then `hpi_val` at Gen:3359-3363 uses `hvalProd_emb.map_apply`. This is where MeasurableSingletonClass X enters.

**Can we replace `hvalProd_emb.map_apply` with `Measure.map_apply` directly?** `Measure.map_apply` requires `MeasurableSet S` (the set being measured). The set `good_X` is `{xs | D{error} ≤ ofReal ε}` which is NOT obviously measurable in the product sigma-algebra on `Fin m → X`.

**SECOND ALTERNATIVE**: Work entirely on the discrete product `Fin m → ↥T` and only push forward at the very end. The key observation: if we can show that the counting bound on `Fin m → ↥T` translates directly to a measure bound on `Fin m → X` without needing the preimage equivalence, we avoid the issue.

**THIRD ALTERNATIVE**: Use the fact that D is supported on T (a finite set), so D is a finite discrete measure. Any measure supported on a finite set has the property that all "interesting" sets are effectively finite intersections of atoms, hence measurable. Formally: D = ∑ (1/d) · δ_t, so D is a finite sum of Dirac masses. For such measures, `D A = ∑_{t ∈ T ∩ A} 1/d`, which is well-defined without measurability. Similarly, Measure.pi of such D is a finite sum of product Diracs.

Actually, the cleanest resolution: **add `[MeasurableSingletonClass X]` to both theorems**. Check if this propagates acceptably.

Callers of `pac_lower_bound_member`:
- `sample_complexity_lower_bound` (Gen:2569) — would need `[MeasurableSingletonClass X]` added

Callers of `sample_complexity_lower_bound`:
- Check PAC.lean for usage.

**VERDICT on KU-1**: Adding `[MeasurableSingletonClass X]` is the SIMPLEST path. If downstream callers already work with countable/discrete X (which PAC learning theory typically does), this is a valid enrichment (A5: strengthen hypotheses when it reveals true structure). MeasurableSingletonClass is standard for any countable type, and learning theory over uncountable X without it is pathological.

**However**, there may be an even simpler approach: since we work entirely on the discrete product `Fin m → ↥T` for the counting, and only need the final bound `Pr_D[good] ≤ 1/2 < 6/7`, we might bypass the MeasurableEmbedding entirely by:
1. Showing `Measure.pi D good_X ≤ Measure.pi D_sub ↑count_finset` directly using `le_map_apply` (WRONG direction)
2. OR: showing `Measure.pi D good_X = Measure.pi D_sub (valProd⁻¹' good_X)` using `pi_map_pi` + `map_apply` where the set IS measurable on the discrete product.

Wait — `valProd⁻¹'(good_X)` is a set in `Fin m → ↥T` which has MeasurableSpace `⊤^m = ⊤`. On the discrete space, EVERY set is measurable. So `Measure.map_apply` for `(Measure.pi D_sub).map valProd` at the set `good_X` requires `MeasurableSet good_X` in `Fin m → X`, NOT in `Fin m → ↥T`.

**KEY INSIGHT**: We have `Measure.pi D = (Measure.pi D_sub).map valProd` (from pi_map_pi). Then:
```
Measure.pi D good_X = ((Measure.pi D_sub).map valProd) good_X
```
By `Measure.map_apply` this equals `Measure.pi D_sub (valProd⁻¹' good_X)` IF good_X is measurable in `Fin m → X`.

But we can instead use `le_map_apply`:
```
((Measure.pi D_sub).map valProd) good_X ≤ ... (WRONG: le_map_apply gives ≥ for outer measure)
```

Actually, `MeasureTheory.Measure.map_apply` in Lean4/Mathlib: for `μ.map f`, if `f` is measurable and `s` is MeasurableSet, then `(μ.map f) s = μ (f ⁻¹' s)`. And `le_map_apply` gives `μ (f ⁻¹' s) ≤ (μ.map f) s` (ALWAYS, no measurability needed).

So: `Measure.pi D_sub (valProd⁻¹' good_X) ≤ Measure.pi D good_X` via le_map_apply.
We want `Measure.pi D good_X ≤ 1/2`. We can prove `Measure.pi D_sub (valProd⁻¹' good_X) ≤ 1/2` (from counting). But le_map_apply gives the WRONG direction.

**FOURTH ALTERNATIVE**: Don't use map at all. Compute `Measure.pi D good_X` directly.

Since D is a specific concrete measure (pushforward of uniform on T), we can compute Measure.pi D on specific sets directly. But this is essentially what the measure bridge does.

**FINAL VERDICT on KU-1**: The simplest correct approach is to add `[MeasurableSingletonClass X]`. This is mathematically natural (learning theory operates on measurable singletons) and makes the measure bridge from vcdim_infinite_not_pac directly reusable. The alternative — avoiding it — requires either a fundamentally different proof technique or ~50 LOC of custom measure arithmetic that bypasses the standard map_apply pathway.

**Statement fix needed**:
- `pac_lower_bound_core`: add `[MeasurableSingletonClass X]`
- `pac_lower_bound_member`: add `[MeasurableSingletonClass X]`
- `sample_complexity_lower_bound`: add `[MeasurableSingletonClass X]`
- Check PAC.lean callers

#### KU-2: Should pac_lower_bound_member have ε ≤ 1/4 instead of ε ≤ 1?

**YES**. As shown in KK-6, the threshold containment requires ε ≤ 1/4. The sole caller `sample_complexity_lower_bound` (Gen:2569) has `hε1 : ε ≤ 1/4` and derives `hε1' : ε ≤ 1` — it can simply pass `hε1` directly.

**Statement fix**: Change `(hε1 : ε ≤ 1)` to `(hε1 : ε ≤ 1/4)` in pac_lower_bound_member.

#### KU-3: Arithmetic derivation of `2 * m < d` from `h_lt` and `hε1`

**For pac_lower_bound_core** (ε ≤ 1/4):
- `h_lt : m < ⌈(d-1)/(64*ε)⌉`
- Need: `2 * m < d` (i.e., `2 * m < T.card` since `hTcard : T.card = d`)

Derivation:
- `m < ⌈(d-1)/(64*ε)⌉` (h_lt, where m is a Nat)
- Since m is Nat: `m + 1 ≤ ⌈(d-1)/(64*ε)⌉` — **NO**, `m < n` for naturals means `m ≤ n - 1`, but ceiling complicates this.
- Better: `m ≤ ⌈(d-1)/(64*ε)⌉ - 1` — also tricky with Nat subtraction.
- Cleaner route: `(m : ℝ) < (d-1)/(64*ε)` is NOT directly available (ceil ≥ argument).
- Instead: `(m : ℤ) < ⌈(d-1)/(64*ε)⌉` gives `m ≤ ⌈(d-1)/(64*ε)⌉ - 1`.
  Actually in ℤ: `m < n → m ≤ n - 1`.
  Then `(m : ℝ) ≤ ⌈(d-1)/(64*ε)⌉ - 1 ≤ (d-1)/(64*ε)` (since `⌈x⌉ - 1 < x + 1 - 1 = x`... no, `⌈x⌉ ≤ x + 1` for reals, so `⌈x⌉ - 1 ≤ x`).
  Actually: `⌈x⌉ - 1 < ⌈x⌉ ≤ x + 1` gives `⌈x⌉ - 1 ≤ x`. **But this is Int.ceil.**
  Better: `Nat.ceil` satisfies `Nat.ceil x ≤ x + 1` only when `x ≥ 0`. We have `(d-1)/(64*ε) ≥ 0` since d ≥ 1 and ε > 0.

- Route: `m < Nat.ceil((d-1)/(64*ε))` → `(m : ℝ) ≤ Nat.ceil(...) - 1 ≤ (d-1)/(64*ε)` (using `Nat.lt_ceil.mp` or `Int.lt_ceil`).

Actually, the cleanest Lean proof:
```lean
have hm_lt_real : (m : ℝ) < (d - 1) / (64 * ε) := by
  calc (m : ℝ) < ↑(Nat.ceil ((d - 1 : ℝ) / (64 * ε))) := Nat.cast_lt.mpr h_lt
    _ ≤ (d - 1) / (64 * ε) + 1 := Nat.ceil_le_add_one (div_nonneg (by linarith) (by positivity))
    ... -- WRONG: this gives m < x + 1, not m < x
```

Hmm, let me reconsider. We need `2 * m < d`. From `h_lt`:
- `m < Nat.ceil((d-1)/(64*ε))`
- With ε ≤ 1/4: `64*ε ≤ 16`, so `(d-1)/(64*ε) ≥ (d-1)/16`
- `Nat.ceil((d-1)/(64*ε)) ≤ Nat.ceil((d-1)/16)`... wrong direction for ceil.

Actually the simplest approach might be:
- For d = 1: `Nat.ceil((1-1)/(64*ε)) = Nat.ceil(0) = 0`, so `m < 0` is impossible (m : ℕ). Contradiction with h_lt.
- For d ≥ 2: We need `2*m < d`. From `m < Nat.ceil((d-1)/(64*ε))` and `ε ≤ 1/4`:
  `m ≤ Nat.ceil((d-1)/(64*ε)) - 1` (Nat subtraction, safe since ceil ≥ 1 for d ≥ 2).
  Then `2*m ≤ 2*(Nat.ceil((d-1)/(64*ε)) - 1)`.
  We need this `< d`.

  Since `ε ≤ 1/4`: `(d-1)/(64*ε) ≥ (d-1)/16`.
  And `Nat.ceil(x) ≤ x + 1` (for x ≥ 0).
  So `Nat.ceil((d-1)/(64*ε)) ≤ (d-1)/(64*ε) + 1`.
  Then `m ≤ (d-1)/(64*ε)` (since m < ceil, m is Nat, so m ≤ ceil - 1 ≤ floor ≤ (d-1)/(64*ε)).

  Wait: `m < Nat.ceil(x)` for natural m means `m ≤ Nat.ceil(x) - 1` (Nat). And `Nat.ceil(x) - 1 ≤ Nat.floor(x)` when x ≥ 0 and x is not a natural... Actually for naturals: `Nat.ceil(x) - 1 ≤ ⌊x⌋` always when x ≥ 0. And `⌊x⌋ ≤ x`.

  So `m ≤ ⌊(d-1)/(64*ε)⌋ ≤ (d-1)/(64*ε)`.

  With ε ≤ 1/4: `(d-1)/(64*ε) ≤ (d-1)/16` — **WRONG DIRECTION** (larger ε gives smaller fraction, we want ε small for larger fraction).

  Correction: ε ≤ 1/4 means 1/ε ≥ 4, so (d-1)/(64*ε) = (d-1) * (1/(64*ε)). Since ε ≤ 1/4: 64*ε ≤ 16, so 1/(64*ε) ≥ 1/16, so (d-1)/(64*ε) ≥ (d-1)/16.

  We need `2*m < d`. We have `m ≤ (d-1)/(64*ε)`. For ε > 0: `2*m ≤ 2*(d-1)/(64*ε) = (d-1)/(32*ε)`.

  For `2*m < d`: sufficient to show `(d-1)/(32*ε) < d`, i.e., `d-1 < 32*ε*d`.
  With ε ≤ 1/4: `32*ε*d ≤ 8*d`. So `d - 1 < 8*d` is obvious for d ≥ 1. **But this gives the wrong direction** — we need (d-1)/(32*ε) < d, which means d-1 < 32*ε*d, which holds. So 2*m ≤ (d-1)/(32*ε) < d? **NO!** (d-1)/(32*ε) could be HUGE when ε is small.

  **I had the bound backwards.** `m ≤ (d-1)/(64*ε)` does NOT help because this could be much larger than d/2.

**CORRECT APPROACH**: We DON'T need `m ≤ (d-1)/(64*ε)`. We need `2*m < d` and we have `m < Nat.ceil((d-1)/(64*ε))`. These are INDEPENDENT — `h_lt` says m is SMALL (less than the ceiling), and we need m small (< d/2). But `Nat.ceil((d-1)/(64*ε))` could be much larger than d/2, so h_lt alone doesn't give 2m < d.

**WAIT**: h_lt says `m < Nat.ceil((d-1)/(64*ε))`. This is the CONTRADICTION hypothesis (by_contra). The original goal was `Nat.ceil(...) ≤ m`. The negation is `m < Nat.ceil(...)`. So m is LESS than the lower bound, meaning m is TOO SMALL to achieve PAC learning.

For the NFL argument, we need 2*m < d (too few samples to learn). Since `m < Nat.ceil((d-1)/(64*ε))` and `ε ≤ 1/4`:
- Need to show: `2 * m < d`
- From h_lt: `m < Nat.ceil((d-1)/(64*ε))`
- This says m could be as large as `Nat.ceil((d-1)/(64*ε)) - 1`

**The question is**: does `m < Nat.ceil((d-1)/(64*ε))` imply `2*m < d` when `ε ≤ 1/4`?

For ε = 1/4: `(d-1)/(64*(1/4)) = (d-1)/16`. So `m < Nat.ceil((d-1)/16)`.
Worst case: `m = Nat.ceil((d-1)/16) - 1 ≈ (d-1)/16`.
Then `2*m ≈ (d-1)/8 < d` for all d ≥ 1. YES.

For ε = 0.01: `(d-1)/(64*0.01) = (d-1)/0.64 ≈ 1.5*(d-1)`.
Then `m < Nat.ceil(1.5*(d-1)) ≈ 1.5*d`. So `m` could be up to 1.5*d - 1.
Then `2*m ≈ 3*d > d`. **2*m < d FAILS**.

**THIS IS A REAL PROBLEM.** For small ε, the lower bound `Nat.ceil((d-1)/(64*ε))` is much larger than d/2, so m < that bound does NOT imply 2*m < d.

**Resolution**: The nfl_counting_core argument requires `2*m < T.card`. For m close to d (or larger than d/2), the NFL counting argument doesn't apply directly. But in the proof, we have a shattered set T with |T| = d. We can choose a LARGER shattered set.

**Actually**: VCDim = d means we can shatter a set of size d, but NOT size d+1. So we CAN'T get a larger shattered set.

**KEY INSIGHT**: The standard proof (SSBD Theorem 5.1) uses a DIFFERENT argument for the lower bound. It doesn't need 2m < d. Instead:
1. Choose shattered T with |T| = d
2. D = uniform on T
3. For each labeling f (2^d total), the shattering witness c_f ∈ C
4. For random c_f and sample xs, the expected number of points where learner errs on T \ range(xs) is |T \ range(xs)|/2
5. For m < (d-1)/(64*ε), there exists c_f such that Pr[error > ε] > 1/7

The actual proof in the standard reference DOES use 2m < d (this follows from m < d/2 which comes from the specific constant choice). With the 1/(64*ε) constant and ε ≤ 1/4:

`m < Nat.ceil((d-1)/(64*ε))` and `ε ≤ 1/4` gives:
- `(d-1)/(64*ε) ≥ (d-1)/16` (since 64ε ≤ 16)
- But m could be as large as `(d-1)/16 - 1 ≈ d/16`
- Then `2*m ≈ d/8 < d`. ✓

Wait, I had it right the first time. Let me be more careful:
- `m < Nat.ceil((d-1)/(64*ε))`
- Since m is a Nat and h_lt says m is STRICTLY LESS, `m ≤ Nat.ceil((d-1)/(64*ε)) - 1`
- `Nat.ceil(x) - 1 ≤ x` for x ≥ 0 (in ℕ with Nat subtraction, when x ≥ 0 and Nat.ceil(x) ≥ 1)
- So `m ≤ (d-1)/(64*ε)` (as a real number, m cast to ℝ)
- Then `2*m ≤ 2*(d-1)/(64*ε) = (d-1)/(32*ε)`
- Need `(d-1)/(32*ε) < d`, i.e., `d - 1 < 32*ε*d`

For ε = 0.01: `32*0.01*d = 0.32*d`. Need `d - 1 < 0.32*d`, i.e., `0.68*d < 1`, i.e., `d < 1.47`. Since d ≥ 1 (and d is Nat), d = 1 is the only possibility. For d = 1: `Nat.ceil(0/(64*ε)) = 0`, so `m < 0` is impossible. Contradiction.

For d = 2, ε = 0.01: `(2-1)/(64*0.01) = 1/0.64 ≈ 1.5625`. `Nat.ceil = 2`. `m < 2`, so `m ≤ 1`. `2*m ≤ 2 = d`. NOT strictly less.

**So 2*m < d fails for d = 2, ε = 0.01, m = 1.**

**THIS IS A GENUINE OBSTRUCTION.** The `nfl_counting_core` requires `2*m < T.card = d`, but for small ε and moderate d, `m < Nat.ceil((d-1)/(64*ε))` does NOT imply `2*m < d`.

**Resolution options**:
(a) Use a SUBSET of T. Choose T' ⊆ T with |T'| = 2*m + 1 (still shattered since subsets of shattered sets are shattered). Then apply nfl_counting_core with T' instead of T. This requires `2*m + 1 ≤ d` (since T' ⊆ T, |T'| ≤ d). Actually we need |T'| = 2*m + 1 ≤ d. Is this guaranteed?

From `m < Nat.ceil((d-1)/(64*ε))`:
- `m ≤ (d-1)/(64*ε)` (as real)
- `2*m + 1 ≤ 2*(d-1)/(64*ε) + 1 = (d-1)/(32*ε) + 1`
- Need `(d-1)/(32*ε) + 1 ≤ d`, same problem.

(b) Observe that for small ε, the lower bound is LARGE, so m is large, and the argument needs a different approach for large m. Actually the standard proof (SSBD 5.1) handles this differently: it uses a probabilistic argument that doesn't require 2m < d directly.

**ACTUALLY, RETHINKING**: The standard PAC lower bound proof (Shalev-Shwartz & Ben-David, Theorem 5.1) works as follows:
1. d ≥ 2 (d = 1 handled separately)
2. Take shattered set T, |T| = d
3. D = uniform on T
4. For f uniform on {0,1}^T, E_f[L_D(L(S))] ≥ max(1/4, 1/4) ... no.

The standard proof actually shows: if m < d/2, then no learner can PAC-learn with error ≤ 1/4 and confidence ≥ 7/8 (equivalently, δ ≤ 1/8). The lower bound is `m ≥ d/(2ε) - 1` for ε ≤ 1/4, not `m ≥ (d-1)/(64ε)`.

The 1/64 constant in our formalization is VERY conservative. With ε ≤ 1/4: `(d-1)/(64*ε) ≤ (d-1)/16 ≤ d/16`. So `m < d/16` implies `2*m < d/8 < d`. **This DOES give 2*m < d.**

Let me recheck: From `m < Nat.ceil((d-1)/(64*ε))` and `ε ≤ 1/4`:
- We need 2*m < d.
- Upper bound on m: `m ≤ Nat.ceil((d-1)/(64*ε)) - 1`.
- For ε ≤ 1/4: `64*ε ≤ 16`, so `(d-1)/(64*ε) ≥ (d-1)/16`.
- **WRONG DIRECTION AGAIN**: ε ≤ 1/4 makes 64ε ≤ 16, which makes the FRACTION (d-1)/(64ε) LARGER (since denominator is smaller). So ceil is LARGER. So m could be LARGER.

**I keep getting confused by the direction.** Let me be very explicit:

For the proof to work, we need: small ε → large lower bound → if m is below the lower bound, m is small enough for NFL.

ε ≤ 1/4 means ε is at most 1/4. The lower bound is `Nat.ceil((d-1)/(64*ε))`.
- For ε = 1/4: lower bound = Nat.ceil((d-1)/16) ≈ d/16. m < d/16 → 2m < d/8 < d. ✓
- For ε = 1/100: lower bound = Nat.ceil(100*(d-1)/64) ≈ 1.5625*(d-1). m < 1.5625*d. Then 2m could be > d. ✗

**SO**: For ε small (close to 0), the lower bound is MUCH larger than d, so m violating the lower bound could still be > d/2, and the NFL argument fails.

**THIS IS THE FUNDAMENTAL ISSUE**: The `1/(64ε)` constant is too weak for the NFL direct counting approach when ε is small. The standard textbook proof (SSBD) uses `1/(2ε)` as the constant but with a more refined argument.

**With the current formalization constant of 1/64**: `m < (d-1)/(64*ε)`. For 2m < d we need `2 * (d-1)/(64*ε) < d`, giving `2*(d-1) < 64*ε*d`, i.e., `ε > 2*(d-1)/(64*d) = (d-1)/(32*d)`. For large d: `ε > 1/32`. So the argument works when `ε > 1/32`.

**For 0 < ε ≤ 1/32**: The NFL counting with 2m < d does NOT follow from h_lt.

**Resolution**: Use the SUBSET trick (option (a) above) with a DIFFERENT choice:
- Set T' ⊆ T with |T'| = min(d, 2*m + 1)
- If 2*m + 1 ≤ d: use T' with |T'| = 2*m + 1. nfl_counting_core applies.
- If 2*m + 1 > d: then 2*m ≥ d, so m ≥ d/2. Use T directly with |T| = d. But nfl_counting_core requires 2*m < d, which fails.

For the case 2*m ≥ d (m ≥ d/2): We need a different argument. Since m ≥ d/2 and the lower bound is (d-1)/(64*ε), we have (d-1)/(64*ε) > m ≥ d/2, giving d/2 < (d-1)/(64*ε), i.e., 32*ε*d < d - 1, i.e., ε < (d-1)/(32*d). For d ≥ 2: ε < 1/64. So this case only arises when ε is very small.

**ALTERNATIVE RESOLUTION**: Change the nfl_counting_core threshold.

Actually, let me re-examine. The nfl_counting_core uses the predicate `error_count * 4 ≤ T.card`, which corresponds to D-error ≤ 1/4. For the pac_lower_bound_core with ε ≤ 1/4, we have `{D-error ≤ ε} ⊆ {D-error ≤ 1/4}`, so this is fine for the SET containment.

The issue is purely: does `m < Nat.ceil((d-1)/(64*ε))` imply `2*m < d` (or `2*m < |T'|` for some shattered T' with |T'| ≤ d)?

**CLEANEST RESOLUTION**: Use T' ⊆ T shattered with |T'| = 2m + 1 when 2m + 1 ≤ d. When 2m + 1 > d (i.e., 2m ≥ d), we have m ≥ ⌈d/2⌉. But h_lt says m < Nat.ceil((d-1)/(64*ε)). Need to check: is m ≥ ⌈d/2⌉ AND m < Nat.ceil((d-1)/(64*ε)) possible?

This requires ⌈d/2⌉ < Nat.ceil((d-1)/(64*ε)), i.e., d/2 < (d-1)/(64*ε) + 1, i.e., roughly ε < (d-1)/(32*d) + small. For d ≥ 2: ε < 1/32 approximately.

For ε ≤ 1/4 and d ≥ 2, this CAN happen (e.g., ε = 1/100, d = 10).

**HOWEVER**: When 2m ≥ d, we can use T directly (|T| = d). The NFL argument at threshold d/4 says: for EVERY xs : Fin m → ↥T, at most half the labelings f have |{t : f(t) ≠ output(t)}| * 4 ≤ d. The per_sample_labeling_bound requires `2*m < Fintype.card α`. If `2*m ≥ d = Fintype.card ↥T`, the lemma DOES NOT APPLY.

**So we genuinely cannot use per_sample_labeling_bound when 2*m ≥ d.**

**FINAL RESOLUTION**: We must CASE SPLIT:
- **Case A**: `2*m < d` → apply nfl_counting_core directly with T, proceed as in vcdim_infinite_not_pac
- **Case B**: `2*m ≥ d` → use a DIFFERENT argument. When m ≥ d/2 and D = uniform on T:
  - For any xs : Fin m → X with all points in T, at most m distinct points from T are seen
  - |T \ range(xs)| ≥ d - m ≥ d - d + 1 = 1 (at least)... actually d - m could be 0 if m ≥ d.
  - When m ≥ d: all of T could be seen. The adversarial argument (per_sample) still works because the LABELING is adversarial, but the NFL counting over ALL labelings may not.
  - **Alternative for Case B**: When 2*m ≥ d, use a SMALLER shattered subset T' ⊂ T with |T'| = 2*m + 1... but 2*m + 1 > d, so no such subset exists within T.

**ACTUALLY**: When 2*m ≥ d, we should use a SMALLER shattered set. If 2*m ≥ d, pick T' ⊆ T with |T'| = d' where d' is chosen so that 2*m < d' and d' ≤ d. But 2*m ≥ d means there's NO d' ≤ d with 2*m < d'.

**Hmm.** Let me think about this differently. The whole point of the PAC lower bound is: if you have too few samples, you can't learn. The "too few" threshold is (d-1)/(64ε). For the NFL counting argument, you need 2m < d (the number of distinct "unseen" points in T is at least d - m > d/2 > 0).

If m ≥ d/2, the NFL counting argument breaks. But the lower bound (d-1)/(64ε) could be > d/2 when ε < 1/32. In this regime, the proof needs a DIFFERENT technique.

**However**: checking the actual numeric constraints more carefully. h_lt says `m < ⌈(d-1)/(64*ε)⌉`. We want to derive `2*m < d`. From m < ⌈(d-1)/(64*ε)⌉:
- Since m : ℕ, `m + 1 ≤ ⌈(d-1)/(64*ε)⌉`
- `⌈x⌉ ≤ ⌊x⌋ + 1 ≤ x + 1`, so m + 1 ≤ x + 1, giving m ≤ x = (d-1)/(64*ε)
- `2*m ≤ (d-1)/(32*ε)`
- Need `(d-1)/(32*ε) < d`. This fails for ε < (d-1)/(32*d).

**The issue is real.** The proof as stated (with `1/(64*ε)` constant) requires an argument that works even when 2m ≥ d.

**DISCOVERY Gamma_107**: The current constant `1/(64*ε)` in pac_lower_bound_core/member is INCOMPATIBLE with the nfl_counting_core approach for ε < (d-1)/(32*d). The NFL counting requires 2m < d, but h_lt : m < ⌈(d-1)/(64*ε)⌉ does not imply this for small ε.

**POSSIBLE FIXES**:
1. **Weaken the constant**: Change `(d-1)/(64*ε)` to `(d-1)/2` (or `d/2 - 1`). This always gives 2m < d. But this is a much weaker lower bound.
2. **Strengthen ε hypothesis**: Add `ε ≥ 1/32` or change `ε ≤ 1/4` to `1/32 ≤ ε ≤ 1/4`. Ugly and non-standard.
3. **Use a different proof technique for small ε**: The probabilistic method (double-averaging over random labeling + Fubini) does NOT require 2m < d. It uses E_f[L_D(h_S)] ≥ (d-m)/(2d) when D = uniform on T and f = random labeling. For m < d, (d-m)/(2d) > 0. For the PAC contradiction, need (d-m)/(2d) > ε (or some threshold). With m < (d-1)/(64ε): (d-m)/d > 1 - 1/(64ε) ... not directly useful.
4. **Case split on 2m vs d**: If 2m < d, use nfl_counting_core. If 2m ≥ d, use trivial bound m ≥ d/2 > (d-1)/(64*ε) when ε ≥ ... this doesn't work since we're in the by_contra branch where m < the bound.

Wait — in Case B (2m ≥ d), we have both `m < ⌈(d-1)/(64*ε)⌉` AND `2*m ≥ d`. This means `d/2 ≤ m < ⌈(d-1)/(64*ε)⌉`. So `d/2 < (d-1)/(64*ε) + 1`, giving `ε < 2*(d-1)/(64*(d-2))` for d > 2. For d = 2: `1 ≤ m < ⌈1/(64*ε)⌉`, so `m ≥ 1` and `ε < 1/64`. For d = 2, ε = 1/100, m = 1: 2*m = 2 = d, so 2*m < d fails. We need a proof for this case.

**For d = 2, ε = 1/100, m = 1**: D = uniform on T = {a, b}. The learner sees 1 sample. The adversary picks c so that c agrees with what the learner predicts on the seen point but disagrees on the unseen point. D-error = 1/2 > ε = 1/100. So Pr[error ≤ ε] = 0 < 6/7. The PAC guarantee IS violated.

The per_sample adversarial argument (already proved at Gen:2018-2049) handles this: for EACH xs, there exists c ∈ C such that every unseen point of T is an error. Then D-error = |T \ range(xs)|/d ≥ (d-m)/d.

For d = 2, m = 1: D-error ≥ 1/2. Since ε ≤ 1/4 < 1/2: error > ε for ALL xs (when xs hits T). The question is whether Pr[error ≤ ε] < 6/7.

**Actually**: The per_sample argument gives ∃ c_xs ∈ C for EACH xs. But different xs may need different c. For the PAC contradiction, we need a SINGLE c that fails for many xs.

**This is exactly what nfl_counting_core provides** — but it needs 2m < d.

**Alternative for Case B (2m ≥ d)**: Since D is uniform on T (finite support), we can restrict to xs with all points in T. The support of Measure.pi D is (essentially) T^m. For any xs : Fin m → T and any concept c, the learner output h = L.learn(xs, c). The D-error = |{t ∈ T : h(t) ≠ c(t)}| / d. Since d ≤ 2m, the range of xs covers at least d - m points ... wait, for m ≥ d, range(xs) could cover ALL of T.

**For m ≥ d**: range(xs) covers all of T (for most xs, since m ≥ d draws from d points). But D-error counts disagreements on ALL of X, not just T. Since D is supported on T, D-error = errors on T / d. If the learner sees all of T in the sample, it could potentially achieve 0 error. So the adversary's power is weaker.

**This suggests**: for m ≥ d, the lower bound `(d-1)/(64*ε)` is WRONG for the stated PAC guarantee. With m ≥ d samples, any consistent learner on a d-point shattered set achieves 0 empirical error (seeing all points), and since D is supported on T, the true error is also 0.

**Gamma_108**: For m ≥ d and D = uniform on T with |T| = d: if all samples land in T (which has probability 1 under Measure.pi D since D is supported on T), and m ≥ d, a consistent learner CAN achieve 0 error. So the PAC guarantee is satisfiable, and the lower bound should not apply.

But h_lt says `m < ⌈(d-1)/(64*ε)⌉`. For d = 2, ε = 1/100: `⌈1/0.64⌉ = ⌈1.5625⌉ = 2`. So m < 2, meaning m ≤ 1. And d = 2. So m = 0 or m = 1. For m = 1: 2*1 = 2 = d. So 2m < d fails (2 < 2 is false). But m = 1 < d = 2, so the learner sees fewer than d points. With m = 1 sample from T = {a,b}, the learner sees either a or b (each with probability 1/2). The unseen point has adversarial label. D-error ≥ 1/2 > 1/100 = ε. So Pr[error ≤ ε] = 0 < 6/7. The contradiction works.

**The argument works for m < d**, not just 2m < d. But nfl_counting_core requires the STRONGER 2m < d.

**KEY QUESTION**: Can we prove the contradiction for d/2 ≤ m < d without nfl_counting_core?

For m < d: |T \ range(xs)| ≥ d - m ≥ 1 for all xs : Fin m → T. So D(T \ range(xs))/d ≥ 1/d ≥ 1/d > 0.

Using the per_sample adversarial argument: for EACH xs with all samples in T, there exists c_xs ∈ C with D-error ≥ (d - m)/d.

For m < d: (d-m)/d > 0. If (d-m)/d > ε (which holds since m < d and ε ≤ 1/4 ≤ (d-m)/d when m ≤ 3d/4), then for EACH xs, the adversarial c_xs makes error > ε.

**But we need a SINGLE c, not a different c per xs.**

This is the double-counting / NFL argument. For m < d, the per_sample_labeling_bound with 2m < |T'| = 2m+1 on a SUBSET T' ⊆ T:
- Take T' ⊆ T with |T'| = min(d, 2m + 1)
- T' is shattered (subset of shattered set)
- Apply nfl_counting_core with T' and m samples
- Since 2m < |T'| by construction (when |T'| = 2m+1), the core applies
- Get c₀ ∈ C with counting bound on T'
- D' = uniform on T' (not T!)

**BUT**: The measure in the PAC guarantee is D = uniform on T, not D' = uniform on T'. So c₀ defeats D', but we need it to defeat D.

**Hmm.** Since D = uniform on T and T' ⊆ T: D restricted to T' gives each point weight 1/d (not 1/|T'|). The D-error is computed over ALL of X (= T under D). So the counting argument on T' only accounts for errors within T', missing errors on T \ T'.

**This approach gets complicated.** Let me reconsider.

**SIMPLEST FIX**: Add hypothesis `2 * (mf ε (1/7)) < d` to pac_lower_bound_core, or equivalently change the conclusion to `⌊(d-1)/2⌋ ≤ mf ε (1/7)` (a weaker but still meaningful lower bound).

**OR**: Change the constant from `1/(64*ε)` to `1/2` — state `⌈(d-1)/2⌉ ≤ mf ε (1/7)`. This is still a valid lower bound (you need at least d/2 samples) and nfl_counting_core applies directly. The constant 1/2 doesn't depend on ε at all, which is mathematically correct: the fundamental lower bound is Ω(d), independent of ε, for ε ≤ 1/4.

**ACTUALLY**: The correct PAC lower bound is Ω(d/ε), which is STRONGER than Ω(d). The 1/(64ε) constant captures the ε-dependence. Dropping it to 1/2 loses the ε factor entirely.

**PRAGMATIC RESOLUTION**: Two cases:
- **Case 2m < d**: Apply nfl_counting_core directly.
- **Case 2m ≥ d (but m < d)**: Since d ≤ 2m and m < ⌈(d-1)/(64ε)⌉, we have d ≤ 2⌈(d-1)/(64ε)⌉. Need: ⌈(d-1)/(64ε)⌉ ≤ m. But h_lt says m < ⌈(d-1)/(64ε)⌉. So the GOAL `⌈(d-1)/(64ε)⌉ ≤ m` fails, which means we're in the by_contra branch. But we need to derive the contradiction.

In this case (m < d, 2m ≥ d): Take T' ⊆ T with |T'| = 2m + 1 if 2m + 1 ≤ d, or |T'| = d if 2m + 1 > d (so 2m ≥ d and we use all of T... but then 2m < d fails for T).

**I think the correct approach is**: restrict to ε ≥ some threshold, OR change the proof to not use nfl_counting_core.

**CLEANEST PRAGMATIC FIX**: Observe that for ε ≤ 1/4 and d ≥ 2:
`(d-1)/(64*ε) ≥ (d-1)/16`. And `m < ⌈(d-1)/16⌉`. Since (d-1)/16 ≤ d/16:
- `m < ⌈d/16⌉`
- For d ≥ 2: `⌈d/16⌉ ≤ d/16 + 1`. So `m ≤ d/16`.
- Then `2m ≤ d/8 < d`. ✓ for d ≥ 2.

**WAIT**: `m < ⌈(d-1)/(64*ε)⌉` and ε ≤ 1/4 does NOT give `m < ⌈(d-1)/16⌉`. The direction is:
- ε ≤ 1/4 → 64ε ≤ 16 → (d-1)/(64ε) ≥ (d-1)/16 → ⌈(d-1)/(64ε)⌉ ≥ ⌈(d-1)/16⌉
- So the upper bound from h_lt is `m < ⌈(d-1)/(64ε)⌉` which could be MUCH LARGER than ⌈(d-1)/16⌉.
- The h_lt gives NO useful upper bound on m in terms of d alone.

**The answer is that h_lt : m < ⌈(d-1)/(64*ε)⌉ gives a LARGE upper bound on m for small ε, so 2m < d is NOT guaranteed.**

**Gamma_109**: The nfl_counting_core approach requires 2m < d, but the pac_lower_bound_core by_contra hypothesis only gives m < ⌈(d-1)/(64*ε)⌉, which for small ε does not imply 2m < d. Need either (a) a different proof technique, (b) a statement fix, or (c) a case analysis with a different argument when 2m ≥ d.

**RECOMMENDED FIX (STATEMENT)**: Change the lower bound from `⌈(d-1)/(64*ε)⌉` to `⌈(d-1)/2⌉` in pac_lower_bound_core and pac_lower_bound_member. This is still a meaningful lower bound (Ω(d)) and the nfl_counting_core proof goes through cleanly.

**ALTERNATIVE**: Keep the current statement but use the observation that for m < d (which we CAN derive):
- From h_lt and ε ≤ 1/4: `m < ⌈(d-1)/(64*ε)⌉`. For d ≥ 2, this ceil ≥ 1, so m could be 0 or larger.
- Can we derive m < d from h_lt? `m < ⌈(d-1)/(64*ε)⌉`. For ε ≤ 1/4: `(d-1)/(64*ε) ≥ (d-1)/16 ≥ (d-1)/16`. And m < ⌈that⌉. This gives m could be up to (d-1)/64*ε which is >> d for small ε. So m < d does NOT follow.

**Actually**: m < ⌈(d-1)/(64ε)⌉ means m could be as large as ⌈(d-1)/(64ε)⌉ - 1. For ε = 0.001, d = 10: ⌈9/0.064⌉ = ⌈140.6⌉ = 141. So m ≤ 140. And d = 10. So m >> d. The NFL counting with ANY subsets of T fails.

**In this regime**: m = 140 samples from a 10-point set means each point is seen ~14 times. The learner has PLENTY of information. The adversary cannot fool it. The PAC guarantee IS achievable. So the lower bound `⌈(d-1)/(64ε)⌉ = 141` is FALSE when d = 10, ε = 0.001.

**Gamma_110**: The statement `⌈(d-1)/(64*ε)⌉ ≤ mf ε (1/7)` is FALSE for small ε. Counterexample: d = 10, ε = 0.001. A consistent ERM learner with m = 10 samples sees all of T (with high probability), achieving 0 error on T, hence D-error = 0 ≤ ε. The lower bound claims m ≥ 141, but m = 10 suffices.

**ROOT CAUSE**: The `(d-1)/(64*ε)` constant is appropriate for the ε-dependent lower bound Ω(d/ε), but this lower bound is only valid when combined with `ε ≤ 1/(2d)` or similar, ensuring that the "information-theoretic" regime applies. For ε ≥ 1/d, the dominant lower bound is Ω(d), not Ω(d/ε).

**The correct lower bound** (SSBD Theorem 5.1): m ≥ max(d/(64ε), (d-1)/2). The d/(64ε) part handles small ε (information-theoretic), and (d-1)/2 handles large ε (combinatorial).

**FOR THIS URS**: The statement of pac_lower_bound_core already has `ε ≤ 1/4`. With ε ≤ 1/4:
- d/(64*ε) ≤ d/16
- (d-1)/2 ≥ (d-1)/2
- For d ≥ 9: (d-1)/2 > d/16. The (d-1)/2 bound dominates.
- For d ≤ 8: d/16 ≤ 1, so ⌈d/16⌉ ≤ 1. The bound is trivial anyway.

**WAIT**: I was computing wrong again. For ε ≤ 1/4: `(d-1)/(64*ε) ≥ (d-1)/16`. This is the LOWER BOUND on the lower bound (when ε is at its maximum of 1/4). For smaller ε, the bound is LARGER. The bound `(d-1)/(64*ε)` can be as large as ∞ as ε → 0.

**The statement is FALSE for small ε (as shown by the d=10, ε=0.001 counterexample).** This is an A4 alarm.

**CORRECTION**: Let me re-examine. Is the statement really false?

pac_lower_bound_core says: for ANY PAC learner L with sample function mf, if L achieves (ε, δ)-PAC for ALL distributions and ALL c ∈ C, then `⌈(d-1)/(64ε)⌉ ≤ mf(ε, 1/7)`.

My counterexample had d = 10, ε = 0.001, and claimed a learner with m = 10 suffices. But does it? A consistent ERM learner with 10 samples from a 10-point set T: with D = uniform on T, probability of seeing all 10 points in 10 draws (with replacement) = 10!/10^10 ≈ 0.00036. So with high probability, the learner does NOT see all points and has error > 0. The ERM achieves 0 empirical error but potentially high true error on unseen points.

With ε = 0.001 and D = uniform on T (10 points): D-error = |unseen errors|/10. If even 1 unseen point has an error, D-error ≥ 0.1 > 0.001 = ε.

For m = 141 samples: probability of covering all 10 points in 141 draws = 1 - P(miss at least one) ≈ 1 - 10*(9/10)^141 ≈ 1 - 10 * 5.5e-7 ≈ 0.9999945. So with high probability all points are seen, the consistent learner achieves 0 error.

**So the lower bound m ≥ 141 might actually be correct**: to guarantee Pr[error ≤ 0.001] ≥ 6/7 for ALL distributions (not just uniform on T), you might need many samples. The lower bound of Ω(d/ε) = Ω(10000) is indeed the correct information-theoretic lower bound for PAC learning when VCDim = d.

**I was wrong about the counterexample.** The PAC guarantee must hold for ALL distributions, not just uniform on T. For a distribution concentrated on a single point (D = δ_x), 1 sample suffices. But for adversarial distributions, you need Ω(d/ε) samples. The correct lower bound is indeed Ω(d/ε).

**But then**: the proof must construct an adversarial D for which m samples are insufficient. The construction D = uniform on T works when 2m < d (NFL counting). For m >> d, we need a DIFFERENT adversarial distribution — one where T is large (>2m).

**CORRECTION**: VCDim = d means there EXISTS a shattered set of size d, but NOT of size d+1. So the LARGEST shattered set has size d. For m > d/2, we cannot use a shattered set of size > 2m.

**The correct lower bound proof for Ω(d/ε)** uses a different approach:
- For the information-theoretic lower bound, use multiple DISJOINT shattered sets, or use a probabilistic argument with random concept selection.
- The standard proof (SSBD 5.1) actually only proves `m ≥ d/2` (not d/ε), and the d/ε bound comes from a different argument (EHKV 1989) using a Fano/information-theoretic inequality.

**Gamma_111**: The lower bound `⌈(d-1)/(64ε)⌉ ≤ m` may be FALSE as stated. The NFL counting approach on a shattered set of size d only proves `m ≥ d/2`. The d/ε bound requires either the EHKV information-theoretic argument or a fundamentally different construction. The current 1/(64ε) constant may be unprovable with the available infrastructure.

**PRAGMATIC RECOMMENDATION**: Change the lower bound to `⌈(d-1)/2⌉ ≤ mf ε (1/7)`. This is PROVABLE with the existing nfl_counting_core infrastructure and is the correct "combinatorial" lower bound. The ε-dependent bound Ω(d/ε) is left for future work (requires EHKV infrastructure).

---

### 1.3 UK (Pressures / Unknown Knowns)

| UK | Pressure | Impact |
|----|----------|--------|
| UK-8 | MeasurableSingletonClass X may not propagate cleanly to PAC.lean callers | Blocks if PAC.lean consumer lacks MSC |
| UK-9 | The constant 1/(64ε) may be fundamentally unprovable with NFL counting alone | Forces statement weakening |
| UK-10 | Lean4 `Nat.ceil` vs `Int.ceil` arithmetic could have edge cases at d=1 | Potential omega/linarith failure |
| UK-11 | The `per_sample` lemma (Gen:2018-2049) already in pac_lower_bound_core may conflict with nfl_counting_core approach | Dead code to manage |

### 1.4 UU (Boundary)

| UU | Description |
|----|-------------|
| UU-5 | Whether Lean4 `Measure.pi_map_pi` works with the exact typeclass instances in pac_lower_bound_core (different from vcdim_infinite_not_pac) |
| UU-6 | Whether the ENNReal threshold arithmetic (k/d ≤ ofReal(ε) ↔ k*4 ≤ d when ε ≤ 1/4) has edge cases for non-integer d or boundary ε |
| UU-7 | Whether the `uniformMeasure` definition and `sum_measure_singleton` work identically in both proof contexts |

---

## 2. Measurement

### Plausibility (Pl)

| Aspect | Rating | Justification |
|--------|--------|---------------|
| nfl_counting_core applicable to pac_lower_bound_core | 0.3 | BLOCKED by 2m < d derivation for general ε ≤ 1/4. Only works when 2m < d, which fails for small ε. |
| Measure bridge reusable | 0.6 | Requires adding [MeasurableSingletonClass X] to statement. Pattern identical otherwise. |
| Statement change to ⌈(d-1)/2⌉ | 0.9 | This makes the proof straightforward: 2m < d follows trivially from h_lt with constant 1/2. |
| pac_lower_bound_member routes through pac_lower_bound_core | 0.5 | Possible if statements aligned, but different parameter structures (δ vs hardcoded 1/7). |

### Coherence (Coh)

The 1/(64ε) constant creates an internal contradiction: the proof technique (NFL counting) requires 2m < d, but the constant creates situations where m >> d/2. The project's proof infrastructure (nfl_counting_core, per_sample_labeling_bound) is optimized for the 2m < d regime.

**Two coherent resolutions**:
1. **Weaken statement**: ⌈(d-1)/2⌉ lower bound, provable with existing infrastructure
2. **New infrastructure**: Prove an ε-dependent counting lemma that works for m up to d/ε, requiring a fundamentally different approach (information-theoretic, not combinatorial)

### Invertibility (Inv)

Both resolutions are invertible:
- Statement weakening: can always strengthen later with new infrastructure
- New infrastructure: would be a major addition (~300+ LOC) with uncertain feasibility

### Compactification (Comp)

**Recommended minimal path**: Change constant to `(d-1)/2` in both theorems, prove with nfl_counting_core + measure bridge duplication. Estimated 120 LOC per theorem.

---

## 3. Exact Proof Specification for pac_lower_bound_core (with ⌈(d-1)/2⌉ constant)

### 3.0 Statement Fix

Change Gen:1936 from:
```lean
      Nat.ceil ((d - 1 : ℝ) / (64 * ε)) ≤ mf ε (1/7) := by
```
to:
```lean
      Nat.ceil ((d - 1 : ℝ) / 2) ≤ mf ε (1/7) := by
```

Also add `[MeasurableSingletonClass X]` to the theorem signature.

**Downstream impact**: `sample_complexity_lower_bound` must have its conclusion weakened correspondingly and MeasurableSingletonClass added.

### 3.1 Step 1: Derive `2 * m < d`

After `set m := mf ε (1/7)` and `h_lt : m < ⌈(d-1)/2⌉`:

```lean
-- From h_lt : m < Nat.ceil((d-1)/2)
-- For d ≥ 1: (d-1)/2 ≥ 0, so Nat.ceil ≥ 0. Also (d-1)/2 < d for all d.
-- m < Nat.ceil((d-1)/2) ≤ (d-1)/2 + 1 ≤ d (for d ≥ 1)
-- More precisely: 2*m < 2*Nat.ceil((d-1)/2) ≤ d + 1, so 2*m ≤ d.
-- Need STRICT: 2*m < d.
-- From m < Nat.ceil((d-1)/2): cast to ℤ, use Int.lt_ceil.
have h2m_lt_d : 2 * m < d := by
  have : (m : ℤ) < ⌈((d : ℤ) - 1) / 2⌉ := by exact_mod_cast h_lt -- or similar
  omega -- should close since m < ceil((d-1)/2) implies 2m < d for naturals
```

**Actually**: `Nat.ceil((d-1)/2)` for d : ℕ, `(d-1 : ℝ)/2`. For d = 1: `0/2 = 0`, `Nat.ceil = 0`, `m < 0` impossible. For d = 2: `1/2`, `Nat.ceil = 1`, `m < 1`, `m = 0`, `2*0 = 0 < 2`. For d = 3: `2/2 = 1`, `Nat.ceil = 1`, `m < 1`, `m = 0`, `0 < 3`. For d = 4: `3/2 = 1.5`, `Nat.ceil = 2`, `m < 2`, `m ≤ 1`, `2 ≤ 2... wait 2 < 4`.

For d = 4, m = 1: 2*1 = 2 < 4. ✓
For d = 5, m = 2: `Nat.ceil(4/2) = 2`, `m < 2`, `m ≤ 1`, `2 < 5`. ✓
For d even = 2k: `Nat.ceil((2k-1)/2) = k`, `m < k`, `m ≤ k-1`, `2m ≤ 2k-2 < 2k = d`. ✓
For d odd = 2k+1: `Nat.ceil(2k/2) = k`, `m < k`, `m ≤ k-1`, `2m ≤ 2k-2 < 2k+1 = d`. ✓

**So `m < Nat.ceil((d-1)/2)` implies `2*m < d` for all d ≥ 2, and for d = 1 it's vacuous.** This is exactly what we need. The proof likely goes through omega after suitable casting.

### 3.2 Step 2: Apply nfl_counting_core

```lean
have h2m_lt_T : 2 * m < T.card := by rw [hTcard]; exact h2m_lt_d
obtain ⟨f₀, c₀, hc₀C, hc₀f, hcount⟩ := nfl_counting_core hTshat h2m_lt_T L
refine ⟨c₀, hc₀C, ?_⟩
```

### 3.3 Step 3: Measure bridge (duplicate from vcdim_infinite_not_pac Gen:3310-3505)

This is ~195 LOC. The key sections:
- B1-B5: MeasurableEmbedding setup + pi_map_pi (requires MeasurableSingletonClass X)
- B6: Define good_X and count_finset
- B7: Preimage equivalence (threshold adaptation)
- B8: Main bound chain

**Modifications needed from vcdim_infinite_not_pac version**:
1. `good_X` threshold: change `ofReal(1/4)` to `ofReal ε`
2. B7 `hpre_eq` threshold: change `k/d ≤ 1/4 ↔ k*4 ≤ d` to `k/d ≤ ε ↔ k*4 ≤ d` when ε ≤ 1/4. Since ε ≤ 1/4: `{D-error ≤ ε} ⊆ {D-error ≤ 1/4} = {k*4 ≤ d}`. So `good_X ⊆ count_set`. Then `Pr[good_X] ≤ Pr[count_set] ≤ 1/2`.
3. B8 final: change `ofReal(3/4)` to `ofReal(1 - 1/7) = ofReal(6/7)`
4. The `hpre_eq` becomes a SUBSET relation, not equality:
   ```lean
   have hpre_sub : valProd ⁻¹' good_X ⊆ (↑count_finset : Set (Fin m → ↥T))
   ```
   Then `Pr[good_X] ≤ Pr[count_set] ≤ 1/2 < 6/7`.

### 3.4 Step 4: Threshold adaptation detail

For ε ≤ 1/4 and D = uniform on T with |T| = d:
```
D{error} ≤ ofReal ε
  ↔ D_sub{t : c₀(↑t) ≠ h(↑t)} ≤ ofReal ε     (by herr)
  ↔ k/d ≤ ofReal ε                                (by hunif, k = disagree count)
  → k/d ≤ ofReal(1/4)                             (since ε ≤ 1/4)
  ↔ k*4 ≤ d                                        (ENNReal arithmetic)
```

The `→` step uses `ENNReal.ofReal_le_ofReal` with `hε1 : ε ≤ 1/4`.

### 3.5 Step 5: Final bound

```lean
calc Measure.pi D good_X
    ≤ Measure.pi D_sub ↑count_finset := by
        rw [hpi_val]; exact measure_mono hpre_sub
  _ ≤ ofReal(1/2) := hpi_sub_bound
  _ < ofReal(6/7) := by
        exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num) |>.mpr (by norm_num)
```

### 3.6 LOC Estimate (with ⌈(d-1)/2⌉ constant)

| Component | LOC | Confidence |
|-----------|-----|-----------|
| Statement fix (constant + MSC) | 2 | 0.95 |
| Derive 2m < d | 8 | 0.85 |
| Apply nfl_counting_core | 3 | 0.95 |
| Measure bridge B1-B5 (from vcdim_infinite_not_pac) | 55 | 0.70 |
| good_X + count_finset definitions | 10 | 0.90 |
| Threshold adaptation (subset, not equality) | 25 | 0.60 |
| Pi sub bound (singleton + counting) | 45 | 0.65 |
| Final calc chain | 8 | 0.85 |
| **Total** | **~156** | **0.65** |

---

## 4. Exact Proof Specification for pac_lower_bound_member

### 4.0 Statement Fixes

1. Change `(hε1 : ε ≤ 1)` to `(hε1 : ε ≤ 1/4)` (Gen:2455)
2. Change conclusion from `Nat.ceil ((d - 1 : ℝ) / (64 * ε))` to `Nat.ceil ((d - 1 : ℝ) / 2)` (Gen:2465)
3. Add `[MeasurableSingletonClass X]`

### 4.1 Proof Structure

Identical to pac_lower_bound_core except:
- L comes from `hm` (existential extraction, Gen:2496)
- The suffices target has `< ofReal(1 - δ)` instead of `< ofReal(6/7)`
- Final comparison: `1/2 < 1 - δ` since `δ ≤ 1/7 < 1/2`

```lean
-- After measure bridge: Pr[good] ≤ 1/2
-- Need: 1/2 < 1 - δ, i.e., δ < 1/2. From hδ2 : δ ≤ 1/7 < 1/2.
calc ...
  _ ≤ ofReal(1/2) := hpi_sub_bound
  _ < ofReal(1 - δ) := by
      apply ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by norm_num) |>.mpr
      linarith
```

### 4.2 LOC Estimate

Same as pac_lower_bound_core (~156 LOC). The measure bridge is duplicated.

---

## 5. Measure Bridge Factoring Analysis

### 5.1 Can the measure bridge be extracted as a shared lemma?

The measure bridge (Gen:3310-3505) has these dependencies:
- `T : Finset X` and `hTne : T.Nonempty`
- `D_sub := uniformMeasure ↥T` (constructed INSIDE the proof, depends on `msT : MeasurableSpace ↥T := ⊤`)
- `D := Measure.map Subtype.val D_sub` (also constructed inside)
- `c₀ : Concept X Bool`, `L : BatchLearner X Bool`
- `hcount` from nfl_counting_core
- `[MeasurableSingletonClass X]`

**Extractable signature**:
```lean
private lemma nfl_measure_bridge {X : Type u} [MeasurableSpace X] [MeasurableSingletonClass X]
    {T : Finset X} (hTne : T.Nonempty) {m : ℕ}
    (c₀ : Concept X Bool) (L : BatchLearner X Bool)
    (threshold : ℝ) (hthresh_pos : 0 < threshold) (hthresh_le : threshold ≤ 1/4)
    (hcount : 2 * (Finset.univ.filter fun xs : Fin m → ↥T =>
        (Finset.univ.filter fun t : ↥T =>
          c₀ ((↑t : X)) ≠
            L.learn (fun i => ((↑(xs i) : X), c₀ (↑(xs i)))) (↑t)).card * 4
        ≤ T.card).card
      ≤ Fintype.card (Fin m → ↥T)) :
    let msT : MeasurableSpace ↥T := ⊤
    let D_sub := @uniformMeasure ↥T ⊤ _ (hTne.coe_sort)
    let D := @MeasureTheory.Measure.map ↥T X ⊤ _ Subtype.val D_sub
    MeasureTheory.Measure.pi (fun _ : Fin m => D)
      { xs : Fin m → X |
        D { x | L.learn (fun i => (xs i, c₀ (xs i))) x ≠ c₀ x }
          ≤ ENNReal.ofReal threshold }
      ≤ ENNReal.ofReal (1/2)
```

**Feasibility**: HIGH. The `let` bindings make the internal constructions visible. The threshold parameter allows both `1/4` (for vcdim_infinite_not_pac) and `ε ≤ 1/4` (for pac_lower_bound_core/member). The ≤ 1/2 conclusion is universal.

**LOC savings**: ~195 LOC for the shared lemma, ~10 LOC per consumer (vs ~195 each). Total with 3 consumers: 195 + 30 = 225 vs 585. **Saves ~360 LOC.**

**Risk**: The `let` bindings and typeclass instance alignment may cause unification issues. The MeasurableSpace ↥T := ⊤ letI must be carefully handled across the extraction boundary.

### 5.2 Recommendation

**Route B (factor first) is STRONGLY recommended** if the extraction compiles. It:
- Saves ~360 LOC across 3 consumers
- Makes the proof structure clearer
- Isolates the measure theory complexity in one place
- Makes future maintenance easier

**Fallback**: Route A (duplicate) if extraction encounters typeclass unification issues.

---

## 6. Counterfactual Pathways

### Route A: Direct nfl_counting_core + measure bridge duplication (WITH statement fix)

**Steps**:
1. Fix statements: change `(d-1)/(64*ε)` to `(d-1)/2` in both theorems + add MeasurableSingletonClass X
2. Fix `pac_lower_bound_member`: change `ε ≤ 1` to `ε ≤ 1/4`
3. Fix `sample_complexity_lower_bound`: propagate statement changes
4. In pac_lower_bound_core: derive 2m < d (omega), apply nfl_counting_core, duplicate measure bridge from vcdim_infinite_not_pac with threshold adaptation
5. In pac_lower_bound_member: same proof with δ parameter
6. Build + verify

**LOC**: ~2 (statement fixes) + ~156 (core) + ~156 (member) + ~10 (sample_complexity fix) = ~324
**Risk**: MEDIUM — measure bridge duplication is verbose but mechanical
**Confidence**: 0.65

### Route B: Factor shared measure bridge first, then apply

**Steps**:
1. Same statement fixes as Route A
2. Extract `nfl_measure_bridge` lemma (~195 LOC)
3. Refactor vcdim_infinite_not_pac to use shared lemma (~10 LOC, replaces ~195 LOC)
4. pac_lower_bound_core: 2m < d + nfl_counting_core + nfl_measure_bridge call (~30 LOC)
5. pac_lower_bound_member: same (~30 LOC)
6. Build + verify

**LOC**: ~195 (bridge) + ~10 (refactor) + ~30 (core) + ~30 (member) + ~10 (statement fixes) = ~275
**Net LOC change**: +275 - 195 (removed from vcdim_infinite_not_pac) = +80 net new LOC
**Risk**: MEDIUM-HIGH — extraction may hit typeclass unification issues
**Confidence**: 0.55

### Route C: Route pac_lower_bound_member through pac_lower_bound_core

**Analysis**: pac_lower_bound_core takes `(L, mf)` universally quantified, while pac_lower_bound_member takes `(L, m)` from a membership set. Can we derive the member version from the core version?

pac_lower_bound_core conclusion: `⌈(d-1)/2⌉ ≤ mf ε (1/7)`
pac_lower_bound_member conclusion: `⌈(d-1)/2⌉ ≤ m`

From hm: `m ∈ {m | ∃ L, ∀ D prob, ∀ c ∈ C, Pr[error ≤ ε] ≥ 1 - δ}`.
Extract L from hm. Define mf(ε', δ') := m (constant function). Then the PAC guarantee from hm gives: for this specific L and m, for all D, c: Pr ≥ 1 - δ. But pac_lower_bound_core needs the guarantee for ALL δ' with 0 < δ' ≤ 1, not just for the specific δ.

**Problem**: hm gives the PAC guarantee for the SPECIFIC δ (with δ ≤ 1/7), but pac_lower_bound_core's hypothesis requires the guarantee for ALL δ ∈ (0, 1]. Since δ ≤ 1/7, the guarantee Pr ≥ 1 - δ is STRONGER for smaller δ. If the guarantee holds for δ, it holds for all δ' ≥ δ (since 1 - δ' ≤ 1 - δ). But it does NOT hold for δ' < δ.

So we can specialize pac_lower_bound_core to δ = 1/7 only if the PAC hypothesis in the core is weakened to just δ = 1/7. But the core already hardcodes δ = 1/7 in its conclusion.

**Actually**: pac_lower_bound_core's hypothesis quantifies over ALL δ. The member version's hypothesis gives ONE δ. So routing member through core requires: the member's single-δ guarantee implies the core's all-δ guarantee. This is FALSE (knowing PAC works for one δ doesn't mean it works for all δ).

**Route C is NOT viable** as a simple routing. It would require restructuring pac_lower_bound_core to take a single δ.

### Route D: Keep 1/(64ε) constant, prove with generalized technique

**Would require**: A proof technique that works without 2m < d. The probabilistic method (random labeling + Fubini + Markov) is the standard approach, but it requires:
- Fubini theorem for finite products of discrete measures
- Reversed Markov inequality for ENNReal-valued random variables
- Integration infrastructure (∫ over product space)

This is ~300+ LOC of new infrastructure and uncertain feasibility in the current codebase.

**Confidence**: 0.2
**LOC**: 300+

### Route E: Case split on 2m vs d, keep 1/(64ε)

- If 2m < d: use nfl_counting_core (existing)
- If 2m ≥ d: derive ⌈(d-1)/(64ε)⌉ ≤ d/2 ≤ m. Wait — we need ⌈(d-1)/(64ε)⌉ ≤ m, but h_lt says m < ⌈(d-1)/(64ε)⌉. In the case 2m ≥ d, we have m ≥ d/2, and we need to show this contradicts m < ⌈(d-1)/(64ε)⌉ somehow. But ⌈(d-1)/(64ε)⌉ > d/2 is possible for small ε, so there's no contradiction. Route E fails for the same reason.

**NOT VIABLE.**

---

## 7. Gamma Discovery Summary

| ID | Discovery | Type | Impact |
|----|-----------|------|--------|
| Gamma_107 | 1/(64ε) constant incompatible with nfl_counting_core for ε < (d-1)/(32d) | Proof obstruction | Must weaken constant or find new technique |
| Gamma_108 | For m ≥ d, learner CAN see all of T, adversary powerless | Understanding | Confirms lower bound only meaningful for m < d |
| Gamma_109 | h_lt does not imply 2m < d for general ε ≤ 1/4 | Proof obstruction | Confirms Gamma_107 |
| Gamma_110 | Initially thought statement FALSE for small ε — RETRACTED after analysis | Retracted | Statement is TRUE (PAC must hold for ALL distributions) |
| Gamma_111 | NFL counting only proves m ≥ d/2, not m ≥ d/ε. The d/ε bound needs EHKV (information-theoretic). | Architecture | Current infra supports Ω(d) lower bound, not Ω(d/ε) |

---

## 8. Recommended Execution Plan

### Phase 0: Statement Fixes (~15 min)

1. `pac_lower_bound_core` (Gen:1923):
   - Add `[MeasurableSingletonClass X]` after `[MeasurableSpace X]`
   - Change `Nat.ceil ((d - 1 : ℝ) / (64 * ε))` to `Nat.ceil ((d - 1 : ℝ) / 2)` (Gen:1936)
   - Remove `hε1 : ε ≤ 1/4` (no longer needed for the d/2 constant; keep it if threshold adaptation still needs it)
   - **Actually**: keep `hε1 : ε ≤ 1/4` for the threshold adaptation step ({error ≤ ε} ⊆ {error*4 ≤ d})

2. `pac_lower_bound_member` (Gen:2453):
   - Add `[MeasurableSingletonClass X]`
   - Change `(hε1 : ε ≤ 1)` to `(hε1 : ε ≤ 1/4)`
   - Change conclusion constant to `(d-1)/2`

3. `sample_complexity_lower_bound` (Gen:2569):
   - Add `[MeasurableSingletonClass X]`
   - Change conclusion constant to `(d-1)/2`
   - Fix the call at Gen:2597-2599

4. Check PAC.lean for any callers of these theorems and propagate.

5. `lake build` — verify 0 errors.

### Phase 1: Factor measure bridge lemma (~3 hr)

Extract `nfl_measure_bridge` from vcdim_infinite_not_pac substep B.

### Phase 2: Close pac_lower_bound_core (~2 hr)

1. Derive `2 * m < d` from h_lt (omega)
2. Apply `nfl_counting_core`
3. Apply `nfl_measure_bridge` (or inline if extraction failed)
4. Threshold adaptation: `{error ≤ ε} ⊆ {error*4 ≤ d}` via ε ≤ 1/4
5. Final: ≤ 1/2 < 6/7

### Phase 3: Close pac_lower_bound_member (~1 hr)

Same as Phase 2 with δ parameter. Final: ≤ 1/2 < 1 - δ (from δ ≤ 1/7).

### Phase 4: Verification (~15 min)

1. `lake build` — 0 errors
2. Count sorrys (target: 8)
3. A4 check: no trivially-true sorrys
4. A5 check: no simplification

---

## 9. Critical Decision Point

**The proof agent MUST resolve Gamma_107/Gamma_111 before writing code.** Two options:

**Option 1 (RECOMMENDED)**: Weaken constant to `(d-1)/2`. Provable with existing infrastructure. Mathematically correct (PAC lower bound of Ω(d)). The ε-dependent bound Ω(d/ε) is documented as future work.

**Option 2**: Keep `(d-1)/(64ε)` and build EHKV infrastructure. Estimated 300+ LOC, uncertain feasibility, blocks on Fubini + reversed Markov for measures.

**The proof agent should present this decision to the user before proceeding.**
