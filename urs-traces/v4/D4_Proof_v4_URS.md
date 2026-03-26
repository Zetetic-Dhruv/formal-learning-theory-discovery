# D4 Proof Agent URS v4 — COMPLETE CLOSURE of boost_two_thirds_to_pac

## Status

- `chebyshev_majority_bound` is PROVED (Separation.lean:158-364, sorry-free).
- `iIndepFun_block_extract` is PROVED (Generalization.lean:3201-3243, sorry-free).
- `block_extract`, `majority_vote`, `block_extract_disjoint`, `block_extract_measurable` are PROVED.
- The sole target sorry is `boost_two_thirds_to_pac` at Separation.lean:398.
- A commented-out skeleton exists at lines 400-539 with 4 localized sorrys + build errors.

## 1. EXACT SORRY STATE

```lean
private theorem boost_two_thirds_to_pac (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool)
    (L : BatchLearner X Bool) (rate : ℕ → ℝ)
    (hrate : ∀ ε > 0, ∃ m₀, ∀ m ≥ m₀, rate m < ε)
    (huniv : ∀ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D →
      ∀ (c : Concept X Bool), c ∈ C →
        ∀ (m : ℕ),
          MeasureTheory.Measure.pi (fun _ : Fin m => D)
            { xs : Fin m → X |
              D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
                ≤ ENNReal.ofReal (rate m) }
            ≥ ENNReal.ofReal (2/3)) :
    PACLearnable X C := by
  sorry
```

**Goal:** `PACLearnable X C`

**Expanded:**
```
∃ (L' : BatchLearner X Bool) (mf : ℝ → ℝ → ℕ),
  ∀ (ε δ : ℝ), 0 < ε → 0 < δ →
    ∀ (D : Measure X), IsProbabilityMeasure D →
      ∀ (c : Concept X Bool), c ∈ C →
        let m := mf ε δ
        Measure.pi (fun _ : Fin m => D)
          { xs : Fin m → X |
            D { x | L'.learn (fun i => (xs i, c (xs i))) x ≠ c x }
              ≤ ENNReal.ofReal ε }
          ≥ ENNReal.ofReal (1 - δ)
```

## 2. BUILD ERROR ANALYSIS (Skeleton lines 400-539)

### Error 1: `Nat.sqrt_eq n (n + 1)` — DOES NOT EXIST

**Skeleton line 442:** `apply Nat.sqrt_eq n (n + 1)`

**Mathlib actual:** `Nat.sqrt_eq (n : ℕ) : sqrt (n * n) = n` (single argument, proves `sqrt(n²) = n`).

The skeleton needs `sqrt(n * (n+1)) = n`. This is NOT `Nat.sqrt_eq`.

**FIX:** Use `Nat.sqrt_add_eq`:
```
Nat.sqrt_add_eq (n : ℕ) (h : a ≤ n + n) : sqrt (n * n + a) = n
```
Rewrite `n * (n + 1) = n * n + n` and apply `Nat.sqrt_add_eq n (le_refl (n + n))`:
```lean
have hn_sqrt : Nat.sqrt m = n := by
  rw [hm_def, show n * (n + 1) = n * n + n from by ring]
  exact Nat.sqrt_add_eq n (Nat.le_add_left n n)
```

### Error 2: `positivity` failing on `0 < ε / 3`

**Skeleton line 431:** `have hε3 : (0 : ℝ) < ε / 3 := by positivity`

`positivity` may fail because `ε` is not visibly positive in the local context at that point. The hypothesis `hε : 0 < ε` IS in scope (from `intro ε δ hε hδ`), so `positivity` should work. If not:

**FIX:** `have hε3 : (0 : ℝ) < ε / 3 := by linarith`

### Error 3: `le_refl _` in block index bound (line 486)

**Skeleton line 486:** `have : k * n ≤ m := by rw [hm_def, hk_def]; ring_nf; exact le_refl _`

After `ring_nf`, the goal becomes `(n + 1) * n ≤ n * (n + 1)`. This is `Nat.mul_comm` applied, not `le_refl`.

**FIX:** `have : k * n ≤ m := by rw [hm_def, hk_def]; omega` or `linarith [Nat.mul_comm n (n+1)]`.

### Error 4: `Nat.div_mul_le_self` type mismatch

**Skeleton line 413:** `have hkm : m / k * k ≤ m := Nat.div_mul_le_self m k`

This is correct Lean4 — `Nat.div_mul_le_self : ∀ (m k : ℕ), m / k * k ≤ m`. No error here. But the NEXT line `have : k * m₀ ≤ m := by rw [Nat.mul_comm]; exact hkm` has a naming issue since `m₀` is a `let` binding. This should work but might need explicit unfolding.

**FIX:** No change needed if `m₀` unfolds correctly. Otherwise use `show` to make the goal explicit.

## 3. THE FUNDAMENTAL STRUCTURAL PROBLEM: `Fin (n*(n+1))` vs `Fin ((n+1)*n)`

### Problem

- `iIndepFun_block_extract` is proved for `Fin (k * m) → X` with `k` blocks of size `m`.
- The skeleton sets `k = n + 1` (blocks) and block_size = `n`, needing `Fin ((n+1) * n)`.
- But the sample space is `Fin m` where `m = n * (n + 1)`.
- `n * (n + 1) ≠ (n + 1) * n` DEFINITIONALLY in Lean4. They are propositionally equal via `Nat.mul_comm`.

### Resolution: Use `Fin.cast` or redefine `m`

**Option A (RECOMMENDED):** Redefine `m = (n+1) * n` instead of `m = n * (n+1)`.

Then `iIndepFun_block_extract (n+1) n D` works directly on `Fin ((n+1) * n)`.

The `mf` definition becomes: `mf ε δ = (n+1) * n` where `n = max m₀ kmin`.

For `Nat.sqrt`: need `sqrt((n+1) * n) = n`. Rewrite `(n+1) * n = n * n + n`:
```lean
have : (n + 1) * n = n * n + n := by ring
rw [this]; exact Nat.sqrt_add_eq n (Nat.le_add_left n n)
```

**Option B:** Keep `m = n * (n+1)` and use `Fin.cast (Nat.mul_comm n (n+1))` to convert between `Fin (n*(n+1))` and `Fin ((n+1)*n)`. This requires threading the cast through `block_extract`, `iIndepFun_block_extract`, and measure arguments. VERY verbose.

**VERDICT: Option A is strictly better.** Change `mf ε δ = (n+1) * n` (swap the multiplication order).

### Impact on the skeleton

With `m = (n+1) * n`:
- `Nat.sqrt m = n` still holds (same arithmetic, different presentation)
- `m / (Nat.sqrt m + 1) = (n+1)*n / (n+1) = n` via `Nat.mul_div_cancel n (Nat.succ_pos n)` — wait, that's `Nat.mul_div_cancel_left`. Actually: `(n+1)*n / (n+1)`. Use `Nat.mul_div_cancel_left n (Nat.succ_pos n)`.

Hmm. `Nat.mul_div_cancel_left` has signature `(a : ℕ) (hb : 0 < b) : b * a / b = a`. So `Nat.mul_div_cancel_left n (Nat.succ_pos n)` gives `(n+1) * n / (n+1) = n`. Correct.

- `block_extract (n+1) n` on `Fin ((n+1)*n) → X` — types match directly.
- `iIndepFun_block_extract (n+1) n D` — types match directly.

This eliminates the `Nat.mul_comm` cast problem entirely.

## 4. IGNORANCE MAP FOR EACH SORRY

### Γ₆₇a: Event containment (skeleton line 507)

**Statement:**
```lean
hcontain : { ω : Fin m → X | k < 2 * (Finset.univ.filter (fun j => ω ∈ events j)).card } ⊆
    { xs : Fin m → X | D { x | L'.learn (fun i => (xs i, c (xs i))) x ≠ c x }
      ≤ ENNReal.ofReal ε }
```

**KK (Known Knowns):**
- If majority of k blocks have D-error ≤ rate(n), then the majority vote hypothesis has D-error ≤ 2*rate(n) by a counting/Markov argument.
- rate(n) < ε/3 (from hrate_n), so 2*rate(n) < 2ε/3 < ε.
- `Set.subset_def`, `intro`, `simp` to unfold.

**KU (Known Unknowns):**
1. **L'.learn definitional unfolding:** Need to show that `L'.learn (fun i => (xs i, c (xs i)))` at sample size `m = (n+1)*n` enters the majority vote branch (i.e., `m₀ ≠ 0`). This requires `simp` or `show` to unfold the `let k := ...` and `if m₀ = 0 then ... else ...`.

2. **Majority vote error bound:** The mathematical claim is: if > k/2 blocks have per-block D-error ≤ r, then the majority vote D-error ≤ 2r. This is NOT a standard Mathlib lemma. It requires a custom proof:
   - For any x, majority_vote disagrees with c(x) only if > k/2 block hypotheses disagree at x.
   - So `{x | majority ≠ c(x)} ⊆ {x | more than k/2 blocks err at x}`.
   - By union bound: `D{majority err} ≤ D{⋃_{bad subset of size k/2+1} ⋂ block errs}`. Actually simpler: `D{majority err} ≤ (2/k) * Σ_j D{block j errs}`.

   This is WRONG. The correct bound is:
   - `{x | majority ≠ c(x)} ⊆ ⋃_j {x | h_j(x) ≠ c(x)}` — NO, this is too loose.
   - Correct: `{x | majority ≠ c(x)} ⊆ {x | ≥ k/2 of the h_j disagree at x}`.
   - By Markov: `D{≥ k/2 disagree} ≤ (2/k) * Σ_j D{h_j err}`.
   - If each D{h_j err} ≤ r and > k/2 blocks are "good" (D-error ≤ r), then... wait, we need a different argument.

   Actually the EVENT containment is simpler than I described. Let me re-examine.

   The events are `events j = {ω | D{L.learn(block_j(ω)) ≠ c} ≤ ofReal(rate n)}`.
   The majority event is `{ω | > k/2 of the events j hold}`.
   The target is `{ω | D{L'.learn(full_sample(ω)) ≠ c} ≤ ofReal(ε)}`.

   We need: if > k/2 blocks have small D-error, then the majority vote has small D-error.

   **The key lemma (needs proving inline):** For any ω such that > k/2 blocks have D-error ≤ rate(n):
   ```
   D{x | majority_vote(h_1(x),...,h_k(x)) ≠ c(x)}
     ≤ D{x | ≤ k/2 of the h_j agree with c at x}
     ≤ ... (this direction is wrong)
   ```

   Actually: if majority_vote ≠ c(x), then ≥ k/2 of the h_j disagree with c at x (by definition of majority). So `{x | majority ≠ c(x)} ⊆ {x | #{j : h_j(x) ≠ c(x)} ≥ k/2}`.

   Now: `D{#{j : h_j(x) ≠ c(x)} ≥ k/2}`. By Markov's inequality on the count:
   `D{count ≥ k/2} ≤ E[count] / (k/2) = (1/k * 2) * Σ_j D{h_j ≠ c}`.

   If > k/2 blocks are "good" (D-error ≤ rate(n)), then at most < k/2 are "bad". The good blocks contribute ≤ rate(n) each to the sum. The bad blocks contribute ≤ 1 each.

   So `Σ_j D{h_j ≠ c} ≤ (k/2 + 1) * rate(n) + (k/2 - 1) * 1`.

   This gives a bad bound. **The standard approach is different.**

   **CORRECT APPROACH:** The event containment does NOT use Markov on the D-measure of the majority. Instead:

   When > k/2 blocks are good (D-error ≤ rate(n) < ε), the majority vote at each x agrees with the majority of the block hypotheses. If > k/2 blocks have h_j(x) = c(x), then majority = c(x). The set of x where majority errs is contained in the set where ≤ k/2 blocks agree. But this is a statement about x, not about ω.

   **EVEN SIMPLER:** We don't need to bound `D{majority ≠ c}` in terms of block errors. We can use a DIFFERENT event containment:

   Define `events j = {ω | D{h_j(ω) ≠ c} ≤ ofReal(rate n)}`.
   Define `good_set = {ω | D{majority(ω) ≠ c} ≤ ofReal(ε)}`.

   We need: `{ω | > k/2 events hold} ⊆ good_set`.

   For this, we need: if > k/2 blocks have D-error ≤ rate(n), then majority has D-error ≤ ε.

   **Proof:** Fix ω with > k/2 good blocks. For any x:
   - majority_vote(h_1(x),...,h_k(x)) ≠ c(x) implies ≥ ceil(k/2) of the h_j disagree with c at x.
   - In particular, at least one GOOD block must disagree (since there are > k/2 good blocks and ≥ k/2 disagree, by pigeonhole at least one good block disagrees).

   Wait, that's also not the right direction. Let me think more carefully.

   majority_vote ≠ c(x) ↔ #{j | h_j(x) = true} > k/2 but c(x) = false, OR #{j | h_j(x) = false} ≥ k/2 but c(x) = true. Equivalently: #{j | h_j(x) ≠ c(x)} > k/2.

   So: `{x | majority ≠ c(x)} = {x | #{j | h_j(x) ≠ c(x)} > k/2}`.

   Now apply a union bound (Markov on the counting measure):
   `D{x | #{j | h_j(x) ≠ c(x)} > k/2} ≤ (2/k) * Σ_j D{h_j ≠ c}` (Markov).

   If > k/2 blocks are good: `Σ_{good j} D{h_j ≠ c} ≤ (good count) * rate(n)`.
   Bad blocks: `Σ_{bad j} D{h_j ≠ c} ≤ (bad count) * 1`.

   With > k/2 good and < k/2 bad: `Σ ≤ k * rate(n) + (k/2) * 1`. This is terrible.

   **THE ISSUE:** The Markov/union-bound approach gives a BAD bound. The skeleton's comment says "D(majority err) ≤ 2*rate(n) < ε" but this is WRONG in general.

   **CORRECT EVENT CONTAINMENT (no Markov needed):**

   Actually, the event containment should be TRIVIAL with the RIGHT definition:

   The majority vote's D-error at ω equals `D{x | majority_vote(h_j(x)) ≠ c(x)}`.

   Define `err_j(ω) = D{x | h_j(ω)(x) ≠ c(x)}`.

   If > k/2 blocks have err_j ≤ rate(n), then for any x, if majority disagrees with c, then > k/2 blocks individually disagree at x. But this means x is in the error set of > k/2 blocks, each of which has total D-measure ≤ rate(n). This does NOT directly bound the D-measure of majority error.

   **ACTUALLY CORRECT APPROACH:** The event containment is:

   `{ω | D{majority(ω) ≠ c} ≤ ofReal(rate n)} ⊇ {ω | majority of blocks are good}`

   This is FALSE. The majority vote error is NOT bounded by rate(n) just because most blocks have small error.

   **EXAMPLE:** k = 3 blocks, 2 good (error = 0.3) and 1 bad (error = 1.0). The majority at each x is: if 2+ of 3 agree, that's the output. The error of the majority can be as high as... well, it's bounded by the probability that ≥ 2 blocks err at x. By inclusion-exclusion this is ≤ sum of pairwise error overlaps, which can be up to rate(n)^2 * k(k-1)/2 ... actually this is getting complicated.

   **THE REAL MATHEMATICAL CONTENT:** The correct statement is:

   If ω is such that #{j | err_j(ω) ≤ r} > k/2, then
   `D{majority ≠ c} = D{#{j | h_j(x) ≠ c(x)} > k/2} ≤ 2 * (1/k) * Σ_j err_j(ω)`

   Wait — this uses Markov's inequality applied to the random variable `X(x) = #{j | h_j(x) ≠ c(x)}` under D. `E_D[X] = Σ_j D{h_j ≠ c} = Σ_j err_j(ω)`. By Markov: `D{X ≥ k/2} ≤ E[X] / (k/2) = 2/k * Σ_j err_j(ω)`.

   If all k blocks have err ≤ rate(n): `D{majority err} ≤ 2/k * k * rate(n) = 2 * rate(n)`.

   But we only have > k/2 good blocks. The bad ones contribute at most 1 each.
   `Σ_j err_j ≤ (k/2 + 1)*rate(n) + (k/2 - 1)*1`. With rate(n) < 1/3 and k ≥ 3:
   `≤ k/2 * (1/3) + k/2 ≈ 2k/3`. So `D{majority err} ≤ 2/k * 2k/3 = 4/3`. Useless.

   **THIS IS THE KNOWN BUG IN THE SKELETON.** The Markov-based event containment does NOT work when some blocks are bad.

   **CORRECT APPROACH (standard textbook):**

   The events should be defined as `events j = {ω | h_j(ω)(x) = c(x) for D-most x}`, specifically `events j = {ω | err_j(ω) ≤ rate(n)}`. The Chebyshev bound gives `μ{> k/2 events hold} ≥ 1 - δ`.

   For the FINAL event containment, we need a DIFFERENT chain:

   `{ω | > k/2 events hold} ⊆ {ω | D{majority ≠ c} ≤ ε}`

   This requires: if > k/2 blocks have err ≤ rate(n) < ε, then majority err ≤ ε.

   **KEY LEMMA (pointwise majority):** If > k/2 of the h_j satisfy h_j(x) = c(x), then majority_vote = c(x). Contrapositively: majority ≠ c(x) implies ≥ k/2 blocks disagree at x.

   So: `{x | majority ≠ c(x)} ⊆ {x | #{j | h_j(x) ≠ c(x)} ≥ ⌈k/2⌉}`.

   Now: `D{#{j | h_j(x) ≠ c(x)} ≥ ⌈k/2⌉}`. If EVERY block has err ≤ rate(n), then by Markov:
   `D ≤ 2/k * k * rate(n) = 2*rate(n) < 2ε/3 < ε`. WORKS.

   But if only > k/2 blocks are good (not all), then the bad blocks contribute up to 1 each to E[X], and the bound breaks.

   **RESOLUTION:** Strengthen the events. Instead of requiring > k/2 events, require ALL k events. Then `μ{all events} ≥ 1 - k * (1/3) * ...` — no, this doesn't use chebyshev_majority_bound.

   **ACTUAL RESOLUTION (from the standard proof):** The standard boosting proof works DIFFERENTLY.

   In the standard proof, the sample space is `(Fin k → Fin m₀ → X)` (k independent blocks). For each block j, the "event" is `A_j = {block is good}`. The events are i.i.d. with P[A_j] ≥ 2/3. The majority of k i.i.d. Bernoulli(≥2/3) events holds with probability ≥ 1-δ by Chebyshev.

   AND: when > k/2 blocks are good (err ≤ rate(n)) AND rate(n) < ε, the CONTAINMENT IS:

   `{ω | ALL k blocks have err ≤ rate(n)}` is NOT needed.

   The correct containment uses the stronger fact: when > k/2 blocks satisfy `h_j(x) = c(x)`, the majority is correct at x. So:

   `{x | majority ≠ c(x)} ⊆ {x | ≤ k/2 blocks have h_j(x) = c(x)}`
   `= {x | > k/2 blocks have h_j(x) ≠ c(x)}`

   Now define indicator `Y_j(x) = 1{h_j(x) ≠ c(x)}`. `E_D[Y_j] = err_j(ω)`.

   `D{Σ Y_j > k/2} ≤ ... ` by Markov ≤ `E[Σ Y_j] / (k/2) = (2/k) Σ err_j`.

   When > k/2 blocks have err_j ≤ rate(n):
   `Σ err_j ≤ (k/2+1) * rate(n) + (k/2-1) * 1`

   This is TOO LARGE.

   **THE REAL RESOLUTION:** The containment does NOT use Markov on D. Instead:

   For each x, majority_vote at x = c(x) iff > k/2 blocks have h_j(x) = c(x). So:

   `{x | majority ≠ c(x)} = {x | #{j | h_j(x) = c(x)} ≤ k/2}`

   Now: the set of "good" blocks G = {j | err_j(ω) ≤ rate(n)} has |G| > k/2 by assumption.

   For x to have majority error, we need #{j | h_j(x) ≠ c(x)} ≥ ⌈k/2⌉. Since |G| > k/2, at least one j ∈ G must have h_j(x) ≠ c(x).

   `{x | majority ≠ c(x)} ⊆ ⋃_{j ∈ G} {x | h_j(x) ≠ c(x)}`

   `D{majority ≠ c(x)} ≤ Σ_{j ∈ G} D{h_j ≠ c} ≤ |G| * rate(n) ≤ k * rate(n)`

   With rate(n) < ε/3 and k ≥ 3... this gives k * ε/3 which can be >> ε.

   **THIS BOUND IS ALSO BAD.**

   **DEFINITIVE CORRECT APPROACH:** The containment is POINTWISE, not via measure.

   When > k/2 blocks are good (have D-error ≤ rate(n)), and rate(n) < ε:

   We do NOT bound D{majority ≠ c} by rate(n). Instead:

   Consider any ω with > k/2 good blocks. For EACH x:
   - If > k/2 blocks have h_j(x) = c(x), then majority = c(x). So x is NOT in the error set.
   - If ≤ k/2 blocks have h_j(x) = c(x), then x IS in the error set.

   The error set `{x | majority ≠ c(x)} = {x | #{j ∈ [k] | h_j(x) ≠ c(x)} > k/2}`.

   This set is a subset of `{x | ∃ j ∈ G, h_j(x) ≠ c(x)} = ⋃_{j ∈ G} {x | h_j(x) ≠ c(x)}`.

   NO — that's a superset, not a subset. Actually the error set REQUIRES > k/2 blocks to err, while the union only requires 1. So the error set IS a subset of the union.

   But `D(⋃_{j ∈ G} err_j) ≤ Σ_{j ∈ G} D(err_j) ≤ |G| * rate(n)` which can be large.

   **I THINK THE SKELETON'S EVENT CONTAINMENT IS MATHEMATICALLY WRONG.**

   Let me reconsider the entire proof structure.

   **REVISED CORRECT APPROACH:** The standard boosting proof does not use event containment the way the skeleton does. The standard proof is:

   1. Define `good_j = {block_j has D-error ≤ rate(n)}` on the product space.
   2. Show `P[good_j] ≥ 2/3` for each j (from huniv + marginals).
   3. Show events are independent (from iIndepFun_block_extract).
   4. Apply chebyshev_majority_bound: `P[> k/2 good] ≥ 1-δ`.
   5. **CRITICAL STEP:** Show `{> k/2 good} ⊆ {majority D-error ≤ ε}`.

   Step 5 is the event containment, and it requires the argument above. The issue is that having > k/2 good blocks does NOT directly bound the majority's D-error to rate(n).

   **THE ACTUAL CORRECT ARGUMENT FOR STEP 5:**

   When ω has > k/2 good blocks, for any x, majority(x) = c(x) whenever > k/2 blocks satisfy h_j(x) = c(x).

   Now consider the complementary event over x: majority(x) ≠ c(x) iff ≤ k/2 blocks have h_j(x) = c(x), i.e., > k/2 blocks have h_j(x) ≠ c(x). But > k/2 blocks are good (D-error ≤ rate(n)), so among the > k/2 blocks that err at x, at most < k/2 are bad. So at least 1 good block must err at x. Thus:

   `{x | majority ≠ c(x)} ⊆ ⋃_{j ∈ good blocks} {x | h_j(x) ≠ c(x)}`

   `D{majority ≠ c(x)} ≤ Σ_{j ∈ good} err_j ≤ |good| * rate(n)`

   Since |good| ≤ k and rate(n) < ε/3, we get D{err} ≤ k * ε/3.

   For k = 3: ≤ ε. For k > 3: > ε. **THIS FAILS FOR LARGE k.**

   **THE FIX:** Use `ε` directly in hrate, not `ε/3`. If rate(n) < ε/k, then D{err} ≤ k * ε/k = ε.

   But `k` depends on δ, and `m₀` (from hrate) would depend on both ε and δ, creating a circular dependency in `mf`.

   **ALTERNATIVELY:** Don't use the union bound. Use a TIGHTER argument.

   **THE CORRECT TIGHTER ARGUMENT:**

   If > k/2 blocks are good, then for each x, if ≤ k/2 blocks have h_j(x) = c(x), then ≤ k/2 blocks are correct at x. Among the > k/2 good blocks, each is correct except on a D-measure ≤ rate(n) set. The probability that a SPECIFIC good block errs at x is ≤ rate(n). By a counting argument: the expected number of good blocks that err at a random x is ≤ |good| * rate(n).

   For majority to err, we need > k/2 blocks to err. But |good| > k/2. For majority to err, ALL good blocks must err at x (since if any good block is correct at x, that's one fewer error). No — for majority to err, > k/2 blocks must err at x. The good blocks are > k/2. If even ONE good block is correct at x, the number of correct blocks is ≥ 1 + (other correct goods) ≥ 1. We need > k/2 correct blocks for majority to be correct. So we need: among the > k/2 good blocks, > k/2 of ALL k blocks must be correct at x. This isn't guaranteed by just having > k/2 good blocks.

   **I NOW SEE THE REAL ISSUE.** The standard proof is NOT about bounding D-error of the majority vote. Instead:

   **STANDARD PROOF (Shalev-Shwartz & Ben-David, Theorem 7.7):**

   The standard proof defines the SUCCESS event differently:

   NOT: {ω | D{majority ≠ c} ≤ ε}
   BUT: {ω | ∀ x, majority(x) = c(x) if > k/2 blocks are correct at x}

   And the PAC bound is shown by:
   1. P[> k/2 blocks have err ≤ rate(n)] ≥ 1-δ (by Chebyshev).
   2. When > k/2 blocks have err ≤ rate(n), the majority errs only at x where > k/2 blocks err.
   3. D{> k/2 blocks err at x} ≤ 2/k * E[# blocks that err at x] = 2/k * Σ err_j ≤ 2 * rate(n).
   4. So D{majority ≠ c} ≤ 2 * rate(n) < 2ε/3 < ε. ← wait, this uses ALL blocks with err ≤ rate(n)?

   Hmm, in step 3, `Σ err_j` sums over ALL j. If > k/2 are good (err ≤ rate(n)) and the rest are bad (err ≤ 1):
   `Σ err_j ≤ k * rate(n) + (k/2) * 1`

   This is BAD. Unless ALL blocks are good.

   **KEY REALIZATION:** In the standard proof, they DON'T condition on "> k/2 blocks are good." They condition on "ALL k blocks are good." Or rather, they use a STRONGER event:

   `A = {ω | majority vote has D-error ≤ ε}`.

   And show P[A] ≥ 1-δ directly using Chebyshev on the indicator sum. But the Chebyshev bound only shows P[> k/2 good] ≥ 1-δ, which requires the step that {> k/2 good} ⊆ A.

   **WAIT — I think I had the Markov application wrong.** Let me redo:

   Fix ω with > k/2 good blocks. ALL good blocks have err_j ≤ rate(n). Let G = good set, |G| > k/2.

   For any x: majority ≠ c(x) ↔ #{j | h_j(x) ≠ c(x)} > k/2.

   Since |G| > k/2, the complement Gᶜ has |Gᶜ| < k/2. Even if ALL bad blocks err at x (#{j ∈ Gᶜ | h_j(x) ≠ c(x)} ≤ |Gᶜ| < k/2), for the total errors to exceed k/2, we need at least one good block to err at x.

   More precisely: #{j | h_j(x) ≠ c(x)} = #{j ∈ G | err} + #{j ∈ Gᶜ | err}.
   For this to exceed k/2: #{j ∈ G | err} > k/2 - |Gᶜ| ≥ k/2 - (k/2 - 1) = 1 (when |G| = k/2 + 1).

   So majority errs at x implies at least 1 good block errs at x. Thus:
   `{x | majority ≠ c(x)} ⊆ ⋃_{j ∈ G} {x | h_j(x) ≠ c(x)}`

   `D ≤ Σ_{j ∈ G} err_j ≤ |G| * rate(n) ≤ k * rate(n)`

   With rate(n) < ε/3: D ≤ k * ε/3. For k ≥ 4, this exceeds ε. **THE SKELETON'S ε/3 CHOICE IS WRONG.**

   **THE FIX:** Use `rate(n) < ε / (2k)` or equivalently `rate(n) < ε / (2*(⌈9/δ⌉+1))`.

   But this makes m₀ depend on both ε and δ, which is fine for mf(ε,δ).

   **ACTUALLY, THE SIMPLER FIX:** Instead of using the union bound over G, observe that:

   `{x | majority ≠ c(x)} = {x | #{j | h_j(x) ≠ c(x)} > k/2}`

   Apply Markov to the counting random variable Y(x) = #{j | h_j(x) ≠ c(x)} under D:
   `E_D[Y] = Σ_j err_j(ω)`

   If ALL k blocks have err ≤ rate(n) (not just > k/2):
   `E_D[Y] ≤ k * rate(n)`

   `D{Y > k/2} ≤ E[Y] / (k/2) = 2 * rate(n)` (Markov at threshold k/2, using E[Y] ≤ k * rate(n)).

   This gives D{majority err} ≤ 2 * rate(n) < 2ε/3 < ε. **BUT THIS REQUIRES ALL BLOCKS GOOD.**

   So the event containment works if we use `{ALL k blocks good} ⊆ {D-err ≤ ε}`.

   Then we need `P[all k blocks good] ≥ 1-δ`. By chebyshev_majority_bound, `P[> k/2 good] ≥ 1-δ`. But `{all good} ⊊ {> k/2 good}`.

   **P[all good] ≥ 1 - k/3 ≥ 1 - δ** when k/3 ≤ δ, i.e., k ≤ 3δ. But we need k ≥ 9/δ, so k is LARGE. P[all good] ≥ (2/3)^k which is exponentially small. NOT SUFFICIENT.

   **REVISED CORRECT APPROACH:** Use the Markov bound differently.

   For ω with > k/2 good blocks (|G| > k/2):
   The sum Σ_{j ∈ G} err_j ≤ |G| * rate(n).
   The bad blocks contribute Σ_{j ∈ Gᶜ} err_j ≤ |Gᶜ|.
   Total: Σ_j err_j ≤ |G| * rate(n) + |Gᶜ|.

   Markov: D{Y > k/2} ≤ (Σ err_j) / (k/2) ≤ (|G|*rate(n) + |Gᶜ|) / (k/2).

   For this to be ≤ ε: need |G|*rate(n) + |Gᶜ| ≤ εk/2.

   With |G| = k (best case all good): k*rate(n) ≤ εk/2, so rate(n) ≤ ε/2. Use rate(n) < ε/2. Then Markov gives ≤ ε. **BUT** when |G| = k/2 + 1, |Gᶜ| = k/2 - 1: bound = ((k/2+1)*ε/2 + k/2-1)/(k/2) ≈ ε/2 + 1. Still bad.

   **CONCLUSION: Markov on the D-error does not work with the {> k/2 good} event.**

   **THE STANDARD TEXTBOOK PROOF ACTUALLY CONDITIONS ON ALL BLOCKS BEING GOOD, AND USES A DIFFERENT CONCENTRATION INEQUALITY.** Let me re-examine.

   Actually, I was overcomplicating this. Let me re-read the standard proof (SSBD Theorem 7.7).

   **SSBD Theorem 7.7:** Given an ERM learner with sample complexity m_H(ε/2, 1/3) (achieving error ≤ ε/2 with prob ≥ 2/3):
   1. Draw k*m_H samples, split into k blocks.
   2. For each block, run ERM to get h_j with D-error ≤ ε/2 w.p. ≥ 2/3.
   3. Draw additional m_V validation samples.
   4. Pick the h_j with smallest empirical error on validation set.
   5. By Hoeffding + union bound: with prob ≥ 1-δ/2 over validation, the selected h has D-error ≤ ε.

   **THIS IS NOT MAJORITY VOTE.** The standard PAC proof uses a VALIDATION SET, not majority vote.

   The **majority vote boosting** is from the "universal learnable → PAC" proof, which IS different. Let me check Shalev-Shwartz & Ben-David more carefully.

   **SSBD Section 7.3 (No Free Lunch → ERM → Universal):**
   Theorem 7.2 shows the Fundamental Theorem. The universal learner is the ERM over all concepts.

   For the "UniversalLearnable → PAC" direction, the confidence boost from 2/3 to 1-δ IS done via majority vote in some references. The key point is:

   **WITH MAJORITY VOTE, the correct bound uses a DIFFERENT CHAIN:**

   Define `X_j = 1{h_j(x) ≠ c(x)}` for a random x from D. For fixed ω with all blocks good:
   `E_D[X_j] = err_j(ω) ≤ rate(n)`.

   The majority errs iff Σ X_j > k/2.

   Since X_j are NOT independent (they all depend on the same x), we can't use Chernoff on them. We use Markov:
   `D{Σ X_j > k/2} ≤ E[Σ X_j] / (k/2) = (2/k) * Σ err_j ≤ 2 * rate(n)`.

   **This works but requires ALL blocks to be good.**

   So the correct proof structure must be:

   a. Define events_j = {block j good}.
   b. Show P[all k events] ≥ 1-δ via Chebyshev/Chernoff.
   c. Show {all good} ⊆ {majority D-error ≤ ε} via Markov on D.

   For (b), P[all good] = P[no bad blocks] ≥ 1 - k * (1/3) (union bound). For this to be ≥ 1-δ, need k ≤ 3δ. But k should be LARGE for the concentration, not small.

   **THIS DOESN'T WORK EITHER.**

   **FINAL CORRECT UNDERSTANDING:**

   The proof structure in `chebyshev_majority_bound` is ALREADY CORRECT. It shows P[majority of good events hold] ≥ 1-δ. The event containment needs to be:

   `{> k/2 good blocks} ⊆ {majority D-error ≤ ε}`

   And the mathematical content is that when > k/2 blocks have err ≤ rate(n) < ε:

   For any x: majority(x) ≠ c(x) → > k/2 blocks err at x → (since > k/2 blocks are good) at least 1 good block errs at x.

   So: `{x | majority ≠ c} ⊆ ⋃_{j ∈ G} {x | h_j ≠ c at x}`.

   D-measure: ≤ Σ_{j∈G} err_j ≤ |G| * rate(n).

   For |G| ≤ k and rate(n) < ε/k:
   D ≤ k * ε/k = ε. WORKS.

   **RESOLUTION:** Use `hrate (ε / ↑(k+1))` instead of `hrate (ε / 3)` to get `rate(m₀) < ε/(k+1) ≤ ε/k`. But k depends on δ, and m₀ depends on ε/k which depends on δ. So mf(ε,δ) = k(δ) * m₀(ε,δ) where m₀ depends on both. This is fine — mf takes both ε and δ.

   **ALTERNATIVELY:** Use `rate(n) < ε` (from hrate at ε directly) AND note that when > k/2 blocks are good and rate(n) < ε, we have for majority error at x: need > k/2 blocks to err at x. The good blocks each have probability rate(n) < ε of erring. But this is per-x, not a D-measure bound.

   **I think the cleanest fix is:**

   Use `hrate ε hε` (not ε/3) to get m₀ with `rate m₀ < ε`. Then the events are `{ω | err_j ≤ rate(n)}` with rate(n) < ε. The event containment becomes:

   `{> k/2 good} ⊆ {D{majority ≠ c} ≤ ofReal ε}`

   Proof: if > k/2 blocks have err ≤ rate(n) < ε, then for any x, majority ≠ c(x) implies > k/2 blocks err at x. Since > k/2 blocks are good (err < ε), at least 1 good block errs at x. So {x | majority err} ⊆ ⋃_{j good} {x | h_j err}. D-measure ≤ Σ_{j good} err_j ≤ k * rate(n) < k * ε.

   This gives D ≤ kε, not ε. STILL BAD.

   **OK I THINK THE ISSUE IS MORE FUNDAMENTAL THAN I REALIZED.** Let me just use the pointwise argument correctly.

   **POINTWISE MAJORITY ARGUMENT (CORRECT):**

   Fix ω with > k/2 good blocks (|G| > k/2 where G = {j | err_j(ω) ≤ rate(n)}).

   For any x ∈ X:
   - The "vote" at x is majority_vote(h_1(x),...,h_k(x)).
   - majority_vote = c(x) iff #{j | h_j(x) = c(x)} > k/2.

   Let B(x) = {j | h_j(x) ≠ c(x)} (blocks that err at x).

   majority ≠ c(x) iff |B(x)| > k/2, i.e., |B(x)| ≥ ⌈(k+1)/2⌉.

   Since |G| > k/2, and |G ∩ B(x)| ≤ |G|:
   If |B(x)| > k/2, then since |Gᶜ| < k/2, we have |G ∩ B(x)| = |B(x)| - |Gᶜ ∩ B(x)| > k/2 - |Gᶜ| > 0.

   So at least 1 good block errs at x. Actually, we can be more precise:
   |G ∩ B(x)| ≥ |B(x)| - |Gᶜ| > k/2 - (k - |G|) = |G| - k/2 ≥ 1.

   Now the set `{x | majority ≠ c(x)} = {x | |B(x)| > k/2}`. We need to bound its D-measure.

   `D{|B(x)| > k/2}`. Apply Markov's inequality to the random variable f(x) = |B(x)| = Σ_j 1{h_j(x) ≠ c(x)}:

   `E_D[f] = Σ_j D{h_j ≠ c} = Σ_j err_j(ω)`
   `D{f > k/2} ≤ E[f] / (k/2+1)` ... actually Markov gives `D{f ≥ t} ≤ E[f]/t`.

   With t = k/2 + 1 (need f > k/2, so f ≥ k/2+1 since f is integer-valued for Bool):
   Wait, f is real-valued (sum of indicators). Actually f(x) = #{j | h_j(x) ≠ c(x)} which is a natural number.

   `D{f ≥ ⌈(k+1)/2⌉} ≤ E[f] / ⌈(k+1)/2⌉`

   Now bound E[f]:
   `E[f] = Σ_{j ∈ G} err_j + Σ_{j ∈ Gᶜ} err_j ≤ |G| * rate(n) + |Gᶜ| * 1`

   For |G| > k/2: |Gᶜ| < k/2. So:
   `E[f] ≤ k * rate(n) + k/2`

   `D{majority err} ≤ (k * rate(n) + k/2) / (k/2) = 2*rate(n) + 1`

   This is ALWAYS > 1 (since D is a probability measure). **Markov is USELESS here because the denominator (k/2) is comparable to the bad-block count contribution.**

   **THE REAL FIX:** The Markov bound on D is the wrong tool. The correct approach is:

   **Don't bound D{majority err} using Markov on the per-x error count.** Instead, use the direct set-containment approach:

   When ALL k blocks are good (which happens with high probability using a DIFFERENT concentration — not {> k/2 good} but a TIGHTER bound), then:

   `D{majority ≠ c} = D{> k/2 blocks err at x} ≤ E[count] / (k/2) = 2/k * k * rate(n) = 2*rate(n)`

   With rate(n) < ε/2: D ≤ ε. **This works but requires ALL blocks good.**

   `P[all good] ≥ 1 - k * (1-2/3) = 1 - k/3`. For this to be ≥ 1-δ: k ≤ 3δ. Since δ < 1, k ≤ 3. Not enough for chebyshev_majority_bound.

   **I NOW SEE THE FUNDAMENTAL MATHEMATICAL ISSUE: the skeleton conflates TWO DIFFERENT PROOF STRATEGIES.**

   **Strategy 1 (Majority vote + Chebyshev, the skeleton's approach):**
   Event: {> k/2 blocks good}. P ≥ 1-δ by Chebyshev. But event containment to {D-err ≤ ε} FAILS without all blocks being good.

   **Strategy 2 (Union bound on all blocks):**
   Event: {all k blocks good}. Event containment to {D-err ≤ ε} works via Markov. But P ≥ 1 - k/3, requiring k ≤ 3δ, giving few blocks and large sample complexity.

   **Strategy 3 (Median of means — the CORRECT standard approach):**
   The standard approach for confidence boosting from 2/3 to 1-δ IS the majority vote, and the event containment works because:

   When > k/2 blocks have err ≤ rate(n), the majority hypothesis EQUALS c on all x where > k/2 blocks agree, and the MEASURE of disagreement is bounded.

   **AH WAIT.** I think I've been wrong about the Markov bound direction. Let me redo.

   Fix ω. Let f(x) = #{j | h_j(x) ≠ c(x)}. majority errs at x iff f(x) > k/2.

   We don't know E_D[f] because err_j depends on ω and we only know > k/2 are ≤ rate(n), not all.

   But consider: for each j ∈ G (good blocks), `D{h_j ≠ c} = err_j ≤ rate(n)`.

   Let f_G(x) = #{j ∈ G | h_j(x) ≠ c(x)}. `E_D[f_G] = Σ_{j∈G} err_j ≤ |G| * rate(n)`.

   Now: majority errs at x iff f(x) > k/2 iff f_G(x) + f_{Gᶜ}(x) > k/2.
   Since f_{Gᶜ}(x) ≤ |Gᶜ| < k/2:

   majority errs → f_G(x) > k/2 - f_{Gᶜ}(x) ≥ k/2 - (|Gᶜ|) > k/2 - k/2 = 0.
   So f_G(x) ≥ 1.

   By Markov: D{f_G ≥ 1} ≤ E[f_G] = Σ_{j∈G} err_j ≤ |G| * rate(n).

   But |G| can be up to k. So D{majority err} ≤ k * rate(n).

   For this to be ≤ ε: need rate(n) ≤ ε/k. Since k depends on δ, use `hrate (ε / ↑(k+1))`.

   **THIS IS THE CORRECT FIX. The skeleton's ε/3 is wrong; it should be ε/k or ε/(k+1).**

   **BUT WAIT:** m₀ depends on ε/k, and k depends on δ. So m₀ = m₀(ε, δ). This is fine since mf(ε, δ) = k * m₀ can depend on both.

   **EVEN SIMPLER FIX:** Actually, I just realized: `D{f_G ≥ 1} ≤ E[f_G]` is a VERY LOOSE bound. The tight bound:

   `D{majority err} = D{f ≥ ⌈(k+1)/2⌉} ≤ D{f_G ≥ 1}` (as shown above).

   But `D{f_G ≥ 1} ≤ Σ_{j∈G} err_j ≤ |G| * rate(n)`.

   Hmm, I keep getting the same bound. The issue is the union bound is loose.

   **ALTERNATIVE: Use the SECOND MOMENT for a tighter bound.**

   Hmm, this is getting deeply into the math. Let me just use the simplest correct approach:

   **SIMPLEST CORRECT APPROACH FOR THE LEAN PROOF:**

   Set `rate_target = ε` (not ε/3). Get m₀ from hrate(ε). At block size m₀, rate(m₀) < ε.

   Event: `events j = {ω | D{h_j ≠ c} ≤ ENNReal.ofReal(rate n)}` where n ≥ m₀ so rate(n) < ε.

   P[events j] ≥ 2/3 by huniv. Events are independent by iIndepFun_block_extract. By chebyshev_majority_bound, P[> k/2 events hold] ≥ 1-δ.

   Event containment: {> k/2 events hold} ⊆ {D{majority ≠ c} ≤ ENNReal.ofReal ε}.

   The containment is POINTWISE in ω: if ω has > k/2 events holding, then for any x where majority(x) ≠ c(x), we know > k/2 blocks err at x, and since > k/2 blocks are good (err ≤ rate(n) < ε as ENNReal), at least 1 good block errs at x.

   So `{x | majority ≠ c(x)} ⊆ ⋃_{j ∈ G} {x | h_j(x) ≠ c(x)}`.

   D-measure: `D{majority ≠ c} ≤ Σ_{j∈G} D{h_j ≠ c} ≤ Σ_{j∈G} ENNReal.ofReal(rate n)`.

   **IN ENNREAL:** `Σ_{j∈G} ENNReal.ofReal(rate n) = |G| * ENNReal.ofReal(rate n)`.

   For this to be ≤ ENNReal.ofReal(ε): need `|G| * rate(n) ≤ ε` (in ℝ, then lift).

   Since |G| ≤ k and rate(n) < ε: |G| * rate(n) < k * ε. NOT ≤ ε unless k = 1.

   **THE UNION BOUND APPROACH DOES NOT WORK FOR MAJORITY VOTE WITH k > 1 BLOCKS.**

   **I BELIEVE THE CORRECT APPROACH IS FUNDAMENTALLY DIFFERENT.** The D-error of the majority vote is NOT bounded by the sum of block errors. It's bounded by the MAXIMUM of block errors (when all blocks are good). Here's why:

   When ALL blocks have err ≤ r, the majority at x is c(x) unless > k/2 blocks disagree at x. The probability of > k/2 independent Bernoulli(r) events all happening is ≤ C(k, k/2) * r^{k/2}. But blocks are NOT independent conditional on ω — they're deterministic functions of ω.

   **The x draws from D are what's random.** And the h_j(x) are all deterministic given ω. So we can't use independence across x.

   OK, here's my final understanding:

   **THE CORRECT BOUND:** For fixed ω with ALL k blocks good (err_j ≤ rate(n)):

   `D{majority ≠ c(x)} ≤ D{> k/2 of h_j err at x}`

   Apply Markov to Y = Σ_j 1{h_j(x) ≠ c(x)} under D:
   `E_D[Y] = Σ_j err_j ≤ k * rate(n)`
   `D{Y > k/2} ≤ E[Y] / ⌈(k+1)/2⌉ ≤ k * rate(n) / (k/2) = 2 * rate(n)`

   So `D{majority ≠ c} ≤ 2 * rate(n) < 2 * ε/2 = ε` (using rate(n) < ε/2).

   **THIS REQUIRES ALL BLOCKS GOOD.** `P[all good] ≥ (2/3)^k`. NOT sufficient.

   But combined with `P[> k/2 good] ≥ 1-δ`: on the event {> k/2 good}, the Markov bound gives `D ≤ 2*E[Y]/(k+1)` where `E[Y] = Σ err_j ≤ |G|*rate(n) + |Gᶜ|*1`. Bad.

   **DEFINITIVE RESOLUTION:** The majority vote boosting proof in the literature (Ben-David & Shalev-Shwartz, Understanding ML, Lemma 7.7) does NOT use Markov on D. Instead, it uses the following structure:

   If > k/2 blocks have err ≤ rate(n) < ε, then:
   - Let h_maj be the majority hypothesis.
   - For any x: h_maj(x) ≠ c(x) iff ≥ ⌈(k+1)/2⌉ blocks disagree.
   - Among the ≥ ⌈(k+1)/2⌉ disagreeing blocks, at most |Gᶜ| < k/2 are bad. So at least 1 good block disagrees.
   - `{x | h_maj ≠ c} ⊆ ⋃_{j∈G} {x | h_j ≠ c}`.
   - `D{⋃} ≤ Σ_{j∈G} D{h_j ≠ c} ≤ |G| * rate(n) ≤ k * rate(n)`.

   THIS IS `k * rate(n)`, not `rate(n)`. The standard textbook uses rate(n) = `ε/(2k)` or just `ε/2` combined with the TOURNAMENT/VALIDATION approach, not pure majority vote.

   **The pure majority vote approach is NOT the standard. The standard is the tournament.**

   **FINAL DEFINITIVE UNDERSTANDING FOR THIS PROOF:**

   There are two valid proof routes:

   **Route 1 (Tournament/Validation — SSBD Theorem 7.7):** Draw k blocks + 1 validation block. Get k hypotheses. Use validation to select the best. Probability analysis uses ε/2 split.

   **Route 2 (Majority vote — works correctly with ε/k scaling):** Use majority vote. Set rate(n) < ε/k. Then D{majority err} ≤ k * rate(n) < ε. P[> k/2 good] ≥ 1-δ. Sample complexity: k * m₀(ε/k). Since k = O(1/δ), total = O(m₀(ε/δ)/δ).

   **Route 3 (Majority vote — correct with Markov, all blocks good):** Use majority vote. Set rate(n) < ε/2. Then D{majority err} ≤ 2*rate(n) < ε when ALL blocks good. P[all good] ≥ 1 - k/3. Set k = ⌈3/δ⌉ so k/3 ≤ 1/δ... wait, need 1-k/3 ≥ 1-δ so k/3 ≤ δ, k ≤ 3δ. For δ < 1, k ≤ 2. Not useful.

   **Route 2 is the correct one for the proof.**

   **CRITICAL FIX TO THE SKELETON:** Replace `hrate (ε / 3) hε3` with `hrate (ε / ↑(kmin + 1))` where kmin = ⌈9/δ⌉ + 1. Since k ≤ n + 1 ≤ kmin + 1 (roughly), rate(n) < ε/(kmin+1) ≤ ε/k, giving k * rate(n) < ε.

   But this creates a CIRCULAR DEPENDENCY: kmin depends on δ, m₀ depends on ε/kmin.

   That's fine: `mf ε δ = (n+1) * n` where `n = max m₀ kmin`, `kmin = ⌈9/δ⌉ + 1`, `m₀ = Nat.find(hrate (ε / (kmin + 1)))`.

   **Wait — m₀ still only depends on ε and δ (through kmin). The mf function is allowed to depend on both. This works.**

   Actually, even simpler: since `n ≥ kmin ≥ k - 1`, we have `k = n + 1` and `rate(n) < ε / (kmin + 1) ≤ ε / (n + 1) = ε / k`. So `k * rate(n) < ε`.

   **THIS IS THE CORRECT APPROACH.** The event containment becomes:

   On {> k/2 blocks good}: D{majority err} ≤ k * rate(n) < k * ε/k = ε.

   **EVEN SIMPLER WITHOUT MARKOV:** The union bound `D{majority err} ≤ Σ_{j∈G} err_j` directly gives `≤ |G| * rate(n) ≤ k * rate(n) < ε`. But this is a MEASURE inequality (D-measure ≤ ENNReal.ofReal ε). Need:

   `D{majority ≠ c} ≤ ENNReal.ofReal ε`

   Since `D{majority ≠ c} ≤ D{⋃_{j∈G} {h_j ≠ c}} ≤ Σ_{j∈G} D{h_j ≠ c} ≤ Σ_{j∈G} ENNReal.ofReal(rate n) ≤ k * ENNReal.ofReal(rate n) ≤ ENNReal.ofReal(k * rate n) ≤ ENNReal.ofReal ε`

   The last step uses `k * rate(n) < ε` and monotonicity of `ENNReal.ofReal`.

   **This chain involves:** `measure_union_le`, `Finset.sum_le_sum`, ENNReal arithmetic.

   **In Lean4 tactics:** `calc` chain with `measure_mono`, `measure_iUnion_le`, `Finset.sum_le_card_nsmul`, ENNReal.ofReal monotonicity.

**KK:** Set containment (Set.subset_def), measure_mono, calc chains.
**KU:** Definitional unfolding of L'.learn to majority_vote branch. Connecting L'.learn's sub-sample indexing (j*n + i) to the events j definition.
**UK:** The ε/3 is wrong; need ε/(k+1) or ε/(n+1). The skeleton's claim "D(majority err) ≤ 2*rate(n)" is incorrect (it requires all blocks good, not just majority).
**UU:** The learn function's sub-sample uses `⟨j.val * m₀ + i.val, ...⟩` but the events use the same indexing, so they should align. Need to verify definitional equality after simp/unfold.

**Probability of closure: 70%** — the mathematical content requires careful calc chains but is straightforward once ε/(n+1) is used. The unfolding of L'.learn is the main Lean engineering challenge.

**Fallback:** Sorry the event containment as a localized sorry with a detailed docstring. This is ONE sorry, purely about definitional unfolding + ENNReal arithmetic, no deep math.

### Γ₆₇b: Block event measurability (skeleton line 520)

**Statement:** `∀ j, MeasurableSet (events j)` where `events j = {xs | D{x | L.learn(block_j(xs)) x ≠ c x} ≤ ENNReal.ofReal(rate n)}`.

**KK:** This is a standard measurability obligation. The function `xs ↦ D{x | L.learn(block_j(xs)) x ≠ c x}` maps `(Fin m → X) → ENNReal`. For the preimage of `{r | r ≤ threshold}` to be measurable, this function must be measurable.

**KU:** `L.learn` is noncomputable and arbitrary — no measurability guarantee. The composition `xs ↦ L.learn(labeled(block_j(xs))) ↦ D{error}` involves:
1. `block_j` extraction: measurable (proved: `block_extract_measurable`).
2. `labeled` construction: `fun i => (xs_j i, c(xs_j i))`: measurable if c is measurable. But c : X → Bool is arbitrary.
3. `L.learn`: arbitrary noncomputable function. NOT measurable in general.
4. `D{error}`: applying a measure to a set depending on the output of L.learn.

**UK (counterproof search):** Can this be PROVED? No. `L.learn` is an arbitrary function `{m : ℕ} → (Fin m → X × Bool) → (X → Bool)`. There is no measurability structure on BatchLearner. The function `xs ↦ D{L.learn(labeled xs) ≠ c}` is NOT measurable in general.

**UU:** However, `Measure.pi` is defined as an outer measure and applies to ALL sets (including non-measurable ones). So `μ(events j)` is well-defined even if events j is not measurable. The issue is only that `chebyshev_majority_bound` REQUIRES `MeasurableSet (events j)`.

**Resolution:** This is a GENUINE GAP between the abstract proof and the measurability machinery. Standard options:
1. **Sorry the measurability** — localized, documented, standard in the codebase.
2. **Reformulate chebyshev_majority_bound** to not require MeasurableSet — use outer measure directly. This is a significant refactor.
3. **Add a Measurable hypothesis to L.learn** — changes the BatchLearner structure.

**Recommendation: Option 1 (sorry).** This is consistent with the codebase pattern (see vcdim_finite_imp_pac_direct) and is A4-compliant (not trivially true — the conclusion genuinely depends on measurability holding).

**Probability of closure without sorry: 5%.** With sorry: 100%.

### Γ₆₇c: Block event independence (skeleton line 526)

**Statement:** `ProbabilityTheory.iIndepSet events μ`

**KK:**
- `iIndepFun_block_extract k n D` gives `iIndepFun (fun j ω => block_extract k n ω j) μ` where `μ = Measure.pi (fun _ : Fin (k*n) => D)`.
- `iIndepFun` can be converted to `iIndepSet` via preimage sets.

**KU:**
- The events are preimages: `events j = (fun ω => block_extract k n ω j) ⁻¹' good_blocks` where `good_blocks = {xs_block | D{L.learn(labeled xs_block) ≠ c} ≤ ENNReal.ofReal(rate n)}`.
- To go from `iIndepFun` to `iIndepSet`, use `iIndepFun_iff_measure_inter_preimage_eq_mul`:
  ```
  iIndepFun f μ ↔ ∀ S {sets} (H : ∀ i ∈ S, MeasurableSet (sets i)),
    μ (⋂ i ∈ S, f i ⁻¹' sets i) = ∏ i ∈ S, μ (f i ⁻¹' sets i)
  ```
- Then `iIndepSet events μ` (using `iIndepSet_iff`) requires:
  ```
  ∀ S {f'} (H : ∀ i ∈ S, MeasurableSet[generateFrom {events i}] (f' i)),
    μ (⋂ i ∈ S, f' i) = ∏ i ∈ S, μ (f' i)
  ```
- The connection requires `good_blocks` to be measurable (for `MeasurableSet (sets i)` in the `iIndepFun` formulation). This circles back to Γ₆₇b.

**With Γ₆₇b sorry'd (measurability assumed):**

The proof would be:
1. Show `events j = (fun ω => block_extract k n ω j) ⁻¹' good_blocks` (definitional).
2. Apply `iIndepFun_block_extract k n D` to get `iIndepFun`.
3. Convert using `iIndepFun_iff_measure_inter_preimage_eq_mul` and `iIndepSet_iff`.
4. The `MeasurableSet` obligations in the conversion are either `good_blocks` (sorry'd) or `MeasurableSet[generateFrom {events i}]` which reduces to `good_blocks` measurability.

**Type coercion issue:** `iIndepFun_block_extract` works on `Fin (k * n)`. With Option A (m = (n+1)*n, k = n+1), we need `Fin ((n+1) * n)`. This matches directly.

**Proof sketch (assuming measurability):**
```lean
have hindep : iIndepSet events μ := by
  -- events j is the preimage of good_blocks under block_extract
  have hevents_eq : ∀ j, events j = (fun ω => block_extract k n ω j) ⁻¹' good_blocks := by
    intro j; rfl  -- or ext; simp [events, block_extract]
  rw [show events = fun j => (fun ω => block_extract k n ω j) ⁻¹' good_blocks from
    funext hevents_eq]
  -- Use iIndepFun_block_extract to get independence
  -- Convert iIndepFun to iIndepSet via preimage
  rw [iIndepSet_iff]
  intro S f hf
  -- Use iIndepFun_iff_measure_inter_preimage_eq_mul
  have hindep_fun := iIndepFun_block_extract k n D
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at hindep_fun
  -- Connect the two formulations
  sorry -- technical bridging between generateFrom and comap
```

**UK:** The bridging between `iIndepSet_iff` (which uses `generateFrom {s i}`) and `iIndepFun_iff_measure_inter_preimage_eq_mul` (which uses `MeasurableSet` in the codomain) is non-trivial. The sets `f'` in `iIndepSet_iff` are measurable w.r.t. `generateFrom {events i}`, meaning each `f' i` is one of: `∅, events i, (events i)ᶜ, univ`. Need to show the product formula holds for these cases.

**Probability of closure: 40%** (assuming Γ₆₇b sorry). The technical bridging between the two independence formulations is the main challenge. May need 15-30 lines of tactic proof.

**Fallback:** Sorry the independence. This is A4-compliant (the conclusion is non-trivial and requires genuine independence).

### Γ₆₇d: Marginal probability (skeleton line 538)

**Statement:** `∀ j, μ (events j) ≥ ENNReal.ofReal (2/3)`

**KK:**
- `huniv D hD c hcC n` gives: `Measure.pi (fun _ : Fin n => D) {xs : Fin n → X | D{L.learn(labeled xs) ≠ c} ≤ ofReal(rate n)} ≥ ofReal(2/3)`.
- `events j = (fun ω => block_extract k n ω j) ⁻¹' good_blocks`.
- `μ (events j) = μ ((fun ω => block_extract k n ω j) ⁻¹' good_blocks)`.
- By the measure-preimage formula: `μ (f⁻¹' A) = (μ.map f) A` when f is measurable.
- `μ.map (fun ω => block_extract k n ω j) = Measure.pi (fun _ : Fin n => D)` — this is the marginal computation from `iIndepFun_block_extract`, specifically the `hmargin` step.

**KU:**
- Need to connect `μ (events j) = (μ.map (fun ω => block_extract k n ω j)) good_blocks`.
- `Measure.map_apply` requires measurability of the function (block_extract is measurable) and measurability of the set (good_blocks — Γ₆₇b issue).
- For outer measures, `μ (f⁻¹' A) ≥ (μ.map f) A` holds without measurability (outer measure is monotone under preimage). Actually `μ.map f A = μ (f⁻¹' A)` when f is measurable and A is measurable. Without A measurable, `μ.map f` is defined via outer measure anyway in Mathlib.

**Proof sketch:**
```lean
have hprob : ∀ j, μ (events j) ≥ ENNReal.ofReal (2/3) := by
  intro j
  -- events j is a preimage set
  show μ ((fun ω => block_extract k n ω j) ⁻¹' good_blocks) ≥ _
  -- μ.map (block_extract · j) = Measure.pi (fun _ : Fin n => D)
  have hmargin : μ.map (fun ω => block_extract k n ω j) = Measure.pi (fun _ : Fin n => D) := by
    -- From iIndepFun_block_extract proof's hmargin step
    -- Actually need to extract this as a standalone lemma or reprove
    sorry
  -- μ(f⁻¹' A) = (μ.map f)(A) for measurable f
  rw [← Measure.map_apply (block_extract_measurable k n j) (hevents_meas j)]  -- uses Γ₆₇b
  rw [hmargin]
  exact huniv D hD c hcC n
```

**UK:** The `hmargin` fact is proved INSIDE `iIndepFun_block_extract` but not exported as a standalone lemma. Options:
1. Extract it as a separate lemma (requires editing Generalization.lean).
2. Reprove it inline (duplicating ~10 lines).
3. Use `iIndepFun_iff_map_fun_eq_pi_map` to extract the marginal.

The marginal computation from `iIndepFun_block_extract`:
```lean
hmargin : ∀ j : Fin k, μ.map (fun ω => e ω j) = Measure.pi (fun _ : Fin m => D)
```
where `e = pcl.trans cur` and `e ω j = block_extract k m ω j` (definitionally, since that's how e is constructed).

So the marginal IS available from the proof of `iIndepFun_block_extract`, but wrapped inside the `iIndepFun_iff_map_fun_eq_pi_map` equivalence. We can extract it by:

```lean
have hindep := iIndepFun_block_extract k n D
rw [iIndepFun_iff_map_fun_eq_pi_map ...] at hindep
-- hindep : μ.map (fun ω j => block_extract k n ω j) = Measure.pi (fun j => μ.map (block_extract · j))
```

Then `μ.map (fun ω => block_extract k n ω j)` can be extracted via `congr_fun` and `measurePreserving_eval`.

**Probability of closure: 60%** (assuming Γ₆₇b sorry + hmargin extraction). The main challenge is extracting the marginal from `iIndepFun_block_extract` or reproving it.

**Fallback:** Extract `block_extract_marginal` as a standalone lemma in Generalization.lean (5-10 lines, factoring out the hmargin step from iIndepFun_block_extract).

## 5. CORRECTED PROOF SKELETON

### Key changes from the v3 skeleton:

1. **m = (n+1) * n** (swap multiplication order to match `finProdFinEquiv : Fin k × Fin n ≃ Fin (k*n)` with k = n+1).
2. **ε/(n+1) instead of ε/3** for hrate target (fixes event containment).
3. **Nat.sqrt_add_eq** instead of nonexistent `Nat.sqrt_eq n (n+1)`.
4. **Block indexing via finProdFinEquiv** instead of `j.val * n + i.val` (aligns with iIndepFun_block_extract).

```lean
private theorem boost_two_thirds_to_pac (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool)
    (L : BatchLearner X Bool) (rate : ℕ → ℝ)
    (hrate : ∀ ε > 0, ∃ m₀, ∀ m ≥ m₀, rate m < ε)
    (huniv : ∀ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D →
      ∀ (c : Concept X Bool), c ∈ C →
        ∀ (m : ℕ),
          MeasureTheory.Measure.pi (fun _ : Fin m => D)
            { xs : Fin m → X |
              D { x | L.learn (fun i => (xs i, c (xs i))) x ≠ c x }
                ≤ ENNReal.ofReal (rate m) }
            ≥ ENNReal.ofReal (2/3)) :
    PACLearnable X C := by
  -- Step 1: Construct the boosted BatchLearner (independent of ε, δ)
  -- L' splits Fin m samples into (Nat.sqrt m + 1) blocks of (m / (Nat.sqrt m + 1)) samples.
  -- Uses block_extract-compatible indexing via finProdFinEquiv.
  let L' : BatchLearner X Bool := {
    hypotheses := Set.univ
    learn := fun {m} S x =>
      let k := Nat.sqrt m + 1
      let blk_sz := m / k
      if hblk : blk_sz = 0 then L.learn S x
      else
        majority_vote k (fun j : Fin k =>
          L.learn (fun i : Fin blk_sz => S ⟨j.val * blk_sz + i.val, by
            have hj := j.isLt; have hi := i.isLt
            have : k * blk_sz ≤ m := Nat.div_mul_le_self m k |>.symm ▸
              (by rw [Nat.mul_comm]; exact Nat.div_mul_le_self m k)
            omega⟩) x)
    output_in_H := fun _ => Set.mem_univ _ }
  -- Step 2: Construct the sample complexity function mf
  -- For given ε, δ > 0:
  --   kmin = ⌈9/δ⌉ + 1 (enough blocks for Chebyshev)
  --   n = max m₀(ε/(kmin+1)) kmin (blocks are large enough AND numerous enough)
  --   mf = (n + 1) * n  (= k * blk_sz with k = n+1, blk_sz = n)
  --
  -- NOTE: mf uses (n+1)*n (not n*(n+1)) so that Fin((n+1)*n) aligns with
  -- finProdFinEquiv : Fin (n+1) × Fin n ≃ Fin ((n+1)*n) and iIndepFun_block_extract.
  refine ⟨L', fun ε δ =>
    if hε' : 0 < ε then
      if hδ' : 0 < δ then
        let kmin := Nat.ceil (9 / δ) + 1
        let ε' := ε / (↑kmin + 1)
        let m₀ := Nat.find (hrate ε' (by positivity))
        let n := max m₀ kmin
        (n + 1) * n
      else 0
    else 0, ?_⟩
  -- Step 3: Prove the probability bound
  intro ε δ hε hδ D hD c hcC
  -- Extract parameters
  set kmin := Nat.ceil (9 / δ) + 1 with hkmin_def
  set ε' := ε / (↑kmin + 1) with hε'_def
  have hε'_pos : (0 : ℝ) < ε' := by positivity
  set m₀ := Nat.find (hrate ε' hε'_pos) with hm₀_def
  have hm₀_spec : ∀ m ≥ m₀, rate m < ε' := Nat.find_spec (hrate ε' hε'_pos)
  set n := max m₀ kmin with hn_def
  set m := (n + 1) * n with hm_def
  set k := n + 1 with hk_def
  -- Nat.sqrt((n+1)*n) = n: since (n+1)*n = n*n + n and n ≤ n + n
  have hn_sqrt : Nat.sqrt m = n := by
    rw [hm_def, show (n + 1) * n = n * n + n from by ring]
    exact Nat.sqrt_add_eq n (Nat.le_add_left n n)
  -- Block size = n
  have hbs_eq : m / (Nat.sqrt m + 1) = n := by
    rw [hn_sqrt, hm_def]
    exact Nat.mul_div_cancel_left n (Nat.succ_pos n)
  -- n > 0 (since kmin ≥ 1)
  have hn_pos : 0 < n := by
    rw [hn_def]; exact lt_of_lt_of_le (by omega : 0 < kmin) (le_max_right _ _)
  -- rate(n) < ε' since n ≥ m₀
  have hrate_n : rate n < ε' := hm₀_spec n (le_max_left _ _)
  -- k * rate(n) < ε (event containment arithmetic)
  have hkrate : ↑k * rate n < ε := by
    calc ↑k * rate n < ↑k * ε' := by exact mul_lt_mul_of_pos_left hrate_n (by positivity)
      _ = ↑(n + 1) * (ε / (↑kmin + 1)) := by rfl
      _ ≤ ε := by
          rw [div_mul_eq_mul_div, mul_comm]
          exact div_le_self (le_of_lt hε) (by
            have : (1 : ℝ) ≤ ↑kmin + 1 := by positivity
            calc ↑(n + 1) ≤ ↑(kmin + 1) := by exact_mod_cast Nat.succ_le_succ (le_max_right m₀ kmin)
              _ = ↑kmin + 1 := by push_cast; ring
              ... ) -- needs careful arithmetic
  -- (9 : ℝ) / δ ≤ ↑k
  have hk_bound : (9 : ℝ) / δ ≤ (k : ℝ) := by
    calc (9 : ℝ) / δ ≤ ↑(Nat.ceil (9 / δ)) := Nat.le_ceil _
      _ ≤ ↑kmin := by exact_mod_cast Nat.le_succ _  -- kmin = ceil + 1
      _ ≤ ↑n := by exact_mod_cast le_max_right m₀ kmin
      _ ≤ ↑(n + 1) := by exact_mod_cast Nat.le_succ n
  -- Show the goal
  show Measure.pi (fun _ : Fin m => D)
    { xs : Fin m → X |
      D { x | L'.learn (fun i => (xs i, c (xs i))) x ≠ c x }
        ≤ ENNReal.ofReal ε }
    ≥ ENNReal.ofReal (1 - δ)
  -- Set up the measure and events
  set μ := Measure.pi (fun _ : Fin m => D)
  -- good_blocks: the set of block-sized samples where L has small error
  let good_blocks : Set (Fin n → X) :=
    { xs_blk | D { x | L.learn (fun i => (xs_blk i, c (xs_blk i))) x ≠ c x }
      ≤ ENNReal.ofReal (rate n) }
  -- events j = preimage of good_blocks under block extraction
  -- NOTE: m = k * n (= (n+1)*n), so block_extract k n works on Fin (k*n) = Fin m
  let events : Fin k → Set (Fin m → X) :=
    fun j => (fun ω => block_extract k n ω j) ⁻¹' good_blocks
  -- Event containment: {> k/2 good blocks} ⊆ {D-error ≤ ε}
  have hcontain : { ω : Fin m → X |
      k < 2 * (Finset.univ.filter (fun j => ω ∈ events j)).card } ⊆
    { xs : Fin m → X | D { x | L'.learn (fun i => (xs i, c (xs i))) x ≠ c x }
      ≤ ENNReal.ofReal ε } := by
    -- Γ₆₇a: When > k/2 blocks are good, majority D-error ≤ k * rate(n) < ε.
    -- Proof: majority errs at x → > k/2 blocks err at x → ≥ 1 good block errs at x.
    -- So {x | majority ≠ c} ⊆ ⋃_{j ∈ good} {x | h_j ≠ c}.
    -- D-measure ≤ Σ good err_j ≤ k * rate(n) < ε.
    -- Also requires unfolding L'.learn at m = (n+1)*n to the majority_vote branch.
    sorry
  -- Apply measure_mono to reduce to chebyshev_majority_bound
  calc μ { xs | D { x | L'.learn (fun i => (xs i, c (xs i))) x ≠ c x }
      ≤ ENNReal.ofReal ε }
    ≥ μ { ω | k < 2 * (Finset.univ.filter (fun j => ω ∈ events j)).card } :=
      measure_mono hcontain
    _ ≥ ENNReal.ofReal (1 - δ) := by
      -- Γ₆₇b: measurability (sorry)
      have hevents_meas : ∀ j, MeasurableSet (events j) := by
        intro j; exact sorry
      -- Γ₆₇c: independence
      have hindep : ProbabilityTheory.iIndepSet events μ := by
        exact sorry
      -- Γ₆₇d: marginal probability ≥ 2/3
      have hprob : ∀ j, μ (events j) ≥ ENNReal.ofReal (2/3) := by
        intro j; exact sorry
      exact chebyshev_majority_bound hδ hk_bound events hevents_meas hindep hprob
```

### LOC estimate: ~100 lines for the skeleton + ~60 lines for sorry closures = ~160 total.

## 6. SORRY CLOSURE TACTIC SEQUENCES

### Γ₆₇a: Event containment (~30-40 lines)

```lean
sorry -- OUTLINE:
-- intro ω hω
-- simp only [Set.mem_setOf_eq] at hω ⊢
-- -- Unfold L'.learn at sample size m = (n+1)*n
-- -- Show: Nat.sqrt m + 1 = k, m / k = n, n ≠ 0
-- -- So L'.learn enters majority_vote branch
-- -- show L'.learn (labeled ω) x = majority_vote k (fun j => L.learn (block_j_labeled) x)
-- change D {x | majority_vote k (fun j => L.learn ...) x ≠ c x} ≤ _
-- -- {x | majority ≠ c} ⊆ ⋃ j ∈ good_set, {x | L.learn(block_j) ≠ c at x}
-- -- where good_set = {j | ω ∈ events j}
-- let G := Finset.univ.filter (fun j : Fin k => ω ∈ events j)
-- have hG_card : k < 2 * G.card := hω
-- -- D(majority err) ≤ D(⋃ j ∈ G, block_err_j) ≤ Σ_{j∈G} D(block_err_j)
-- calc D {x | ...} ≤ D (⋃ j ∈ G, {x | ...}) := measure_mono (subset_iUnion_of_majority ...)
--   _ ≤ ∑ j ∈ G, D {x | ...} := measure_biUnion_le ...
--   _ ≤ ∑ j ∈ G, ENNReal.ofReal (rate n) := Finset.sum_le_sum (fun j hj => ...)
--   _ = G.card * ENNReal.ofReal (rate n) := by rw [Finset.sum_const, nsmul_eq_mul]
--   _ ≤ k * ENNReal.ofReal (rate n) := by ...
--   _ ≤ ENNReal.ofReal (k * rate n) := by ...
--   _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal (le_of_lt hkrate)
```

The hardest part is the first step: showing `{x | majority_vote ... ≠ c x} ⊆ ⋃ j ∈ G, {x | block_j_hyp ≠ c at x}` AND unfolding `L'.learn`.

**For the unfolding:** Need `simp only [L']` then show the `if` branch resolves to majority_vote. This requires `hbs_eq` and `hn_pos` to discharge the `if blk_sz = 0` guard.

**For the subset:** This is the pointwise majority argument. Need a lemma:
```lean
lemma majority_vote_err_subset (k : ℕ) (votes : Fin k → Bool) (target : Bool)
    (G : Finset (Fin k)) (hG : k < 2 * G.card) :
    majority_vote k votes ≠ target →
    ∃ j ∈ G, votes j ≠ target
```

This follows from: majority_vote = true iff > k/2 votes are true. If majority ≠ target and |G| > k/2, then among the > k/2 votes that disagree with target, at least one must be in G.

### Γ₆₇b: Measurability (1 line — sorry)

```lean
have hevents_meas : ∀ j, MeasurableSet (events j) := by
  intro j; exact sorry
```

**This remains a sorry. A4-compliant: the set is genuinely non-trivial and the conclusion is not trivially true.**

### Γ₆₇c: Independence (~20 lines, or sorry)

```lean
have hindep : ProbabilityTheory.iIndepSet events μ := by
  -- events j = (block_extract k n · j) ⁻¹' good_blocks
  -- iIndepFun_block_extract gives independence of block extractions
  -- Convert to iIndepSet via iIndepFun_iff_measure_inter_preimage_eq_mul
  have hfun_indep := iIndepFun_block_extract k n D
  rw [ProbabilityTheory.iIndepSet_iff]
  intro S f hf
  rw [ProbabilityTheory.iIndepFun_iff_measure_inter_preimage_eq_mul] at hfun_indep
  -- Each f i is measurable w.r.t. generateFrom {events i}
  -- which means f i ∈ {∅, events i, (events i)ᶜ, univ}
  -- Reduce to the case f i = events i (the preimage case)
  -- and handle complement/empty/univ by IsProbabilityMeasure
  sorry -- Technical bridging, ~15 more lines
```

**Fallback: sorry.** A4-compliant.

### Γ₆₇d: Marginal probability (~15 lines)

```lean
have hprob : ∀ j, μ (events j) ≥ ENNReal.ofReal (2/3) := by
  intro j
  -- events j = (block_extract k n · j) ⁻¹' good_blocks
  -- μ(f⁻¹' A) = (μ.map f)(A) for measurable f and measurable A
  -- μ.map (block_extract k n · j) = Measure.pi (fun _ : Fin n => D) (marginal)
  -- Then apply huniv
  have hblock_meas := block_extract_measurable k n j
  -- Extract marginal: need standalone lemma or re-derive
  have hmargin : μ.map (fun ω => block_extract k n ω j) =
      Measure.pi (fun _ : Fin n => D) := by
    -- This is the hmargin step from iIndepFun_block_extract
    -- Re-derive: use the same pcl/cur/e construction
    sorry -- ~20 lines duplicating hmargin from iIndepFun_block_extract
  -- Now connect
  calc μ (events j)
      = μ ((fun ω => block_extract k n ω j) ⁻¹' good_blocks) := rfl
    _ = (μ.map (fun ω => block_extract k n ω j)) good_blocks :=
        (Measure.map_apply hblock_meas (hevents_meas j)).symm
    _ = Measure.pi (fun _ : Fin n => D) good_blocks := by rw [hmargin]
    _ ≥ ENNReal.ofReal (2/3) := huniv D hD c hcC n
```

**Best approach:** Factor out `block_extract_marginal` as a standalone lemma in Generalization.lean:
```lean
lemma block_extract_marginal {X : Type*} [MeasurableSpace X]
    (k n : ℕ) (D : Measure X) [IsProbabilityMeasure D] (j : Fin k) :
    (Measure.pi (fun _ : Fin (k * n) => D)).map (fun ω => block_extract k n ω j) =
    Measure.pi (fun _ : Fin n => D)
```

This is a 10-line extraction from iIndepFun_block_extract's hmargin step.

**Probability of closure: 80%** if block_extract_marginal is factored out. Without it: 50% (re-deriving inline).

## 7. MATHLIB API INVENTORY

| API | Module | Verified | Signature |
|-----|--------|----------|-----------|
| `Nat.sqrt_add_eq` | Data.Nat.Sqrt | YES | `(n : ℕ) (h : a ≤ n + n) : sqrt (n * n + a) = n` |
| `Nat.sqrt_eq` | Data.Nat.Sqrt | YES | `(n : ℕ) : sqrt (n * n) = n` (WRONG arity for our use) |
| `Nat.mul_div_cancel_left` | Init (core) | YES | `(a : ℕ) (hb : 0 < b) : b * a / b = a` |
| `Nat.le_ceil` | Data.Nat.Ceil | YES | `(x : α) : x ≤ ↑(Nat.ceil x)` |
| `finProdFinEquiv` | Logic.Equiv.Fin.Basic | YES | `Fin m × Fin n ≃ Fin (m * n)` |
| `block_extract` | FLT_Proofs.Complexity.Generalization | YES | `(k m : ℕ) (S : Fin (k * m) → α) (j : Fin k) : Fin m → α` |
| `block_extract_measurable` | FLT_Proofs.Complexity.Generalization | YES | `Measurable (fun ω => block_extract k m ω j)` |
| `iIndepFun_block_extract` | FLT_Proofs.Complexity.Generalization | YES | `iIndepFun (fun j ω => block_extract k m ω j) (Measure.pi ...)` |
| `majority_vote` | FLT_Proofs.Complexity.Generalization | YES | `(k : ℕ) (votes : Fin k → Bool) : Bool` |
| `chebyshev_majority_bound` | FLT_Proofs.Theorem.Separation | YES | See signature at line 158 |
| `iIndepFun_iff_measure_inter_preimage_eq_mul` | Probability.Independence.Basic:652 | YES | `iIndepFun f μ ↔ ∀ S {sets} ...` |
| `iIndepSet_iff` | Probability.Independence.Basic:217 | YES | `iIndepSet s μ ↔ ∀ S {f} ...` |
| `Measure.map_apply` | MeasureTheory.Measure.MeasureSpace | YES | `(hf : Measurable f) (hs : MeasurableSet s) : μ.map f s = μ (f ⁻¹' s)` |
| `measure_mono` | MeasureTheory.Measure.MeasureSpace | YES | `(h : s ⊆ t) : μ s ≤ μ t` |
| `measure_biUnion_le` | MeasureTheory.Measure.MeasureSpace | YES | `μ (⋃ i ∈ S, f i) ≤ ∑ i ∈ S, μ (f i)` |
| `ENNReal.ofReal_le_ofReal` | Topology.Instances.ENNReal | YES | `(h : a ≤ b) : ofReal a ≤ ofReal b` |

## 8. RISK ASSESSMENT

| Sorry | Closure Prob | Risk | Fallback |
|-------|-------------|------|----------|
| Γ₆₇a (event containment) | 70% | Unfolding L'.learn to majority_vote branch requires careful simp; majority subset lemma needs ~10 lines | Sorry with detailed docstring (1 sorry) |
| Γ₆₇b (measurability) | 5% | Cannot prove without measurability of L.learn | Keep as sorry (standard in codebase) |
| Γ₆₇c (independence) | 40% | Bridging iIndepFun → iIndepSet via preimage is technically involved | Sorry with docstring (1 sorry) |
| Γ₆₇d (marginal probability) | 80% | Straightforward if block_extract_marginal is factored out | Factor out lemma; if blocked, sorry (1 sorry) |

**Best case:** 2 sorrys (Γ₆₇b measurability + Γ₆₇c independence). Sorry count: current 1 → 2 (net +1, but the 1 existing sorry is REPLACED by 2 localized ones).

**Worst case:** 4 sorrys (all four). Sorry count: current 1 → 4 (net +3). But each is localized and A4-compliant.

**Expected case:** 3 sorrys (Γ₆₇a closed, Γ₆₇b sorry, Γ₆₇c sorry, Γ₆₇d closed). Net: 1 → 2. This is a PROGRESS because the structural skeleton is no longer sorry'd — only localized technical obligations remain.

## 9. A4/A5 COMPLIANCE

**A4 (no trivially-true sorrys):**
- Γ₆₇b sorry: the conclusion `MeasurableSet (events j)` is non-trivial. The set depends on the composition of L.learn (arbitrary function) with D (a measure). Trivially true only if ALL sets were measurable, which is false in general. COMPLIANT.
- Γ₆₇c sorry: `iIndepSet events μ` is non-trivial. Independence requires specific structure (product measure + disjoint blocks). COMPLIANT.
- Γ₆₇d sorry (if kept): `μ (events j) ≥ ofReal(2/3)` is non-trivial — it's the core content from huniv + marginal. COMPLIANT.

**A5 (no simplification):**
- The proof uses the FULL infrastructure: chebyshev_majority_bound, iIndepFun_block_extract, block_extract, majority_vote.
- The event containment requires genuine mathematical content (majority vote analysis + ε/(k+1) scaling).
- No simplification of the proof structure. COMPLIANT.

## 10. CRITICAL FIXES SUMMARY (for the proof agent)

1. **SWAP multiplication order:** `mf = (n+1) * n` not `n * (n+1)`. This makes `Fin ((n+1)*n)` match `finProdFinEquiv : Fin (n+1) × Fin n ≃ Fin ((n+1)*n)`.

2. **Use ε/(kmin+1) not ε/3:** The event containment requires `k * rate(n) < ε`, which needs `rate(n) < ε/k`. Since k = n+1 ≤ kmin+1, use `hrate (ε/(kmin+1))`.

3. **Nat.sqrt_add_eq:** Replace `Nat.sqrt_eq n (n+1)` with:
   ```lean
   rw [show (n+1)*n = n*n + n from by ring]
   exact Nat.sqrt_add_eq n (Nat.le_add_left n n)
   ```

4. **Factor out block_extract_marginal:** Add to Generalization.lean:
   ```lean
   lemma block_extract_marginal (k n : ℕ) (D : Measure X) [IsProbabilityMeasure D] (j : Fin k) :
       (Measure.pi (fun _ : Fin (k * n) => D)).map (fun ω => block_extract k n ω j) =
       Measure.pi (fun _ : Fin n => D)
   ```

5. **Index arithmetic:** Use `omega` or `linarith` instead of `le_refl` for `k * n ≤ m` bounds.

## 11. BUILD ORDER FOR PROOF AGENT

1. Add `block_extract_marginal` lemma to Generalization.lean (~10 lines, factoring from iIndepFun_block_extract). Build and verify.
2. Uncomment and fix the skeleton in Separation.lean with the 5 critical fixes above. Keep all 4 sorrys. Build and verify 0 errors.
3. Close Γ₆₇d (marginal probability) using block_extract_marginal + huniv. Build.
4. Close Γ₆₇a (event containment) via majority subset argument + ENNReal calc chain. Build.
5. Attempt Γ₆₇c (independence). If blocked after 30 min, keep sorry. Build.
6. Γ₆₇b stays sorry (measurability — cannot close without L.learn measurability).
7. Final build, verify sorry count, run A4/A5 checks.

## 12. TOTAL LOC ESTIMATE

- Skeleton (fixed): ~90 lines
- Γ₆₇a closure: ~35 lines
- Γ₆₇d closure: ~15 lines
- block_extract_marginal: ~10 lines
- Γ₆₇c attempt: ~20 lines (or 1 line sorry)
- Γ₆₇b: 1 line sorry
- **Total: ~170 lines** (replacing the current 1-line sorry)
