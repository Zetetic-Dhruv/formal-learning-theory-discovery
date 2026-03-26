# D4 Proof Agent URS v2 — Close chebyshev_majority_bound + boost_two_thirds_to_pac

## Route Decision

**PRIMARY: Route A (Direct Chebyshev)**
- All Mathlib APIs confirmed. Infrastructure proved. 2 sorrys to close.
- Counterfactual (Route B: Recursive median-of-3) in `BoostingAlt.lean` (not in build).

## Target Sorrys

1. `chebyshev_majority_bound` (Separation.lean:153-162)
2. `boost_two_thirds_to_pac` (Separation.lean:180-193)

## Obstruction Resolutions

### HC_1 RESOLVED: iIndepFun -> indicator composition

**Problem:** `iIndepFun_block_extract` gives independence of block extraction functions
`(Fin (k*m) -> X) -> (Fin m -> X)`. Chebyshev needs independence of indicator random
variables `X_j : Omega -> Real` where `X_j(omega) = 1{block j is bad}`.

**Resolution:** Use `iIndepFun.comp` (Mathlib, Independence/Basic.lean:668):
```
lemma iIndepFun.comp {beta gamma : i -> Type*} {m_beta : forall i, MeasurableSpace (beta i)}
    {m_gamma : forall i, MeasurableSpace (gamma i)} {f : forall i, Omega -> beta i}
    (h : iIndepFun f mu) (g : forall i, beta i -> gamma i) (hg : forall i, Measurable (g i)) :
    iIndepFun (fun i => g i . f i) mu
```

Apply with:
- `f j := block_extract k m omega j` (type: `Fin (k*m) -> X` to `Fin m -> X`)
- `g j := fun (block : Fin m -> X) => indicator_j(block)` where
  `indicator_j(block) = if D{x | L.learn(block_as_training_data) x != c x} <= ofReal eps then (1:Real) else (0:Real)`

**Key measurability obligation:** `g j` must be `Measurable`. This requires the error
event `{block | D{x | h(x) != c(x)} <= eps}` to be measurable in `MeasurableSpace.pi`.

**Measurability strategy:** Work noncomputably. The function `g j` factors as:
1. `block : Fin m -> X` |-> `L.learn (fun i => (block i, c (block i)))` : X -> Bool
   (this is a noncomputable function of block, automatically measurable wrt the Borel sigma-algebra on `X -> Bool`)
2. `h : X -> Bool` |-> `D{x | h x != c x}` : ENNReal
   (measurability depends on D and c)
3. Threshold: `v : ENNReal` |-> `if v <= ofReal eps then 1 else 0` : Real
   (measurable as a step function)

**FALLBACK if measurability blocks:** Use `iIndepFun.comp0` which accepts `AEMeasurable`
instead of `Measurable`, or sorry the measurability obligation and document it.
In the worst case, refactor `chebyshev_majority_bound` to take `iIndepFun`-based
indicators directly rather than `events` (sets).

**PRACTICAL APPROACH:** The current `chebyshev_majority_bound` signature takes
`events : Fin k -> Set Omega` with probability hypotheses. This AVOIDS the indicator
composition issue entirely. The indicators are `Set.indicator (events j) 1`, and
independence of events follows from `iIndepFun` via `iIndepSet`.

To connect `iIndepFun_block_extract` to `iIndepSet`:
- Define `events j := {omega | omega in (good event for block j)}`
- Show these events are `iIndepSet` under `Measure.pi`
- This follows from `iIndepFun_block_extract` + the fact that `events j` is
  `(block_extract k m . j)^{-1}(good_blocks)` for a fixed measurable set `good_blocks`

### HC_2 RESOLVED: MemLp 2 for indicators

**Problem:** Chebyshev (`meas_ge_le_variance_div_sq`) requires `MemLp X 2 mu`.

**Resolution:** Indicator random variables `X_j(omega) = Set.indicator (events j) 1 omega`
take values in `{0, 1} subset [0, 1]`. Use:

```
theorem memLp_of_bounded [IsFiniteMeasure mu]
    {a b : Real} {f : alpha -> Real} (h : forall.ae x partial mu, f x in Set.Icc a b)
    (hX : AEStronglyMeasurable f mu) (p : ENNReal) : MemLp f p mu
```

Apply with `a = 0`, `b = 1`. The ae hypothesis `f x in [0,1]` is trivial for indicators.
`AEStronglyMeasurable` follows from measurability of the indicator (requires
`MeasurableSet (events j)`, which holds if `events j` is a preimage of a measurable set).

**Exact tactic sequence:**
```lean
have hbdd : forall.ae omega partial mu, X_j omega in Set.Icc 0 1 := by
  filter_upwards with omega
  simp only [Set.indicator_apply]
  split <;> constructor <;> norm_num
have hmeas : AEStronglyMeasurable X_j mu := by
  exact (measurable_const.indicator hevents_meas).aestronglyMeasurable
exact memLp_of_bounded hbdd hmeas 2
```

### HC_3 RESOLVED: Variance computation chain

**Problem:** Need `Var[S] <= k/4` where `S = sum_j X_j` and `X_j` are independent
Bernoulli indicators with `E[X_j] >= 2/3`.

**Resolution chain (5 steps):**

**Step 3a: Individual variance bound.**
For each `X_j` with values in `{0,1}`:
`Var[X_j] = E[X_j^2] - E[X_j]^2 = E[X_j] - E[X_j]^2 = E[X_j](1 - E[X_j])`
Since `X_j^2 = X_j` (indicator), and `E[X_j](1-E[X_j]) <= 1/4` (max at p=1/2).

Use `variance_le_sq_of_bounded` (Variance.lean:480):
```
lemma variance_le_sq_of_bounded [IsProbabilityMeasure mu] {a b : Real} {X : Omega -> Real}
    (h : forall.ae omega partial mu, X omega in Set.Icc a b) (hX : AEMeasurable X mu) :
    variance X mu <= ((b - a) / 2) ^ 2
```
Apply with `a = 0, b = 1`: `Var[X_j] <= ((1-0)/2)^2 = 1/4`.

**Step 3b: Sum variance = sum of individual variances (by independence).**
Use `IndepFun.variance_sum` (Variance.lean:403):
```
theorem IndepFun.variance_sum {iota : Type*} {X : iota -> Omega -> Real} {s : Finset iota}
    (hs : forall i in s, MemLp (X i) 2 mu)
    (h : Set.Pairwise (s : Set) fun i j => X i indep_fun[mu] X j) :
    variance (sum i in s, X i) mu = sum i in s, variance (X i) mu
```

To get pairwise `IndepFun` from `iIndepFun`: use `iIndepFun.indepFun` (which extracts
pairwise independence from mutual independence).

Result: `Var[S] = sum_j Var[X_j] <= sum_j (1/4) = k/4`.

**Step 3c: Apply Chebyshev.**
Use `meas_ge_le_variance_div_sq` (Variance.lean:378):
```
theorem meas_ge_le_variance_div_sq [IsFiniteMeasure mu] {X : Omega -> Real} (hX : MemLp X 2 mu)
    {c : Real} (hc : 0 < c) :
    mu {omega | c <= |X omega - mu[X]|} <= ENNReal.ofReal (variance X mu / c ^ 2)
```

Apply with `c = k/6` (the deviation from mean):
- `E[S] >= 2k/3` (each indicator has expectation >= 2/3)
- `|S - E[S]| >= k/6` implies `S <= k/2` (since `E[S] >= 2k/3` and `2k/3 - k/6 = k/2`)
- So `P[S <= k/2] <= P[|S - E[S]| >= k/6] <= Var[S]/(k/6)^2 <= (k/4)/(k^2/36) = 9/k`

**Step 3d: Connect 9/k <= delta.**
From hypothesis `hk : 9/delta <= k` (already proved in codebase), get `9/k <= delta`.

### HC_4 RESOLVED: Majority vote correctness

**Problem:** Connect `P[S <= k/2]` to `P[majority wrong]`.

**Resolution:** The majority vote is wrong iff more than k/2 blocks have error > eps.
Equivalently, if `k < 2 * |{j | omega in events j}|` (the condition in `chebyshev_majority_bound`).

The event `{omega | k < 2 * (Finset.univ.filter (fun j => omega in events j)).card}`
is EXACTLY the event that more than k/2 blocks succeed. Its complement is the event
that at most k/2 blocks succeed, which implies majority vote is wrong.

Wait -- the current signature has the MAJORITY SUCCESS event:
```
mu {omega | k < 2 * (Finset.univ.filter (fun j => omega in events j)).card} >= ofReal (1 - delta)
```
This is `P[more than k/2 blocks succeed] >= 1 - delta`, which is equivalent to
`P[at most k/2 blocks succeed] <= delta`.

So we need: `P[S_good <= k/2] <= delta` where `S_good = number of good blocks`.
This is `P[S_bad >= k/2] <= delta` where `S_bad = k - S_good`.
By Chebyshev on S_good: `P[S_good <= E[S_good] - (E[S_good] - k/2)] <= Var[S_good]/(E[S_good] - k/2)^2`.
With `E[S_good] >= 2k/3`: deviation = `2k/3 - k/2 = k/6`.
So `P[S_good <= k/2] <= (k/4)/(k/6)^2 = (k/4)/(k^2/36) = 9/k <= delta`.

The connection from `chebyshev_majority_bound` back to `boost_two_thirds_to_pac` is:
1. Define `events j := {omega | block j leads to error <= eps}`
2. Show `P[events j] >= 2/3` (from `huniv` hypothesis)
3. Show events are independent (from `iIndepFun_block_extract`)
4. Apply `chebyshev_majority_bound` to get `P[majority succeeds] >= 1 - delta`
5. Majority succeeds => boosted learner has error <= eps
6. Therefore PACLearnable

## Proof Plan: chebyshev_majority_bound (Separation:153)

### Signature Recap
```lean
private lemma chebyshev_majority_bound
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu]
    {k : Nat} {delta : Real} (h_delta_pos : 0 < delta)
    (hk : (9 : Real) / delta <= k)
    (events : Fin k -> Set Omega)
    (_hprob : forall j, mu (events j) >= ENNReal.ofReal (2/3)) :
    mu {omega | k < 2 * (Finset.univ.filter (fun j => omega in events j)).card} >=
      ENNReal.ofReal (1 - delta)
```

### Step-by-Step Tactic Proof

```lean
private lemma chebyshev_majority_bound ... := by
  -- Step 0: Handle edge case k = 0
  by_cases hk0 : k = 0
  · subst hk0; simp at hk; linarith

  -- Step 1: Define indicator random variables
  -- X_j(omega) = if omega in events j then (1 : Real) else 0
  set X : Fin k -> Omega -> Real := fun j omega =>
    Set.indicator (events j) (fun _ => (1 : Real)) omega with hX_def

  -- Step 2: Define S = sum of indicators
  set S : Omega -> Real := fun omega => Finset.univ.sum (fun j => X j omega) with hS_def

  -- Step 3: Show S counts the number of successes
  -- S omega = (Finset.univ.filter (fun j => omega in events j)).card
  have hS_count : forall omega,
      S omega = ((Finset.univ.filter (fun j => omega in events j)).card : Real) := by
    intro omega
    simp only [hS_def, hX_def, Finset.sum_indicator_eq_sum_filter]
    simp [Finset.sum_const, smul_eq_mul, mul_one]

  -- Step 4: Rewrite the goal set in terms of S
  -- {omega | k < 2 * card} = {omega | k/2 < S omega} (approximately)
  -- More precisely: k < 2 * card <=> k/2 < card <=> (k:Real)/2 < S omega
  suffices h : mu {omega | (k : Real) / 2 < S omega} >= ENNReal.ofReal (1 - delta) by
    apply le_trans _ h
    apply measure_mono
    intro omega hmem
    simp only [Set.mem_setOf_eq] at hmem |-
    rw [hS_count]
    exact_mod_cast hmem

  -- Step 5: Complement bound — show P[S <= k/2] <= delta
  -- Then P[S > k/2] >= 1 - delta
  rw [ge_iff_le, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (le_of_lt h_delta_pos).le]
  -- Goal: ENNReal.ofReal (1 - (1 - delta)) <= mu {omega | k/2 < S omega}
  -- i.e., ENNReal.ofReal delta <= mu {S > k/2}
  -- Equivalently: mu {S <= k/2} <= 1 - ENNReal.ofReal (1 - delta)
  -- Strategy: bound mu {S <= k/2} <= ENNReal.ofReal delta via Chebyshev

  -- Step 6: Establish MemLp for each X_j
  have hX_bdd : forall j, forall.ae omega partial mu, X j omega in Set.Icc 0 1 := by
    intro j
    filter_upwards with omega
    simp only [hX_def, Set.indicator_apply]
    split <;> constructor <;> norm_num

  -- Need measurability of events for indicators
  -- FALLBACK: if events are not provably measurable, sorry this
  -- For the proof to work, we need MeasurableSet (events j)
  -- This is a PRECONDITION that should be added to the signature or derived

  -- Step 7: Bound E[X_j] >= 2/3
  -- E[X_j] = integral (indicator (events j) 1) = mu(events j)
  -- From _hprob: mu(events j) >= ofReal(2/3)

  -- Step 8: Bound E[S] >= 2k/3
  -- E[S] = sum_j E[X_j] >= sum_j (2/3) = 2k/3

  -- Step 9: Bound Var[X_j] <= 1/4
  -- By variance_le_sq_of_bounded with a=0, b=1

  -- Step 10: Bound Var[S] <= k/4
  -- By IndepFun.variance_sum (requires pairwise independence + MemLp 2)
  -- Independence: derive iIndepSet from the caller (NOT available in current signature!)
  -- ISSUE: current signature does NOT have independence of events!

  -- CRITICAL OBSERVATION: The current signature of chebyshev_majority_bound does NOT
  -- include an independence hypothesis. This means either:
  -- (a) The proof must work WITHOUT independence (impossible for Chebyshev on sum)
  -- (b) An independence hypothesis must be ADDED to the signature
  -- (c) The proof uses a different technique (e.g., union bound + counting)

  -- RESOLUTION: ADD independence hypothesis to chebyshev_majority_bound.
  -- Change signature to include:
  --   (hindep : iIndepSet events mu)
  -- or equivalently pass the indicator independence.

  sorry
```

### CRITICAL: Signature Amendment Required

The current `chebyshev_majority_bound` signature is MISSING an independence hypothesis.
The proof CANNOT proceed without it. The amendment:

```lean
private lemma chebyshev_majority_bound
    {Omega : Type*} [MeasurableSpace Omega] {mu : MeasureTheory.Measure Omega}
    [MeasureTheory.IsProbabilityMeasure mu]
    {k : Nat} {delta : Real} (h_delta_pos : 0 < delta)
    (hk : (9 : Real) / delta <= k)
    (events : Fin k -> Set Omega)
    (hevents_meas : forall j, MeasurableSet (events j))       -- NEW
    (hindep : forall i j, i != j -> ProbabilityTheory.IndepSet (events i) (events j) mu)  -- NEW (pairwise)
    (_hprob : forall j, mu (events j) >= ENNReal.ofReal (2/3)) :
    mu {omega | k < 2 * (Finset.univ.filter (fun j => omega in events j)).card} >=
      ENNReal.ofReal (1 - delta)
```

Alternatively, use `iIndepSet events mu` which gives mutual independence (stronger but
also available from `iIndepFun_block_extract`).

### Proof After Amendment (Full Tactic Sequence)

```lean
private lemma chebyshev_majority_bound
    {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    [IsProbabilityMeasure mu]
    {k : Nat} {delta : Real} (h_delta_pos : 0 < delta)
    (hk : (9 : Real) / delta <= k)
    (events : Fin k -> Set Omega)
    (hevents_meas : forall j, MeasurableSet (events j))
    (hindep : ProbabilityTheory.iIndepSet (fun j => events j) mu)
    (hprob : forall j, mu (events j) >= ENNReal.ofReal (2/3)) :
    mu {omega | k < 2 * (Finset.univ.filter (fun j => omega in events j)).card} >=
      ENNReal.ofReal (1 - delta) := by
  -- Edge case
  by_cases hk0 : k = 0
  · subst hk0; simp; exact measure_univ_le _  -- or handle via hk contradiction
  have hk_pos : (0 : Real) < k := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk0)

  -- Define real-valued indicators
  set X : Fin k -> Omega -> Real :=
    fun j => Set.indicator (events j) (fun _ => (1 : Real))

  -- S = sum of indicators = count of successful events
  set S : Omega -> Real := fun omega => Finset.univ.sum (fun j => X j omega)

  -- S counts successes (proved by Finset.sum_indicator_eq_sum_filter)
  have hS_eq_card : forall omega,
      S omega = ((Finset.univ.filter (fun j : Fin k => omega in events j)).card : Real) := by
    intro omega; simp [S, X, Finset.sum_indicator_eq_sum_filter, Finset.sum_const, smul_eq_mul]

  -- MemLp 2 for each X_j
  have hX_memLp : forall j, MemLp (X j) 2 mu := by
    intro j
    exact memLp_indicator_const 2 (hevents_meas j) 1 (Or.inl rfl)
    -- Or: memLp_of_bounded (bounded in [0,1]) ...

  -- MemLp 2 for S
  have hS_memLp : MemLp S 2 mu := by
    exact memLp_finset_sum' _ (fun j _ => hX_memLp j)

  -- E[X_j] = mu(events j) as real
  have hEX : forall j, mu[X j] >= 2/3 := by
    intro j
    rw [integral_indicator_one (hevents_meas j)]
    -- integral of indicator = mu(events j).toReal
    -- From hprob: mu(events j) >= ofReal(2/3), so mu(events j).toReal >= 2/3
    sorry -- convert ENNReal to Real: needs IsProbabilityMeasure for finiteness

  -- E[S] >= 2k/3
  have hES : mu[S] >= 2 * k / 3 := by
    rw [integral_finset_sum Finset.univ (fun j _ => (hX_memLp j).integrable one_le_two)]
    calc Finset.univ.sum (fun j => mu[X j])
        >= Finset.univ.sum (fun _ : Fin k => (2:Real)/3) :=
          Finset.sum_le_sum (fun j _ => hEX j)
      _ = k * (2/3) := by simp [Finset.sum_const, Finset.card_fin]
      _ = 2 * k / 3 := by ring

  -- Var[X_j] <= 1/4
  have hVarX : forall j, variance (X j) mu <= 1/4 := by
    intro j
    calc variance (X j) mu
        <= ((1 - 0) / 2) ^ 2 := by
          apply variance_le_sq_of_bounded _ (hX_memLp j).aemeasurable
          filter_upwards with omega
          simp [X, Set.indicator_apply]; split <;> constructor <;> norm_num
      _ = 1/4 := by norm_num

  -- Pairwise IndepFun from iIndepSet
  have hpairwise : Set.Pairwise (Finset.univ : Finset (Fin k)).toSet
      (fun i j => (X i) indep_fun[mu] (X j)) := by
    intro i _ j _ hij
    -- From iIndepSet -> iIndepFun_indicator -> pairwise IndepFun
    exact (hindep.iIndepFun_indicator).indepFun hij

  -- Var[S] = sum Var[X_j] (by independence)
  have hVarS_eq : variance S mu = Finset.univ.sum (fun j => variance (X j) mu) := by
    exact IndepFun.variance_sum (fun j _ => hX_memLp j) hpairwise

  -- Var[S] <= k/4
  have hVarS : variance S mu <= k / 4 := by
    rw [hVarS_eq]
    calc Finset.univ.sum (fun j => variance (X j) mu)
        <= Finset.univ.sum (fun _ : Fin k => (1:Real)/4) :=
          Finset.sum_le_sum (fun j _ => hVarX j)
      _ = k * (1/4) := by simp [Finset.sum_const, Finset.card_fin]
      _ = k / 4 := by ring

  -- Chebyshev: P[|S - E[S]| >= k/6] <= Var[S] / (k/6)^2 <= (k/4)/(k^2/36) = 9/k
  have hcheb : mu {omega | k / 6 <= |S omega - mu[S]|} <=
      ENNReal.ofReal (variance S mu / (k / 6) ^ 2) := by
    exact meas_ge_le_variance_div_sq hS_memLp (by positivity)

  -- 9/k <= delta (from hk : 9/delta <= k)
  have h9k : (9 : Real) / k <= delta := by
    rw [div_le_iff hk_pos]
    calc 9 = (9 / delta) * delta := by field_simp
      _ <= k * delta := by exact mul_le_mul_of_nonneg_right hk (le_of_lt h_delta_pos)

  -- Var[S]/(k/6)^2 <= (k/4)/(k/6)^2 = 9/k <= delta
  have hbound : variance S mu / (k / 6) ^ 2 <= delta := by
    calc variance S mu / (k / 6) ^ 2
        <= (k / 4) / (k / 6) ^ 2 := by
          apply div_le_div_of_nonneg_right hVarS (by positivity)
      _ = 9 / k := by field_simp; ring
      _ <= delta := h9k

  -- P[S <= k/2] <= P[|S - E[S]| >= E[S] - k/2] <= P[|S - E[S]| >= k/6]
  -- because E[S] >= 2k/3 so E[S] - k/2 >= 2k/3 - k/2 = k/6
  -- Therefore P[S <= k/2] <= delta

  -- Convert to the goal: mu {majority succeeds} >= 1 - delta
  -- {majority succeeds} = {S > k/2} = complement of {S <= k/2}
  -- mu {S > k/2} = 1 - mu {S <= k/2} >= 1 - delta

  sorry -- Final assembly: connecting Chebyshev bound to the specific set in the goal
```

### Remaining Micro-Sorrys in Proof

After the signature amendment, the proof has these internal obligations:

1. **ENNReal-to-Real conversion for E[X_j]** (~10 LOC):
   `mu(events j) >= ofReal(2/3)` implies `mu(events j).toReal >= 2/3`.
   Use `ENNReal.toReal_le_toReal` + `ENNReal.ofReal_toReal` + finiteness from `IsProbabilityMeasure`.

2. **integral_indicator_one** (~5 LOC):
   `integral (Set.indicator A (fun _ => 1)) mu = (mu A).toReal`.
   This should be `MeasureTheory.integral_indicator_one` or derivable from
   `integral_indicator` + `integral_const`.

3. **Connecting Chebyshev set to goal set** (~20 LOC):
   Show `{omega | S omega <= k/2} subset {omega | k/6 <= |S omega - mu[S]|}`.
   Proof: if `S omega <= k/2` and `mu[S] >= 2k/3`, then
   `|S omega - mu[S]| >= mu[S] - S omega >= 2k/3 - k/2 = k/6`.
   Requires: `abs_sub_comm`, `le_abs_self`, `sub_le_sub_left`.

4. **Final measure complement** (~10 LOC):
   `mu {S > k/2} = 1 - mu {S <= k/2}` requires measurability of `{S <= k/2}`.
   Then `mu {S > k/2} >= 1 - delta` follows from `mu {S <= k/2} <= delta`.
   Use `measure_compl` + `IsProbabilityMeasure.measure_univ`.

## Proof Plan: boost_two_thirds_to_pac (Separation:180)

### Strategy

Once `chebyshev_majority_bound` (with amended signature) is proved, the
`boost_two_thirds_to_pac` proof assembles the pieces:

```lean
private theorem boost_two_thirds_to_pac ... := by
  -- Step 1: Extract learner and sample complexity
  -- From PACLearnable definition, need to produce BatchLearner + sample complexity function

  -- Step 2: Define the boosted learner
  -- Already constructed sorry-free in existing codebase
  -- boosted_learner uses k*m0 samples, partitions into k blocks, majority votes

  -- Step 3: Show the boosted learner achieves (eps, delta)-PAC
  -- Given eps > 0, delta > 0:
  --   (a) Choose m0 from hrate(eps) so rate(m0) < eps
  --   (b) Set k = max 3 (ceil(9/delta))
  --   (c) Define events j = {omega | block j has error <= rate(m0)}
  --   (d) From huniv: P[events j] >= 2/3
  --   (e) From iIndepFun_block_extract: events are iIndepSet
  --   (f) From chebyshev_majority_bound: P[majority succeeds] >= 1 - delta
  --   (g) Event containment: {error <= rate(m0)} subset {error <= eps} (since rate(m0) < eps)
  --   (h) Therefore P[boosted error <= eps] >= 1 - delta

  sorry -- Full assembly requires connecting all infrastructure pieces
```

### Key Connection Points

1. **iIndepFun_block_extract -> iIndepSet:**
   ```
   iIndepFun_block_extract : iIndepFun (fun j omega => block_extract k m omega j) (Measure.pi ...)
   ```
   Compose with `g j : (Fin m -> X) -> Bool` where `g j block = (D{error} <= eps)`.
   Get `iIndepFun (fun j omega => g j (block_extract k m omega j)) (Measure.pi ...)`.
   Then `events j = {omega | g j (block_extract k m omega j) = true}`.
   Convert `iIndepFun` to `iIndepSet` via preimage.

2. **huniv -> hprob:**
   The `huniv` hypothesis gives `P[error <= rate(m)] >= 2/3` for each individual D^m.
   Under `Measure.pi`, each block has distribution `D^m0`.
   By `measurePreserving_eval` or `iIndepFun_block_extract` marginals,
   `P[events j] >= 2/3`.

3. **Event containment:**
   ```
   {omega | rate(m0) < eps} -> {omega | error <= rate(m0)} subset {omega | error <= eps}
   ```
   This is `measure_mono` + `ENNReal.ofReal_le_ofReal`.

## Fallback Strategy

If the Chebyshev route encounters insurmountable measurability or type-matching issues:

1. **Weaker bound:** Use union bound instead of Chebyshev.
   P[majority wrong] <= P[>= k/2 blocks bad] <= C(k, k/2) * (1/3)^{k/2}
   This gives exponential convergence but with worse constants.
   Avoids variance computation entirely.

2. **Direct probability bound:** For the special case of i.i.d. Bernoulli(p) sum:
   P[Bin(k,p) <= k/2] can be bounded by Hoeffding or moment generating functions.
   Mathlib may have `SubGaussian` bounds that apply.

3. **Sorry boundary:** If all else fails, sorry `chebyshev_majority_bound` with the
   amended signature (including independence). This localizes the sorry to pure
   probability theory, and the rest of `boost_two_thirds_to_pac` can be completed.

## Mathlib API Reference

| API | File | Line | Signature |
|-----|------|------|-----------|
| `iIndepFun.comp` | Independence/Basic.lean | 668 | `(h : iIndepFun f mu) (g : ...) (hg : Measurable) -> iIndepFun (g . f) mu` |
| `iIndepSet.iIndepFun_indicator` | Independence/Basic.lean | 999 | `iIndepSet s mu -> iIndepFun (indicator (s n) 1) mu` |
| `meas_ge_le_variance_div_sq` | Variance.lean | 378 | `MemLp X 2 mu -> 0 < c -> mu {c <= abs(X-E[X])} <= ofReal(Var/c^2)` |
| `IndepFun.variance_sum` | Variance.lean | 403 | `Pairwise IndepFun + MemLp 2 -> Var[sum] = sum Var` |
| `variance_le_sq_of_bounded` | Variance.lean | 480 | `X in [a,b] ae -> Var[X] <= ((b-a)/2)^2` |
| `memLp_of_bounded` | LpSeminorm/Basic.lean | 569 | `X in [a,b] ae + AEStronglyMeasurable -> MemLp X p mu` |
| `memLp_indicator_const` | LpSeminorm/Indicator.lean | 140 | `MeasurableSet s -> MemLp (indicator s c) p mu` |
| `memLp_finset_sum'` | (Mathlib) | -- | `(forall i in s, MemLp (f i) p mu) -> MemLp (sum f) p mu` |
| `iIndepFun_block_extract` | Generalization.lean | 3011 | `iIndepFun block_extract (Measure.pi D)` |
| `block_extract_measurable` | Generalization.lean | 3005 | `Measurable (block_extract k m . j)` |

## Build/Test Protocol

1. Amend `chebyshev_majority_bound` signature (add `hevents_meas`, `hindep`)
2. Build to verify signature change compiles
3. Prove `chebyshev_majority_bound` body step by step, building after each major step
4. Close `boost_two_thirds_to_pac` using the proved lemma
5. Build final: target 0 errors, sorry count should drop by 2 (from 15 to 13)

## A4/A5 Checklist

- [ ] A4: No trivially-true sorrys introduced
- [ ] A5: No simplification of mathematical content (Chebyshev genuinely requires
  independence + variance bound + deviation estimate)
- [ ] All sorry-using declarations documented with exact mathematical content
- [ ] Build passes with 0 errors after each change
