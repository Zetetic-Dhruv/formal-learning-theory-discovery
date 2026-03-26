# D7 Advice Elimination URS v2 -- COMPLETE CLOSURE of advice_elimination

## Will

Close the `advice_elimination` sorry in `Theorem/Extended.lean:92`. This is the Ben-David & Dichterman (1998) result: PAC learnability with concept-dependent advice from a FINITE set A implies PAC learnability without advice. Attack the hard proof. Build rich structure. No retreat to easy closes.

## Build State

- **0 errors, 10 sorry-using declarations** (current baseline per git HEAD)
- Target sorry: `advice_elimination` at `lean4/FLT_Proofs/Theorem/Extended.lean:92`
- The sorry body is a single `sorry` replacing the entire proof

---

## 1. AMRT-Organized K/U Universe

### 1.1 KK -- Known Knowns

#### KK_1: PACLearnableWithAdvice EXACT definition (Criterion/Extended.lean:68-80)

```lean
def PACLearnableWithAdvice (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (A : Type*) : Prop :=
  exists (LA : LearnerWithAdvice X Bool A) (mf : R -> R -> Nat),
    forall (eps delta : R), 0 < eps -> 0 < delta ->
      forall (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D ->
        forall (c : Concept X Bool), c in C ->
          exists (a : A),
            let m := mf eps delta
            MeasureTheory.Measure.pi (fun _ : Fin m => D)
              { xs : Fin m -> X |
                D { x | LA.learnWithAdvice a (fun i => (xs i, c (xs i))) x != c x }
                  <= ENNReal.ofReal eps }
              >= ENNReal.ofReal (1 - delta)
```

**Quantifier structure (outermost to innermost):**
```
exists LA : LearnerWithAdvice X Bool A       -- FIXED learner (advice-augmented)
exists mf : R -> R -> Nat                     -- FIXED sample complexity (advice-INDEPENDENT)
forall eps delta : R                          -- accuracy/confidence parameters
  forall D : Measure X                        -- distribution
    forall c : Concept X Bool, c in C         -- target concept
      exists a : A                            -- CONCEPT-DEPENDENT advice
        [PAC guarantee for LA with advice a]
```

**Critical observations:**
- `mf` does NOT depend on `a`. The sample complexity is uniform over all advice values.
- `a` is inside `forall c`, so it is concept-dependent: different target concepts may require different advice.
- `LA` is FIXED outside all quantifiers: the same learner-with-advice handles all (eps, delta, D, c).
- The `exists a` is the ONLY thing that makes this strictly weaker than PACLearnable.

#### KK_2: PACLearnable EXACT definition (Criterion/PAC.lean:56-69)

```lean
def PACLearnable (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) : Prop :=
  exists (L : BatchLearner X Bool) (mf : R -> R -> Nat),
    forall (eps delta : R), 0 < eps -> 0 < delta ->
      forall (D : Measure X), IsProbabilityMeasure D ->
        forall (c : Concept X Bool), c in C ->
          let m := mf eps delta
          Measure.pi (fun _ : Fin m => D)
            { xs : Fin m -> X |
              D { x | L.learn (fun i => (xs i, c (xs i))) x != c x }
                <= ENNReal.ofReal eps }
            >= ENNReal.ofReal (1 - delta)
```

**Quantifier structure:**
```
exists L : BatchLearner X Bool               -- FIXED learner (NO advice)
exists mf : R -> R -> Nat                     -- FIXED sample complexity
forall eps delta : R
  forall D : Measure X
    forall c : Concept X Bool, c in C
      [PAC guarantee for L -- NO advice dependency]
```

**Structural diff from PACLearnableWithAdvice:**
- PACLearnable has NO `exists a` inside `forall c`.
- PACLearnable uses `BatchLearner.learn` (type: `{m : Nat} -> (Fin m -> X x Y) -> Concept X Y`).
- PACLearnableWithAdvice uses `LearnerWithAdvice.learnWithAdvice` (type: `A -> {m : Nat} -> (Fin m -> X x Y) -> Concept X Y`).
- To produce a `BatchLearner` from a `LearnerWithAdvice`, we must HARDCODE or SELECT the advice value.

#### KK_3: LearnerWithAdvice structure (Learner/Active.lean:35-39)

```lean
structure LearnerWithAdvice (X : Type u) (Y : Type v) (A : Type*) where
  base : BatchLearner X Y
  learnWithAdvice : A -> {m : Nat} -> (Fin m -> X x Y) -> Concept X Y
```

- `learnWithAdvice` takes advice `a : A` as FIRST argument, then sample, returns hypothesis.
- `base` is the underlying BatchLearner (not used in the PAC-with-advice definition directly).

#### KK_4: BatchLearner structure (Learner/Core.lean:33-39)

```lean
structure BatchLearner (X : Type u) (Y : Type v) where
  hypotheses : HypothesisSpace X Y
  learn : {m : Nat} -> (Fin m -> X x Y) -> Concept X Y
  output_in_H : forall {m : Nat} (S : Fin m -> X x Y), learn S in hypotheses
```

- `output_in_H` proof obligation: the learn function must map into the hypothesis space.
- For constructed learners, setting `hypotheses := Set.univ` and `output_in_H := fun _ => Set.mem_univ _` is standard (used in boost_two_thirds_to_pac at Separation.lean:359).

#### KK_5: advice_elimination EXACT statement (Theorem/Extended.lean:89-92)

```lean
theorem advice_elimination (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (A : Type*) [Fintype A] [Nonempty A] :
    PACLearnableWithAdvice X C A -> PACLearnable X C := by
  sorry
```

- Universe: `X : Type u` (universe-polymorphic, matching PACLearnable).
- Typeclass constraints: `[Fintype A]` (finite advice set) and `[Nonempty A]` (inhabited).
- The proof must: extract LA and mf from the hypothesis, construct a BatchLearner, construct a new sample complexity function, and prove the PAC guarantee.

#### KK_6: Existing infrastructure for union bounds

- `measure_iUnion_fintype_le` is available in Mathlib (used at Generalization.lean:700).
- `chebyshev_union_bound` exists in ESChebyshev.lean:225 but is specific to growth function context.
- `union_bound_consistent` exists in Generalization.lean:641 (dead code, but compiled).

#### KK_7: Existing infrastructure for sample splitting

- `block_extract` at Generalization.lean:3046: `{alpha : Type*} (k m : Nat) (S : Fin (k * m) -> alpha) (j : Fin k) : Fin m -> alpha`
- `block_extract_disjoint` at Generalization.lean:3054: proved.
- `block_extract_measurable` at Generalization.lean:3067: proved.
- `iIndepFun_block_extract` at Generalization.lean:3074: proved. Block extractions under product measure are independent.

#### KK_8: boost_two_thirds_to_pac construction pattern (Separation.lean:340-376)

The boosting proof constructs `L' : BatchLearner` with:
- `hypotheses := Set.univ`
- `learn` that splits sample into blocks, runs L on each, takes majority
- `output_in_H := fun _ => Set.mem_univ _`
- Sample complexity function uses `Nat.ceil`, `max`, arithmetic on eps, delta

This is the EXACT pattern advice_elimination needs.

### 1.2 KU -- Known Unknowns

#### KU_1: Quantifier order correctness of PACLearnableWithAdvice

**Question:** Is the `exists a` in the right place?

**Analysis:** The definition has `forall c in C, exists a : A, [guarantee]`. This means the advice `a` can depend on the target concept `c`. This is CORRECT for the Ben-David & Dichterman model: the advice is a "hint" about which concept is the target, and different targets may need different hints.

**Counterproof check:** If `exists a` were OUTSIDE `forall c` (i.e., `exists a, forall c in C, [guarantee]`), then the advice would be concept-independent, meaning one fixed `a` works for ALL targets. In that case, `LA.learnWithAdvice a` would be a fixed `BatchLearner`, and PACLearnableWithAdvice would trivially imply PACLearnable (just use `LA.learnWithAdvice a`). The theorem would be trivially true -- A4 alarm.

**Verdict:** The quantifier order IS correct. The `exists a` inside `forall c` makes the theorem non-trivial for |A| > 1.

#### KU_2: Can the L' construction reuse D4 block_extract infrastructure?

**Analysis:** The D4 (boost_two_thirds_to_pac) construction splits a sample into k blocks and runs L on each block independently. The D7 (advice_elimination) construction needs to:
1. Split sample into TRAINING + VALIDATION portions
2. Run LA.learnWithAdvice(a, training) for EACH a in Fintype.elems A
3. Select best hypothesis via validation

**Difference from D4:** D4 splits into k IDENTICAL blocks and runs the SAME learner on each. D7 splits into 2 portions (train/validate) and runs DIFFERENT advice values on the SAME training set.

**Shared components:**
- Sample splitting into portions: YES, but D7 needs 2-way split (not k-way).
- `block_extract` can handle 2-way split with k=2.
- `iIndepFun_block_extract` for independence between train and validation: YES, directly applicable.

**Non-shared components:**
- Iterating over Fintype.elems A: new (uses Finset.univ).
- Argmin selection on validation: new.
- Union bound over |A| advice values: uses `measure_iUnion_fintype_le` (Mathlib), not D4 infrastructure.

**Verdict:** Partial reuse. The 2-way sample split and independence are reusable. The advice iteration and validation selection are new.

#### KU_3: Does the validation step require Hoeffding?

**Analysis:** The validation step needs: "the hypothesis with lowest empirical error on the validation set has true error close to the best hypothesis's true error."

This requires UNIFORM CONVERGENCE over |A| candidate hypotheses. Standard approach:
- Hoeffding's inequality for each candidate: Pr[|emp_err - true_err| > eps] <= 2*exp(-2*m*eps^2)
- Union bound over |A| candidates: Pr[exists bad candidate] <= 2*|A|*exp(-2*m*eps^2)
- Set m_val so that 2*|A|*exp(-2*m_val*eps^2) <= delta

**Alternative (simpler):** Since we only need to show the SELECTED hypothesis is good (not uniform convergence over all), we can use a WEAKER argument:
- The correct advice a*(c) produces a hypothesis h* with true error <= eps/2 (from the training PAC guarantee).
- If the selected hypothesis h_sel has empirical error <= empirical error of h*, then by Hoeffding on h_sel AND h*, true_err(h_sel) <= true_err(h*) + eps.
- This still requires Hoeffding for 2 hypotheses (h_sel and h*).

**Infrastructure gap:** `chebyshev_union_bound` in ESChebyshev.lean is specific to the growth function context. A general Hoeffding bound is NOT proved in the codebase. However, `chebyshev_majority_bound` IS proved (Separation.lean:149). The Chebyshev approach could work but is weaker (polynomial rather than exponential tail).

**Verdict:** YES, the validation step requires either Hoeffding or Chebyshev. This is the SAME infrastructure gap as Gamma_67 (D4 boosting). The proof of advice_elimination is BLOCKED by the same concentration inequality gap as boost_two_thirds_to_pac.

#### KU_4: EXACT type of the constructed BatchLearner

The constructed `L' : BatchLearner X Bool` needs:
```lean
learn : {m : Nat} -> (Fin m -> X x Bool) -> Concept X Bool
```

The construction must:
1. Split `S : Fin m -> X x Bool` into `S_train : Fin m_train -> X x Bool` and `S_val : Fin m_val -> X x Bool`.
2. For each `a : A`, compute `h_a := LA.learnWithAdvice a S_train : Concept X Bool`.
3. Compute empirical error of each `h_a` on `S_val`.
4. Select `a* := argmin_a emp_err(h_a, S_val)`.
5. Return `h_{a*} : Concept X Bool`.

**Type-level concern:** `LA.learnWithAdvice` has type `A -> {m : Nat} -> (Fin m -> X x Y) -> Concept X Y`. The implicit `{m}` is resolved from the training sample size. The training sample is obtained by restricting `S` to the first `m_train` indices.

**Construction pattern:** Same as `boost_two_thirds_to_pac` in Separation.lean:342-358. The index arithmetic for extracting sub-samples from `Fin m` is the SAME pattern as the block extraction in D4.

**[Fintype A] usage:** `Finset.univ : Finset A` gives the finite enumeration. Iterate via `Finset.univ.image` or `Finset.sup'` for argmin.

#### KU_5: Is [Fintype A] sufficient or do we need [DecidableEq A]?

**Analysis:** To compute argmin over `Finset.univ : Finset A`, we need:
- `Finset.argmin` or manual `Finset.fold` over A.
- `Finset.argmin` requires `[DecidableLinearOrder]` on the VALUES being compared (empirical errors, which are `ENNReal` -- has DecidableEq and LinearOrder).
- It does NOT require DecidableEq on A itself for the argmin computation.

However, to construct the `Finset` mapping `a -> h_a`, we may use `Finset.image` which requires `[DecidableEq (Concept X Bool)]`. This is problematic since `Concept X Bool = X -> Bool` is not decidably equal in general.

**Workaround:** Instead of building a Finset of hypotheses, iterate directly over `Finset.univ : Finset A` and compute empirical errors lazily. The argmin is over `A` with the comparison function `a -> emp_err(LA.learnWithAdvice a S_train, S_val)`.

**Lean4 API:** `Finset.univ.argmin (fun a => emp_err(h_a, S_val)) : Option A` (returns Option because Finset could be empty, but we have [Nonempty A] which gives `Finset.univ.nonempty`).

Actually, `Finset.argmin` returns `Option A`. With `Finset.univ.nonempty` (from [Nonempty A] and [Fintype A]), we can use `Finset.exists_min_image` or `Finset.min'` patterns.

**Verdict:** `[Fintype A]` is sufficient. `[DecidableEq A]` is NOT needed. But we need `classical` for the noncomputable construction (standard for proof-relevant constructions in this codebase).

### 1.3 UK -- Unknown Knowns

#### UK_1: Pressure from shared infrastructure with D4

Both `advice_elimination` and `boost_two_thirds_to_pac` require concentration inequalities that are sorry'd. The infrastructure gap is the SAME gap (Gamma_67). Closing D7 after D4 would allow reuse of:
- Sample splitting machinery (block_extract with k=2).
- Concentration bounds (whatever form D4 uses: Chebyshev or Hoeffding).
- Product measure marginal arguments (marginal of D^m on first m_train coordinates = D^m_train).

However, D4 and D7 have DIFFERENT concentration needs:
- D4 needs: Pr[majority of k i.i.d. Bernoulli(>=2/3) is wrong] <= delta. This is Chebyshev on binomial.
- D7 needs: Pr[|emp_err - true_err| > eps for some candidate] <= delta. This is Hoeffding + union bound.

The overlap is at the LEVEL of "concentration inequality for i.i.d. samples" but the specific lemma is different.

#### UK_2: The `mf` uniformity is a GIFT

The fact that `mf` in PACLearnableWithAdvice does NOT depend on `a` is crucial. It means the training sample size is the SAME regardless of which advice value is used. This eliminates a major complication: we don't need to take max over different sample sizes for different advice values.

The new sample complexity is:
```
mf'(eps, delta) = mf(eps/2, delta/(2*|A|)) + m_val(eps/2, delta/2)
```

where `m_val` is the validation sample size. The `mf(eps/2, delta/(2*|A|))` ensures each advice-augmented run succeeds with appropriate probability, and `m_val` ensures the validation step has enough samples for uniform convergence over |A| candidates.

### 1.4 UU -- Unknown Unknowns

#### UU_1: Infinite A (countable advice)

For countable A, the finite union bound fails. The Ben-David & Dichterman approach does not extend directly. Countable advice elimination requires structural risk minimization or description-length arguments. This is OUTSIDE the scope of the current theorem (which requires [Fintype A]).

#### UU_2: Whether the `base` field of LearnerWithAdvice is used

The `LearnerWithAdvice` structure has a `base : BatchLearner X Y` field. The `PACLearnableWithAdvice` definition only uses `LA.learnWithAdvice`, never `LA.base`. The `base` field is dead weight for this theorem. This means we cannot extract a BatchLearner from `LA.base` -- it may not satisfy any PAC guarantee. The BatchLearner must be CONSTRUCTED from the `learnWithAdvice` function.

---

## 2. Measurement (Pl/Coh/Inv/Comp)

### 2.1 Pl -- Plausibility of the proof route

**Route assessment:** The proof route is CORRECT for the given definitions. The key steps are:
1. Extract `(LA, mf, hpac_adv)` from `PACLearnableWithAdvice`.
2. Construct `L' : BatchLearner X Bool` that runs all advice values and selects via validation.
3. Construct `mf' : R -> R -> Nat` with appropriate sample complexity.
4. Prove PAC guarantee using union bound + validation generalization.

**Plausibility score:** 0.85. The proof route is mathematically standard. The main risk is Lean4 formalization friction (sample splitting index arithmetic, ENNReal arithmetic for union bound, noncomputable construction).

### 2.2 Coh -- Coherence of quantifier structures

**Source (PACLearnableWithAdvice):**
```
exists LA mf, forall eps delta D c, exists a, [guarantee with m = mf eps delta]
```

**Target (PACLearnable):**
```
exists L mf', forall eps delta D c, [guarantee with m = mf' eps delta]
```

**Composition analysis:**

To produce `forall c, [guarantee]` from `forall c, exists a, [guarantee]`, we must:
- For each c, the hypothesis gives us SOME a(c) that works.
- We cannot USE a(c) in L' because L' doesn't know c.
- Instead, L' tries ALL a in A and picks the best via validation.
- The proof then says: for the true c, a*(c) is among the candidates tried by L'.
- With high probability, the validation selects a candidate at least as good as h_{a*(c)}.

**Quantifier compatibility:** The `exists a` disappears because L' enumerates all of A. The key step is:
```
forall c, exists a, Pr[h_a good] >= 1 - delta'
==>
forall c, Pr[h_{a*(c)} is among L's candidates AND validation selects a good one] >= 1 - delta
```

This is coherent. The `exists a` is eliminated by exhaustive search over [Fintype A].

### 2.3 Inv -- Invariants and alternative approaches

#### Alternative Route A: Direct ERM without validation

Instead of validation, run LA with each advice on the FULL sample and select via ERM (empirical risk minimization on the same sample). This avoids the sample split but requires ERM generalization bounds (uniform convergence for a finite hypothesis class of size |A|).

**Pros:** No sample splitting. Sample complexity = mf(eps, delta/|A|).
**Cons:** ERM generalization requires the SAME Hoeffding + union bound infrastructure. No net savings.

#### Alternative Route B: Reduction to D4 boosting

Treat advice as a "block selector": for each a in A, the advice-augmented learner is a separate BatchLearner `fun S => LA.learnWithAdvice a S`. Then the advice elimination is: given |A| BatchLearners, at least one of which is PAC, find which one is PAC and use it.

This is NOT a reduction to D4 boosting. D4 boosts a SINGLE weak learner. D7 selects among MULTIPLE learners. Different problem structure.

#### Alternative Route C: Occam with counting (no validation)

For finite A, the set of candidate hypotheses produced by L' has at most |A| elements. If the hypothesis class is effectively of size |A|, then by the Occam bound (or finite hypothesis class PAC bound), the ERM over these |A| hypotheses is PAC-learnable with sample complexity O(log(|A|)/eps).

**Pros:** Avoids validation entirely. Uses existing ERM PAC bound infrastructure.
**Cons:** Requires that we can perform ERM over the |A| candidates on a FRESH sample. This is still a sample split (training + ERM sample). Net effect is similar to Route A.

### 2.4 Comp -- What's already proved

| Component | Status | Location |
|-----------|--------|----------|
| `PACLearnableWithAdvice` definition | DONE | Criterion/Extended.lean:68-80 |
| `advice_elimination` statement | DONE | Theorem/Extended.lean:89-92 |
| `block_extract` (sample splitting) | PROVED | Generalization.lean:3046 |
| `iIndepFun_block_extract` (independence) | PROVED | Generalization.lean:3074 |
| `measure_iUnion_fintype_le` (union bound) | MATHLIB | Used at Generalization.lean:700 |
| Hoeffding-type concentration | NOT PROVED | Same gap as Gamma_67 |
| Chebyshev concentration (weaker) | PROVED | `chebyshev_majority_bound` at Separation.lean:149 |
| Validation/model selection | NOT PROVED | New infrastructure needed |
| ENNReal arithmetic lemmas | PARTIAL | Various files |

---

## 3. Proof Decomposition

### Sub-lemma A: Sample splitting (training + validation)

**Purpose:** Split `S : Fin m -> X x Bool` into `S_train : Fin m_train -> X x Bool` and `S_val : Fin m_val -> X x Bool` where `m = m_train + m_val`.

**Type signature:**
```lean
private def split_sample {X Y : Type*} (m_train m_val : Nat)
    (S : Fin (m_train + m_val) -> X x Y) :
    (Fin m_train -> X x Y) x (Fin m_val -> X x Y) :=
  (fun i => S (Fin.castAdd m_val i),
   fun j => S (Fin.natAdd m_train j))
```

**Tactic sketch:** Definitional. No proof needed -- this is a pure function.

**LOC estimate:** 5 lines.

**Blockers:** None. This is simpler than `block_extract` (which handles k-way splits). Can alternatively be expressed as `block_extract 2 m_half S 0` and `block_extract 2 m_half S 1` for even splits.

**Independence result needed:**
```lean
-- Under Measure.pi (fun _ : Fin (m_train + m_val) => D),
-- the restrictions to Fin m_train and Fin m_val are independent
-- and each has marginal D^m_train resp. D^m_val.
```
This follows from `iIndepFun_block_extract` with k=2 (after rewriting `2 * m_half = m_train + m_val`), or can be proved directly from `Measure.pi` properties. The `iIndepFun_block_extract` is proved for `Fin (k * m)` indexing; adapting to `Fin (m_train + m_val)` where `m_train` may differ from `m_val` requires either:
- Padding to make both equal (use `m_half = max(m_train, m_val)`, waste some samples).
- Direct proof of independence for the additive decomposition `Fin (m_train + m_val)`.

**Risk:** Medium. The Fin arithmetic for non-equal splits is more involved than the k-way equal split.

### Sub-lemma B: Running all |A| advice values

**Purpose:** Given training sample `S_train`, produce |A| candidate hypotheses.

**Type signature:**
```lean
private noncomputable def run_all_advice {X : Type u} [MeasurableSpace X]
    (A : Type*) [Fintype A]
    (LA : LearnerWithAdvice X Bool A) {m_train : Nat}
    (S_train : Fin m_train -> X x Bool) : A -> Concept X Bool :=
  fun a => LA.learnWithAdvice a S_train
```

**Tactic sketch:** Definitional. Pure function application.

**LOC estimate:** 3 lines.

**Blockers:** None. This is a direct application of `LA.learnWithAdvice`.

### Sub-lemma C: Validation selection (argmin empirical error)

**Purpose:** Given |A| candidate hypotheses and a validation sample, select the one with lowest empirical error.

**Type signature:**
```lean
private noncomputable def select_best {X : Type u} (A : Type*) [Fintype A] [Nonempty A]
    (candidates : A -> Concept X Bool) {m_val : Nat}
    (S_val : Fin m_val -> X x Bool) : Concept X Bool :=
  let emp_err := fun a =>
    (Finset.univ.filter (fun i : Fin m_val => candidates a (S_val i).1 != (S_val i).2)).card
  candidates (Finset.univ.argmin emp_err).get (by
    simp [Finset.argmin, Finset.univ_nonempty])
```

**Tactic sketch:** Definitional construction. The `Finset.argmin` returns `Option A`; we need to extract the value using `Finset.univ_nonempty` (from [Nonempty A] + [Fintype A]).

**LOC estimate:** 10-15 lines (including the Option extraction).

**Blockers:**
- Need `[DecidableEq Bool]` for the filter (available: `Bool.instDecidableEq`).
- Need `[DecidableEq X]` ? No -- we compare `candidates a x.1` with `x.2 : Bool`, which has DecidableEq.
- Actually, `candidates a (S_val i).1 != (S_val i).2` requires `DecidableEq Bool` which is available.
- The `Finset.argmin` API: `Finset.argmin (f : alpha -> beta) (s : Finset alpha) [LinearOrder beta] : Option alpha`. The comparison is on `Nat` (cardinality), which has LinearOrder. This works.

**Alternative:** Use `Finset.univ.inf'` or manual fold. The `argmin` approach is cleanest.

### Sub-lemma D: Union bound over A

**Purpose:** If for each `a : A`, the failure event has probability <= delta/|A|, then the union of failure events has probability <= delta.

**Type signature (proof-level):**
```lean
private lemma advice_union_bound {Omega : Type*} [MeasurableSpace Omega]
    (mu : MeasureTheory.Measure Omega) [MeasureTheory.IsFiniteMeasure mu]
    {A : Type*} [Fintype A]
    (events : A -> Set Omega) (delta : R) (hdelta : 0 < delta)
    (hbound : forall a : A,
      mu (events a) <= ENNReal.ofReal (delta / Fintype.card A)) :
    mu (Set.iUnion events) <= ENNReal.ofReal delta := by
  calc mu (Set.iUnion events)
      <= sum_{a : A} mu (events a) := measure_iUnion_fintype_le mu events
    _ <= sum_{a : A} ENNReal.ofReal (delta / Fintype.card A) := Finset.sum_le_sum (fun a _ => hbound a)
    _ = Fintype.card A * ENNReal.ofReal (delta / Fintype.card A) := by simp [Finset.sum_const]
    _ = ENNReal.ofReal delta := by [ENNReal arithmetic]
```

**Tactic sketch:** Chain `measure_iUnion_fintype_le` (Mathlib) with sum bound and ENNReal simplification.

**LOC estimate:** 15-25 lines (mostly ENNReal arithmetic: `card * (delta/card) = delta`).

**Blockers:**
- `measure_iUnion_fintype_le` requires measurability of each `events a`. In our context, the events are `{ xs | [PAC condition] }`, whose measurability is the same open question as in D4 (outer measure handles it).
- ENNReal arithmetic: `ENNReal.ofReal (delta / n) * n = ENNReal.ofReal delta` requires careful handling when `delta > 0` and `n > 0`. Lemmas: `ENNReal.ofReal_div_of_pos`, `ENNReal.mul_comm`, `ENNReal.ofReal_mul`.

**Risk:** Medium. The ENNReal arithmetic is fiddly but standard.

### Sub-lemma E: Validation generalization (Hoeffding for selection)

**Purpose:** With high probability over the validation sample, the selected hypothesis has true error at most eps more than the best candidate's true error.

**Formal statement:**
```lean
private lemma validation_selection_bound {X : Type u} [MeasurableSpace X]
    (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D]
    (c : Concept X Bool) (A : Type*) [Fintype A] [Nonempty A]
    (candidates : A -> Concept X Bool)
    (eps delta : R) (heps : 0 < eps) (hdelta : 0 < delta)
    (m_val : Nat)
    (hm_val : m_val >= Nat.ceil (Real.log (2 * Fintype.card A / delta) / (2 * eps ^ 2))) :
    -- With probability >= 1 - delta over S_val ~ D^m_val,
    -- if exists a* with true_err(h_{a*}) <= eps0,
    -- then the argmin-selected hypothesis has true_err <= eps0 + 2*eps.
    sorry_statement_placeholder
```

**This is the HARD sub-lemma.** It requires:
1. Hoeffding's inequality for bounded random variables (NOT proved in the codebase).
2. Union bound over |A| candidates.
3. The result: for ALL candidates simultaneously, |emp_err - true_err| <= eps with probability >= 1 - delta.
4. Therefore the argmin over emp_err selects a hypothesis with true_err <= min_true_err + 2*eps.

**LOC estimate:** 50-80 lines (if Hoeffding were available; without it, this is the primary sorry).

**Blockers:** HOEFFDING'S INEQUALITY IS NOT PROVED. This is the same infrastructure gap as Gamma_67. Without Hoeffding, this sub-lemma must be sorry'd.

**Alternative (Chebyshev-based):** Use `chebyshev_majority_bound` (proved) instead of Hoeffding. This gives a WEAKER bound: sample complexity O(|A|/(delta * eps^2)) instead of O(log(|A|/delta)/eps^2). The Chebyshev route is:
- For each candidate, Chebyshev gives Pr[|emp_err - true_err| > eps] <= Var/(m_val * eps^2) <= 1/(4 * m_val * eps^2).
- Union bound: Pr[exists bad] <= |A|/(4 * m_val * eps^2).
- Set m_val = |A|/(4 * delta * eps^2).

The Chebyshev route avoids Hoeffding but gives worse (polynomial) sample complexity. Both routes require union bound + ENNReal arithmetic.

**Risk:** HIGH. This is the bottleneck sub-lemma.

### Sub-lemma F: Assembly (combine into PACLearnable)

**Purpose:** Assemble the constructed BatchLearner, sample complexity function, and PAC guarantee into the PACLearnable existential.

**Type signature:** This is the overall proof structure, not a separate lemma.

**Proof skeleton:**
```lean
theorem advice_elimination (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (A : Type*) [Fintype A] [Nonempty A] :
    PACLearnableWithAdvice X C A -> PACLearnable X C := by
  intro hadvice
  obtain (LA, mf, hpac_adv) := hadvice
  -- Construct L' : BatchLearner X Bool
  let L' : BatchLearner X Bool := {
    hypotheses := Set.univ
    learn := fun {m'} S x =>
      -- Split S into training (first m_train indices) and validation (last m_val indices)
      -- Run LA.learnWithAdvice a S_train for each a in Fintype.elems A
      -- Select best via validation
      -- Return selected hypothesis applied to x
      sorry  -- construction
    output_in_H := fun _ => Set.mem_univ _
  }
  -- Construct mf' : R -> R -> Nat
  let mf' : R -> R -> Nat := fun eps delta =>
    let m_train := mf (eps / 2) (delta / (2 * Fintype.card A))
    let m_val := Nat.ceil (Real.log (2 * Fintype.card A * 2 / delta) / (2 * (eps / 2) ^ 2))
    m_train + m_val
  refine (L', mf', ?_)
  intro eps delta heps hdelta D hD c hcC
  -- From hpac_adv: exists a, [guarantee for LA with advice a]
  -- The proof combines Sub-lemmas A-E
  sorry  -- PAC guarantee proof
```

**LOC estimate:** 30-50 lines for the skeleton, plus Sub-lemma LOCs.

**Blockers:** Depends on all other sub-lemmas.

---

## 4. Shared Infrastructure with D4

### 4.1 Sample splitting

| Component | D4 (boosting) | D7 (advice elimination) | Shared? |
|-----------|--------------|-------------------------|---------|
| Split type | k-way equal split (k blocks of size n) | 2-way unequal split (m_train + m_val) | PARTIAL |
| API | `block_extract k m S j : Fin m -> alpha` | `split_sample m_train m_val S : pair` | Can adapt block_extract with k=2 |
| Independence | `iIndepFun_block_extract` (k-way) | Need 2-way independence | Reusable with k=2 |
| Marginal | Block marginal = D^n (not explicitly proved) | Train marginal = D^m_train, val marginal = D^m_val | Same proof technique |

### 4.2 Concentration inequalities

| Component | D4 (boosting) | D7 (advice elimination) | Shared? |
|-----------|--------------|-------------------------|---------|
| Type | Chebyshev for majority (binomial concentration) | Hoeffding for empirical error + union bound | DIFFERENT |
| Infrastructure | `chebyshev_majority_bound` (PROVED) | Hoeffding NOT proved; Chebyshev alternative possible | PARTIAL |
| Union bound | Over k blocks (implicit in Chebyshev) | Over |A| candidates (explicit) | SAME Mathlib API |

### 4.3 BatchLearner construction

| Component | D4 (boosting) | D7 (advice elimination) | Shared? |
|-----------|--------------|-------------------------|---------|
| Pattern | `hypotheses := Set.univ`, construct learn | Same pattern | YES |
| output_in_H | `fun _ => Set.mem_univ _` | Same | YES |
| Learn body | Split + run L on each block + majority | Split + run LA with each a + argmin validation | DIFFERENT |

### 4.4 Ordering recommendation

**Can advice_elimination be proved AFTER D4, reusing D4's infrastructure?**

YES, with caveats:
1. If D4 establishes Hoeffding as a lemma (rather than using Chebyshev), D7 can reuse it directly.
2. If D4 only uses Chebyshev, D7 can use Chebyshev for a weaker (polynomial) bound. This is still mathematically valid but gives sub-optimal sample complexity.
3. The sample splitting and independence infrastructure (block_extract, iIndepFun_block_extract) is ALREADY proved and usable by both.
4. The BatchLearner construction pattern is a code pattern, not a lemma -- both use the same `Set.univ` approach.

**Recommendation:** Prove D4 first (it has more developed skeleton and URS history), then D7 can reuse the concentration infrastructure.

---

## 5. Counterfactual Pathways

### Route A: Full validation (sample split + Hoeffding + union bound) -- RECOMMENDED

**Strategy:**
1. Split sample: m = m_train + m_val.
2. For each a in A, compute h_a := LA.learnWithAdvice a S_train.
3. Validate: select a* := argmin_a emp_err(h_a, S_val).
4. By PACLearnableWithAdvice: for the true c, exists a_good(c) such that Pr[true_err(h_{a_good}) <= eps/2] >= 1 - delta/(2|A|).
5. Union bound: Pr[true_err(h_{a_good}) <= eps/2] >= 1 - delta/2 (absorbing the union over all a).

Wait -- this is not quite right. Let me be more precise:

**Corrected strategy:**
1. From `hpac_adv`: for the true `c`, `exists a_good : A` such that with training sample of size `mf(eps/2, delta/2)`, `Pr[true_err(h_{a_good}) <= eps/2] >= 1 - delta/2`.
2. The training sample has size `m_train = mf(eps/2, delta/2)`. Note: mf does NOT depend on a, so the sample size works for ALL a, including a_good.
3. With probability >= 1 - delta/2 over S_train, the hypothesis `h_{a_good}` has true error <= eps/2.
4. On the validation set of size m_val, by Hoeffding + union bound over |A| candidates: with probability >= 1 - delta/2, ALL candidates have |emp_err - true_err| <= eps/2 simultaneously.
5. On both events (probability >= 1 - delta by union bound): the selected h* has emp_err(h*) <= emp_err(h_{a_good}), so true_err(h*) <= emp_err(h*) + eps/2 <= emp_err(h_{a_good}) + eps/2 <= true_err(h_{a_good}) + eps/2 + eps/2 <= eps/2 + eps/2 = eps.
6. The combined event has probability >= (1 - delta/2) * (1 - delta/2) >= 1 - delta... NO, this is wrong. The events are NOT independent (different parts of the sample).

**Actually:** Since S_train and S_val are independent (by iIndepFun_block_extract / sample splitting), the two events ARE independent. But we don't need independence -- a simple union bound suffices:
- Pr[training fails OR validation fails] <= Pr[training fails] + Pr[validation fails] <= delta/2 + delta/2 = delta.
- So Pr[both succeed] >= 1 - delta.

**Sample complexity:**
```
m_train = mf(eps/2, delta/2)
m_val = ceil(log(2 * |A| / (delta/2)) / (2 * (eps/2)^2))
     = ceil(log(4 * |A| / delta) / (eps^2 / 2))
     = ceil(2 * log(4 * |A| / delta) / eps^2)
m_total = m_train + m_val
```

Wait, re-examining step 4: the training guarantee is already per-advice. The `hpac_adv` gives us: for the true c, `exists a_good` such that with sample size `mf(eps/2, delta/2)`:
```
Pr_{S_train ~ D^m_train}[true_err(h_{a_good(c)}) <= eps/2] >= 1 - delta/2
```

This is the guarantee for ONE specific `a_good(c)`. We don't need a union bound over A for the training step! The union bound is only needed if we want ALL advice values to simultaneously work. But we only need ONE (a_good) to work.

So the training step uses `mf(eps/2, delta/2)` -- no |A| factor in the training sample complexity. The |A| factor appears ONLY in the validation step (uniform convergence over |A| candidates).

**Revised sample complexity:**
```
m_train = mf(eps/2, delta/2)
m_val = ceil(2 * log(4 * |A| / delta) / eps^2)     [Hoeffding version]
  OR  = ceil(|A| / (2 * delta * eps^2))              [Chebyshev version]
m_total = m_train + m_val
```

**Difficulty:** HIGH (requires Hoeffding or Chebyshev for validation).

### Route B: Direct ERM over all advice (no validation split)

**Strategy:**
1. Use the FULL sample of size m for training.
2. For each a in A, compute h_a := LA.learnWithAdvice a S.
3. Select h* via ERM: minimize empirical error on the SAME sample S.
4. Argue: since h_{a_good} has low true error with high probability, and h* has at most the same empirical error as h_{a_good}, h* also has low true error.

**Problem:** ERM on the SAME sample used for training introduces dependence between the selection and the error estimate. Overfitting is possible. To control this, we need uniform convergence over the |A| candidate hypotheses.

**But:** The |A| candidates are data-dependent (each h_a depends on S). So we need a data-dependent uniform convergence bound. This is HARDER than the validation approach, which uses an independent validation set.

**Alternative within Route B:** Use "leave-one-out" or "sample compression" arguments. Since |A| is finite, the effective hypothesis class has size |A|. The Occam/finite-class bound gives: for any FIXED set of |A| hypotheses, with probability >= 1 - delta, all |A| have |emp_err - true_err| <= sqrt(log(2|A|/delta) / (2m)). But these hypotheses are NOT fixed -- they depend on the sample. So we need a PAC-Bayes or Rademacher argument.

**Verdict:** Route B is MORE complex than Route A. Not recommended.

### Route C: Reduction to structural risk minimization

**Strategy:** View the advice elimination as a model selection problem. We have |A| "models" (one per advice value). Use SRM to select the best model.

This is essentially Route A with a more sophisticated validation procedure. No net benefit for the finite-A case.

**Verdict:** Over-engineered for finite A. Route A is simplest.

---

## 6. Definition Health Check

### 6.1 The `exists a` is concept-dependent (inside `forall c`)

**Verified.** In `PACLearnableWithAdvice` (Criterion/Extended.lean:73-74):
```lean
        forall (c : Concept X Bool), c in C ->
          exists (a : A),
```

The `exists a` is INSIDE `forall c in C`. Therefore `a` can depend on `c`. This is correct.

### 6.2 The learner LA is fixed (outside `forall eps, delta`)

**Verified.** In `PACLearnableWithAdvice` (Criterion/Extended.lean:69-71):
```lean
  exists (LA : LearnerWithAdvice X Bool A) (mf : R -> R -> Nat),
    forall (eps delta : R), 0 < eps -> 0 < delta ->
```

`LA` is bound by `exists` at the outermost level. It is fixed for all `(eps, delta, D, c)`.

### 6.3 The sample complexity mf does NOT depend on a

**Verified.** In `PACLearnableWithAdvice` (Criterion/Extended.lean:70):
```lean
  exists (LA : LearnerWithAdvice X Bool A) (mf : R -> R -> Nat),
```

`mf : R -> R -> Nat` takes only `eps` and `delta`. It does NOT take `a : A` as an argument. Therefore `mf eps delta` is the same sample size for ALL advice values.

**This is crucial for the proof:** it means L' can use a SINGLE training sample size for ALL advice values. If mf depended on a, we would need `max_{a in A} mf_a eps delta`, which would require knowing |A| at the definition level.

### 6.4 PACLearnableWithAdvice is strictly weaker than PACLearnable for |A| > 1

**Verified.**

**Direction PACLearnable => PACLearnableWithAdvice:**
Given `(L, mf, hpac)` witnessing PACLearnable, construct:
```
LA := { base := L, learnWithAdvice := fun _ S => L.learn S }
```
Then for any c, choose a := arbitrary (from [Nonempty A]). The guarantee follows from `hpac` directly. So PACLearnable implies PACLearnableWithAdvice (with the advice being ignored).

**Direction PACLearnableWithAdvice => PACLearnable (for |A| > 1):**
This is NOT trivial. The advice-augmented learner may NEED different advice for different concepts. Without knowing which concept is the target, L' cannot determine the right advice a priori. This is WHY advice elimination requires the sample-based selection procedure.

**Strictly weaker witness:** Consider A = {0, 1} and a concept class C = C0 union C1 where C0 and C1 are disjoint. Define LA that uses advice 0 to learn C0 and advice 1 to learn C1. Then PACLearnableWithAdvice holds (for each c in C0, use a=0; for each c in C1, use a=1). But PACLearnable may not hold if neither C0 nor C1 is individually PAC-learnable without knowing which sub-class the target belongs to. (Though for |A|=2, the elimination theorem says PACLearnable DOES hold -- the point is the proof is non-trivial.)

---

## 7. Proof Execution Plan

### 7.1 Recommended sorry decomposition

Given the infrastructure gaps, the recommended decomposition is:

**Option 1: Single sorry (current state)**
Keep `advice_elimination` as a single sorry. This is A4-compliant (the statement is non-trivial) and A5-compliant (no simplification from prior state).
- **Pro:** Clean, no risk of A4-failing sub-sorrys.
- **Con:** Large sorry scope; no progress on sub-components.

**Option 2: Decompose into 2 sorrys**
```lean
-- Sub-sorry 1: Construction + assembly (no sorry -- definitional)
-- Sub-sorry 2: The PAC guarantee (sorry -- requires concentration)
```
This is exactly what `boost_two_thirds_to_pac` does: the construction is given explicitly, and only the PAC guarantee proof is sorry'd.

**Option 3: Decompose into 3 sorrys**
```lean
-- Sub-sorry 1: validation_selection_bound (concentration + union bound)
-- Sub-sorry 2: training_guarantee_transfer (marginal of product measure)
-- Sub-sorry 3: Assembly of training + validation guarantees
```

**Recommendation:** Option 2. Build the explicit `BatchLearner` construction and sample complexity function. Sorry only the PAC guarantee proof. This mirrors the D4 pattern and makes the construction checkable by Lean4's type system.

### 7.2 Concrete construction for L'

```lean
theorem advice_elimination (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (A : Type*) [Fintype A] [Nonempty A] :
    PACLearnableWithAdvice X C A -> PACLearnable X C := by
  intro ⟨LA, mf, hpac_adv⟩
  classical
  -- The constructed learner:
  -- 1. Splits sample into training (first m_train) and validation (last m_val)
  -- 2. Runs LA.learnWithAdvice a on training for each a in A
  -- 3. Selects the a with lowest empirical error on validation
  -- 4. Returns the selected hypothesis
  let L' : BatchLearner X Bool := {
    hypotheses := Set.univ
    learn := fun {m'} S x =>
      if h : m' = 0 then LA.learnWithAdvice (Classical.arbitrary A) S x
      else
        let m_train := m' / 2
        let m_val := m' - m_train
        let S_train : Fin m_train -> X x Bool :=
          fun i => S ⟨i.val, by omega⟩
        let S_val : Fin m_val -> X x Bool :=
          fun j => S ⟨m_train + j.val, by omega⟩
        -- Run all advice values on training set
        let candidates : A -> (X -> Bool) :=
          fun a => LA.learnWithAdvice a S_train
        -- Compute empirical errors on validation set
        let emp_err : A -> Nat :=
          fun a => (Finset.univ.filter (fun j : Fin m_val =>
            candidates a (S_val j).1 != (S_val j).2)).card
        -- Select advice with lowest empirical error
        match Finset.univ.argmin emp_err with
        | some a_best => candidates a_best x
        | none => LA.learnWithAdvice (Classical.arbitrary A) S_train x
    output_in_H := fun _ => Set.mem_univ _
  }
  -- Sample complexity function:
  -- m_train = mf(eps/2, delta/2)
  -- m_val = sufficient for validation (Hoeffding/Chebyshev bound)
  -- m_total = 2 * max(m_train, m_val) [to simplify the half-split]
  refine ⟨L', fun eps delta =>
    if 0 < eps ∧ 0 < delta then
      let m_train := mf (eps / 2) (delta / 2)
      -- Chebyshev-based validation size: |A| / (2 * delta * (eps/2)^2)
      -- Simplified: 2 * |A| / (delta * eps^2)
      let m_val := Nat.ceil (2 * Fintype.card A / (delta * eps ^ 2)) + 1
      2 * max m_train m_val  -- factor of 2 for the half-split
    else 0, ?_⟩
  intro eps delta heps hdelta D hD c hcC
  -- The PAC guarantee proof:
  -- 1. From hpac_adv: exists a_good(c) such that on training portion,
  --    Pr[true_err(h_{a_good}) <= eps/2] >= 1 - delta/2.
  -- 2. By uniform convergence on validation (Hoeffding + union bound over |A|):
  --    Pr[|emp_err(h_a) - true_err(h_a)| <= eps/2 for all a] >= 1 - delta/2.
  -- 3. On both events: selected h* has true_err <= eps.
  -- 4. Union bound: Pr[both] >= 1 - delta.
  sorry
```

### 7.3 LOC estimates

| Component | LOC | Status |
|-----------|-----|--------|
| L' construction (learn body) | 25-30 | Writable now |
| mf' construction | 10 | Writable now |
| PAC guarantee proof | 60-100 | BLOCKED by concentration |
| Sub-lemma: union bound | 15-25 | Writable now (uses Mathlib) |
| Sub-lemma: validation bound | 50-80 | BLOCKED by Hoeffding |
| **Total** | **160-245** | Partially writable |

### 7.4 Critical path

```
                  advice_elimination
                        |
            +-----------+-----------+
            |                       |
     Construction (L', mf')    PAC Guarantee
     [writable NOW]                 |
                           +--------+--------+
                           |                 |
                    Training bound     Validation bound
                    [needs marginal]   [needs concentration]
                           |                 |
                    hpac_adv + split    Hoeffding + union bound
                    [writable NOW]     [BLOCKED: Gamma_67]
```

The **critical path blocker** is the concentration inequality (Hoeffding or Chebyshev for validation). This is the SAME blocker as D4 (boost_two_thirds_to_pac).

---

## 8. Risk Assessment

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| Concentration inequality unavailable (Gamma_67) | 0.95 | HIGH | Accept sorry at concentration step; or use Chebyshev (proved but weaker) |
| Fin arithmetic for unequal sample split | 0.4 | MEDIUM | Use `2 * max(m_train, m_val)` for equal halves; waste samples |
| `Finset.argmin` API friction | 0.3 | LOW | Use manual fold; or `Finset.exists_min_image` pattern |
| ENNReal arithmetic in union bound | 0.5 | MEDIUM | Careful lemma-by-lemma; use `norm_num` and `ring` where possible |
| Marginal of product measure on subindex | 0.3 | MEDIUM | Use `iIndepFun_block_extract` with k=2 for equal split |
| `mf` type mismatch (needs eps/2, delta/2 to be positive) | 0.2 | LOW | Add `have` for positivity before calling mf |
| `classical` needed for `Finset.argmin` noncomputability | 0.1 | LOW | Already standard in codebase |

---

## 9. Gamma Discoveries

| ID | Discovery | Type | Source |
|----|-----------|------|--------|
| Gamma_106 | `mf` in PACLearnableWithAdvice is advice-INDEPENDENT (takes only eps, delta). This is a structural GIFT: training sample size is uniform over all advice values, eliminating a max-over-A complication | Structural insight | Definition analysis |
| Gamma_107 | The `base` field of `LearnerWithAdvice` is UNUSED by `PACLearnableWithAdvice` and the entire `advice_elimination` proof. Only `learnWithAdvice` matters. The `base` field is dead weight. | Dead code | Definition analysis |
| Gamma_108 | The training step does NOT need union bound over A. Only ONE advice value (a_good(c)) needs to succeed. The |A| factor appears ONLY in the validation step. This halves the sample complexity compared to naive analysis. | Sample complexity refinement | Proof analysis |
| Gamma_109 | advice_elimination and boost_two_thirds_to_pac share the SAME infrastructure blocker (concentration inequality, Gamma_67) but need DIFFERENT specific lemmas: D4 needs Chebyshev for majority, D7 needs Hoeffding for uniform convergence over |A| candidates. Chebyshev can substitute for Hoeffding at the cost of polynomial (vs logarithmic) dependence on |A|. | Infrastructure alignment | Comparative analysis |
| Gamma_110 | For the L' construction, `Finset.univ.argmin` returns `Option A` (not `A`). Extraction requires proving `Finset.univ.nonempty` from `[Nonempty A]` and `[Fintype A]`. The Mathlib lemma is `Finset.univ_nonempty`. | API detail | Lean4/Mathlib analysis |
| Gamma_111 | PACLearnableWithAdvice is strictly weaker than PACLearnable precisely because the advice `a` is INSIDE `forall c`. If it were outside, PACLearnableWithAdvice would trivially imply PACLearnable (hardcode the advice). The quantifier placement is the ENTIRE content of the definition. | Quantifier analysis | Definition health check |

---

## 10. Session Directive

### Immediate actions (writable now):
1. Build the explicit `BatchLearner` construction for L' and verify it type-checks.
2. Build the sample complexity function mf'.
3. Prove the union bound sub-lemma using `measure_iUnion_fintype_le`.
4. Prove the training guarantee transfer: marginal of D^m on training indices = D^m_train.

### Blocked actions (awaiting Gamma_67 resolution):
5. Prove the validation selection bound (requires Hoeffding or Chebyshev for validation).
6. Close the overall PAC guarantee.

### Priority:
- If D4 infrastructure is being developed in parallel, coordinate: ensure the concentration lemma is stated generally enough for BOTH D4 (majority Chebyshev) and D7 (validation uniform convergence).
- If D4 is not in progress, consider the Chebyshev-based validation route (weaker but provable with existing `chebyshev_majority_bound` infrastructure).

### Exit criteria for this sorry:
The `advice_elimination` sorry is CLOSED when:
1. The `BatchLearner` L' is explicitly constructed (no sorry in the construction).
2. The sample complexity mf' is explicitly defined.
3. The PAC guarantee proof chains: training guarantee (from hpac_adv) + validation guarantee (from concentration) + union bound (from Mathlib).
4. All sub-lemmas compile with 0 errors.
