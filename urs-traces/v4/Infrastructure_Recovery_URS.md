# Infrastructure Recovery URS: Lost Session 4-5 Code

## Status

Sessions 4-5 built infrastructure for D4 boosting (block extraction, majority vote,
block independence, Chebyshev majority bound) in an uncommitted working copy.
A `git checkout` reverted all uncommitted changes. This URS documents the EXACT
code to recover, derived from:

- Session transcript (`f4345c6f-...jsonl`): Edit/Write tool calls
- URS files: D4_Proof_v3_URS, D4_Proof_v4_URS, D0_IndepFun_RESOLVED.md
- SESSION_END_NOTES.md: file-level change summary
- Agent task outputs: D0-Fin-Proof agent (`ab1e2eca03208ef2f.output`)

## Critical Finding

**D4_Proof_v3_URS line 5 claims `chebyshev_majority_bound` was "PROVED
(Separation.lean:158-364, sorry-free)".** This claim is INCORRECT. Searching ALL
Edit/Write tool calls to Separation.lean in the session transcript finds ZERO writes
of `chebyshev_majority_bound`. The D4_Proof_v3/v4 URS documents were written as
*planning documents* that assumed the prior session's working copy was intact; they
describe the STATE OF THE PLANNED CODE, not verified compilation results.

The SESSION_END_NOTES.md (line 91) confirms: "FinBlockInfrastructure section
(lines 2978-3011): `block_extract`, `majority_vote`, `block_extract_disjoint`
(sorry-free), `iIndepFun_block_extract` (sorry)". This section WAS built in
Generalization.lean. The Separation.lean changes (lines 93-96) mention
"boost_two_thirds_to_pac: significantly expanded" but NOT `chebyshev_majority_bound`.

**Conclusion**: `chebyshev_majority_bound` was NEVER written to any .lean file.
It existed only as a proof strategy in URS documents. The infrastructure that
WAS built and lost consists of 4 definitions/lemmas in Generalization.lean.

---

## Piece 1: `block_extract` (Definition)

**File**: `Generalization.lean`
**Insertion point**: After line 3104 (`end NFLCounting`), before `section PACTheoremHelpers`
**Status**: Was sorry-free. Definition only.

### Code

```lean
section FinBlockInfrastructure

open Equiv in
/-- Extract block j from a flat array of k*m elements, using finProdFinEquiv. -/
def block_extract {α : Type*} (k m : ℕ) (S : Fin (k * m) → α) (j : Fin k) : Fin m → α :=
  fun i => S (finProdFinEquiv (j, i))
```

**Notes**: Uses `finProdFinEquiv : Fin k × Fin m ≃ Fin (k * m)` from
`Mathlib/Logic/Equiv/Fin/Basic.lean`. Column-major: `(j, i) -> i + m*j`.

---

## Piece 2: `majority_vote` (Definition)

**File**: `Generalization.lean`
**Insertion point**: Immediately after `block_extract`

### Code

```lean
/-- Boolean majority vote: returns true iff strictly more than half the votes are true. -/
def majority_vote (k : ℕ) (votes : Fin k → Bool) : Bool :=
  decide (2 * (Finset.univ.filter (fun j => votes j = true)).card > k)
```

**Notes**: The `boosted_majority` in Separation.lean:141 uses a slightly different form:
`k < 2 * ((Finset.univ.filter (fun j => votes j)).card)`. These are equivalent
(filter on `votes j` vs `votes j = true` for Bool). The Generalization.lean version
is the canonical one.

---

## Piece 3: `block_extract_disjoint` (Lemma, sorry-free)

**File**: `Generalization.lean`
**Insertion point**: After `majority_vote`

### Code

```lean
/-- Block index sets are disjoint for distinct blocks. -/
lemma block_extract_disjoint (k m : ℕ) (j₁ j₂ : Fin k) (hne : j₁ ≠ j₂) :
    Disjoint
      (Finset.image (fun i : Fin m => finProdFinEquiv (j₁, i)) Finset.univ)
      (Finset.image (fun i : Fin m => finProdFinEquiv (j₂, i)) Finset.univ) := by
  rw [Finset.disjoint_iff_ne]
  intro a ha b hb
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at ha hb
  obtain ⟨i₁, rfl⟩ := ha
  obtain ⟨i₂, rfl⟩ := hb
  intro heq
  exact hne (congr_arg Prod.fst (finProdFinEquiv.injective heq))
```

**Notes**: Proof relies on `finProdFinEquiv.injective`. If `finProdFinEquiv (j1, i1) =
finProdFinEquiv (j2, i2)`, then `(j1, i1) = (j2, i2)`, so `j1 = j2`, contradicting `hne`.
The `congr_arg Prod.fst` extracts the first component equality.

**Alternative proof** (if `congr_arg` does not unify cleanly):
```lean
  exact hne (by
    have := finProdFinEquiv.injective heq
    exact Prod.mk.inj this |>.1)
```

---

## Piece 4: `block_extract_measurable` (Lemma, sorry-free)

**File**: `Generalization.lean`
**Insertion point**: After `block_extract_disjoint`

### Code

```lean
/-- Block extraction is measurable: extracting block j from a pi-type is measurable. -/
lemma block_extract_measurable {X : Type*} [MeasurableSpace X]
    (k m : ℕ) (j : Fin k) :
    Measurable (fun (ω : Fin (k * m) → X) => block_extract k m ω j) := by
  exact measurable_pi_lambda _ (fun i => measurable_pi_apply _)
```

**Notes**: `measurable_pi_lambda` constructs measurability of a function into a pi type
from measurability of each component. Each component `fun ω => ω (finProdFinEquiv (j, i))`
is `measurable_pi_apply` (coordinate projection is measurable).

---

## Piece 5: `iIndepFun_block_extract` (Lemma, sorry in Session 4)

**File**: `Generalization.lean`
**Insertion point**: After `block_extract_measurable`

### Status at Session End

The D0-Fin-Proof agent wrote a partial proof attempt with a sorry. The proof strategy
from D0_IndepFun_RESOLVED.md (Route A) was partially implemented but
`infinitePi_map_curry` type parameters did not match. The sorry remained.

### Statement

```lean
/-- Block extractions are independent under the product measure.
    Key infrastructure for boosting (D4) and probability amplification. -/
lemma iIndepFun_block_extract {X : Type*} [MeasurableSpace X]
    (k m : ℕ) (D : MeasureTheory.Measure X) [MeasureTheory.IsProbabilityMeasure D] :
    ProbabilityTheory.iIndepFun (β := fun _ : Fin k => Fin m → X)
      (fun (j : Fin k) (ω : Fin (k * m) → X) => block_extract k m ω j)
      (MeasureTheory.Measure.pi (fun _ : Fin (k * m) => D)) := by
  sorry
```

### Proof Strategy (from D0_IndepFun_RESOLVED.md, Route A)

**Mathematical content**: `block_extract` = currying via MeasurableEquiv. The product
measure on `Fin (k*m) -> X` pushes forward to the nested product on `Fin k -> (Fin m -> X)`.
Under the nested product, coordinate projections are `iIndepFun` by `iIndepFun_pi`.

**Tactic outline**:

```lean
  -- Step 1: Define the currying equivalence
  let pcl := (MeasurableEquiv.piCongrLeft (fun _ => X) finProdFinEquiv).symm
  let cur := MeasurableEquiv.curry (Fin k) (Fin m) X
  let e := pcl.trans cur
  -- e : (Fin (k*m) -> X) ≃ᵐ (Fin k -> (Fin m -> X))

  -- Step 2: Show block_extract = eval ∘ e
  have he : ∀ j ω, block_extract k m ω j = e ω j := by
    intro j ω; ext i
    simp [block_extract, e, MeasurableEquiv.piCongrLeft, MeasurableEquiv.curry]

  -- Step 3: Rewrite
  simp_rw [he]

  -- Step 4: Show μ.map e = nested pi
  -- Via measurePreserving_piCongrLeft + infinitePi_map_curry (or pi_eq)
  -- Step 4a: μ.map pcl = Measure.pi (fun _ : Fin k × Fin m => D)
  -- Step 4b: (flat pi).map cur = Measure.pi (fun _ : Fin k => Measure.pi (fun _ : Fin m => D))

  -- Step 5: Apply iIndepFun_pi on the target space
  -- iIndepFun (fun j ω' => ω' j) (Measure.pi (fun _ => Measure.pi (fun _ => D)))

  -- Step 6: Transport back through e being measure-preserving
  sorry
```

**Required import**: `import Mathlib.Probability.ProductMeasure` (for `infinitePi_eq_pi`
and `infinitePi_map_curry`). This import is NOT in the current Generalization.lean.
Add to the import list.

**Key Mathlib lemmas**:
- `measurePreserving_piCongrLeft` (`Constructions/Pi.lean:744`)
- `infinitePi_map_curry` (`ProductMeasure.lean:557`)
- `infinitePi_eq_pi` (`ProductMeasure.lean:509`)
- `iIndepFun_pi` (`Probability/Independence/Basic.lean:784`)

**Difficulty**: Medium-hard. The mathematical content is standard but the
`infinitePi_map_curry` type parameter alignment is the technical obstacle
that blocked the D0-Fin-Proof agent.

### Section Closer

```lean
end FinBlockInfrastructure
```

---

## Piece 6: `chebyshev_majority_bound` (NOT previously built)

**File**: `Separation.lean`
**Insertion point**: Before `boost_two_thirds_to_pac` (before line 169)
**Status**: NEVER WRITTEN. Must be built from scratch.

### Statement (from D4_Proof_v3_URS design)

```lean
/-- Chebyshev bound for majority vote: if k independent events each have
    probability >= 2/3, then the probability that > k/2 events hold is >= 1 - 9/(4k).
    This gives >= 1 - delta when k >= 9/delta.
    Proof uses Chebyshev's inequality on the count of successful events. -/
private lemma chebyshev_majority_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (k : ℕ) (hk : 0 < k)
    (events : Fin k → Set Ω)
    (hevents_meas : ∀ j, MeasurableSet (events j))
    (hevents_prob : ∀ j, μ (events j) ≥ ENNReal.ofReal (2/3))
    (hindep : ProbabilityTheory.iIndepSet events μ) :
    μ { ω | k < 2 * (Finset.univ.filter (fun j => ω ∈ events j)).card }
      ≥ ENNReal.ofReal (1 - 9 / (4 * k)) := by
  sorry
```

### Proof Strategy (from D4_Proof_v3_URS analysis)

1. **Define indicator random variables**: `X_j : Ω -> R := Set.indicator (events j) 1`
2. **MemLp 2**: `memLp_indicator_const` gives `MemLp 2 X_j μ`
3. **Variance bound**: `variance_le_sq_of_bounded` with a=0, b=1 gives `Var(X_j) <= 1/4`
4. **Independence of indicators**: `IndepFun.variance_sum` from `hindep`
5. **Total variance**: `Var(S) = sum Var(X_j) <= k/4`
6. **Expected value**: `E[S] = sum E[X_j] >= k * 2/3`
7. **Chebyshev**: `meas_ge_le_variance_div_sq` gives:
   `P[S <= k/2] <= P[|S - E[S]| >= E[S] - k/2] <= Var(S) / (E[S] - k/2)^2`
8. **Arithmetic**: `E[S] - k/2 >= 2k/3 - k/2 = k/6`. So bound <= (k/4) / (k/6)^2 = 9/(k)
9. **Complement**: `P[S > k/2] >= 1 - 9/(4k)`

**Key Mathlib lemmas**:
- `ProbabilityTheory.variance` in `Probability/Variance.lean`
- `ProbabilityTheory.IndepFun.variance_sum` for independent rv variance
- `ProbabilityTheory.meas_ge_le_variance_div_sq` (Chebyshev)
- `MeasureTheory.memLp_indicator_const` for indicator MemLp

**Estimated LOC**: 80-120 (significant measure-theory boilerplate)

**Alternative**: Use `measure_sum_ge_le_of_iIndepFun` (sub-Gaussian Hoeffding) directly,
which may be cleaner but operates on `Measure.real` requiring an ENNReal bridge.

---

## Recovery Plan

### Phase 1: Add Definitions (Generalization.lean, after line 3104)

Insert the `section FinBlockInfrastructure` with:
1. `block_extract` (3 LOC)
2. `majority_vote` (3 LOC)
3. `block_extract_disjoint` (10 LOC)
4. `block_extract_measurable` (4 LOC)
5. `iIndepFun_block_extract` (sorry, 8 LOC)
6. `end FinBlockInfrastructure`

**Total**: ~30 LOC. Expected: 0 errors, +1 sorry-using declaration.

### Phase 2: Add Import (Generalization.lean, line 17)

```lean
import Mathlib.Probability.ProductMeasure
```

Required for `iIndepFun_block_extract` proof (Phase 3).

### Phase 3: Prove `iIndepFun_block_extract` (Generalization.lean)

Replace the sorry with Route A proof. Requires:
- Defining the currying MeasurableEquiv
- Proving the measure identity via `infinitePi_map_curry`
- Applying `iIndepFun_pi` and transporting

**Estimated LOC**: 40-60.

### Phase 4: Build `chebyshev_majority_bound` (Separation.lean)

Insert before `boost_two_thirds_to_pac`. Requires:
- Indicator variable setup
- Variance computation
- Chebyshev application
- ENNReal arithmetic

**Estimated LOC**: 80-120.

### Phase 5: Close `boost_two_thirds_to_pac` (Separation.lean)

Use all infrastructure from Phases 1-4. Requires:
- Learner unfolding (Nat.sqrt arithmetic)
- Event definition
- Independence via `iIndepFun_block_extract`
- Concentration via `chebyshev_majority_bound`
- Event containment (majority vote correctness)

**D4_Proof_v4_URS documents the structural problems in detail**, especially:
- The `Fin (n*(n+1))` vs `Fin ((n+1)*n)` issue (Resolution: redefine `mf` as `(n+1)*n`)
- The event containment bug (majority error != 2*rate(n) when some blocks are bad)
- The correct event containment: pointwise majority + measure monotonicity

**Estimated LOC**: 100-150. Multiple localized sorrys expected (measurability).

---

## Dependency Graph

```
import Mathlib.Probability.ProductMeasure    (Phase 2)
  |
  v
block_extract                                 (Phase 1, sorry-free)
majority_vote                                 (Phase 1, sorry-free)
block_extract_disjoint                        (Phase 1, sorry-free)
block_extract_measurable                      (Phase 1, sorry-free)
  |
  v
iIndepFun_block_extract                       (Phase 3, sorry -> proof)
  |
  v
chebyshev_majority_bound                      (Phase 4, new, sorry -> proof)
  |
  v
boost_two_thirds_to_pac                       (Phase 5, sorry -> proof with localized sorrys)
  |
  v
universal_imp_pac                             (already sorry-free, routes through boost)
```

---

## A4/A5 Checklist

- [ ] A4: No trivially-true sorrys in recovered code
- [ ] A5: `iIndepFun_block_extract` sorry is genuine (requires non-trivial measure theory)
- [ ] A5: `chebyshev_majority_bound` sorry is genuine (requires concentration inequality)
- [ ] Build: 0 errors after Phase 1-2
- [ ] Sorry count: current + 1 (iIndepFun_block_extract) after Phase 1
