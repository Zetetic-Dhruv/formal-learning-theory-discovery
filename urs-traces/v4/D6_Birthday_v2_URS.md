# D6 Birthday Bound v2 URS -- Complete Closure Plan (2026-03-20)

## Status Delta from v1

**CRITICAL CORRECTION:** The v1 URS (D6_Birthday_URS.md) listed 5 sorrys in `rademacher_lower_bound_on_shattered` (lines 435, 560, 569, 575, 589). This was stale. The current code has only **1 sorry** in this function: **line 636**. The auxiliary sorrys (measurability, integral_indicator, integrability) have ALL been closed. Line 435 is in `vcdim_bounds_rademacher_quantitative` (a different function). The function body is now lines 472-636.

**Total sorrys in Rademacher.lean:** 2 (line 435 = vcdim upper bound, line 636 = birthday bound).

---

## Target

**File:** `lean4/FLT_Proofs/Complexity/Rademacher.lean`, line 636.
**Function:** `rademacher_lower_bound_on_shattered` (lines 472-636)
**Goal at sorry:** `(1 : R) / 2 <= (mu A).toReal`

where:
- `mu := MeasureTheory.Measure.pi (fun _ : Fin m => D)` (line 536)
- `D := MeasureTheory.Measure.map Subtype.val D_sub` (line 493)
- `D_sub := @uniformMeasure T top _ hTne_type` = `(1/|T|) * count` on `(T, top)` (line 488)
- `A := { xs : Fin m -> X | Function.Injective xs /\ forall i, xs i in T }` (line 543)
- `mu_sub := Measure.pi (fun _ : Fin m => D_sub)` (line 565-566)
- `phi := fun ys i => Subtype.val (ys i)` (line 569)
- `hmu_eq : mu = mu_sub.map phi` (line 582-584)
- `hphi_emb : MeasurableEmbedding phi` (line 571-580)
- `hA_meas : MeasurableSet A` (line 556-560)
- `|T| >= 4 * m^2 + 1`, `0 < m`

**Proof chain already done (lines 596-623):** `(mu A).toReal <= integral EmpRad d mu` via indicator lower bound on finite type.

**Suffices reduction (line 627):** `suffices h_birthday : (1 : R) / 2 <= (mu A).toReal by linarith`

---

## 1. AMRT-Organized K/U Universe

### KK (Known Knowns -- Verified in Current Code)

**KK_1:** `D_sub = (1/|T|) * count` on `(T, top)`. (Rademacher.lean:488, Generalization.lean:1762)

**KK_2:** `D = D_sub.map Subtype.val`. For `x in T`, `D({x}) = 1/|T|`. For `x not in T`, `D({x}) = 0`. (Rademacher.lean:493)

**KK_3:** `mu = Measure.pi (fun _ : Fin m => D)`. Probability measure via `pi.instIsProbabilityMeasure`. (Rademacher.lean:536-538)

**KK_4:** `hmu_eq : mu = mu_sub.map phi` -- PROVED at line 582-584 via `pi_map_pi`. This is the pi_map_pi bridge, fully available in scope at the sorry.

**KK_5:** `hphi_emb : MeasurableEmbedding phi` -- PROVED at line 571-580. Available in scope.

**KK_6:** `hA_meas : MeasurableSet A` -- PROVED at line 556-560 via `Set.Finite.measurableSet`. Available in scope.

**KK_7:** `mu_sub` is a probability measure (line 567-568). Available in scope.

**KK_8:** `MeasurableSingletonClass (Fin m -> T)` (line 564). All subsets of `Fin m -> T` are measurable. Available in scope.

**KK_9:** `Measure.pi_pi` (Mathlib): `Measure.pi mu (pi univ s) = prod_i mu_i (s_i)` for `SigmaFinite` measures. (Mathlib/MeasureTheory/Constructions/Pi.lean:293)

**KK_10:** `MeasureTheory.measure_biUnion_le` (Mathlib): `mu (Union_{i in I} s i) <= tsum_{i : I} mu (s i)` for countable I. (Mathlib/MeasureTheory/OuterMeasure/Basic.lean:77)

**KK_11:** `prob_compl_eq_one_sub` (Mathlib): For probability measures, `mu(s^c) = 1 - mu(s)` when `MeasurableSet s`. (Mathlib/MeasureTheory/Measure/Typeclasses/Probability.lean:151)

**KK_12:** `Measure.count_apply_finite` (Mathlib): `count(s) = |s.toFinset|` for finite s with MeasurableSingletonClass. (Mathlib/MeasureTheory/Measure/Count.lean:59)

**KK_13:** Mathlib's `Archive/Wiedijk100Theorems/BirthdayProblem.lean` proves the birthday problem for `Fin 23 -> Fin 365` using `Fintype.card_embedding_eq` and `uniformOn`. Different approach (exact computation via descFactorial) but confirms that `Fintype.card (alpha emb beta) = card(beta).descFactorial(card(alpha))` is available.

**KK_14:** `Finset.card_biUnion_le` (Mathlib): `|s.biUnion t| <= sum_{i in s} |t i|`. (Mathlib/Algebra/BigOperators/Group/Finset/Basic.lean:970)

**KK_15:** `empRad_eq_one_of_injective_in_shattered` (Rademacher.lean:440-462) is PROVED. `hEmpRad_inj` (line 510-514) applies it.

**KK_16:** `shatters_subset` (Rademacher.lean:324-338) is PROVED.

### KU (Known Unknowns -- Articulated with Counterproof Attempts)

**CKU_16: Transfer mu(A) to mu_sub on subtype.**
The bridge `hmu_eq` is ALREADY in scope. So:
```
mu(A) = mu_sub.map phi (A)
      = mu_sub (phi^{-1}' A)     -- by MeasurableEmbedding.map_apply or Measure.map_apply
```
But wait: `phi` is not surjective onto A. `phi^{-1}' A` captures the preimage. We need `mu(A) >= something`, not `mu(A) = mu_sub(phi^{-1}' A)`.

Actually for MeasurableEmbedding, `(mu_sub.map phi)(A) = mu_sub(phi^{-1}' A)` by `Measure.map_apply`. But `mu = mu_sub.map phi` does NOT mean `mu(A) = mu_sub(phi^{-1}' A)` in general -- it does because `mu_sub.map phi` is NOT a general pushforward, it IS the pushforward. So `mu(A) = (mu_sub.map phi)(A) = mu_sub(phi^{-1}' A)`.

Actually no. For the Lean `Measure.map`, `(mu.map f)(s) = mu(f^{-1}' s)` when either `f` is measurable and `s` is measurable, or `f` is AEMeasurable. Here `phi` is measurable (part of MeasurableEmbedding) and `A` is measurable (KK_6). So:
```
mu(A) = (mu_sub.map phi)(A) = mu_sub(phi^{-1}' A)
```
This is a direct equality. Then:
```
phi^{-1}' A = {ys : Fin m -> T | phi(ys) in A}
            = {ys | Injective (val o ys) /\ forall i, (ys i).val in T}
            = {ys | Injective ys}    -- since val injective on T, and range automatic
```
So `mu(A) = mu_sub({ys | Injective ys})`.

**Counterproof attempt:** Could `phi^{-1}' A` be strictly LARGER than `{ys | Injective ys}`? No. `phi(ys) in A` iff `Injective (fun i => (ys i).val)` and `forall i, (ys i).val in T`. The second is automatic. For the first: `Injective (val o ys)` implies `Injective ys` (since val is injective implies val o ys injective implies ys injective... wait, that's wrong direction). `Injective (val o ys)` iff `Injective ys` (since val is injective: if ys i = ys j then val(ys i) = val(ys j); conversely if val(ys i) = val(ys j) then ys i = ys j since val is injective on subtypes). So the two conditions are equivalent.

**Resolution:** `mu(A) = mu_sub(B)` where `B = {ys : Fin m -> T | Injective ys}`. This is exact.

**CKU_17: Computing mu_sub(B) on finite type.**
`mu_sub = Measure.pi (fun _ => D_sub)` where `D_sub = (1/|T|) * count` on `(T, top)`.
`B = {ys : Fin m -> T | Injective ys}`.

We need: `mu_sub(B) >= 1/2`.

Approach: `mu_sub(B^c) <= 1/2` then `mu_sub(B) = 1 - mu_sub(B^c) >= 1/2`.

For this we need `MeasurableSet B` -- TRUE since `Fin m -> T` is finite, so all subsets are measurable under the discrete (top) measurable space + MeasurableSingletonClass (KK_8).

Then `prob_compl_eq_one_sub` (KK_11): `mu_sub(B^c) = 1 - mu_sub(B)`. So `mu_sub(B) >= 1/2` iff `mu_sub(B^c) <= 1/2`.

**CKU_18: Union bound on B^c.**
`B^c = {ys : Fin m -> T | not Injective ys} = {ys | exists i j, i != j /\ ys i = ys j}`
`= Union_{i < j} C_{ij}` where `C_{ij} = {ys | ys i = ys j}`.

The pairs `(i,j)` with `i < j` form a finite set of size `m.choose 2`.

By measure_biUnion_le or direct finite sum:
`mu_sub(B^c) <= sum_{i < j} mu_sub(C_{ij})`

Each `mu_sub(C_{ij})`:
`C_{ij} = {ys : Fin m -> T | ys i = ys j}`
`= pi univ (fun k => if k = i then T else if k = j then ... else T)`

Actually, this is NOT a product set in the pi sense because the constraint couples coordinates i and j. We need a different approach.

For the counting approach: since `mu_sub = (1/|T|)^m * count` on the finite type `Fin m -> T`, we have `mu_sub(S) = |S| / |T|^m` for any S. Then:

`|C_{ij}| = |{ys : Fin m -> T | ys i = ys j}|`

Fix the shared value v in T (|T| choices). Fix all other coordinates freely (|T|^{m-2} choices for the m-2 remaining coordinates, plus the shared value determines both i and j). Wait: fix v (|T| choices), set ys i = ys j = v (1 choice for both), and ys k for k not in {i,j} freely (|T|^{m-2} choices). But this undercounts: we should think of it as: ys i = ys j, so there are |T| choices for ys i (= ys j), and |T|^{m-2} choices for the remaining m-2 coordinates. Total: |T|^{m-1}.

Alternatively: the map `ys -> (ys restricted to {i,j}^c, ys i)` is a bijection from C_{ij} to `(({i,j}^c -> T) x T)`, giving `|C_{ij}| = |T|^{m-2} * |T| = |T|^{m-1}`. But wait, `|{i,j}^c|` in `Fin m` has `m-2` elements, so we get `|T|^{m-2} * |T| = |T|^{m-1}`. Correct.

So `mu_sub(C_{ij}) = |T|^{m-1} / |T|^m = 1/|T|`.

And `mu_sub(B^c) <= m.choose 2 * (1/|T|) = m*(m-1)/(2*|T|)`.

**Counterproof attempt on CKU_18:** Does `Measure.pi` of `(c * count)` equal `c^m * count` on a finite product? Let's verify. `Measure.pi` is defined as the unique measure satisfying `pi_pi`: `Measure.pi mu (pi univ s) = prod_i mu_i(s_i)`. For `mu_i = c * count`, `mu_i(s_i) = c * |s_i|`. So `Measure.pi mu (pi univ s) = prod_i (c * |s_i|) = c^m * prod_i |s_i|`. And `c^m * count (pi univ s) = c^m * prod_i |s_i|` (since count on a product of finite types gives the product of cardinalities on cylinder sets). So yes, `Measure.pi (fun _ => c * count) = c^m * Measure.pi (fun _ => count) = c^m * count` on the product.

But we don't need this factorization explicitly. We can compute `mu_sub(C_{ij})` directly:

Method 1 (via pi_pi on complement representation): Not directly applicable since C_{ij} is not a pi set.

Method 2 (via counting): `mu_sub(S) = |S| / |T|^m` for any S, because `mu_sub` is a probability measure on a finite type where each element has equal mass. This follows from `mu_sub` being the product of identical copies of `D_sub = (1/|T|) * count`, which on the finite product gives `(1/|T|)^m * count = (1/|T|^m) * count`.

To prove this in Lean: we need `mu_sub(S) = (Fintype.card S : ENNReal) / (Fintype.card (Fin m -> T) : ENNReal)`.

**CKU_19: Cardinality of C_{ij}.**
`Fintype.card {ys : Fin m -> T | ys i = ys j} = Fintype.card T ^ (m - 1)`

This requires exhibiting an explicit bijection or using a cardinality argument. The cleanest route: the fiber of the evaluation map `(eval i, eval j) : (Fin m -> T) -> T x T` over the diagonal has cardinality `|T|^{m-1}`. Or: the constraint `ys i = ys j` reduces the free coordinates from m to m-1 (one coordinate is determined by another). Formally: the projection `ys -> (ys i, fun k : Fin m \ {j} -> ys k)` bijects C_{ij} with `T x (Fin (m-1) -> T)`. This gives `|C_{ij}| = |T| * |T|^{m-2}`. Wait, that's `|T|^{m-1}` only when we count correctly: the remaining coordinates are indexed by `Fin m \ {j}` which has m-1 elements, and ys i = ys j is guaranteed by the constraint. So the bijection sends ys to `(fun k : ({j}^c : Finset (Fin m)) -> ys k)`. This has type `(Fin m \ {j}) -> T` which has cardinality `|T|^{m-1}`. Correct.

In Lean: `Fintype.card {ys : Fin m -> T | ys i = ys j} = Fintype.card T ^ (m - 1)` via an `Equiv` with `({j}^c : Finset (Fin m)) -> T`, then `Fintype.card_fun` and `Finset.card_compl_singleton`.

**CKU_20: MeasurableSet B -- RESOLVED.** B = {ys : Fin m -> T | Injective ys} is measurable because `Fin m -> T` is finite and all sets are measurable under `MeasurableSingletonClass (Fin m -> T)` (KK_8). Specifically: `Set.Finite.measurableSet (Set.toFinite B)`.

### UK (Unknown Knowns -- Pressures to Verify)

**UK_8: Direct Mathlib lemma for Measure.pi of smul.**
Searched for `Measure.pi_smul`, `Measure.pi_const_smul` -- NOT FOUND in Mathlib. There is no direct lemma. We must derive `mu_sub(S) = |S| / |T|^m` from first principles using `pi_pi` on singletons or the uniform measure characterization.

**Alternative route for UK_8:** Since `mu_sub` is a probability measure on a finite type with `MeasurableSingletonClass`, and all elements have equal mass (by symmetry of the product of identical uniform measures), `mu_sub({ys}) = 1 / |Fin m -> T| = 1 / |T|^m` for each ys. Then `mu_sub(S) = |S| / |T|^m` by finite additivity. The equal-mass property follows from `pi_pi`: `mu_sub(pi univ {fun _ => t}) = prod_i D_sub({t_i})` and D_sub is uniform.

Actually, the simplest route: `mu_sub({ys}) = prod_i D_sub({ys i})` by `Measure.pi_pi` applied to singletons (viewing `{ys}` as `pi univ (fun i => {ys i})`). Each `D_sub({ys i}) = 1/|T|`. So `mu_sub({ys}) = (1/|T|)^m = 1/|T|^m`. Then `mu_sub(S) = sum_{ys in S} mu_sub({ys}) = |S| / |T|^m`. This is the COUNTING route.

**UK_9: ENNReal arithmetic.**
We need: given `|T| >= 4*m^2 + 1` and `0 < m`:
```
m.choose 2 / (|T| : ENNReal) <= 1/2
```
equivalently: `2 * m.choose 2 <= |T|`.
Since `m.choose 2 = m*(m-1)/2`, we need `m*(m-1) <= |T|`.
Since `|T| >= 4*m^2 + 1 > m*(m-1)` for all `m >= 1`, this holds.

Actually we want the tighter bound: `mu_sub(B^c) <= 1/2`, i.e., `m*(m-1)/(2*|T|) <= 1/2`, i.e., `m*(m-1) <= |T|`. This is immediate from `|T| >= 4*m^2 + 1 >= m^2 >= m*(m-1)`.

Even tighter: `m*(m-1)/(2*|T|) <= m^2/(2*(4*m^2+1)) < 1/8`. So `mu_sub(B^c) < 1/8`, giving `mu_sub(B) > 7/8 > 1/2`.

For the Lean proof, the simplest arithmetic: show `2 * m.choose 2 <= |T|` (or `2 * m * (m-1) <= 2 * |T|` after clearing denominators), then deduce `mu_sub(B^c) <= 1/2`.

**UK_10: Route B (direct on subtype) -- RULED OUT.** The existing code committed to the `mu(A)` approach. At line 627, the goal is `1/2 <= (mu A).toReal`. We must prove THIS, not restructure.

### UU (Unknown Unknowns -- Boundary)

**UU_1:** Can the `mu(A) = mu_sub(phi^{-1}' A)` equality be established via `Measure.map_apply` directly, or does it require the `MeasurableEmbedding` machinery? Since `phi` is measurable and `A` is measurable, `Measure.map_apply hphi_emb.measurable hA_meas` suffices. But `hmu_eq` gives `mu = mu_sub.map phi`, so we can rewrite and apply map_apply. This is straightforward.

**UU_2:** The finite sum over collision pairs -- is it `Finset.sum` over `Finset.filter (fun p : Fin m x Fin m => p.1 < p.2) univ` or over a custom Finset? The cleanest encoding: `Finset.sum (Finset.univ.filter (fun p : Fin m x Fin m => p.1 < p.2)) (fun p => mu_sub (C p.1 p.2))`. The cardinality of this Finset is `m.choose 2` by `Finset.card_filter_lt_pairs` or similar.

Alternatively, work with `Finset.Iio` pairs or `Finset.offDiag`.

---

## 2. Measurement (Pl/Coh/Inv/Comp)

### Transfer Layer (mu(A) = mu_sub(B))
**HC: 0.95.** All infrastructure is in scope. `hmu_eq`, `hphi_emb`, `hA_meas` are proved. The transfer is `Measure.map_apply` + preimage identification. The preimage identification (`phi^{-1}' A = B`) is a straightforward `ext` + `simp`. ~8 LOC.

### Counting Layer (mu_sub(B^c) via union bound)
**HC: 0.75.** The collision union bound requires:
1. Expressing B^c as a union of C_{ij} sets (~5 LOC, set extensionality)
2. Applying measure_biUnion_le or a finite sum bound (~5 LOC)
3. Computing mu_sub(C_{ij}) = 1/|T| (~15 LOC, the hardest substep)
The bottleneck is step 3: computing mu_sub on a non-pi set requires reducing to counting.

### Arithmetic Layer (birthday bound)
**HC: 0.90.** Pure Nat/ENNReal arithmetic. `m.choose 2 <= |T|/2` follows from `|T| >= 4*m^2+1`. May need `omega` or `norm_num` after casting. ~8 LOC.

### ENNReal-to-Real Layer
**HC: 0.90.** Convert `mu_sub(B) >= 1/2` in ENNReal to `(mu_sub B).toReal >= 1/2` in Real. Standard API: `ENNReal.toReal_le_toReal` or `ENNReal.one_div_le_iff`. ~5 LOC.

---

## 3. The Single Sorry -- Complete Specification

### Line 636: `(1 : R) / 2 <= (mu A).toReal`

**Context in scope:**
```
mu : Measure (Fin m -> X) := Measure.pi (fun _ => D)
mu_sub : Measure (Fin m -> T) := Measure.pi (fun _ => D_sub)
D_sub := (1/|T|) * count on T
D := D_sub.map Subtype.val
phi : (Fin m -> T) -> (Fin m -> X) := fun ys i => (ys i).val
A := {xs : Fin m -> X | Injective xs /\ forall i, xs i in T}
hmu_eq : mu = mu_sub.map phi
hphi_emb : MeasurableEmbedding phi
hA_meas : MeasurableSet A
hm : 0 < m
hT_large : 4 * m ^ 2 + 1 <= T.card
hT_card_pos : 0 < T.card
msT : MeasurableSpace T := top
inst_MSC_pi_T : MeasurableSingletonClass (Fin m -> T)
inst_prob_mu_sub : IsProbabilityMeasure mu_sub
```

**Goal type:** `(1 : R) / 2 <= (mu A).toReal`

**Exact tactic sequence:**

```lean
-- Step 1: Transfer mu(A) to mu_sub via map_apply.
have hmuA_eq : mu A = mu_sub (phi ^(-1)' A) := by
  rw [hmu_eq, MeasureTheory.Measure.map_apply hphi_emb.measurable hA_meas]

-- Step 2: Identify preimage.
have hpre : phi ^(-1)' A = {ys : Fin m -> T | Function.Injective ys} := by
  ext ys
  simp only [Set.mem_preimage, Set.mem_setOf_eq, A, phi]
  exact ⟨fun ⟨hinj, _⟩ => hinj.of_comp,
         fun hinj => ⟨Subtype.val_injective.comp hinj, fun i => (ys i).property⟩⟩

-- Step 3: Set up B = injective set on subtype.
set B := {ys : Fin m -> T | Function.Injective ys} with B_def
have hB_meas : MeasurableSet B := Set.Finite.measurableSet (Set.toFinite B)

-- Step 4: mu(A) = mu_sub(B).
have hmuA_B : mu A = mu_sub B := by rw [hmuA_eq, hpre]

-- Step 5: Complement bound via union bound on collision pairs.
-- B^c = {ys | not Injective ys} = Union_{i<j} {ys | ys i = ys j}
have hBc_union : B^c = Set.iUnion (fun (p : {p : Fin m x Fin m // p.1 < p.2}) =>
    {ys : Fin m -> T | ys p.val.1 = ys p.val.2}) := by
  ext ys; simp only [Set.mem_compl_iff, Set.mem_setOf_eq, B_def,
    Function.Injective, not_forall, Set.mem_iUnion, Subtype.exists,
    Prod.exists]; exact ...  -- push_neg + exists_lt_pair
  -- This is: not Injective ys <-> exists i j, i < j /\ ys i = ys j

-- Step 6: Union bound.
-- mu_sub(B^c) <= sum over pairs of mu_sub(C_{ij})
-- Each mu_sub(C_{ij}) = 1/|T| (by pi measure of uniform on finite type)
-- Number of pairs: m.choose 2 = m*(m-1)/2
-- Total: m*(m-1)/(2|T|)

-- Step 7: Show mu_sub(B^c) <= 1/2.
-- Since |T| >= 4*m^2+1 >= m*(m-1)+1 > m*(m-1), we have m*(m-1)/(2|T|) < 1/2.

-- Step 8: mu_sub(B) >= 1/2.
-- From prob_compl_eq_one_sub: mu_sub(B) = 1 - mu_sub(B^c) >= 1 - 1/2 = 1/2.

-- Step 9: Transfer to Real.
-- (mu A).toReal = (mu_sub B).toReal >= 1/2.
-- Using ENNReal.toReal_le_toReal or direct computation.
```

**Required Mathlib APIs:**
- `MeasureTheory.Measure.map_apply` (transfer)
- `Subtype.val_injective` (preimage identification)
- `Function.Injective.of_comp` (preimage identification)
- `Set.Finite.measurableSet`, `Set.toFinite` (measurability of B)
- `MeasureTheory.measure_biUnion_le` or `MeasureTheory.measure_iUnion_le` (union bound)
- `MeasureTheory.prob_compl_eq_one_sub` (complement in probability measure)
- `MeasureTheory.Measure.pi_pi` (singleton computation)
- `MeasureTheory.Measure.count_apply_finite` (counting on finite sets)
- `ENNReal.toReal_le_toReal` or `ENNReal.ofReal_le_iff_le_toReal` (ENNReal-to-Real)
- `Nat.choose_two_right` or manual `m*(m-1)/2` computation
- `Fintype.card_fun`, `Fintype.card_fin`, `Fintype.card_coe` (cardinality of function spaces)

**LOC estimate:** ~60-70 total.

---

## 4. Counterfactual Routes

### Route A: Pushforward (work on X, use pi_map_pi bridge) -- FORCED

**Why forced:** The existing proof structure at lines 540-627 defines A on X, proves the integral lower bound via indicator on X, and reduces to `1/2 <= (mu A).toReal` at line 627. All infrastructure (`hmu_eq`, `hphi_emb`, `hA_meas`) is already built for this route.

**Proof chain:**
1. `mu(A) = mu_sub(phi^{-1}' A)` via `map_apply` -- uses `hmu_eq` (in scope)
2. `phi^{-1}' A = B` (injective on subtype) -- basic set theory
3. `mu_sub(B) >= 1/2` via complement + union bound + counting
4. Transfer ENNReal to Real

### Route B: Direct on subtype (bypass pushforward) -- IMPOSSIBLE

Would require restructuring lines 540-627. The suffices goal is `1/2 <= (mu A).toReal` where `mu` is on X, not on T. Cannot change this without rewriting the entire integral bound.

### Route C: Via Fintype.card_embedding_eq (Mathlib birthday)

Could compute `mu_sub(B) = Fintype.card (Fin m emb T) / Fintype.card (Fin m -> T)` using the equivalence `B iso (Fin m emb T)`, then use `Fintype.card_embedding_eq` to get `descFactorial(|T|, m) / |T|^m`. But this gives an EXACT value, not a lower bound, and the arithmetic to show `descFactorial(n, m) / n^m >= 1/2` is harder than the union-bound approach.

**Verdict:** Route A with union bound is optimal.

---

## 5. Exact Proof Specification for Line 636

### Decomposition into `have` blocks

```lean
-- At sorry (line 636). Goal: (1 : R) / 2 <= (mu A).toReal

-- ========== PHASE 1: Transfer to subtype (5 LOC) ==========
have hmuA_eq : μ A = μ_sub (φ ⁻¹' A) := by
  rw [hμ_eq, MeasureTheory.Measure.map_apply hφ_emb.measurable hA_meas]

have hpre : φ ⁻¹' A = {ys : Fin m → ↥T | Function.Injective ys} := by
  ext ys
  simp only [Set.mem_preimage, A, Set.mem_setOf_eq, φ]
  constructor
  · rintro ⟨hinj, -⟩; exact hinj.of_comp
  · intro hinj
    exact ⟨Subtype.val_injective.comp hinj, fun i => (ys i).property⟩

set B := {ys : Fin m → ↥T | Function.Injective ys}
have hB_meas : MeasurableSet B := Set.Finite.measurableSet (Set.toFinite B)
have hmuA_B : μ A = μ_sub B := by rw [hmuA_eq, hpre]

-- ========== PHASE 2: Lower bound mu_sub(B) via complement (40 LOC) ==========

-- Step 2a: mu_sub(B) = 1 - mu_sub(B^c)
have hB_compl : μ_sub B = 1 - μ_sub Bᶜ :=
  (prob_compl_eq_one_sub hB_meas).symm ▸ by
    rw [ENNReal.sub_sub_cancel (measure_le_one _)]
-- Alternative: directly from prob_compl applied to B^c

-- Step 2b: Bound mu_sub(B^c) via counting.
-- mu_sub is uniform on Fin m -> T: each element has mass 1/|T|^m.
-- mu_sub(S) = |S| / |T|^m for any S.
set n := Fintype.card ↥T -- = T.card

-- Each singleton has mass (1/n)^m under mu_sub.
have hmu_sub_singleton : ∀ ys : Fin m → ↥T, μ_sub {ys} = (1 / (n : ENNReal)) ^ m := by
  intro ys
  -- {ys} = pi univ (fun i => {ys i})
  have h_pi_eq : ({ys} : Set (Fin m → ↥T)) = Set.pi Set.univ (fun i => {ys i}) := by
    ext zs; simp [Set.mem_pi, funext_iff]
  rw [h_pi_eq, MeasureTheory.Measure.pi_pi]
  simp only [μ_sub]
  congr 1; ext i
  -- D_sub({ys i}) = 1/n
  show D_sub {ys i} = 1 / (n : ENNReal)
  simp only [D_sub, uniformMeasure, MeasureTheory.Measure.smul_apply, smul_eq_mul]
  rw [@MeasureTheory.Measure.count_apply_finite' ↥T ⊤ _
    (Set.finite_singleton _) MeasurableSpace.measurableSet_top]
  simp [Set.Finite.toFinset, n]

-- mu_sub(S) = |S| / n^m for any S.
have hmu_sub_card : ∀ (S : Set (Fin m → ↥T)),
    μ_sub S = (Fintype.card (↥S) : ENNReal) / ((n : ENNReal) ^ m) := by
  intro S
  -- S is finite on a Fintype. mu_sub(S) = sum_{ys in S} mu_sub({ys}) = |S| * (1/n)^m
  rw [← MeasureTheory.tsum_indicator_apply_singleton _ _ S]
  -- ... or by direct computation from hmu_sub_singleton
  sorry -- ~8 LOC: finite additivity on Fintype

-- Step 2c: Collision pair bound.
-- |B^c| <= m.choose 2 * n^(m-1)
have hBc_card_bound : Fintype.card ↥(Bᶜ) ≤ m.choose 2 * n ^ (m - 1) := by
  -- B^c = {ys | not Injective ys} = Union_{i<j} {ys | ys i = ys j}
  -- |{ys | ys i = ys j}| = n^(m-1) for each pair (i,j) with i != j
  -- Number of pairs with i < j: m.choose 2
  sorry -- ~15 LOC: union bound + cardinality of each collision set

-- Step 2d: mu_sub(B^c) <= m.choose 2 / n
have hBc_measure : μ_sub Bᶜ ≤ (m.choose 2 : ENNReal) / (n : ENNReal) := by
  -- From hmu_sub_card and hBc_card_bound:
  -- mu_sub(B^c) = |B^c| / n^m <= m.choose 2 * n^(m-1) / n^m = m.choose 2 / n
  sorry -- ~5 LOC: ENNReal division arithmetic

-- Step 2e: m.choose 2 / n <= 1/2 (birthday arithmetic).
have harith : (m.choose 2 : ENNReal) / (n : ENNReal) ≤ 1 / 2 := by
  -- n >= 4*m^2+1, m.choose 2 = m*(m-1)/2 <= m^2/2
  -- So m.choose 2 / n <= (m^2/2) / (4*m^2+1) < 1/2 * m^2 / (4*m^2) = 1/8 < 1/2
  -- Simpler: 2 * m.choose 2 <= n.
  -- m.choose 2 = m*(m-1)/2. 2*m*(m-1)/2 = m*(m-1) <= m^2 <= 4*m^2 < 4*m^2+1 <= n.
  sorry -- ~8 LOC: Nat arithmetic via omega after casting

-- ========== PHASE 3: Assembly (10 LOC) ==========

-- mu_sub(B^c) <= 1/2
have hBc_half : μ_sub Bᶜ ≤ 1 / 2 := le_trans hBc_measure harith

-- mu_sub(B) >= 1/2 in ENNReal
have hB_half : 1 / 2 ≤ μ_sub B := by
  rw [hB_compl]; -- mu_sub B = 1 - mu_sub B^c
  -- 1/2 <= 1 - mu_sub(B^c) when mu_sub(B^c) <= 1/2
  linarith [hBc_half] -- or tsub_le_tsub_left in ENNReal
  -- Actually ENNReal subtraction is tricky. Better:
  -- mu_sub(B) + mu_sub(B^c) = 1 (prob measure, measurable sets)
  -- mu_sub(B^c) <= 1/2
  -- so mu_sub(B) = 1 - mu_sub(B^c) >= 1 - 1/2 = 1/2
  sorry -- ~5 LOC: ENNReal arithmetic with tsub

-- mu(A) >= 1/2 in ENNReal
have hmuA_half : 1 / 2 ≤ μ A := by rw [hmuA_B]; exact hB_half

-- Transfer to Real
-- (mu A).toReal >= 1/2
-- Since 1/2 <= mu A and mu A <= 1 < top:
show (1 : R) / 2 ≤ (μ A).toReal
rw [div_le_iff (two_pos)]; ring_nf
-- Or directly:
exact ENNReal.le_toReal_of_le_ofReal (by norm_num) hmuA_half
-- Or via:
-- have := ENNReal.toReal_mono (measure_ne_top mu A) hmuA_half
-- simp at this; linarith
sorry -- ~3 LOC
```

### Sub-sorry analysis within the specification

There are 5 internal sub-proofs that need fleshing out:

| Sub-proof | LOC | Difficulty | Core API |
|-----------|-----|-----------|----------|
| `hmu_sub_card` (finite additivity) | 8 | MEDIUM | `tsum_indicator_singleton` or `Measure.sum_smul_dirac` |
| `hBc_card_bound` (collision cardinality) | 15 | MEDIUM-HARD | `Finset.card_biUnion_le`, bijection for each C_{ij} |
| `hBc_measure` (ENNReal division) | 5 | LOW | ENNReal div_le_div |
| `harith` (birthday Nat arithmetic) | 8 | LOW | `omega` or `norm_num` after `Nat.choose_two_right` |
| ENNReal complement / assembly | 8 | MEDIUM | `ENNReal.sub_le_iff`, `prob_compl_eq_one_sub` |

**TOTAL: ~60-70 LOC for line 636.**

---

## 6. Refined Sub-proof: hmu_sub_card (Uniform Measure on Finite Type)

The deepest sub-proof is showing `mu_sub(S) = |S| / n^m`. Two routes:

### Route 1: Via singleton computation + finite additivity
```
mu_sub(S) = sum_{ys in S} mu_sub({ys})     -- finite additivity (tsum_indicator)
          = sum_{ys in S} (1/n)^m           -- hmu_sub_singleton
          = |S| * (1/n)^m                   -- sum of constant
          = |S| / n^m                       -- algebra
```
Requires: `MeasureTheory.measure_eq_sum_singletons` or similar for finite types.

### Route 2: Direct from uniformOn characterization
Since `mu_sub` on the finite type `Fin m -> T` is `(1/n^m) * count` (product of uniform measures), `mu_sub(S) = (1/n^m) * count(S) = |S| / n^m`. This requires proving `Measure.pi (fun _ => (1/n) * count) = (1/n)^m * count`. No direct Mathlib lemma found.

### Route 3 (RECOMMENDED): Bypass hmu_sub_card entirely
Instead of computing mu_sub abstractly, prove `mu_sub(B^c) <= 1/2` directly:

```
mu_sub(B^c) <= sum_{i<j} mu_sub(C_{ij})              -- measure_biUnion_le
            = sum_{i<j} (1/n)                          -- each C_{ij} by pi_pi argument
            = m.choose 2 / n                           -- counting pairs
            <= 1/2                                     -- birthday arithmetic
```

For `mu_sub(C_{ij}) = 1/n`, the pi_pi approach:
```
C_{ij} = {ys | ys i = ys j}
mu_sub(C_{ij}) = sum_{t in T} mu_sub({ys | ys i = t /\ ys j = t})
               = sum_{t in T} mu_sub(pi univ (fun k => if k = i then {t} elif k = j then {t} else univ))
```
Hmm, each such pi set has measure `(1/n)^2 * 1^{m-2} = 1/n^2` by `pi_pi`. And we sum over n values of t: `n * 1/n^2 = 1/n`. This works!

So the key calculation:
```lean
have hC_meas : ∀ (i j : Fin m), μ_sub {ys | ys i = ys j} = 1 / (n : ENNReal) := by
  intro i j
  -- mu_sub({ys | ys i = ys j}) = sum_{t : T} mu_sub({ys | ys i = t /\ ys j = t /\ forall k, ys k in T})
  -- Each inner set is a pi set with measure (1/n)^2 * 1^{m-2} = 1/n^2
  -- Sum over n values: n / n^2 = 1/n
  sorry -- ~12 LOC
```

This requires decomposing C_{ij} as a disjoint union over the shared value, computing each piece via `pi_pi`, and summing.

---

## 7. Dependency DAG

```
sorry (line 636): 1/2 <= (mu A).toReal
  |
  +-- hmuA_eq: mu(A) = mu_sub(phi^{-1}' A)
  |   Uses: hmu_eq (in scope), map_apply
  |   ~2 LOC
  |
  +-- hpre: phi^{-1}' A = B
  |   Uses: val_injective, Injective.of_comp, subtype property
  |   ~6 LOC
  |
  +-- hmuA_B: mu(A) = mu_sub(B)
  |   Uses: hmuA_eq, hpre
  |   ~1 LOC
  |
  +-- hBc_measure_bound: mu_sub(B^c) <= 1/2
  |   |
  |   +-- Union decomposition: B^c = Union_{i<j} C_{ij}
  |   |   ~8 LOC
  |   |
  |   +-- measure_biUnion_le: mu_sub(B^c) <= sum mu_sub(C_{ij})
  |   |   ~3 LOC
  |   |
  |   +-- hC_each: mu_sub(C_{ij}) = 1/n for each pair
  |   |   Uses: pi_pi on pi sets, D_sub singleton mass
  |   |   ~12 LOC (HARDEST SUB-STEP)
  |   |
  |   +-- harith: m.choose 2 / n <= 1/2
  |       Uses: hT_large, omega
  |       ~8 LOC
  |
  +-- ENNReal-to-Real assembly
      Uses: prob_compl_eq_one_sub, ENNReal.toReal_mono
      ~8 LOC

TOTAL: ~48-60 LOC
```

---

## 8. Risk Assessment (Updated)

| Component | LOC | Risk | Note |
|-----------|-----|------|------|
| Transfer (hmuA_eq + hpre + hmuA_B) | 9 | LOW | All infrastructure in scope |
| Union decomposition of B^c | 8 | LOW-MEDIUM | Set extensionality + not_injective characterization |
| Each mu_sub(C_{ij}) = 1/n | 12 | MEDIUM | Need pi_pi on disjoint union + D_sub singleton mass |
| Birthday arithmetic | 8 | LOW | Nat omega after choose_two expansion |
| ENNReal complement arithmetic | 8 | MEDIUM | ENNReal subtraction is awkward |
| ENNReal-to-Real final step | 5 | LOW | Standard API |
| **TOTAL** | **~50-60** | **LOW-MEDIUM** | |

**Critical path:** `mu_sub(C_{ij}) = 1/n` computation. This is the only step that requires non-trivial measure theory on the product space.

**Highest risk:** ENNReal arithmetic throughout. ENNReal subtraction and division require careful handling of `ne_top` conditions.

---

## 9. Recommended Execution Order

1. **Transfer block** (hmuA_eq, hpre, hmuA_B) -- 9 LOC, establishes mu(A) = mu_sub(B)
2. **hC_each** (collision probability) -- 12 LOC, the hard calculation
3. **Union decomposition + measure bound** -- 11 LOC, combines with hC_each
4. **Birthday arithmetic** -- 8 LOC, pure computation
5. **ENNReal assembly** -- 8 LOC, complement + subtraction
6. **Real transfer** -- 5 LOC, final step

Start with step 1 to get the sorry down to `1/2 <= (mu_sub B).toReal`. Then step 2 is the mathematical core. Steps 3-6 are plumbing.

---

## 10. Mathlib API Index

| API | Module | Exact Signature | Purpose |
|-----|--------|-----------------|---------|
| `Measure.map_apply` | MeasureSpace | `(hf : Measurable f) (hs : MeasurableSet s) : (mu.map f) s = mu (f ^{-1}' s)` | Transfer |
| `Function.Injective.of_comp` | Function.Basic | `(h : Injective (g o f)) : Injective f` | Preimage |
| `Subtype.val_injective` | Init.Prelude | `Injective (Subtype.val)` | Preimage |
| `Set.Finite.measurableSet` | MeasureSpace | `(hf : s.Finite) [MSC] : MeasurableSet s` | Measurability |
| `Measure.pi_pi` | Constructions.Pi | `(s : i -> Set (a i)) : pi mu (pi univ s) = prod_i mu_i (s i)` | Singleton mass |
| `count_apply_finite` | Measure.Count | `[MSC] (s : Set a) (hs : s.Finite) : count s = hs.toFinset.card` | Counting |
| `prob_compl_eq_one_sub` | Typeclasses.Probability | `(hs : MeasurableSet s) : mu s^c = 1 - mu s` | Complement |
| `measure_biUnion_le` | OuterMeasure.Basic | `(hI : I.Countable) (s : i -> Set a) : mu (Union_{i in I} s i) <= tsum mu (s i)` | Union bound |
| `Nat.choose_two_right` | Combinatorics.Choose | `m.choose 2 = m * (m-1) / 2` | Pair counting |
| `ENNReal.toReal_mono` | ENNReal.Basic | `(h : b != top) (hab : a <= b) : a.toReal <= b.toReal` | Real transfer |
| `Fintype.card_fun` | Fintype.Basic | `card (a -> b) = card b ^ card a` | Cardinality |
| `Fintype.card_embedding_eq` | CardEmbedding | `card (a emb b) = card(b).descFactorial(card a)` | Alternative route |
| `Finset.card_biUnion_le` | BigOperators.Group | `card (s.biUnion t) <= sum_{i in s} card (t i)` | Finset union bound |

---

## 11. ENNReal Subtraction Strategy

ENNReal subtraction is the biggest technical hazard. Key facts:
- `a - b` in ENNReal is truncated: if `b > a`, result is 0.
- `prob_compl_eq_one_sub hs` gives `mu(s^c) = 1 - mu(s)` (OK since mu(s) <= 1).
- To go from `mu(B^c) <= 1/2` to `mu(B) >= 1/2`:
  ```
  mu(B) = 1 - mu(B^c)     -- by prob_compl, applied to B not B^c!
  ```
  Wait: `prob_compl_eq_one_sub hB_meas` gives `mu(B^c) = 1 - mu(B)`. We want:
  ```
  mu(B) = 1 - mu(B^c) -- follows from mu(B) + mu(B^c) = 1
  ```
  This is `measure_compl hB_meas (measure_ne_top mu_sub B)`: `mu(B^c) = mu(univ) - mu(B) = 1 - mu(B)`. So `mu(B) = 1 - mu(B^c)`.

  Then: `mu(B) = 1 - mu(B^c) >= 1 - 1/2 = 1/2` uses `ENNReal.sub_le_sub_left`: if `a <= b` then `c - b <= c - a`. So `mu(B^c) <= 1/2` implies `1 - mu(B^c) >= 1 - 1/2`.

  In Lean: `ENNReal.tsub_le_tsub_left (h : a <= b) (c : ENNReal) : c - b <= c - a` ... actually the direction might be wrong. Let me think:
  - `tsub_le_tsub_left : a ≤ b → ∀ (c : α), c - b ≤ c - a` -- YES, this gives `c - b <= c - a` when `a <= b`. So with `a = mu(B^c)`, `b = 1/2`: if `mu(B^c) <= 1/2`, then `1 - 1/2 <= 1 - mu(B^c)`, i.e., `1/2 <= mu(B)`. CORRECT.

  Alternative: use `ENNReal.le_sub_of_add_le` or the `linarith`-like approach via `have : mu(B) + mu(B^c) = 1`.

---

## 12. Alternative Simpler Approach: Direct Counting Without pi_pi

Instead of computing `mu_sub(C_{ij})` via `pi_pi`, we could:

1. Show `mu_sub` is the uniform probability measure on `Fin m -> T` (each element has mass `1/|Fin m -> T|`).
2. Then `mu_sub(S) = |S| / |Fin m -> T|` for all S.
3. Reduce entirely to Fintype.card arithmetic.

Step 1 follows from: `mu_sub` is a probability measure on a finite type, and for any `ys`, `mu_sub({ys}) = prod_i D_sub({ys i}) = prod_i (1/n) = (1/n)^m = 1/n^m = 1/|Fin m -> T|`. So mu_sub is the uniform measure.

This might be cleaner because it reduces EVERYTHING to cardinality bounds, no measure theory needed after the initial characterization. The birthday bound becomes:
```
|B^c| / |Fin m -> T| <= 1/2
iff 2 * |B^c| <= |Fin m -> T| = n^m
```
And `|B^c| <= m.choose 2 * n^{m-1}` by Finset.card_biUnion_le. So we need `2 * m.choose 2 * n^{m-1} <= n^m`, i.e., `2 * m.choose 2 <= n`. Since `n >= 4*m^2+1` and `m.choose 2 <= m^2/2`, we need `m^2 <= 4*m^2+1`. True.

---

## 13. Key Insight for Implementation

The SIMPLEST proof strategy avoids all measure-theoretic subtlety after the transfer:

```lean
-- After establishing mu(A) = mu_sub(B):
-- mu_sub is a probability measure on a FINITE type.
-- Every probability measure on a finite type satisfies:
--   mu(S) = sum_{x in S} mu({x})
-- And mu_sub({ys}) = (1/n)^m for all ys (by pi_pi on singletons).
-- So mu_sub(S) = |S| * (1/n)^m = |S| / n^m.
-- This reduces the ENTIRE problem to:
--   |B| / n^m >= 1/2
--   iff 2 * |B| >= n^m
--   iff n^m - |B| <= n^m / 2
--   iff |B^c| <= n^m / 2
-- And |B^c| = |{ys | not Injective ys}| <= m.choose 2 * n^{m-1}
-- So need: m.choose 2 * n^{m-1} <= n^m / 2
--   iff 2 * m.choose 2 <= n
-- Which follows from n >= 4*m^2+1 > 2*m.choose 2 = m*(m-1).

-- The entire proof after the transfer is PURE FINTYPE CARDINALITY + NAT ARITHMETIC.
-- No ENNReal subtraction, no measure_biUnion_le, no complement reasoning.
-- Just: count and compare.
```

This is the recommended implementation path. It has lower risk than the measure-theoretic approach because it stays in Nat arithmetic as long as possible, only converting to ENNReal/Real at the very end.
