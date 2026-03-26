# D6 Birthday Bound URS -- Closing the Birthday Sorry (2026-03-20)

## Target

**File:** `FLT_Proofs/Complexity/Rademacher.lean`, line 589.
**Function:** `rademacher_lower_bound_on_shattered`
**Goal at sorry:** `(1 : R) / 2 <= (mu A).toReal`

where:
- `mu := MeasureTheory.Measure.pi (fun _ : Fin m => D)`
- `D := MeasureTheory.Measure.map Subtype.val D_sub`
- `D_sub := @uniformMeasure T top _ hTne_type` = `(1/|T|) * count` on `T`
- `A := { xs : Fin m -> X | Function.Injective xs /\ forall i, xs i in T }`
- `|T| >= 4 * m^2 + 1`, `0 < m`

**Enclosing sorry count in function:** 5 total (lines 435, 560, 569, 575, 589). This URS targets line 589 only. Lines 560, 569, 575 are auxiliary sorrys (measurability, integral-of-1, integrability) that are prerequisites for the birthday sorry but have independent proof paths.

---

## Mathematical Content

Birthday bound via union bound on collision pairs:

1. D is supported on T (D = pushforward of uniform on T), so mu-a.s. all coordinates land in T. Therefore `mu({xs | forall i, xs i in T}) = 1`.
2. Define collision set `B_{ij} := {xs | xs i = xs j}` for `i < j`. Then `{not injective} = Union_{i<j} B_{ij}`.
3. Union bound: `mu(not injective) <= Sum_{i<j} mu(B_{ij})`.
4. Each `mu(B_{ij}) = P_D[xs i = xs j]`. Under product of D:
   `P_D[xs i = xs j] = Sum_x D({x})^2 = Sum_{t in T} (1/|T|)^2 = |T| / |T|^2 = 1/|T|`.
5. Number of pairs: `C(m,2) = m*(m-1)/2`.
6. So `mu(not injective) <= m*(m-1) / (2*|T|)`.
7. Since `|T| >= 4*m^2 + 1`:
   `m*(m-1)/(2*|T|) <= m^2 / (2*(4*m^2+1)) < m^2 / (8*m^2) = 1/8`.
8. `mu(A) = mu(injective AND range in T) = 1 - mu(not injective) >= 1 - 1/8 = 7/8 >= 1/2`.

---

## Full Ignorance Map

### KK (Known Knowns -- Verified)

**KK_1:** `D_sub = (1/|T|) * count` on `(T, top)`. Each singleton has mass `1/|T|`. (Rademacher.lean:488, Generalization.lean:1760)

**KK_2:** `D = D_sub.map Subtype.val`. So `D({x}) = D_sub({t : t.val = x})`. For `x in T`, `D({x}) = 1/|T|`. For `x not in T`, `D({x}) = 0`. (Rademacher.lean:493)

**KK_3:** `mu = Measure.pi (fun _ : Fin m => D)`. By `pi.instIsProbabilityMeasure`, mu is a probability measure. (Rademacher.lean:537-538)

**KK_4:** The pi_map_pi bridge `mu = (Measure.pi D_sub).map valProd` is proved in Generalization.lean:3330-3355. This exact pattern can be reused (or invoked) for the birthday proof.

**KK_5:** `empRad_eq_one_of_injective_in_shattered` (Rademacher.lean:440) is PROVED. `hEmpRad_inj` (line 510-514) applies it.

**KK_6:** `shatters_subset` is PROVED. Any subset of a shattered set is shattered.

**KK_7:** `MeasureTheory.measure_union_le` gives `mu(A union B) <= mu(A) + mu(B)`. Used in Generalization.lean:1049, 1328.

**KK_8:** `MeasureTheory.Measure.pi_pi` computes `Measure.pi mu (Set.pi univ S) = prod_i mu_i (S i)`. Used in Generalization.lean:563.

**KK_9:** `MeasurableSingletonClass (Fin m -> X)` is available via `Pi.instMeasurableSingletonClass` (Rademacher.lean:555). Under this instance, ALL subsets of `Fin m -> X` are measurable when X has MeasurableSingletonClass. This trivializes measurability sorrys.

**KK_10:** Under `MeasurableSingletonClass`, `A` is measurable. Actually, `Pi.instMeasurableSingletonClass` gives `MeasurableSingletonClass (Fin m -> X)`, which means every singleton is measurable. For countable types this gives all sets measurable. But `X` may be uncountable. However, `A` is a countable union/intersection of preimages of singletons, so it is measurable in the pi sigma algebra regardless.

### KU (Known Unknowns -- Articulated)

**CKU_16:** How to go from the pi_map_pi bridge to a birthday bound. The existing bridge (Generalization.lean:3330-3355) gives `mu(S) = (Measure.pi D_sub)(valProd^{-1} S)`. For the birthday bound, we need to compute `(Measure.pi D_sub)(valProd^{-1} A^c)`. Since `D_sub` is `(1/|T|) * count` on a finite type, `Measure.pi D_sub = (1/|T|^m) * count` on `Fin m -> T`. So we can reduce to COUNTING.

**CKU_17:** The counting route requires: `|{xs : Fin m -> T | not (Injective (val o xs))}| / |T|^m <= 1/8`. The numerator is `|T|^m - |injective functions from Fin m to T|`. The denominator is `|T|^m`. By inclusion-exclusion on collision pairs: `|not injective| <= Sum_{i<j} |{xs | xs i = xs j}| = C(m,2) * |T|^{m-1}`. So the ratio is `<= C(m,2)/|T| = m(m-1)/(2|T|) < 1/8`.

**CKU_18:** How to convert `(Measure.pi D_sub)(not_injective)` to a counting ratio. Since `D_sub = (1/|T|) * count`, `Measure.pi D_sub = (1/|T|)^m * Measure.count` on the finite type `Fin m -> T`. Then `(Measure.pi D_sub)(S) = |S| / |T|^m` for any set `S` in `Fin m -> T`. The key Mathlib lemma is `MeasureTheory.Measure.pi_pi` applied to singleton/finite sets, or direct computation from the smul definition.

**CKU_19:** Lean formalization of `Sum_{i<j} |{xs | xs i = xs j}| <= C(m,2) * |T|^{m-1}`. Need: `Finset.card (Finset.univ.filter (fun xs => xs i = xs j)) = |T|^{m-1}` for fixed `i != j`. This is because choosing the shared value and the remaining `m-1` coordinates gives `|T|^{m-1}` possibilities. In Lean: `Fintype.card {xs : Fin m -> T | xs i = xs j} = Fintype.card T ^ (m-1)` via a bijection with `(Fin (m-1) -> T) x T` or direct cardinality argument.

**CKU_20:** Auxiliary sorry at line 560 (`MeasurableSet A`). Under `MeasurableSingletonClass (Fin m -> X)` and the fact that `A` involves only finitely many conditions (injective is `forall i j, i != j -> xs i != xs j`; range in T is `forall i, xs i in T`), `A` is a countable intersection of measurable sets. But the cleaner route: since `Fin m -> X` may not be countable, we need `A` to be in the pi sigma-algebra. The injectivity condition is: `A_inj = Inter_{i<j} {xs | xs i != xs j}` where each `{xs | xs i != xs j} = (pi_i x pi_j)^{-1}(diagonal^c)`. The diagonal complement is measurable. The range condition is: `Inter_i (pi_i)^{-1}(T)` where `T` is a finite (hence measurable) set. Both are measurable in the product sigma-algebra.

**CKU_21:** Auxiliary sorry at line 569 (`integral_indicator_eq_measure`). This is `integral x in A, 1 d mu = (mu A).toReal`. Mathlib has `MeasureTheory.setIntegral_const` giving `integral x in s, c d mu = c * (mu s).toReal`. Applying with `c = 1` gives the result.

**CKU_22:** Auxiliary sorry at line 575 (integrability of EmpRad). Since `0 <= EmpRad <= 1` and `mu` is a probability measure, EmpRad is integrable. Mathlib: `MeasureTheory.Integrable.of_bound 1 (ae_of_all mu (fun xs => ...))` or `Integrable.mono` with the constant function 1.

### UK (Unknown Unknowns -- Pressures)

**UK_8:** Is there a direct Mathlib lemma for `Measure.pi` of a `smul` measure? I.e., `Measure.pi (fun _ => c * count) = c^m * Measure.pi (fun _ => count)`? If so, the counting reduction is immediate. If not, we need to unfold through `pi_pi` on each singleton and reassemble. **Search target:** `Measure.pi_smul`, `Measure.pi_const_smul`.

**UK_9:** The ENNReal arithmetic for the birthday bound. We need: `m*(m-1)/(2*|T|) < 1/8` when `|T| >= 4*m^2+1`. This requires careful Nat/ENNReal/Real casting. The cleanest approach is to work entirely in Nat until the final step: `8 * m * (m-1) < 2 * |T|` (which follows from `|T| >= 4*m^2+1` and `m*(m-1) < m^2`).

**UK_10:** Can we bypass the measure-theoretic route entirely and work on the SUBTYPE `Fin m -> T`? Since `D_sub` is uniform on `T`, `Measure.pi D_sub` is uniform on `Fin m -> T`. The set of interest is `{xs : Fin m -> T | Injective xs}` (the range-in-T condition is automatic on the subtype). Then `mu_sub(injective) = |injective| / |T|^m` and we just need the counting bound. This is ROUTE B and avoids all pushforward complications.

---

## Two Proof Routes

### Route A: Pushforward (work on X, use pi_map_pi bridge)

**Strategy:** Use the existing pi_map_pi bridge (Generalization.lean:3330-3355) to transfer from `mu` on `Fin m -> X` to `Measure.pi D_sub` on `Fin m -> T`. Then compute the birthday bound on the finite type.

**Steps:**
1. `mu(A) = (Measure.pi D_sub)(valProd^{-1} A)` via pi_map_pi + map_apply.
2. `valProd^{-1} A = {ys : Fin m -> T | Injective ys}` (range-in-T is automatic for subtype).
3. `(Measure.pi D_sub)(injective) = |injective| / |T|^m` (uniform on finite type).
4. `|injective| >= |T|^m - C(m,2) * |T|^{m-1}` (complement of union bound on collisions).
5. Divide: `mu(A) >= 1 - C(m,2)/|T| >= 1 - 1/8 = 7/8`.
6. `7/8 >= 1/2`.

**LOC estimate:** ~60 (reusing pi_map_pi from Generalization.lean).
**Risk:** MEDIUM. The pi_map_pi bridge exists but needs adaptation (different `good_X` set).

### Route B: Direct on subtype (bypass pushforward entirely)

**Strategy:** Instead of computing `mu(A)` on `Fin m -> X`, transfer the INTEGRAL to `Fin m -> T` first, then bound it. Since `D = D_sub.map val`, by `integral_map` we have:
```
integral EmpRad d(Measure.pi D) = integral (EmpRad o valProd) d(Measure.pi D_sub)
```
On `Fin m -> T`, `EmpRad o valProd` takes value 1 on injective tuples (by `hEmpRad_inj`). So:
```
integral >= mu_sub(injective) * 1 = |injective| / |T|^m >= 7/8 >= 1/2.
```

This avoids computing `mu(A)` at all. We directly bound the integral by transferring to the subtype.

**Steps:**
1. Transfer: `integral EmpRad d mu = integral (EmpRad o valProd) d (Measure.pi D_sub)`.
   Uses: `MeasureTheory.integral_map` + pi_map_pi.
2. Lower bound: `integral (EmpRad o valProd) d mu_sub >= mu_sub({ys | Injective ys}).toReal`.
   Uses: `EmpRad o valProd >= indicator_{injective} 1` + `integral_mono_of_nonneg`.
3. Counting: `mu_sub({ys | Injective ys}) >= 1 - C(m,2)/|T|`.
   Uses: uniform measure on finite type + union bound on collision pairs.
4. Arithmetic: `1 - C(m,2)/|T| >= 7/8 >= 1/2`.

**LOC estimate:** ~50 (more direct, fewer intermediate lemmas).
**Risk:** LOW-MEDIUM. Cleaner because it avoids `mu(A)` and works on a finite type throughout.

**WAIT -- Route B conflicts with the existing proof structure.** The existing code at lines 540-580 already committed to the `mu(A)` approach:
- `A` is defined (line 543)
- `h_pointwise` bounds EmpRad by indicator_A (lines 545-552)
- `h_int_bound` derives `mu(A).toReal <= integral EmpRad` (line 563)
- `suffices h_birthday` reduces to `1/2 <= mu(A).toReal` (line 580)

So the sorry at line 589 must prove `1/2 <= (mu A).toReal` within the EXISTING proof structure. Route B would require restructuring the entire proof. **Route A is mandatory given the existing code.**

### Route A (Detailed Tactic Sequence)

```
-- Goal: 1/2 <= (mu A).toReal
-- where mu = Measure.pi (fun _ : Fin m => D), A = {xs | Injective xs /\ forall i, xs i in T}

-- STEP 1: Transfer mu(A) to the subtype via pi_map_pi.
-- Reuse the same pi_map_pi infrastructure as Generalization.lean:3330-3355.
-- mu(A) = (Measure.pi D_sub)(valProd^{-1} A)
-- where valProd : (Fin m -> T) -> (Fin m -> X) := fun ys i => (ys i).val

-- STEP 2: Identify valProd^{-1}(A).
-- valProd^{-1} A = {ys : Fin m -> T | Injective (val o ys) /\ forall i, (ys i).val in T}
-- The range condition is automatic: (ys i).val in T for all ys : Fin m -> T.
-- Injective (val o ys) iff Injective ys (since val is injective on T).
-- So valProd^{-1} A = {ys : Fin m -> T | Injective ys} =: A_T.

-- STEP 3: Compute mu_sub(A_T) on the finite type.
-- mu_sub = Measure.pi D_sub where D_sub = (1/|T|) * count on T.
-- mu_sub = (1/|T|)^m * count on (Fin m -> T).   [by pi of smul]
-- mu_sub(A_T) = |A_T| / |T|^m.

-- STEP 4: Bound |A_T| from below.
-- |A_T| = |{ys : Fin m -> T | Injective ys}|
-- |(Fin m -> T) \ A_T| = |{ys | not Injective ys}|
--   = |Union_{i<j} {ys | ys i = ys j}|
--   <= Sum_{i<j} |{ys | ys i = ys j}|
--   = C(m,2) * |T|^{m-1}
-- So |A_T| >= |T|^m - C(m,2) * |T|^{m-1}.
-- mu_sub(A_T) >= 1 - C(m,2)/|T| = 1 - m(m-1)/(2|T|).

-- STEP 5: Arithmetic.
-- |T| >= 4*m^2+1
-- m*(m-1) < m^2 (for m >= 1)
-- m*(m-1)/(2*(4*m^2+1)) < m^2/(2*(4*m^2)) = 1/8
-- So mu_sub(A_T) > 1 - 1/8 = 7/8 >= 1/2.
-- Hence mu(A).toReal >= 1/2.
```

---

## Dependency DAG for This Sorry

```
sorry (line 589): 1/2 <= (mu A).toReal
  |
  +-- [NEW] pi_map_pi_transfer: mu(A) = mu_sub(valProd^{-1} A)
  |     Uses: pi_map_pi (Generalization.lean:3344), map_apply
  |     ~10 LOC
  |
  +-- [NEW] preimage_identification: valProd^{-1} A = {ys | Injective ys}
  |     Uses: Subtype.val_injective, subtype membership
  |     ~8 LOC
  |
  +-- [NEW] uniform_pi_counting: mu_sub(S) = |S cap (Fin m -> T)| / |T|^m
  |     Uses: uniformMeasure definition, Measure.pi_pi or direct smul computation
  |     ~15 LOC (this is CKU_18)
  |
  +-- [NEW] collision_union_bound: |{ys : Fin m -> T | not Injective ys}| <= C(m,2) * |T|^{m-1}
  |     Uses: Finset.card_biUnion_le, cardinality of {ys | ys i = ys j}
  |     ~15 LOC (this is CKU_19)
  |
  +-- [NEW] birthday_arithmetic: m*(m-1)/(2*(4*m^2+1)) < 1/8
  |     Uses: Nat arithmetic, omega or norm_num
  |     ~5 LOC (this is UK_9)
  |
  +-- [NEW] ennreal_to_real_bound: (mu A).toReal >= 7/8 >= 1/2
  |     Uses: ENNReal.toReal_le_toReal, ge_iff_le
  |     ~7 LOC
```

**Total new LOC for line 589:** ~60.

---

## Auxiliary Sorrys (Lines 560, 569, 575)

These must also be closed to make the birthday proof fully functional. They are INDEPENDENT of the birthday bound itself.

### Line 560: `MeasurableSet A`

```lean
-- A = {xs | Injective xs /\ forall i, xs i in T}
-- Under MeasurableSingletonClass (Fin m -> X) (line 555):
-- Every singleton {f} is measurable. For a finite/countable type, all sets are measurable.
-- BUT Fin m -> X is not necessarily countable.
--
-- CORRECT APPROACH: A is in the product sigma-algebra.
-- {xs | xs i in T} = pi_i^{-1}(T) is measurable (T is finite hence measurable).
-- {xs | xs i != xs j} = (pi_i, pi_j)^{-1}(diagonal^c) is measurable.
-- A = (Inter_i {xs | xs i in T}) inter (Inter_{i<j} {xs | xs i != xs j}).
-- Finite intersection of measurable sets is measurable.
--
-- In Lean:
-- MeasurableSet.inter (MeasurableSet.iInter (fun i => ...)) (MeasurableSet.iInter (fun i => ...))
-- Each factor: measurable_pi_apply i measurable_set_T
--   or measurable_pi_apply i |>.prod_mk (measurable_pi_apply j) |>.preimage diagonal_compl_meas
--
-- SIMPLER: Under MeasurableSingletonClass (Fin m -> X), every Finset.toSet is measurable
-- (it's a finite union of singletons). But A is not necessarily a Finset.
--
-- SIMPLEST: The sigma-algebra on Fin m -> X generated by MeasurableSingletonClass X
-- makes all "cylinder" sets measurable. A is a finite boolean combination of cylinders.
-- ~8 LOC.
```

### Line 569: `integral x in A, 1 d mu = (mu A).toReal`

```lean
-- Mathlib: MeasureTheory.setIntegral_const
-- setIntegral_const : integral x in s, c d mu = c * (mu s).toReal (when mu s < top)
-- Apply with c = 1: integral x in A, 1 d mu = 1 * (mu A).toReal = (mu A).toReal
-- Needs: mu A < top (true since mu is a probability measure, so mu A <= 1 < top).
-- ~3 LOC: rw [MeasureTheory.setIntegral_const]; ring
```

### Line 575: `Integrable EmpRad mu`

```lean
-- EmpRad is bounded: 0 <= EmpRad <= 1 (from hEmpRad_nn and hEmpRad_le).
-- mu is a probability measure (hence finite).
-- Mathlib: MeasureTheory.Integrable.of_bound or memLp_top_of_bound
-- Integrable.of_bound (c := 1) (hf := ae_of_all mu (fun xs => by simp [abs_le]; ...))
-- Or: Integrable.mono (integrable_const 1) (ae_of_all mu ...) (ae_of_all mu ...)
-- ~5 LOC.
```

---

## Risk Assessment

| Component | LOC | Risk | Blocker |
|-----------|-----|------|---------|
| pi_map_pi_transfer | 10 | LOW | Existing pattern in Generalization.lean |
| preimage_identification | 8 | LOW | Basic set theory |
| uniform_pi_counting | 15 | MEDIUM | CKU_18: need to unfold Measure.pi of smul-count |
| collision_union_bound | 15 | MEDIUM | CKU_19: cardinality of collision set |
| birthday_arithmetic | 5 | LOW | Pure Nat/Real arithmetic |
| ennreal_to_real_bound | 7 | LOW | ENNReal API |
| MeasurableSet A (line 560) | 8 | LOW | Product sigma-algebra |
| integral_const (line 569) | 3 | LOW | setIntegral_const |
| integrability (line 575) | 5 | LOW | bounded function on prob measure |
| **TOTAL** | **76** | **LOW-MEDIUM** | |

**Highest-risk component:** `uniform_pi_counting` (CKU_18). The question is whether `Measure.pi (fun _ => c * count) = c^m * Measure.pi (fun _ => count)` has a direct Mathlib lemma, or whether we need to unfold through `pi_pi` on finite sets.

---

## Recommended Proof Order

1. **Line 560** (MeasurableSet A) -- unblocks lines 567, 569
2. **Line 569** (integral of 1 = measure) -- unblocks h_int_ind
3. **Line 575** (integrability) -- unblocks h_int_bound
4. **Line 589** (birthday bound) -- the core content

Steps 1-3 are infrastructure (~16 LOC). Step 4 is the mathematical content (~60 LOC).

---

## Detailed Tactic Sketch for Line 589

```lean
-- At this point we have:
-- mu : Measure (Fin m -> X) := Measure.pi (fun _ => D)
-- A : Set (Fin m -> X) := {xs | Injective xs /\ forall i, xs i in T}
-- Goal: 1/2 <= (mu A).toReal

-- === STEP 1: Transfer to subtype ===
-- Reuse valProd from the scope (or define it locally).
let valProd : (Fin m -> T) -> (Fin m -> X) := fun ys i => (ys i).val
-- mu_sub := Measure.pi (fun _ : Fin m => D_sub)
set mu_sub := @MeasureTheory.Measure.pi (Fin m) (fun _ => T) _
  (fun _ => (top : MeasurableSpace T)) (fun _ => D_sub) with mu_sub_def
-- pi_map_pi gives: mu = mu_sub.map valProd
have hpi_map : mu = mu_sub.map valProd := by
  -- [reuse Generalization.lean:3330-3349 pattern]
  sorry -- placeholder for ~10 LOC
-- Therefore mu(A) = mu_sub(valProd^{-1} A)
have htransfer : mu A = mu_sub (valProd ^{-1}' A) := by
  rw [hpi_map]; exact MeasurableEmbedding.map_apply ... A

-- === STEP 2: Simplify preimage ===
have hpre : valProd ^{-1}' A = {ys : Fin m -> T | Function.Injective ys} := by
  ext ys
  simp only [Set.mem_preimage, A, Set.mem_setOf_eq, valProd]
  constructor
  . rintro ⟨h_inj, h_range⟩
    exact fun i j hij => Subtype.val_injective (h_inj hij) |> Subtype.ext_iff.mp |>.mp
    -- Actually: Injective (val o ys) -> Injective ys since val is injective
    exact h_inj.of_comp
  . intro h_inj
    exact ⟨Subtype.val_injective.comp h_inj, fun i => (ys i).property⟩

-- === STEP 3: Count on finite type ===
-- mu_sub is uniform on Fin m -> T (finite type).
-- mu_sub(S) = |S| / |T|^m.
-- |Fin m -> T| = |T|^m.
set n := Fintype.card T  -- = T.card
set inj_set := {ys : Fin m -> T | Function.Injective ys}

-- mu_sub(inj_set) = |inj_set| / n^m
-- Complement: |not_inj| = n^m - |inj_set|
-- |not_inj| <= Sum_{i<j} |{ys | ys i = ys j}| = C(m,2) * n^{m-1}
-- So |inj_set| >= n^m - C(m,2) * n^{m-1}
-- mu_sub(inj_set) >= 1 - C(m,2)/n = 1 - m(m-1)/(2n)

-- Key lemma: mu_sub(S) for finite type
have hmu_sub_eq : mu_sub inj_set =
    (Finset.univ.filter (fun ys : Fin m -> T => Function.Injective ys)).card /
      (n ^ m : ENNReal) := by
  -- Unfold mu_sub = Measure.pi D_sub where D_sub = (1/n) * count
  -- Measure.pi of (1/n * count) = (1/n)^m * Measure.pi count = (1/n^m) * count
  -- on (Fin m -> T, top) where all sets are measurable.
  -- count(S) for a Finset S on a Fintype = S.card.
  sorry -- ~15 LOC

-- Collision bound
have hcollision : (Finset.univ.filter (fun ys : Fin m -> T =>
    not (Function.Injective ys))).card <=
    m.choose 2 * n ^ (m - 1) := by
  -- Union bound over pairs (i, j) with i < j.
  -- For each pair, |{ys | ys i = ys j}| = n^{m-1}:
  --   Choose ys i = ys j (n choices for the shared value)
  --   and ys k for k != i, k != j (n^{m-2} choices).
  --   Wait: that gives n * n^{m-2} = n^{m-1}. Correct.
  -- Total: C(m,2) * n^{m-1}.
  sorry -- ~15 LOC

-- Arithmetic
have harith : 1 - m.choose 2 / (n : ENNReal) >= 1/2 := by
  -- n >= 4*m^2+1
  -- m.choose 2 = m*(m-1)/2
  -- m*(m-1)/2 / (4*m^2+1) < m^2 / (8*m^2+2) < 1/8
  -- 1 - 1/8 = 7/8 > 1/2
  sorry -- ~5 LOC (omega or norm_num after Nat casting)

-- Assembly
calc (1 : R) / 2
    <= (mu_sub inj_set).toReal := by ...
  _ = (mu A).toReal := by rw [htransfer, hpre]
```

---

## Mathlib API Targets (to grep/verify before coding)

| API | Purpose | Search term |
|-----|---------|-------------|
| `Measure.pi_map_pi` | Transfer from D_sub to D | `pi_map_pi` |
| `MeasurableEmbedding.map_apply` | mu(A) = mu_sub(pre A) | `map_apply` |
| `Measure.pi_pi` | Product of singleton measures | `pi_pi` |
| `Measure.count_apply_finite'` | count(S) = |S| for finite S | `count_apply_finite` |
| `setIntegral_const` | integral 1 = measure | `setIntegral_const` |
| `Integrable.of_bound` | Bounded functions integrable | `Integrable.of_bound` |
| `Finset.card_biUnion_le` | Union bound on cardinality | `card_biUnion_le` |
| `ENNReal.toReal_le_toReal` | Transfer ENNReal inequality to Real | `toReal_le_toReal` |
| `ENNReal.one_sub_le_one` | 1 - x <= 1 for ENNReal | `one_sub` |
| `Nat.choose_two_right` | C(m,2) = m*(m-1)/2 | `choose_two` |

---

## K/U Update

### New KK
- **KK_18:** The existing proof has already committed to the `mu(A)` approach (lines 540-580). Route B (integral transfer) would require restructuring. Route A is mandatory.
- **KK_19:** The pi_map_pi pattern from Generalization.lean:3330-3355 is directly reusable.
- **KK_20:** All 4 auxiliary sorrys (560, 569, 575) have clear 3-8 LOC solutions.

### New CKU
- **CKU_16-19:** As documented above.

### New UK
- **UK_8-10:** As documented above. UK_10 (bypass via subtype) is ruled out by existing proof structure.

### Resolved
- **CKU_14** (from v2 URS): Uniform measure construction is ALREADY DONE in the enclosing code (lines 482-497). Not a blocker for the birthday sorry.
- **CKU_15** (from v2 URS): Birthday probability lower bound is the CONTENT of this URS. Route A via counting + union bound is the recommended approach.

---

## Literature

1. Shalev-Shwartz & Ben-David (2014). Understanding Machine Learning. Cambridge. Theorem 26.2 (birthday bound in Rademacher lower bound).
2. Dasgupta (2005). Coarse sample complexity bounds for active learning. NIPS. (Birthday bound for sample distinctness.)
3. Mathlib docs: `MeasureTheory.Measure.pi_map_pi`, `MeasureTheory.Measure.pi_pi`.
