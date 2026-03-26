# D6 Birthday v3 URS — Complete Closure Specification
**Date**: 2026-03-20 | **Supersedes**: D6_Birthday_v2_URS.md
**Target**: Close the single `sorry` in `rademacher_lower_bound_on_shattered` (Rademacher.lean:~736)
**Goal**: `(1 : R) / 2 <= (mu A).toReal`
**Predecessor State**: 98 LOC landed, 2 inner sorrys + 1 collision measure sorry remain

---

## 0. Will — Discovery Axiom

Attack the collision measure sorry FIRST (KU_1) — it's the deepest mathematical content. The ENNReal arithmetic sorrys (KU_2) are mechanical once the collision bound is proved. Do NOT retreat to weakening statements. If the collision bound resists, MAP the obstruction — what about the fiber structure is hard?

**Termination condition**: Comp >= 0.95 AND Inv >= 0.95. The agent may NOT terminate until `lake build` shows zero new sorrys in the Birthday section (lines 736-848) OR a genuine Gamma discovery is documented explaining why closure is impossible.

---

## 1. Surviving Code Audit (What Exists)

### Phase 1 — Transfer (COMPLETE, lines 737-749)
```
hμA_eq : μ A = μ_sub (φ ⁻¹' A)     -- via MeasureTheory.Measure.map_apply
hpre : φ ⁻¹' A = {ys | Injective ys} -- preimage identification
hB_def : B = {ys : Fin m → ↥T | Injective ys}
hB_meas : MeasurableSet B             -- via Set.Finite.measurableSet
hμA_B : μ A = μ_sub B                 -- composition
```
**Pl**: 1.0. **Coh**: 1.0. **Inv**: 1.0. Fully proved, no sorrys.

### Phase 2 — Complement Bound (90% complete, lines 750-820)
```
hDsub_sing : ∀ t, D_sub {t} = 1/(n : ENNReal)      -- PROVED
hμsub_sing : ∀ ys, μ_sub {ys} = (1/n)^m             -- PROVED via pi_pi
hBc_sub : Bᶜ ⊆ ⋃ p ∈ pairs, {ys | ys p.1 = ys p.2} -- PROVED
Union bound assembly via measure_biUnion_finset_le    -- PROVED
```
**3 sorrys remain in this phase** (see Section 3).

### Phase 3 — ENNReal→Real Transfer (COMPLETE, lines 821-848)
```
hBc_half → hB_ge : 1/2 ≤ μ_sub B     -- via prob_compl_eq_one_sub + tsub_le_tsub_left
→ ENNReal.toReal_mono                  -- final transfer
```
**Pl**: 1.0. **Coh**: 1.0 (given Phase 2 closes). **Inv**: 1.0.

---

## 2. KK Universe — Complete Inventory

| # | Component | Location | Status | Role |
|---|-----------|----------|--------|------|
| KK_1 | `MeasureTheory.Measure.map_apply` | Mathlib | AVAILABLE | Transfer μ(A) = μ_sub(φ⁻¹'A) |
| KK_2 | `MeasurableEmbedding.measurable` | Mathlib | AVAILABLE | φ is measurable (from hφ_emb) |
| KK_3 | `Set.Finite.measurableSet` | Mathlib | AVAILABLE | B is measurable (Fin m → ↥T is finite) |
| KK_4 | `MeasureTheory.Measure.pi_pi` | Mathlib | AVAILABLE | μ_sub({ys}) = Π_i D_sub({ys i}) |
| KK_5 | `measure_biUnion_finset_le` | Mathlib | AVAILABLE | Union bound over collision pairs |
| KK_6 | `prob_compl_eq_one_sub` | Mathlib | AVAILABLE | μ(Bᶜ) = 1 - μ(B) for prob measure |
| KK_7 | `ENNReal.toReal_mono` | Mathlib | AVAILABLE | ENNReal inequality → Real inequality |
| KK_8 | `Function.Injective` / `not_forall` / `push_neg` | Mathlib | AVAILABLE | Decompose ¬Injective into ∃ collision |
| KK_9 | `lt_or_gt_of_ne` | Mathlib | AVAILABLE | Order collision pair (i < j) |
| KK_10 | `Fintype.card_fun` | Mathlib | AVAILABLE | |Fin m → T| = n^m |
| KK_11 | `Fintype.card_coe` | Mathlib | AVAILABLE | |↥T| = |T| |
| KK_12 | `hT_large : 4 * m ^ 2 + 1 ≤ Fintype.card ↥T` | In scope | HYPOTHESIS | Gives 2m² ≤ n |
| KK_13 | `hmu_eq`, `hphi_emb`, `hA_meas`, `h_int_bound` | In scope | PROVED | All infrastructure hypotheses |
| KK_14 | `uniformMeasure` / `D_sub` | Defined in proof | PROVED | Uniform measure on T |
| KK_15 | `mu_sub = Measure.pi (fun _ => D_sub)` | In scope | PROVED | Product of uniform |

---

## 3. KU Universe — The 3 Remaining Sorrys

### KU_1: Collision Set Measure Bound (CRITICAL — attack first)
**Location**: `hcoll_meas` sorry inside Phase 2
**Goal**: `∀ i j, i ≠ j → μ_sub {ys : Fin m → ↥T | ys i = ys j} ≤ 1/(n : ENNReal)`

#### AMRT Analysis
- **Pl**: 0.90 — the mathematics is standard birthday problem
- **Coh**: 0.85 — the joint from "collision set has measure ≤ 1/n" to the union bound is clean (just plugs in)
- **Inv**: 0.95 — this bound is invariant to any future refactoring

#### Proof Route A (Cardinality — RECOMMENDED)
Show `|C_{ij}| = n^{m-1}` where `C_{ij} = {ys | ys i = ys j}`.

**Step 1**: Define the injection `φ_{ij} : (Fin (m-1) → ↥T) × ↥T → C_{ij}` that maps `(f, t)` to the function that puts `t` at positions `i` and `j` and fills the rest from `f`. This is a bijection.

**Step 2**: `|C_{ij}| = |Fin (m-1) → ↥T| × 1 = n^{m-1}` ... actually wrong. It should be: for each `t : T`, the fiber `{ys ∈ C_{ij} | ys i = t}` has cardinality `n^{m-2}` (free choice on m-2 other coordinates, j is forced to t). There are n choices of t. So `|C_{ij}| = n * n^{m-2} = n^{m-1}`.

Actually simpler: `C_{ij} ≅ T × (Fin (m-1) → T)` via the map that records `ys i` (= `ys j`) as the first component, and `ys` restricted to coordinates ≠ j as the second. This gives `|C_{ij}| = n * n^{m-1} = n^m`... no that's wrong too.

**CORRECT**: `C_{ij} ≅ (↥T) × ((Fin m \ {j}) → ↥T)` is NOT right because `Fin m \ {j}` is not `Fin (m-1)`.

**CORRECT approach**: Use `Measure.pi_pi` directly.
```
μ_sub(C_{ij}) = μ_sub({ys | ys i = ys j})
```
We cannot decompose this directly via pi_pi because C_{ij} is NOT a product set.

**Route A-measure (RECOMMENDED)**: Marginalize.
```
μ_sub({ys | ys i = ys j})
  = ∫ t, μ_sub({ys | ys i = t ∧ ys j = t ∧ ∀ k ≠ i, k ≠ j, ys k ∈ univ}) dD_sub(t)
  ≤ ∫ t, μ_sub({ys | ys i = t ∧ ys j = t}) dD_sub(t)
  = Σ_t D_sub({t})² * Π_{k≠i,j} D_sub(univ)
  = Σ_t (1/n)² * 1
  = n * (1/n)²
  = 1/n
```
Wait, that's not right either. Under μ_sub = Measure.pi, the coordinates are independent. So:
```
μ_sub({ys | ys i = ys j})
  = Σ_{t : T} μ_sub({ys | ys i = t ∧ ys j = t})
  = Σ_{t : T} D_sub({t}) * D_sub({t})     [independence of coordinates i, j]
  = Σ_{t : T} (1/n)²
  = n * (1/n)²
  = 1/n
```

In Lean, this requires:
1. Decompose the event `{ys | ys i = ys j} = ⋃_t {ys | ys i = t ∧ ys j = t}` (disjoint union over t)
2. μ_sub of each term = D_sub({t}) * D_sub({t}) * Π_{k≠i,j} 1 (by independence under Measure.pi)
3. Sum = n * (1/n)² = 1/n

**Lean API needed**:
- `MeasureTheory.Measure.pi_eval_preimage` or manual decomposition via `iIndepFun` for coordinate independence
- `Finset.sum_const` for Σ_t (1/n)² = n * (1/n)²

**Alternative Route B (Pure cardinality)**:
Since T is finite and μ_sub = uniform on T^m:
```
μ_sub(S) = |S| / n^m    for any S ⊆ T^m
```
Then `|C_{ij}| = n^{m-1}` (choosing ys i freely and forcing ys j = ys i, with m-2 other coordinates free).
So `μ_sub(C_{ij}) = n^{m-1} / n^m = 1/n`.

In Lean: use `MeasureTheory.Measure.count_apply` + uniform normalization. Need:
```
μ_sub(S) = |S| / |T^m|    -- from uniformMeasure definition
|C_{ij}| = n^{m-1}         -- cardinality computation
|T^m| = n^m                -- Fintype.card_fun
```

The cardinality `|C_{ij}| = n^{m-1}` via:
```
Fintype.card {ys : Fin m → ↥T | ys i = ys j}
  = Fintype.card (↥T) ^ (m - 1)
```
Proof: the equivalence `{ys | ys i = ys j} ≃ (Fin (m-1) → T)` given by "drop coordinate j and recover it from i". Formally use `Equiv.piCongrLeft` or construct manually.

**Counterproof search (Route A-measure)**:
- CP_1: Does `iIndepFun` give us coordinate independence under Measure.pi? YES — `iIndepFun_pi` (KK_19 analog for our measure)
- CP_2: Can we decompose `{ys | ys i = ys j}` as a disjoint union? YES — `⋃_t {ys | ys i = t} ∩ {ys | ys j = t}` is disjoint over t
- CP_3: Does the sum Σ_t D_sub({t})² = Σ_t (1/n)² work in ENNReal? YES — `Finset.sum_const`
**No counterproof found. Route A-measure is viable. Pl: 0.90.**

**Counterproof search (Route B-cardinality)**:
- CP_1: Can we compute `Fintype.card {ys | ys i = ys j}` in Lean4? UNKNOWN — requires `Fintype.card_subtype` + equivalence. More API friction.
- CP_2: Does `uniformMeasure` give `μ(S) = |S|/|Ω|` in ENNReal? Need to verify the exact definition. If `uniformMeasure = (1/|Ω|) • count`, then `μ(S) = |S|/|Ω|` follows from `count_apply`.
**Route B is viable but more API friction. Pl: 0.80.**

**DECISION**: Route A-measure (marginalization via independence) is recommended. Fallback to Route B if independence API is unavailable.

### KU_2: ENNReal Arithmetic (2 inner sorrys)
**Location**: End of `hBc_half` calc block (lines ~815-820)
**Goal**: `(m * m : ℕ) * (1 / (n : ENNReal)) ≤ 1 / 2` from `2 * m^2 ≤ n`

#### AMRT Analysis
- **Pl**: 0.95 — pure arithmetic
- **Coh**: 0.98 — plugs directly into calc chain
- **Inv**: 1.0 — invariant to everything

#### Proof Route (Nat-first — ONLY viable route)
The predecessor FAILED by trying ENNReal division lemmas (`ENNReal.div_le_iff`). These require non-zero / non-top guards and are fragile.

**CORRECT approach**: Do ALL arithmetic in Nat, cast at the end.
```lean
-- From hT_large : 4 * m ^ 2 + 1 ≤ Fintype.card ↥T
-- We get: 2 * m * m ≤ n   (by omega or nlinarith)
--
-- Goal: (↑(m * m) : ENNReal) * (1 / ↑n) ≤ 1 / 2
-- Rewrite as: ↑(m * m) / ↑n ≤ 1 / 2
-- Equivalently: 2 * ↑(m * m) ≤ ↑n  (in ENNReal, since n ≠ 0 and n ≠ ⊤)
-- This follows from: 2 * (m * m) ≤ n  (in Nat)
-- Cast: Nat.cast_le.mpr (by omega)
```

**Specific tactic sequence**:
```lean
rw [ENNReal.mul_comm, ENNReal.div_le_iff
  (ENNReal.natCast_ne_zero.mpr (by omega)) ENNReal.natCast_ne_top]
-- Goal: 1/2 * ↑n ≤ ... ? No, this doesn't work cleanly.
-- BETTER: convert to a single fraction comparison
suffices h : (↑(m * m) : ENNReal) ≤ ↑n / 2 by
  calc ↑(m * m) * (1 / ↑n) = ↑(m * m) / ↑n := by ring
    _ ≤ (↑n / 2) / ↑n := by exact ENNReal.div_le_div_right h ↑n
    _ = 1 / 2 := by rw [ENNReal.div_div_cancel_left (ENNReal.natCast_ne_zero.mpr (by omega)) ENNReal.natCast_ne_top]
-- Prove: ↑(m * m) ≤ ↑n / 2
-- From: 2 * m * m ≤ n
exact_mod_cast Nat.le_div_iff_mul_le (by omega) |>.mpr (by omega)
```

**Counterproof search**:
- CP_1: Does `ENNReal.div_div_cancel_left` exist? UNKNOWN — may need `ENNReal.div_self` + manipulation. Fallback: `simp [ENNReal.div_self]`.
- CP_2: Does `ENNReal.div_le_div_right` exist? YES — monotonicity of division.
- CP_3: Can `exact_mod_cast` bridge Nat to ENNReal here? YES — `Nat.cast_le` is definitional for ENNReal.
**No fatal counterproof. Route is viable. Pl: 0.90.**

---

## 4. UK Universe — Pressures

| # | Pressure | Impact | Resolution Status |
|---|----------|--------|-------------------|
| UK_1 | The `uniformMeasure` definition in scope — does it match `(1/n) • count`? | HIGH for Route A | CHECK at runtime. If different, adapt. |
| UK_2 | Whether `iIndepFun` for coordinate projections is directly available under the `μ_sub = Measure.pi (fun _ => D_sub)` we have | HIGH for KU_1 Route A | `iIndepFun_pi` gives this, but need to verify the exact instantiation |
| UK_3 | Line numbers may have shifted from Massart insertion | LOW | Read file before editing |

---

## 5. UU Boundary

| # | Region |
|---|--------|
| UU_1 | Whether Lean's ENNReal automation (`norm_num`, `simp`) can close the arithmetic sorrys without manual calc chains |
| UU_2 | Whether there exists a 1-line Mathlib lemma for "collision probability under product uniform measure" that we haven't found |

---

## 6. Counterproof Pathways — Route Elimination

### Route C (Direct computation without independence): ELIMINATED
Try to compute `μ_sub(C_{ij})` without using coordinate independence.
- Would need to enumerate all elements of C_{ij} and sum their singleton measures
- `|C_{ij}| = n^{m-1}` requires either the equivalence (Route B) or independence (Route A)
- Without either, we cannot compute the cardinality
**Counterproof**: No API path from `μ_sub(C_{ij})` to `1/n` without either cardinality or independence decomposition.
**Pl**: 0.00. **ELIMINATED.**

### Route D (Weaken the bound to μ_sub(Bᶜ) ≤ 1): ELIMINATED (A5 violation)
Could replace `hBc_half : μ_sub Bᶜ ≤ 1/2` with `μ_sub Bᶜ ≤ 1` (trivially true).
This makes `hB_ge` give `0 ≤ μ_sub B` instead of `1/2 ≤ μ_sub B`.
**Counterproof**: The downstream `suffices h_birthday : (1 : R) / 2 ≤ (mu A).toReal` needs the 1/2 bound.
**A5 violation**: Weakening the bound changes the mathematical content.
**ELIMINATED.**

### Route E (Use Mathlib's Birthday Problem): INVESTIGATED, PARTIALLY VIABLE
Mathlib's `Archive/Wiedijk100Theorems/BirthdayProblem.lean` proves:
```
card_injective_embedding = descFactorial n m
```
Using `uniformOn` and `Measure.count_apply_finite`.

**Counterproof**: Their approach uses exact computation (descFactorial/n^m), not union bound. The exact computation gives a TIGHTER bound but requires different API. The union bound approach (Route A) is more robust and already 90% built.
**Partial viability**: Could extract `descFactorial` computation, but would require restructuring the existing 98 LOC. **NOT worth the rewrite cost.**

---

## 7. Action Space

### Total Action Space (before restriction)
1. Route A-measure: close KU_1 via independence, close KU_2 via Nat-first arithmetic
2. Route B-cardinality: close KU_1 via Fintype.card, close KU_2 same
3. Route A-measure + Mathlib Birthday API: hybrid
4. Route E: complete rewrite using descFactorial

### Restricted Action Space (after counterproof elimination)
**Route A-measure → KU_1 → KU_2**: the ONLY route.
- KU_1: ~15 LOC (disjoint union + independence + sum)
- KU_2: ~10 LOC (Nat arithmetic + ENNReal cast)
- Total remaining: ~25 LOC

### Verification Restriction
After each sorry closure:
1. `lake build` — must show 0 new errors
2. A4 check — the closed sorry was non-trivial
3. A5 check — no statement modification
4. Comp measurement — what fraction of the Birthday proof is now sorry-free?
5. Inv measurement — does the closed sorry survive `git stash && lake build && git stash pop`?

---

## 8. Termination Protocol

The agent tracks two metrics continuously:

**Comp** = (proved obligations) / (total obligations in Birthday section)
- Phase 1: 5/5 = 1.0
- Phase 2: (8 proved + 3 sorry) / 11 = 0.73 currently
- Phase 3: 4/4 = 1.0
- Overall: 17/20 = 0.85 currently
- Target: >= 0.95

**Inv** = probability that the proof survives future codebase changes
- Current: 0.95 (the Birthday proof is self-contained, doesn't depend on other sorrys)
- Target: >= 0.95

**Termination conditions (ALL must hold)**:
1. `lake build` passes with 0 new errors
2. Comp >= 0.95 (at most 1 sorry remaining, and that sorry must be a documented Gamma)
3. Inv >= 0.95 (no fragile dependencies introduced)
4. A4/A5 post-build check passes
5. World model update written (K/U transitions logged)

**If termination conditions cannot be met**: document the blocker as a Gamma discovery with full counterproof analysis, and propose the minimum intervention needed to unblock.

---

## 9. Exclusive File Access

**WRITE**: `FLT_Proofs/Complexity/Rademacher.lean` lines 736-848 ONLY
**READ**: Any file in the codebase
**DO NOT TOUCH**: Lines 1-735 (Massart section), lines 849+ (Rademacher↔PAC section)
