# D2 NFL v6 URS — Lower Bound Complete Closure
**Date**: 2026-03-20 | **Supersedes**: D2_Proof_v5_URS.md
**Target**: Close `pac_lower_bound_core` and `pac_lower_bound_member` in Generalization.lean
**Predecessor State**: PAC.lean constant weakened to `(d-1)/2` (LANDED). Proof code NOT written.

---

## 0. Will — Discovery Axiom

The NFL lower bound is an Ω(d) result, not Ω(d/ε). The full Ω(d/ε) requires EHKV (Fano inequality) which exists in `EHKV.lean` but is not yet connected. Do NOT attempt to prove Ω(d/ε) — that's a separate task. Close the Ω(d) bound cleanly.

Attack `pac_lower_bound_member` FIRST — it's the stronger statement from which `pac_lower_bound_core` follows. The proof pattern exists in `vcdim_infinite_not_pac` — duplicate and adapt.

**Termination condition**: Comp >= 0.95 AND Inv >= 0.95. Both sorrys must be closed, or genuine Gamma discovered.

---

## 1. KK Universe

### Proved Infrastructure (sorry-free)
| # | Component | Location | Role |
|---|-----------|----------|------|
| KK_1 | `nfl_counting_core` | Gen:2539 | Core combinatorial bound: for |T| ≥ 2m, ∃ distribution on T^m × {concepts} s.t. no learner achieves < 1/4 error on > 1/2 of concepts |
| KK_2 | `nfl_core` | Gen:2480 | Wrapper around nfl_counting_core for finite domains |
| KK_3 | `vcdim_infinite_not_pac` | Gen:~2989 | VCDim = ∞ → not PAC. Contains the MEASURE BRIDGE we need to duplicate |
| KK_4 | `uniformMeasure_isProbability` | Gen:~2900 | uniformMeasure on nonempty Fintype is probability measure |
| KK_5 | `SampleComplexity` definition | PAC.lean | `sInf {m | ∀ L, PAC guarantee holds for m samples}` |
| KK_6 | `PACLearnable` definition | Criterion/PAC.lean | Standard PAC definition |
| KK_7 | `pac_lower_bound` (PAC.lean:169) | PAC.lean | Wrapper that chains to `pac_lower_bound_core` — CURRENTLY SORRY'd |
| KK_8 | `Nat.ceil` | Mathlib | Ceiling function |
| KK_9 | `MeasurableSingletonClass` | Mathlib | Makes all singletons measurable — needed for measure bridge |
| KK_10 | `Set.Finite.measurableSet` | Mathlib | Finite set → MeasurableSet (under MeasurableSingletonClass) |
| KK_11 | PAC.lean constant already weakened to `(d-1)/2` | PAC.lean:172 | LANDED by predecessor |

### The Measure Bridge Pattern (from vcdim_infinite_not_pac)
The existing proof at Gen:~2989 contains the exact pattern we need:
1. Extract shattered set S of size d from VCDim hypothesis
2. Build uniformMeasure on S (or on a type with |S| elements)
3. Embed S into X via the shattering witness
4. Construct D = pushforward of uniform on S
5. Apply `nfl_counting_core` with this D
6. The counting core gives ∃ bad concept, so ∀ L, error ≥ 1/4 on some concept

**This pattern is ~50 LOC in the existing code.** We duplicate it.

---

## 2. KU Universe — The 2 Sorrys

### KU_1: `pac_lower_bound_member` (Gen:~2680)
**Current signature**:
```lean
theorem pac_lower_bound_member (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (d : ℕ) (hd : VCDim X C = d) (hd_pos : 1 ≤ d)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1/4)
    (m : ℕ) (hm : m < Nat.ceil ((d - 1 : ℝ) / 2)) :
    ∃ (D : MeasureTheory.Measure X), MeasureTheory.IsProbabilityMeasure D ∧
    ∃ (c ∈ C), ∀ (L : BatchLearner X Bool),
      MeasureTheory.Measure.pi (fun _ : Fin m => D)
        {xs | TrueErrorReal X (L.learn (fun i => (xs i, c (xs i)))) c D > ε} > 0
```

#### AMRT
- **Pl**: 0.85 — the measure bridge pattern exists, just needs `[MeasurableSingletonClass X]`
- **Coh**: 0.80 — the joint from shattered set → uniformMeasure → nfl_counting_core is the tightest
- **Inv**: 0.90 — the Ω(d) bound is the correct result for counting techniques

#### Proof Route (~50 LOC)

**Step 1** (~5 LOC): Add `[MeasurableSingletonClass X]` to the signature (or add as hypothesis).
```lean
-- REQUIRED: without MeasurableSingletonClass, Set.Finite.measurableSet fails
-- and the embedding from the finite shattered set into X cannot produce MeasurableSets
```
**A5 check**: Adding `[MeasurableSingletonClass X]` NARROWS the theorem. Is this A5-valid?
- `MeasurableSingletonClass` holds for ALL standard spaces (ℝ, ℕ, Fin n, countable types)
- The only spaces where it fails are exotic non-Hausdorff spaces with non-atomic σ-algebras
- The PAC learning theory literature universally assumes measurable singletons
- **VERDICT**: A5-valid. This is a regularity condition, not a simplification.

**Step 2** (~10 LOC): Extract shattered set from VCDim.
```lean
-- VCDim X C = d means ∃ S : Finset X, |S| = d ∧ C shatters S
obtain ⟨S, hS_card, hS_shattered⟩ := vcdim_ge_iff_exists_shattered.mp (by rw [hd]; exact le_refl d)
```

**Step 3** (~15 LOC): Build uniform distribution on S.
```lean
-- D = (1/d) * Σ_{x ∈ S} dirac x
-- This is uniformMeasure on the subtype ↥S, pushed forward to X
set D := MeasureTheory.Measure.map Subtype.val (uniformMeasure (↥S))
have hD_prob : IsProbabilityMeasure D := ...
```

**Step 4** (~15 LOC): Apply `nfl_counting_core`.
```lean
-- nfl_counting_core requires |T| ≥ 2*m (where T = S, |T| = d)
-- We have m < ⌈(d-1)/2⌉, so m ≤ (d-1)/2, so 2m ≤ d-1 < d = |S|. ✓
-- This gives: ∃ c, ∀ L, bad probability > 0
```

**Step 5** (~5 LOC): Package into the required existential form.

#### Counterproof Search
- CP_1: Does `hm : m < ⌈(d-1)/2⌉` give `2*m < d`? YES: `m ≤ ⌈(d-1)/2⌉ - 1 ≤ (d-1)/2`, so `2m ≤ d-1 < d`. Via `Nat.lt_of_ceil_lt` or manual arithmetic.
- CP_2: Does `nfl_counting_core` require the distribution to be on a finite type? CHECK — if it requires `[Fintype X]`, we need to work on the subtype `↥S` instead of `X`. The existing `vcdim_infinite_not_pac` handles this.
- CP_3: The `MeasurableEmbedding` from `↥S` to `X` — does `Subtype.val` give this under `[MeasurableSingletonClass X]`? YES: `MeasurableEmbedding.subtype_val` + finite set measurability.
**No fatal counterproof. Route is viable.**

### KU_2: `pac_lower_bound_core` (Gen:~2083)
**Current signature**: Similar to `pac_lower_bound_member` but with different packaging.

#### AMRT
- **Pl**: 0.90 — chains through `pac_lower_bound_member`
- **Coh**: 0.95 — direct application
- **Inv**: 0.95

#### Proof Route (~25 LOC)
Chain through `pac_lower_bound_member`. The main work is showing that the sample complexity lower bound `⌈(d-1)/2⌉` matches the `SampleComplexity` definition (which uses `sInf`).

```lean
-- SampleComplexity X C ε δ = sInf {m | ∀ L, PAC guarantee for m samples}
-- Need: ⌈(d-1)/2⌉ ≤ SampleComplexity
-- Proof: for any m < ⌈(d-1)/2⌉, pac_lower_bound_member gives ∃ bad D,c
-- So m ∉ {m | ∀ L, PAC guarantee for m samples}
-- So SampleComplexity ≥ ⌈(d-1)/2⌉
apply Nat.le_csInf
intro m hm
by_contra h_bad
push_neg at h_bad
exact absurd (pac_lower_bound_member X C d hd hd_pos ε hε hε1 m h_bad) (not_exists.mpr ...)
```

---

## 3. UK Universe

| # | Pressure | Impact | Status |
|---|----------|--------|--------|
| UK_1 | `nfl_counting_core` exact signature — does it take `Fin m → X` or a more abstract type? | HIGH | CHECK at runtime by reading Gen:2539 |
| UK_2 | `vcdim_ge_iff_exists_shattered` — does this lemma exist with the right type? | MEDIUM | CHECK — may be `vcdim_ge_iff_shattered` or similar |
| UK_3 | The `TrueErrorReal` vs `TrueError` distinction — which does the statement use? | LOW | Read the exact sorry statement |
| UK_4 | Whether `pac_lower_bound` in PAC.lean needs updating after we add `[MeasurableSingletonClass X]` | MEDIUM | CHECK — it may need the same instance |

---

## 4. UU Boundary

| # | Region |
|---|--------|
| UU_1 | Whether EHKV.lean infrastructure could give the Ω(d/ε) bound with reasonable effort (~100 LOC) |
| UU_2 | Whether the sample complexity definition is compatible with the lower bound packaging |

---

## 5. Route Elimination

### Route A (Direct nfl_counting_core): THE ROUTE (described above)
### Route B (EHKV / Fano inequality for Ω(d/ε)): ELIMINATED for this task
Requires connecting EHKV.lean infrastructure to the main lower bound. That's a separate sorry (not in scope).
### Route C (Information-theoretic via Le Cam): ELIMINATED
No Le Cam infrastructure in codebase. Would require ~300 LOC of new definitions.
### Route D (Probabilistic method without nfl_counting_core): ELIMINATED
Would duplicate existing proved infrastructure. A5 violation (not building on what exists).

---

## 6. Action Space (Restricted)

| Step | Target | LOC | Pl |
|------|--------|-----|-----|
| 1 | Read exact signatures of `pac_lower_bound_member`, `pac_lower_bound_core`, `nfl_counting_core` | 0 | — |
| 2 | Add `[MeasurableSingletonClass X]` to both theorem signatures | 2 | 0.98 |
| 3 | Close `pac_lower_bound_member` via measure bridge duplication | 50 | 0.85 |
| 4 | Close `pac_lower_bound_core` via chain through member | 25 | 0.90 |
| 5 | Update `pac_lower_bound` in PAC.lean if needed | 5 | 0.95 |

**Total**: ~82 LOC.

---

## 7. Termination Protocol

**Comp** = (closed sorrys) / 2
- Target: 2/2 = 1.0

**Inv** = 0.90 (the Ω(d) bound is robust; the `[MeasurableSingletonClass X]` addition is a non-breaking change for all downstream users)

**Termination conditions**:
1. `lake build` passes
2. Both `pac_lower_bound_core` and `pac_lower_bound_member` are sorry-free
3. `pac_lower_bound` in PAC.lean compiles
4. A4/A5 check passes (especially: `[MeasurableSingletonClass X]` addition is A5-valid)
5. K/U transitions logged

---

## 8. Exclusive File Access

**WRITE**: `FLT_Proofs/Complexity/Generalization.lean` lines 2500-2750, `FLT_Proofs/Theorem/PAC.lean` lines 160-200
**READ**: Any file
**DO NOT TOUCH**: Gen lines 1-2499 (UC/symmetrization territory), Gen lines 2750+ (existing proved lemmas)
