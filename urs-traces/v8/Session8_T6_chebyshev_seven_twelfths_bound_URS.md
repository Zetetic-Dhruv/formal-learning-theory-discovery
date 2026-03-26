---
session: 8
date: 2026-03-26
task_id: T6
target: chebyshev_seven_twelfths_bound
file: FLT_Proofs/Theorem/Separation.lean
status: closed
---

## T6: `chebyshev_seven_twelfths_bound` (line 550)

**File**: `FLT_Proofs/Theorem/Separation.lean`, line 550
**Scope**: Replace the `sorry` at line 550. Do not touch any other line.
**Dependencies**: None — standalone. Mirrors `chebyshev_majority_bound` (lines 152–302).

### Current state (lines 538–550):

```lean
private lemma chebyshev_seven_twelfths_bound
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    {k : ℕ} {δ : ℝ} (h_delta_pos : 0 < δ)
    (hk : (36 : ℝ) / δ ≤ k)
    (events : Fin k → Set Ω)
    (hevents_meas : ∀ j, MeasurableSet (events j))
    (hindep : ProbabilityTheory.iIndepSet (fun j => events j) μ)
    (hprob : ∀ j, μ (events j) ≥ ENNReal.ofReal (2/3)) :
    μ {ω | 7 * k ≤ 12 * (Finset.univ.filter (fun j => ω ∈ events j)).card} ≥
      ENNReal.ofReal (1 - δ) := by
  sorry
```

### Route

**Copy `chebyshev_majority_bound` (lines 163–302) verbatim, with exactly 4 changes:**

| # | What | Old (lines 152–302) | New (T6) |
|---|------|---------------------|----------|
| 1 | Step 8 constant | `(0 : ℝ) < 9 / δ` | `(0 : ℝ) < 36 / δ` |
| 2 | Step 14 gap | `hk6_pos : (0 : ℝ) < ↑k / 6` | `hk12_pos : (0 : ℝ) < ↑k / 12` |
| 3 | Step 15 ratio | `= 9 / ↑k`, `h9 : 9 / δ * δ = 9` | `= 36 / ↑k`, `h36 : 36 / δ * δ = 36` |
| 4 | Steps 17–21 event | `{↑k / 2 < S ω}` with gap `k/6` | `{(7:ℝ) * ↑k / 12 ≤ S ω}` with gap `k/12` |

### Compiled API names (all verified working at lines 152–302)

```
ProbabilityTheory.iIndepSet.iIndepFun_indicator        -- line 176
ProbabilityTheory.variance_le_sq_of_bounded            -- line 193
ProbabilityTheory.IndepFun.variance_sum                -- line 201
ProbabilityTheory.meas_ge_le_variance_div_sq           -- line 239
MeasureTheory.memLp_of_bounded                         -- line 187
MeasureTheory.integral_indicator_const                  -- line 211
MeasureTheory.integral_finset_sum                       -- line 220
MeasureTheory.memLp_finset_sum                          -- line 228
MeasureTheory.measure_add_measure_compl                 -- line 276
Finset.sum_boole                                        -- line 172
ENNReal.ofReal_sub                                      -- line 279
ENNReal.sub_eq_of_eq_add                                -- line 289
ProbabilityTheory.IndepFun.indepFun                     -- line 198 (via hindep_fun.indepFun)
```

### Exact substitutions

**Step 8** (was line 207):
```lean
  have hk_pos : (0 : ℝ) < ↑k := lt_of_lt_of_le (by positivity : (0 : ℝ) < 36 / δ) hk
```

**Step 14** (was line 238–239):
```lean
  have hk12_pos : (0 : ℝ) < ↑k / 12 := by positivity
  have hcheb := meas_ge_le_variance_div_sq hS_memLp hk12_pos
```

**Step 15** (was lines 241–249):
```lean
  have hcheb_bound : ProbabilityTheory.variance S μ / ((↑k / 12) ^ 2) ≤ δ := by
    calc ProbabilityTheory.variance S μ / ((↑k / 12) ^ 2)
        ≤ (↑k / 4) / ((↑k / 12) ^ 2) :=
          div_le_div_of_nonneg_right hvar_S_fn (sq_nonneg _)
      _ = 36 / ↑k := by field_simp; ring
      _ ≤ δ := by
          rw [div_le_iff₀ hk_pos]
          have h36 : 36 / δ * δ = 36 := div_mul_cancel₀ 36 (ne_of_gt h_delta_pos)
          nlinarith [hk]
```

**Step 16** (was line 251):
```lean
  have hbad_le : μ {ω | ↑k / 12 ≤ |S ω - ∫ ω, S ω ∂μ|} ≤ ENNReal.ofReal δ :=
    le_trans hcheb (ENNReal.ofReal_le_ofReal hcheb_bound)
```

**Step 17** (was lines 254–261) — **NOTE: uses `≤` not `<`, gap changes from `k/6` to `k/12`**:
```lean
  have hcompl_sub : {ω | (7 : ℝ) * ↑k / 12 ≤ S ω}ᶜ ⊆
      {ω | ↑k / 12 ≤ |S ω - ∫ ω, S ω ∂μ|} := by
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hω
    simp only [Set.mem_setOf_eq]
    have hgap : ∫ ω, S ω ∂μ - S ω ≥ ↑k / 12 := by linarith [hES, hω]
    calc ↑k / 12 ≤ ∫ ω, S ω ∂μ - S ω := hgap
      _ ≤ |S ω - ∫ ω, S ω ∂μ| := by rw [abs_sub_comm]; exact le_abs_self _
```

Gap arithmetic: `E[S] ≥ 2k/3 = 8k/12` and `S ω < 7k/12`, so `E[S] - S ω > 8k/12 - 7k/12 = k/12`. ✓

**Steps 18–20**: Replace all `{↑k / 2 < S ω}` with `{(7 : ℝ) * ↑k / 12 ≤ S ω}`.

**Step 19 measurability** (was line 270–271) — **CRITICAL CHANGE: `≤` needs `measurableSet_Ici`, not `measurableSet_lt`**:
```lean
  have hmeas : MeasurableSet {ω | (7 : ℝ) * ↑k / 12 ≤ S ω} :=
    hS_meas measurableSet_Ici
```
The old proof used `measurableSet_lt measurable_const hS_meas` for strict `<`. The new event uses `≤` so needs `measurableSet_Ici` or `measurableSet_le`. If `hS_meas measurableSet_Ici` doesn't work, try `measurableSet_le measurable_const hS_meas`.

**Step 21** (was lines 296–302):
```lean
  apply le_trans hgood
  apply μ.mono
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  rw [hS_count ω] at hω
  have : (7 : ℝ) * ↑k ≤ 12 * ↑(Finset.univ.filter (fun j => ω ∈ events j)).card := by
    linarith
  exact_mod_cast this
```

### Negative space — what FAILS (from agent JSONL analysis)

The previous T6 agents (831KB agent with 186 errors, 0 build successes) failed on:

1. **DO NOT try to write T6 from scratch.** Copy the working proof at lines 163–302 and make the 4 substitutions. The agents that failed tried to construct the proof independently and got stuck on API mismatches.

2. **DO NOT use `variance_div_sq` without `meas_ge_le_` prefix.** The correct name is `ProbabilityTheory.meas_ge_le_variance_div_sq`, not `meas_ge_le_variance_div_sq` alone (the `open` at line 163 brings it into scope).

3. **DO NOT change the `open` statement.** The existing proof uses `open MeasureTheory ProbabilityTheory Finset in`. Keep exactly this.

4. **The `hS_count` step uses `Finset.sum_boole` followed by `rfl`.** Do not try `simp` alone — the `rfl` is needed because `sum_boole` produces `Finset.card (filter ...)` which is definitionally equal to the cast.

5. **`div_mul_cancel₀` is the correct name** (not `div_mul_cancel`). Takes `(a : α) (h : b ≠ 0)` and gives `a / b * b = a`.

6. **`memLp_of_bounded` requires the `aestronglyMeasurable` argument**, not `aemeasurable`. The exact pattern from line 187–188 must be preserved.

### Estimated LOC: ~140 (copy of 140-line proof with 4 substitutions)

### Guardrails
- A4/A5 checks
- No new sorry
- Edit only line 550 (will expand to ~140 lines)
- Do not touch any other lemma
- NEVER run `git checkout`, `git restore`, or any working-tree discard command

---

Now stashing: