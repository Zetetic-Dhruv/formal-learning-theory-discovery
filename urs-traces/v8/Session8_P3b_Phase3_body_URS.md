---
session: 8
date: 2026-03-26
task_id: P3b
target: Phase 3 body (everything except hlearn_unfold)
file: FLT_Proofs/Theorem/Separation.lean
status: closed
---

## P3b: Phase 3 body (everything except hlearn_unfold)

**File**: `FLT_Proofs/Theorem/Separation.lean`, line 1037
**Scope**: Replace the sorry at line 1037 with the full proof. Use `sorry` for `hlearn_unfold` ONLY.

### What compiled in previous agents (from JSONL extraction)

The Phase 3 agent (ae52008009cdc77b7) successfully compiled all steps except `hlearn_unfold`. Here is the exact structure that worked:

**Step 3a — Parameter extraction** (compiled):
```lean
  dsimp only
  rw [dif_pos hε, dif_pos hδ]
  have hε'_pos : 0 < ε / 7 := by positivity
  set kmin := Nat.ceil (36 / δ) + 2 with hkmin_def
  set n := max (Nat.find (hrate (ε / 7) hε'_pos)) (kmin - 1) with hn_def
  have hn_pos : 0 < n := by simp [n, kmin]; omega
  have hn1_pos : 0 < n + 1 := by omega
  have hsqrt : Nat.sqrt ((n + 1) * n) = n := by
    rw [show (n + 1) * n = n * n + n from by ring]
    exact Nat.sqrt_add_eq n (Nat.le_add_self n n)
  have hblk : (n + 1) * n / (n + 1) = n := Nat.mul_div_cancel_left n (by omega)
  have hblk_ne : ((n + 1) * n / (Nat.sqrt ((n + 1) * n) + 1)) ≠ 0 := by
    rw [hsqrt, hblk]; omega
  have hrate_n : rate n < ε / 7 := by
    exact Nat.find_spec (hrate (ε / 7) hε'_pos) n (le_max_left _ _)
  have h36k : (36 : ℝ) / δ ≤ (n + 1 : ℝ) := by
    calc (36 : ℝ) / δ ≤ ↑(Nat.ceil (36 / δ)) := Nat.le_ceil _
      _ ≤ ↑kmin := by simp [kmin]; omega
      _ ≤ ↑(n + 1) := by exact_mod_cast (by omega : kmin ≤ n + 1)
```

**Step 3b — Concentration instantiation** (compiled):
```lean
  have hevents_meas := goodBlockEvent_measurable L hL_meas D c (hc_meas c hcC) rate (n + 1) n
  have hindep := iIndepSet_goodBlockEvents L hL_meas D c (hc_meas c hcC) rate (n + 1) n
  have hprob := fun j => goodBlockEvent_prob_ge_two_thirds C L hL_meas rate huniv D c hcC
    (hc_meas c hcC) (n + 1) n j
  have hconc := chebyshev_seven_twelfths_bound hδ h36k
    (goodBlockEvent L D c rate (n + 1) n) hevents_meas hindep hprob
```

**Step 3c — Rate bound** (compiled):
```lean
  have h7rate : 7 * max (rate n) 0 ≤ ε := by
    have : max (rate n) 0 ≤ ε / 7 := by
      rcases le_or_lt 0 (rate n) with h | h
      · simp [max_eq_left h]; linarith
      · simp [max_eq_right (le_of_lt h)]; positivity
    linarith
```

**Step 3d — hlearn_unfold** (SORRY — the only gap):
```lean
  have hlearn_unfold : ∀ (ω : Fin ((n + 1) * n) → X) (x : X),
      L'.learn (fun i => (ω i, c (ω i))) x =
      boosted_majority (n + 1) (fun j =>
        L.learn (fun i => (block_extract (n + 1) n ω j i,
                           c (block_extract (n + 1) n ω j i))) x) := by
    sorry
```

**Step 3e — Error set equality** (compiled, using hlearn_unfold):
```lean
  have herr_set_eq : ∀ (ω : Fin ((n + 1) * n) → X),
      {x | L'.learn (fun i => (ω i, c (ω i))) x ≠ c x} =
      {x | boosted_majority (n + 1) (fun j =>
        L.learn (fun i => (block_extract (n + 1) n ω j i,
                           c (block_extract (n + 1) n ω j i))) x ≠ c x} := by
    intro ω; ext x; simp [hlearn_unfold ω x]
```

**Step 3f — Subset** (compiled):
```lean
  have hsub : {ω | 7 * (n + 1) ≤ 12 *
      (Finset.univ.filter (fun j => ω ∈ goodBlockEvent L D c rate (n + 1) n j)).card} ⊆
      {xs | D {x | L'.learn (fun i => (xs i, c (xs i))) x ≠ c x} ≤ ENNReal.ofReal ε} := by
    intro ω hω
    rw [Set.mem_setOf_eq, herr_set_eq ω]
    have hbound := boosted_sample_error_le_of_good_blocks D c (hc_meas c hcC) L hL_meas
      rate (n + 1) n ω (by omega) hω
    exact le_trans hbound (ENNReal.ofReal_le_ofReal h7rate)
```

**Step 3g — Final composition** (compiled):
```lean
  exact le_trans hconc (MeasureTheory.measure_mono hsub)
```

### Negative space (from JSONL: what FAILED)

1. **`simp only [dif_pos hε, dif_pos hδ]` alone FAILS** — need `dsimp only` first or use `rw`
2. **`Nat.find` needs the positivity proof explicitly** — `hrate (ε / 7) hε'_pos` not `hrate ε' ...`
3. **The calc step for `h36k`** failed with `exact_mod_cast` alone when kmin wasn't fully unfolded — need `(by omega : kmin ≤ n + 1)` as the cast target
4. **`hconc` type**: The concentration bound is on `Fin ((n+1)*n) → X`, which must match the goal's `Fin (mf ε δ) → X`. After `dsimp only; rw [dif_pos hε, dif_pos hδ]`, the `mf ε δ` reduces to `(n+1)*n`. If it doesn't, need `show` or `change` to force the match.
5. **DO NOT try to unfold L' in the subset step** — use `herr_set_eq` to bridge instead

### Guardrails
- A4/A5 checks
- `sorry` ONLY for `hlearn_unfold` — everything else must compile
- Do NOT touch any helper lemma or the learner/mf construction
- NEVER run `git checkout`, `git restore`, or any working-tree discard command
- `lake build` must pass (with the single `hlearn_unfold` sorry)