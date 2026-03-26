---
session: 8
date: 2026-03-26
task_id: S10
target: Fix hlearn_unfold compile error (congrArg ladder)
file: FLT_Proofs/Theorem/Separation.lean
status: blocked
note: Superseded by P3c after file reset
---

## S10: Fix `hlearn_unfold` compile error (line 962–1010)

**File**: `FLT_Proofs/Theorem/Separation.lean`, lines 962–1010
**Scope**: Replace the body of `hlearn_unfold` (lines 967–1010). Keep the statement (lines 962–966) and everything after line 1010 untouched.
**Nature**: The agent's proof is structurally correct but has a compile error at line 1009 (`omega` fails on a partially-unfolded goal). Replace with the user's cleaner `congrArg` ladder approach.

### What to replace

Delete lines 967–1010 (the body after `by`) and replace with:

```lean
    intro ω x
    have hblk_ne : (n + 1) * n / (Nat.sqrt ((n + 1) * n) + 1) ≠ 0 := by rw [hsqrt, hblk]; omega
    simp only [L']
    rw [dif_pos hblk_ne]
    simp only [hsqrt, hblk]
    -- Now both sides are boosted_majority (n+1) (fun j => L.learn (...) x)
    -- LHS uses ⟨j.1 * n + i.1, _⟩, RHS uses block_extract = finProdFinEquiv(j,i)
    refine congrArg (boosted_majority (n + 1)) ?_
    funext j
    refine congrArg (fun S : Fin n → X × Bool => L.learn S x) ?_
    funext i
    have hidx : (⟨j.1 * n + i.1, by
        have hj : j.1 < n + 1 := j.2
        have hi : i.1 < n := i.2
        calc j.1 * n + i.1 < j.1 * n + n := by omega
          _ = (j.1 + 1) * n := by ring
          _ ≤ (n + 1) * n := by nlinarith⟩
        : Fin ((n + 1) * n)) = finProdFinEquiv (j, i) := by
      ext
      simp [finProdFinEquiv]
      omega
    simpa [block_extract] using congrArg (fun t : Fin ((n + 1) * n) => (ω t, c (ω t))) hidx
```

### Why this works

1. `simp only [L']` unfolds the learner definition
2. `rw [dif_pos hblk_ne]` forces the majority branch (blk ≠ 0)
3. `simp only [hsqrt, hblk]` rewrites `Nat.sqrt` and division to get both sides using `n+1` and `n`
4. `congrArg (boosted_majority (n+1))` peels through the outer function
5. `funext j` + `congrArg (fun S => L.learn S x)` peels through L.learn
6. `funext i` gets to the per-index level
7. `hidx` proves the Fin index equality: `⟨j*n+i, _⟩ = finProdFinEquiv (j, i)` via `Fin.ext` + `omega`
8. `simpa [block_extract]` finishes by pushing the index equality through `(ω t, c (ω t))`

### Contingencies

If `simp only [L']` doesn't unfold (let-binding resistance), use `unfold L'` or `delta L'` followed by `dsimp only`.

If `simp [finProdFinEquiv]` doesn't unfold enough for `omega`, use:
```lean
      ext
      show j.1 * n + i.1 = (finProdFinEquiv (j, i)).1
      rw [show (finProdFinEquiv (j, i)).1 = i.1 + n * j.1 from rfl]
      omega
```

If the `simpa [block_extract]` at the end doesn't close, use:
```lean
    exact Prod.ext (congrArg ω hidx) (congrArg c (congrArg ω hidx))
```

### Guardrails
- A4/A5 checks
- No new sorry
- Edit only lines 967–1010
- Do not touch any other line
- `lake build` must pass
- `grep -n sorry Separation.lean` shows nothing (only comments mentioning "sorry")