---
session: 8
date: 2026-03-26
task_id: P3c
target: hlearn_unfold congrArg ladder
file: FLT_Proofs/Theorem/Separation.lean
status: closed
---

## P3c: Close `hlearn_unfold` (line 1077) — congrArg ladder

**File**: `FLT_Proofs/Theorem/Separation.lean`, line 1077
**Scope**: Replace the `sorry` at line 1077. Do not touch any other line.
**Dependencies**: `hsqrt`, `hblk`, `hn_pos`, `hblk_ne` all in scope from P3b.

### Statement (lines 1068–1077):

```lean
  have hlearn_unfold : ∀ (ω : Fin ((n + 1) * n) → X) (x : X),
      L'.learn (fun i => (ω i, c (ω i))) x =
      boosted_majority (n + 1) (fun j =>
        L.learn (fun i => (block_extract (n + 1) n ω j i,
                           c (block_extract (n + 1) n ω j i))) x) := by
    sorry
```

### Route: congrArg ladder (from user's sketch)

```lean
    intro ω x
    simp only [L']
    rw [dif_pos hblk_ne]
    simp only [hsqrt, hblk]
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

After `simp only [L']; rw [dif_pos hblk_ne]; simp only [hsqrt, hblk]`, the goal becomes:
```
boosted_majority (n+1) (fun j => L.learn (fun i => (ω ⟨j.1*n+i.1, _⟩, c(ω ⟨j.1*n+i.1, _⟩))) x)
= boosted_majority (n+1) (fun j => L.learn (fun i => (block_extract (n+1) n ω j i, c(block_extract (n+1) n ω j i))) x)
```

The congrArg ladder peels through: boosted_majority → L.learn → sample function → pair `(ω t, c (ω t))`. At the bottom, `hidx` proves `⟨j*n+i, _⟩ = finProdFinEquiv (j,i)` via `Fin.ext` + `omega` (since `j*n+i = i+n*j`).

### Contingencies from previous agents (JSONL-verified)

1. **If `simp only [L']` doesn't unfold**: Use `unfold L'` or `delta L'` followed by `dsimp only`
2. **If `dif_pos hblk_ne` doesn't match**: The `if` condition may be `n = 0` after simp, not `blk = 0`. Try `simp only [show (n = 0) = False from by omega, ite_false]` instead
3. **If `simp [finProdFinEquiv]` doesn't unfold enough for omega**: Use the fallback:
   ```lean
       ext
       show j.1 * n + i.1 = (finProdFinEquiv (j, i)).1
       rw [show (finProdFinEquiv (j, i)).1 = i.1 + n * j.1 from rfl]
       omega
   ```
4. **If `simpa [block_extract]` doesn't close**: Use:
   ```lean
   exact Prod.ext (congrArg ω hidx) (congrArg c (congrArg ω hidx))
   ```
5. **If orientation is reversed** (`hidx` goes wrong direction): Use `hidx.symm`

### Estimated LOC: ~15

### Guardrails
- A4/A5 checks
- No new sorry
- Edit only line 1077
- Do not touch any other line
- NEVER run `git checkout`, `git restore`, or any working-tree discard command
- `lake build` must pass with 0 errors
- `grep -n sorry Separation.lean` shows nothing (only comments)