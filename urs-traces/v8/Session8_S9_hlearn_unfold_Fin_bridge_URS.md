---
session: 8
date: 2026-03-26
task_id: S9
target: hlearn_unfold Fin bridge (earlier attempt)
file: FLT_Proofs/Theorem/Separation.lean
status: blocked
note: Superseded by P3c after file reset
---

## S9: Close `hlearn_unfold` (line 985)

**File**: `FLT_Proofs/Theorem/Separation.lean`, line 985
**Scope**: Replace the `sorry` at line 985. Do not touch any other line.
**Dependencies**: All T1–T8 proved. hsqrt, hblk, hn_pos, hblk_ne all in scope.

### What's in scope (from lines 943–946, 929–933)

```
hsqrt : Nat.sqrt ((n + 1) * n) = n
hblk : (n + 1) * n / (n + 1) = n
hn_pos : 0 < n
hn1_pos : 0 < n + 1
hblk_ne : (n + 1) * n / (Nat.sqrt ((n + 1) * n) + 1) ≠ 0
```

### The goal after `simp only [hsqrt, hblk, finProdFinEquiv]` (line 983)

The LHS has unfolded L' into something like:
```
boosted_majority (Nat.sqrt ((n+1)*n) + 1) (fun j =>
  L.learn (fun i => (ω ⟨j * ((n+1)*n / (Nat.sqrt((n+1)*n)+1)) + i, _⟩,
                     c (ω ⟨j * ((n+1)*n / (Nat.sqrt((n+1)*n)+1)) + i, _⟩))) x)
```

The RHS is:
```
boosted_majority (n + 1) (fun j =>
  L.learn (fun i => (block_extract (n+1) n ω j i,
                     c (block_extract (n+1) n ω j i))) x)
```

Where `block_extract (n+1) n ω j i = ω ⟨(finProdFinEquiv (j, i)).val, _⟩ = ω ⟨i + n * j, _⟩`.

### Route

**Do NOT use `simp` to close the whole thing.** The agent already tried that and it failed.

**Route A (recommended)**: Unfold everything manually, then use `congr` + `Fin.ext` + `omega`.

```lean
    intro ω x
    simp only [L']
    -- Discharge the dif_pos for blk ≠ 0
    rw [dif_pos (by rw [hsqrt, hblk]; exact hn_pos.ne')]
    -- Now both sides are boosted_majority with the same k
    -- LHS: k = Nat.sqrt((n+1)*n) + 1, RHS: k = n+1
    -- Rewrite Nat.sqrt
    simp only [hsqrt, hblk]
    -- Now both are boosted_majority (n+1) (fun j => L.learn (fun i => (ω ⟨...⟩, c(ω ⟨...⟩))) x)
    -- The difference is in the Fin index: LHS has ⟨j*n+i, _⟩, RHS has block_extract = ⟨i+n*j, _⟩
    congr 1
    ext j
    congr 1
    ext i
    congr 1
    · congr 1; exact Fin.ext (by simp [block_extract, finProdFinEquiv]; omega)
    · congr 1; exact Fin.ext (by simp [block_extract, finProdFinEquiv]; omega)
```

**Route B (if `dif_pos` is the issue)**: The L' definition may use `if blk = 0 then ... else ...`. The `blk` is `(n+1)*n / (Nat.sqrt((n+1)*n) + 1)`. After rewriting with `hsqrt`, this becomes `(n+1)*n / (n+1) = n`. So `blk ≠ 0` iff `n ≠ 0`, which is `hn_pos.ne'`.

```lean
    intro ω x
    unfold L' boosted_majority
    simp only [hsqrt, hblk]
    split_ifs with h
    · -- blk = 0 case: contradicts hn_pos
      omega
    · -- blk ≠ 0: both sides compute the same majority vote
      congr 1; ext j; congr 1; ext i
      simp only [block_extract, finProdFinEquiv]
      congr 1 <;> exact Fin.ext (by omega)
```

**Route C (funext + show)**: If `congr` doesn't peel through correctly:

```lean
    intro ω x
    show (L'.learn (fun i => (ω i, c (ω i)))) x = _
    unfold L'
    simp only [hsqrt, hblk, hn_pos.ne', ↓reduceDIte]
    -- Now goal should be about boosted_majority with matching k
    simp only [boosted_majority, block_extract, finProdFinEquiv]
    -- Fin matching
    congr 1; ext j; congr 1; ext i
    constructor <;> intro h <;> convert h using 2 <;> congr 1 <;> exact Fin.ext (by omega)
```

### Key: the `omega` step

The core equation is `j.val * n + i.val = i.val + n * j.val`. This is `Nat.add_comm` composed with `Nat.mul_comm`. `omega` handles this.

### Contingency

If the `L'` definition has additional `let` bindings that resist `simp`, try:
```lean
    intro ω x
    delta L'  -- or `unfold L'`
    dsimp only
    rw [hsqrt, hblk]
    ...
```

If `dif_pos` / `split_ifs` doesn't work because `blk` is behind too many `let`s, try `show` to rewrite the goal to the expected form, then close with `rfl` or `congr`.

### Estimated LOC: ~15

### Guardrails
- A4/A5 checks
- No new sorry
- Edit only line 985 (may expand to ~15 lines)
- Do not touch any other line
- `lake build` must pass
- `grep -n sorry Separation.lean` shows nothing after completion