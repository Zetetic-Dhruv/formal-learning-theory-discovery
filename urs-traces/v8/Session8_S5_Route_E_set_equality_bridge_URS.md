---
session: 8
date: 2026-03-25
task_id: S5
target: Route E set-equality bridge for Nat.unpair binder cast
file: FLT_Proofs/Theorem/Extended.lean
status: closed
---

## S5: Route E — Set-equality bridge for Nat.unpair binder cast (line 1027)

**File**: `FLT_Proofs/Theorem/Extended.lean`, line 1027
**Scope**: Replace the `sorry` at line 1027. May add code immediately before line 1027 (after line 1026). Do not touch any other line.
**Dependency**: S1–S3 closed. Build passes. This is the last FP5 sorry.

### 0. Situation

`h_combined` (lines 1014–1026) proves:
```
π(D) ExplicitSet ≥ ofReal(1 - δ)
```
where `ExplicitSet` uses `Fin m₁` and `Fin m₂` types.

The goal is:
```
π(D) GoalSet ≥ ofReal(1 - δ)
```
where `GoalSet` uses `Fin (Nat.unpair (Nat.pair m₁ m₂)).1` and `Fin (Nat.unpair (Nat.pair m₁ m₂)).2` types — from the learner's `let` bindings at lines 541–542.

These sets are propositionally equal (`Nat.unpair_pair`) but not definitionally. The S4 agent failed (63 edits, 87 builds, 1 hour) because it tried to `convert` the whole inequality instead of rewriting the event set.

### 1. Root Cause

The learner definition (lines 540–548) binds:
```lean
let m₁ := (Nat.unpair m).1
let m₂ := (Nat.unpair m).2
```

After `case mf` specializes `m := Nat.pair m₁ m₂`, the goal retains `Nat.unpair (Nat.pair m₁ m₂)` inside lambda binder types. `simp_rw [Nat.unpair_pair]` at line 562 cannot penetrate these binders. The proof's `set m₁` (line 559) creates a different binding that shadows but doesn't unify with the learner's `m₁`.

### 2. Route E — Set-equality bridge

**Do NOT use**: `convert h_combined`, `conv` into binder types, restructuring the learner, or trying to make `simp_rw` rewrite the whole goal globally. The S4 agent exhausted all of those.

**The fix**: Rewrite the **event set**, not the whole inequality.

1. Define `GoalSet` — name the goal's set with its exact `Nat.unpair` types
2. Define `ExplicitSet` — name `h_combined`'s set with `Fin m₁` / `Fin m₂` types
3. Prove `h_goalset_eq : GoalSet = ExplicitSet` by `ext xs; simp [Nat.unpair_pair]`
4. `change` the goal to use `GoalSet`
5. `rw [h_goalset_eq]`
6. `exact h_combined`

**Why `simp [Nat.unpair_pair]` works here**: After `ext xs`, we're proving a proposition `xs ∈ GoalSet ↔ xs ∈ ExplicitSet`. Inside that proposition, the `let`-bound terms are concrete — `simp` can rewrite `Nat.unpair (Nat.pair m₁ m₂)` to `(m₁, m₂)` through the nested expressions. This is much easier for Lean than rewriting under lambda binder types in the goal.

### 3. Contingency

If `simp [GoalSet, ExplicitSet, Nat.unpair_pair]` gets stuck (likely on proof-irrelevant Fin constructors), use:
```lean
ext xs
constructor <;> intro hx <;>
  simpa [GoalSet, ExplicitSet, Nat.unpair_pair] using hx
```

If that sticks too, extract the hypothesis function:
```lean
ext xs
change (D {x | F_goal xs x ≠ c x} ≤ ENNReal.ofReal ε) ↔
       (D {x | F_explicit xs x ≠ c x} ≤ ENNReal.ofReal ε)
have h_fun : F_goal xs = F_explicit xs := by
  funext x; simp [F_goal, F_explicit, Nat.unpair_pair]
simpa [h_fun]
```

### 4. Practical notes

To spell `GoalSet` correctly: the agent must read the exact goal type. Either:
- Use `set_option pp.all false` + a deliberate type error to get Lean to print the goal
- Or read the type mismatch from the earlier `exact h_combined` attempt (already captured in the conversation — the expected type uses `Nat.unpair (Nat.pair (mf_adv (ε / 2) (δ / 2)) (⌈1 / (2 * min (ε / 4) 1 ^ 2) * Real.log (4 * ↑(Fintype.card A) / δ)⌉₊ + 1))`)

The `ExplicitSet` is already the set in `h_combined` (lines 1015–1024). The agent can name it directly from those lines.

### 5. Anti-pattern warning

The S4 agent's failure mode: 63 edits cycling `convert`, `congr`, `ext`, `funext`, `rfl`, `simp only [m₁]`, `maxHeartbeats 800000` — never diagnosing that the unit of rewriting is the set, not the inequality.

The agent MUST:
1. Read the goal type first (one diagnostic build)
2. Write `GoalSet` matching the goal exactly
3. Write `ExplicitSet` matching `h_combined` exactly
4. Prove equality by `ext xs; simp [Nat.unpair_pair]`
5. Bridge and close

If `h_goalset_eq` doesn't close after 3 attempts at the `simp` line, STOP and report the exact stuck goal. Do not loop.

### 6. Termination

- `grep -n sorry FLT_Proofs/Theorem/Extended.lean` shows ONLY line 39 (`bhmz_middle_branch`)
- `lake build` passes with 0 errors
- A4: no trivially-true sorrys
- A5: theorem statement UNCHANGED

### 7. Guardrails

- A4/A5 checks after every edit
- MUST close the sorry. No new sorry acceptable.
- Do not simplify. Follow the given ignorance structure.
- Edit only at/around line 1027. Do not touch lines 1–1026 or 1028+.