---
session: 8
date: 2026-03-25
task_id: S4
target: Final calc step (UK_7) / Nat.unpair cast
file: FLT_Proofs/Theorem/Extended.lean
status: closed
---

## S4: UK_7 — Final calc step (line 857)

**File**: `FLT_Proofs/Theorem/Extended.lean`, line 857
**Scope**: Edit ONLY the `sorry` at line 857. Do not touch any other line.
**Dependency**: S1, S2, S3 must all be closed first.

**Available facts**:
- `hGoodFull_sub_goal : GoodFull ⊆ {xs | D {...} ≤ ENNReal.ofReal ε}` (line ~712)
- `h_transport : π(D)(GoodFull) = (μ₁.prod μ₂)(GoodPair)` (line ~841)
- `hGoodPair_bound : (μ₁.prod μ₂)(GoodPair) ≥ ENNReal.ofReal (1 - δ)` (line ~814)

**Route**: This is a 3-line `calc`:
```lean
calc MeasureTheory.Measure.pi (fun _ : Fin (Nat.pair m₁ m₂) => D) {xs | ...}
    ≥ MeasureTheory.Measure.pi (fun _ : Fin (Nat.pair m₁ m₂) => D) GoodFull :=
      (MeasureTheory.Measure.pi _).mono hGoodFull_sub_goal
  _ = (μ₁.prod μ₂) GoodPair := h_transport
  _ ≥ ENNReal.ofReal (1 - δ) := hGoodPair_bound
```

If the goal set doesn't syntactically match `hGoodFull_sub_goal`'s target, use `convert` or `exact le_trans hGoodPair_bound (h_transport ▸ (MeasureTheory.Measure.pi _).mono hGoodFull_sub_goal)`. The `simp_rw [Nat.unpair_pair]` at line 561 should have already rewritten binder types.

**Guardrails**: A4/A5. No new sorry. No simplification. Edit only line 857.

---