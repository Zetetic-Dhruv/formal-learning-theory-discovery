---
session: 8
date: 2026-03-25
task_id: S3
target: Hoeffding arithmetic (UK_2)
file: FLT_Proofs/Theorem/Extended.lean
status: closed
---

## S3: UK_2 — Hoeffding arithmetic (line 792)

**File**: `FLT_Proofs/Theorem/Extended.lean`, line 792
**Scope**: Edit ONLY the `sorry` at line 792. Do not touch any other line.
**Dependency**: S1 and S2 must be closed first (file must compile up to this point).

**Goal** (after `apply ENNReal.ofReal_le_ofReal`):
```
⊢ (Fintype.card A : ℝ) * 2 * Real.exp (-2 * ↑m₂ * (min (ε / 4) 1) ^ 2) ≤ δ / 2
```

Where `m₂ = ⌈(8 / ε²) * Real.log (4 * ↑(Fintype.card A) / δ)⌉ + 1`.

**Route**:
1. Since we're in the `ε < 4` branch: `min (ε/4) 1 = ε/4`. Prove via `min_eq_left (le_of_lt (by linarith : ε/4 < 1))`.
2. `(ε/4)² = ε²/16`, so exponent = `-2 * m₂ * ε²/16 = -m₂ * ε²/8`.
3. `m₂ ≥ ⌈(8/ε²) * log(4|A|/δ)⌉ ≥ (8/ε²) * log(4|A|/δ)` (from `Nat.le_ceil`).
4. `m₂ * ε²/8 ≥ log(4|A|/δ)`.
5. `exp(-m₂ * ε²/8) ≤ exp(-log(4|A|/δ)) = δ/(4|A|)` (using `Real.exp_neg`, `Real.exp_log` with positivity).
6. `|A| * 2 * δ/(4|A|) = δ/2`. ✓

**Key Mathlib**: `Nat.le_ceil`, `Real.exp_le_exp_of_le` (or `exp_monotone`), `Real.exp_log`, `Real.exp_neg`.

**Guardrails**: A4/A5. No new sorry. No simplification. Edit only line 792.

---