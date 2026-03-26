# URS: Sorry 4 — sauer_shelah_exp_bound (CLOSED)

## Statement
```lean
theorem sauer_shelah_exp_bound {X : Type u} (C : ConceptClass X Bool)
    (d m : ℕ) (hd : 0 < d) (hdm : d ≤ m) (hvc : VCDim X C = ↑d) :
    GrowthFunction X C m ≤ (Real.exp 1 * m / d) ^ d
```

## Status: CLOSED (Session 7, ~480 LOC including 3 helper lemmas)

## Proof Method — 2 Sub-problems

### Sub-problem A: GF(C,m) ≤ ∑_{i≤d} C(m,i)
- `ncard_restrictions_le_sum_choose_set`: Per-S bound for Set-based C on Fintype ↥S
  - Converts restriction set to Finset family using `classical` + `Finset.univ.filter`
  - Applies Mathlib `card_le_card_shatterer` + `card_shatterer_le_sum_vcDim`
  - Shows vcDim of restricted family ≤ d by lifting shattered sets back to X
- `growth_function_le_sum_choose_set`: Lifts per-S bound to GrowthFunction via `csSup_le'`

### Sub-problem B: ∑_{i≤d} C(m,i) ≤ (em/d)^d
- `sum_choose_le_exp_pow`: Exponential tilting technique
  - Multiplies by `(d/m)^i · (m/d)^i = 1` weights
  - Uses `(m/d)^i ≤ (m/d)^d` since `m/d ≥ 1`
  - Extends partial sum to full binomial sum `(1+d/m)^m`
  - Applies `(1+x) ≤ exp(x)` iterated to get `(1+d/m)^m ≤ e^d`
  - Combines: `≤ (m/d)^d · e^d = (em/d)^d`

## Key Insight (from prior art)
- Google formal-ml: Sauer-Shelah via Finset induction on S (Lean 3)
- Their Set↔Finset approach: filter `S.powerset` against set-level predicate using `classical`
- Our approach: work on `↥S` (Fintype) for each S, apply Mathlib shatterer bound
- The exponential corollary `(em/d)^d` was NOT in any prior art — proved from scratch

## Measurements
| Pl | Coh | Inv | Comp |
|----|-----|-----|------|
| 0.99 | 0.90 | 0.95 | 1.0 |

## γ Discoveries
- γ₁₆: Set↔Finset gap resolved by working on `↥S` (always Fintype) + `classical` for decidability
- γ₁₇: `Finset.mem_filter` under `classical` wraps predicate in `Decidable.decide` — use `exact` with explicit terms rather than `rcases` on membership proofs
- γ₁₈: The binomial→exponential bound `∑ C(m,i) ≤ (em/d)^d` requires ~100 lines of careful ℕ↔ℝ casting
