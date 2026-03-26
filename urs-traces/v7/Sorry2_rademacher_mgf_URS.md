# URS: Sorry 2 — rademacher_mgf_bound (CLOSED)

## Statement
```lean
theorem rademacher_mgf_bound {m : ℕ} (hm : 0 < m) (a : Fin m → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (ha : ∀ i, |a i| ≤ c) (t : ℝ) (ht : 0 ≤ t) :
    (1 / (Fintype.card (SignVector m) : ℝ)) *
      ∑ σ : SignVector m, Real.exp (t * ((1 / (m : ℝ)) * ∑ i, a i * boolToSign (σ i))) ≤
    Real.exp (t ^ 2 * c ^ 2 / (2 * m))
```

## Status: CLOSED (Session 7, ~80 LOC)

## Proof Method — 4 Steps
1. **Factor exponential**: `exp(t · (1/m) · ∑ aᵢσᵢ) = ∏ exp(t·aᵢ·σᵢ/m)` via `Real.exp_sum`
2. **Factor expectation**: `∑_σ ∏_i g(σᵢ) = ∏_i ∑_b g(b)` via `Finset.sum_prod_piFinset` + `Fintype.piFinset_univ`
3. **Per-coordinate cosh bound**: `(1/2)(exp(u) + exp(-u)) = cosh(u) ≤ exp(u²/2)` via `Real.cosh_eq` + `cosh_le_exp_sq_half`
4. **Product collapse**: `∏ exp(uᵢ²/2) = exp(∑ uᵢ²/2) ≤ exp(t²c²/(2m))` via `← Real.exp_sum` + `∑ aᵢ² ≤ mc²`

## Key Mathlib Infrastructure
- `Real.exp_sum` at `Mathlib.Analysis.Complex.Exponential:222`
- `Finset.sum_prod_piFinset` at `Mathlib.Algebra.BigOperators.Ring.Finset:158`
- `Fintype.piFinset_univ` at `Mathlib.Data.Fintype.Pi:139`
- `Real.cosh_eq` at `Mathlib.Analysis.Complex.Trigonometric:768`

## Measurements
| Pl | Coh | Inv | Comp |
|----|-----|-----|------|
| 0.99 | 0.95 | 0.95 | 1.0 |

## γ Discoveries
- γ₁₀: Product-over-sum factorization (`sum_prod_piFinset`) requires `piFinset_univ` bridge to convert `piFinset (fun _ => univ) = univ`
- γ₁₁: `Fintype.sum_bool` gives `f false + f true` (not `f true + f false`) — use `add_comm` when matching `cosh_eq`
- γ₁₂: The `(1/2^m) ↔ ∏(1/2)` conversion uses `Finset.prod_const` + `Finset.card_fin` + `← Finset.prod_mul_distrib`
