# URS: Sorry 3 — finite_massart_lemma (CLOSED)

## Statement
```lean
theorem finite_massart_lemma {m : ℕ} (hm : 0 < m) {N : ℕ} (hN : 0 < N)
    (Z : Fin N → SignVector m → ℝ) (σ_param : ℝ) (hσ : 0 < σ_param)
    (h_mgf : ∀ j t, 0 ≤ t →
      (1 / (Fintype.card (SignVector m) : ℝ)) *
        ∑ sv : SignVector m, Real.exp (t * Z j sv) ≤
      Real.exp (t ^ 2 * σ_param ^ 2 / 2)) :
    haveI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
    (1 / (Fintype.card (SignVector m) : ℝ)) *
      ∑ sv : SignVector m, Finset.univ.sup' Finset.univ_nonempty (fun j => Z j sv) ≤
    σ_param * Real.sqrt (2 * Real.log N)
```

## Status: CLOSED (Session 7, ~170 LOC)

## Proof Method — 5 Steps
1. **Jensen**: `exp(t · E[max Z_j]) ≤ E[exp(t · max Z_j)]` via `convexOn_exp` + `ConvexOn.map_sum_le`
2. **Soft-max**: `exp(t · max Z_j) ≤ ∑ exp(t · Z_j)` via `exp_mul_sup'_le_sum` (Sorry 1)
3. **Linearity + MGF**: `E[∑ exp] = ∑ E[exp] ≤ N · exp(t²σ²/2)` via `Finset.sum_comm` + `h_mgf`
4. **Log + divide**: `t · E[max] ≤ log N + t²σ²/2` → `E[max] ≤ log(N)/t + tσ²/2`
5. **Optimize t**: Set `t = √(2 log N)/σ`, get `E[max] ≤ σ√(2 log N)`. N=1 case handled separately.

## Key Mathlib Infrastructure
- `convexOn_exp` at `Mathlib.Analysis.Convex.SpecificFunctions.Basic:63`
- `ConvexOn.map_sum_le` at `Mathlib.Analysis.Convex.Jensen:68`
- `Real.log_exp`, `Real.exp_log` at `Mathlib.Analysis.SpecialFunctions.Log.Basic`

## Measurements
| Pl | Coh | Inv | Comp |
|----|-----|-----|------|
| 0.99 | 0.95 | 0.95 | 1.0 |

## γ Discoveries
- γ₁₃: Jensen for finite averages = `ConvexOn.map_sum_le` with `smul_eq_mul` normalization
- γ₁₄: N=1 edge case needs separate handling (log 1 = 0, t optimization undefined). Proved E[Z₀] ≤ 0 by contradiction from MGF.
- γ₁₅: The `smul` ↔ `*` conversion in `ConvexOn.map_sum_le` requires `simp only [smul_eq_mul]`
