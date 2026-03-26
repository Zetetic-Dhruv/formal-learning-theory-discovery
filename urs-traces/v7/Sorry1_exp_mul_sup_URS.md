# URS: Sorry 1 — exp_mul_sup'_le_sum (CLOSED)

## Statement
```lean
theorem exp_mul_sup'_le_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (hs : s.Nonempty)
    (f : ι → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (t * s.sup' hs f) ≤ ∑ i ∈ s, Real.exp (t * f i)
```

## Status: CLOSED (Session 7, 7 LOC)

## Proof Method
- `Finset.exists_mem_eq_sup'` gives witness `i₀ ∈ s` with `f i₀ = sup'`
- `calc` block: `exp(t * sup') = exp(t * f i₀) ≤ ∑ exp(t * f i)` by `Finset.single_le_sum`
- Required explicit `(f := fun i => Real.exp (t * f i))` annotation for elaborator

## Measurements
| Pl | Coh | Inv | Comp |
|----|-----|-----|------|
| 0.99 | 0.95 | 1.0 | 1.0 |

## γ Discoveries
- γ₈: `Finset.single_le_sum` needs explicit function annotation — elaborator can't infer composed functions
- γ₉: `rw [← hmax]` rewrite direction confusion — use `calc` instead for clarity
