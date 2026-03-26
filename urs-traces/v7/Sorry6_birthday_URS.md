# URS: Sorry 6 — rademacher_lower_bound_on_shattered / Birthday Proof (CLOSED)

## Statement
```
suffices h_birthday : (1 : ℝ) / 2 ≤ (μ A).toReal by linarith
```
Inside `rademacher_lower_bound_on_shattered`. Birthday probability: P[m draws from n ≥ 4m²+1 points are all distinct] ≥ 1/2.

## Status: CLOSED (Session 7, ~180 LOC)

## Proof Method — 3 Phases

### Phase 1: Transfer μ(A) = μ_sub(B) (~15 lines)
- `B = {ys : Fin m → ↥T | Injective ys}`
- `φ⁻¹'(A) = B` via `ext` + `of_comp` / `val_injective.comp`
- `μ A = μ_sub B` via `Measure.map_apply` + preimage equality

### Phase 2: μ_sub(Bᶜ) ≤ 1/2 (~120 lines, the bulk)
- `D_sub {t} = 1/n` via `uniformMeasure` definition + `Measure.count_apply` + `Set.encard_singleton`
- Per-pair collision bound: `μ_sub{ys | ys i = ys j} ≤ 1/n`
  - Decompose as `⋃_t {ys | ys i = t ∧ ys j = t}`
  - Each is cylinder set `Set.pi univ (fun k => if k=i then {t} else if k=j then {t} else univ)`
  - `Measure.pi_pi` gives product = `(1/n)² · 1^{m-2}`
  - Product decomposition via `Finset.mul_prod_erase` (distinguished element FIRST)
  - Sum over n values: `n · (1/n)² = 1/n`
- Union bound: `measure_biUnion_finset_le` over pairs with `p.1 < p.2`
- `pairs.card ≤ m²` via `Finset.card_filter_le` + `Fintype.card_prod` + `Fintype.card_fin`
- `m² · (1/n) ≤ 1/2` since `2m² ≤ n` from `hT_large`

### Phase 3: ENNReal → ℝ transfer (~20 lines)
- `prob_compl_eq_one_sub` gives `μ_sub Bᶜ = 1 - μ_sub B`
- `1/2 ≤ μ_sub B` via `tsub_le_tsub_left` + `ENNReal.sub_sub_cancel`
- `ENNReal.toReal_mono` transfers to ℝ

## Key Mathlib Infrastructure (ALL verified)
| Theorem | Purpose |
|---------|---------|
| `Measure.pi_pi` | Product measure of cylinder sets |
| `measure_biUnion_finset_le` | Finite union bound |
| `ENNReal.mul_inv_cancel` | n * (1/n) = 1 |
| `Finset.mul_prod_erase` | f(a) * ∏(erase a) = ∏ full |
| `prob_compl_eq_one_sub` | P(Aᶜ) = 1 - P(A) |
| `ENNReal.sub_sub_cancel` | a - (a-b) = b |
| `ENNReal.toReal_mono` | Monotonicity of toReal |
| `div_eq_mul_inv` | UNQUALIFIED (not ENNReal.div_eq_mul_inv) |
| `ENNReal.div_le_iff` | x/y ≤ z ↔ x ≤ z*y |

## Measurements
| Pl | Coh | Inv | Comp |
|----|-----|-----|------|
| 0.99 | 0.95 | 0.90 | 1.0 |

## γ Discoveries
- γ₂₂: `ENNReal.div_eq_mul_inv` does NOT exist as qualified name. Use `div_eq_mul_inv` (unqualified) or `ENNReal.div_eq_inv_mul`
- γ₂₃: `Finset.mul_prod_erase` requires distinguished element FIRST. Use `Finset.prod_erase_mul` for opposite order.
- γ₂₄: `μ_sub` defined via `set` doesn't unfold cleanly for `Measure.pi_pi` — need explicit `SigmaFinite` instances via `haveI`
- γ₂₅: The `Measure.count_apply` on `↥T` with `msT := ⊤` requires `MeasurableSpace.measurableSet_top` for the measurability hypothesis
