# URS: Sorry 5 — vcdim_bounds_rademacher_quantitative (CLOSED)

## Statement
```lean
theorem vcdim_bounds_rademacher_quantitative (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) (D : MeasureTheory.Measure X) (m : ℕ) (hm : 0 < m)
    (d : ℕ) (hd : VCDim X C = ↑d) (hd_pos : 0 < d) (hdm : d ≤ m)
    [IsProbabilityMeasure (Measure.pi (fun _ : Fin m => D))] :
    RademacherComplexity X C D m ≤ Real.sqrt (2 * d * Real.log (Real.exp 1 * ↑m / d) / m)
```

## Status: CLOSED (Session 7, ~250 LOC)

## Constant Change (2m/d → em/d)
- Changed from `Real.log (2 * ↑m / d)` to `Real.log (Real.exp 1 * ↑m / d)`
- Updated `analytical_log_sqrt_bound` statement + proof (simplified: `log(et) = 1 + log(t)`)
- Updated `vcdim_finite_imp_rademacher_vanishing` references
- Matches SSBD, Mohri, Kakade-Tewari standard form

## Proof Method — 5 Steps (Chain A, NO symmetrization)

### Key Discovery: Chain A vs Chain B
- **Chain A** (this theorem): VCDim → GF bound → Massart → Rademacher bound. Uses ONLY Sauer-Shelah + Massart. No symmetrization. No McDiarmid. No ghost samples.
- **Chain B** (Generalization.lean): Rademacher → generalization gap. Uses symmetrization + McDiarmid. DIFFERENT proof, DIFFERENT file.
- Predecessor conflated these chains. Session 7 separated them.

### Steps:
1. **Restriction collapse (sSup → Finset.sup')**: Define `dpats : Finset (Fin m → Bool)` via `Finset.univ.filter`. Show `sSup {corr(h,σ,xs) | h ∈ C} ≤ dpats.sup' corr_pat(·,σ)` since corr factors through restriction.
2. **EmpRad ≤ sup' form**: Replace each sSup with sup' via `Finset.sum_le_sum`.
3. **Apply finite_massart_lemma**: Index dpats by `Fin N` via `Fintype.equivFin`. Each Z_j satisfies MGF bound with `σ_param = 1/√m` via `rademacher_mgf_bound` (coefficients = `boolToSign`, `c = 1`).
4. **Bound N via Sauer-Shelah**: `dpats.card ≤ (em/d)^d` via injection into restriction set + `sauer_shelah_exp_bound`.
5. **Combine**: `(1/√m) · √(2 log N) ≤ (1/√m) · √(2d · log(em/d)) = √(2d·log(em/d)/m) = B`.

## Measurements
| Pl | Coh | Inv | Comp |
|----|-----|-----|------|
| 0.99 | 0.90 | 0.90 | 1.0 |

## γ Discoveries
- γ₇ (CRITICAL): VCDim→Rad does NOT need symmetrization. This unblocked T5 from T2 dependency.
- γ₁₉: `Fintype.equivFin` on `{ p // p ∈ dpats }` provides the `Fin N ≃ dpats` bridge for `finite_massart_lemma`
- γ₂₀: The sSup → sup' bridge uses `≤` (not `=`) to simplify — only upper bound direction needed
- γ₂₁: `dpats.card` bounded via injection into restriction set on `range(xs)`, then Sauer-Shelah
