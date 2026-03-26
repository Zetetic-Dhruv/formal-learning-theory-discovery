# ESChebyshev v2 URS — Parallel UC Route Complete Closure
**Date**: 2026-03-20 | **Supersedes**: v1 (implicit in Extended_Closure_URS.md)
**Target**: Close all chain sorrys in ESChebyshev.lean. Accept 2 axiom-sorrys (efronStein_general, mcdiarmid_via_zhang).
**File**: `FLT_Proofs/Complexity/ESChebyshev.lean` — EXCLUSIVE access, no conflicts

---

## 0. Will — Discovery Axiom

The ESChebyshev file is a PARALLEL UC route for finite/countable hypothesis classes. It does NOT replace the symmetrization route (which handles uncountable C). Its value: (1) demonstrates the Efron-Stein + Chebyshev proof technique in Lean4, (2) provides UC for the common case where C is finite, (3) exercises infrastructure (bounded differences, variance bounds) that may be reused.

The Gamma_92 obstruction (uncountable union bound) is resolved by adding `[Fintype (↥C)]`. This is A5-valid because the general case is handled by symmetrization in Generalization.lean.

Attack from the bottom of the chain upward: `efronStein_bounded_diff` → `chebyshev_single_hypothesis` → `chebyshev_union_bound` → `chebyshev_uc`.

**Termination condition**: Comp >= 0.90 AND Inv >= 0.85. All CHAIN sorrys closed. The 2 axiom-sorrys (`efronStein_general`, `mcdiarmid_via_zhang`) remain as documented dependencies.

---

## 1. File Structure and Sorry Map

```
ESChebyshev.lean (11 sorrys total):
├── mcdiarmid_via_zhang (line 84)           — AXIOM SORRY (Zhang bridge)
├── efronStein_general (line 101)           — AXIOM SORRY (ANOVA decomposition)
├── mcdiarmid_inequality (line 112)         — CHAIN: depends on mcdiarmid_via_zhang
├── efronStein_bounded_diff (line ~155)     — CHAIN: depends on efronStein_general [KU_1]
├── chebyshev_single_hypothesis (line ~199) — CHAIN: depends on efronStein_bounded_diff [KU_2]
├── chebyshev_union_bound (line ~251)       — CHAIN: depends on chebyshev_single [KU_3, GAMMA_92]
├── chebyshev_uc (line ~329)               — CHAIN: depends on chebyshev_union_bound [KU_4]
└── symmetrization_lemma (line ~154)        — SEPARATE: in ConcentrationAlt section
```

**Strategy**: Close KU_1 → KU_2 → KU_3 → KU_4. Leave axiom sorrys and mcdiarmid_inequality.

---

## 2. KK Universe

| # | Component | Status | Role |
|---|-----------|--------|------|
| KK_1 | `EmpiricalError` | DEFINED | (1/m) * Σ loss(h(x_i), y_i) |
| KK_2 | `TrueErrorReal` | DEFINED | ∫ loss(h(x), c(x)) dD |
| KK_3 | `zeroOneLoss` | DEFINED | 0-1 loss function |
| KK_4 | `HasUniformConvergence` | DEFINED | ∀ ε δ, ∃ m₀, ∀ D c m ≥ m₀, Pr[∃ h bad] ≤ δ |
| KK_5 | `GrowthFunction` | DEFINED | max over m-samples of distinct restrictions |
| KK_6 | Chebyshev's inequality | IN MATHLIB | `meas_ge_le_variance_div_sq` or `ProbabilityTheory.variance_le_of_sq_le` |
| KK_7 | `Finset.sum_le_sum` | IN MATHLIB | Monotone finite sum |
| KK_8 | `measure_biUnion_finset_le` | IN MATHLIB | Union bound |
| KK_9 | `Fintype.card` | IN MATHLIB | Cardinality of finite type |

---

## 3. KU Universe — The 4 Chain Sorrys

### KU_1: `efronStein_bounded_diff` (line ~155)
**Statement (expected)**:
```lean
theorem efronStein_bounded_diff {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {f : (Fin m → Ω) → ℝ}
    (c : Fin m → ℝ) (hbd : ∀ i xs xs', |f xs - f (Function.update xs i (xs' i))| ≤ c i)
    (hf_int : Integrable f (Measure.pi (fun _ => μ))) :
    Var[f, Measure.pi (fun _ => μ)] ≤ ∑ i, c i ^ 2
```

#### AMRT
- **Pl**: 0.80 — chains through `efronStein_general` (sorry'd axiom)
- **Coh**: 0.85 — the bounded differences bound on each summand is standard
- **Inv**: 0.90 — the statement is invariant

#### Proof Route (~15 LOC)
```lean
-- Chain: Var(f) ≤ Σ_i E[(f - E^{(i)}f)²]   [efronStein_general]
--              ≤ Σ_i c_i²                     [bounded differences bound each term]
calc Var[f, μ_prod]
    ≤ ∑ i, ∫ x, (f x - conditionalExpectation_minus_i f μ i x) ^ 2 ∂μ_prod
      := efronStein_general f μ hf_int
  _ ≤ ∑ i, c i ^ 2 := by
      apply Finset.sum_le_sum; intro i _
      -- E[(f - E^{(i)}f)²] ≤ c_i² because:
      -- |f(x) - E^{(i)}f(x)| ≤ sup_{x_i'} |f(x) - f(x[i↦x_i'])| ≤ c_i
      -- So (f - E^{(i)}f)² ≤ c_i² a.e.
      -- Integrate: E[...] ≤ c_i²
      sorry -- ~10 LOC: bounded differences → L² bound per summand
```

**Counterproof**: The inner sorry requires showing `E^{(i)}f(x)` (conditional expectation given all coordinates except i) satisfies `|f(x) - E^{(i)}f(x)| ≤ c_i`. This follows because `E^{(i)}f(x)` is an average of `f(x[i↦x_i'])` over `x_i'`, and each `|f(x) - f(x[i↦x_i'])| ≤ c_i`. By triangle inequality and convexity of | · |: `|f(x) - avg(f(x[i↦·]))| ≤ avg(|f(x) - f(x[i↦·])|) ≤ c_i`. **Viable.**

**BUT**: This requires `efronStein_general` to be stated with the right conditional expectation type. READ THE FILE to verify the exact statement matches.

### KU_2: `chebyshev_single_hypothesis` (line ~199)
**Statement (expected)**:
```lean
theorem chebyshev_single_hypothesis {X : Type*} [MeasurableSpace X]
    (D : Measure X) [IsProbabilityMeasure D] (h c : Concept X Bool)
    (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 < ε) :
    Measure.pi (fun _ : Fin m => D)
      {xs | |TrueErrorReal X h c D - EmpiricalError X Bool h (labeled xs c) (zeroOneLoss Bool)| ≥ ε}
    ≤ ENNReal.ofReal (1 / (m * ε ^ 2))
```

#### AMRT
- **Pl**: 0.85 — specializes efronStein_bounded_diff + Chebyshev
- **Coh**: 0.90 — clean interface
- **Inv**: 0.90

#### Proof Route (~20 LOC)
```lean
-- Specialize efronStein_bounded_diff with:
-- f(xs) = EmpiricalError (1/m * Σ loss(h(x_i), c(x_i)))
-- c_i = 1/m (changing one sample changes EmpErr by at most 1/m)
-- Var(f) ≤ Σ (1/m)² = m * (1/m²) = 1/m
-- By Chebyshev: Pr[|f - Ef| ≥ ε] ≤ Var(f)/ε² ≤ 1/(m*ε²)
have hvar : Var[emp_err_fun, μ_prod] ≤ 1 / m := by
  calc Var[...] ≤ ∑ i : Fin m, (1 / m : ℝ) ^ 2 := efronStein_bounded_diff (fun _ => 1/m) ...
    _ = m * (1/m)^2 := by simp [Finset.sum_const, Finset.card_fin]
    _ = 1 / m := by ring
exact chebyshev_inequality emp_err_fun hvar ε hε
```

**Counterproof**: Does Mathlib have Chebyshev's inequality in the form `Pr[|X - EX| ≥ ε] ≤ Var/ε²`?
- `ProbabilityTheory.meas_ge_le_variance_div_sq` — CHECK existence and exact type
- If not, use Markov's inequality (`meas_ge_le_mul_integral`) on `(X - EX)²`
**Fallback exists. Pl: 0.80.**

### KU_3: `chebyshev_union_bound` (line ~251) — GAMMA_92 RESOLUTION
**Statement (MODIFIED — add [Fintype (↥C)])**:
```lean
theorem chebyshev_union_bound {X : Type*} [MeasurableSpace X]
    (D : Measure X) [IsProbabilityMeasure D]
    (C : ConceptClass X Bool) [Fintype (↥C)]  -- ADDED: resolves Gamma_92
    (c : Concept X Bool) (m : ℕ) (hm : 0 < m) (ε : ℝ) (hε : 0 < ε) :
    Measure.pi (fun _ : Fin m => D)
      {xs | ∃ h ∈ C, |TrueErrorReal X h c D - EmpErr ...| ≥ ε}
    ≤ ENNReal.ofReal (Fintype.card (↥C) / (m * ε ^ 2))
```

#### AMRT
- **Pl**: 0.90 — with `[Fintype (↥C)]`, the union bound is standard
- **Coh**: 0.85 — the `[Fintype (↥C)]` addition must propagate to `chebyshev_uc`
- **Inv**: 0.85 — narrower than the symmetrization route but correct for finite C

#### A5 Analysis of `[Fintype (↥C)]` Addition
- **Is this simplification?** YES, it narrows the hypothesis class to finite.
- **Is it A5-valid?** YES, because:
  1. The general (uncountable C) case is handled by symmetrization in Generalization.lean
  2. ESChebyshev.lean is explicitly documented as a PARALLEL route for finite C
  3. The finite case is the one where Efron-Stein + Chebyshev is the natural proof
  4. Adding `[Fintype]` makes the statement TRUE and PROVABLE without changing the mathematical content
- **Gamma_92 confirmation**: Without `[Fintype]`, the union bound over uncountable C is invalid. This is not a proof difficulty — it's a mathematical impossibility. The narrowing is forced by the mathematics.

#### Proof Route (~20 LOC)
```lean
-- {xs | ∃ h ∈ C, bad(h)} ⊆ ⋃ h : ↥C, {xs | bad(h.val)}
-- By measure_biUnion_finset_le on Finset.univ (using [Fintype]):
calc μ_prod {xs | ∃ h ∈ C, ...}
    ≤ μ_prod (⋃ h : ↥C, {xs | ...}) := measure_mono (set inclusion)
  _ ≤ ∑ h : ↥C, μ_prod {xs | ...} := measure_iUnion_le _  -- or measure_biUnion_finset_le
  _ ≤ ∑ h : ↥C, ENNReal.ofReal (1/(m*ε²)) := by
      apply Finset.sum_le_sum; intro h _
      exact chebyshev_single_hypothesis D h.val c m hm ε hε
  _ = Fintype.card (↥C) * ENNReal.ofReal (1/(m*ε²)) := by simp [Finset.sum_const]
  _ = ENNReal.ofReal (Fintype.card (↥C) / (m * ε²)) := by ...
```

**Counterproof**: `measure_iUnion_le` requires countable union. With `[Fintype (↥C)]`, the union is finite, which is countable. **No issue.**

### KU_4: `chebyshev_uc` (line ~329) — ASSEMBLY
**Statement (MODIFIED — add [Fintype (↥C)])**:
```lean
theorem chebyshev_uc {X : Type*} [MeasurableSpace X]
    (C : ConceptClass X Bool) [Fintype (↥C)]
    (hC : VCDim X C < ⊤) :
    HasUniformConvergence X C
```

#### AMRT
- **Pl**: 0.85 — chains through chebyshev_union_bound + arithmetic
- **Coh**: 0.80 — the `HasUniformConvergence` definition requires ∀ ε δ, ∃ m₀. Need to construct m₀.
- **Inv**: 0.85

#### Proof Route (~15 LOC)
```lean
intro ε δ hε hδ
-- Choose m₀ = ⌈|C| / (δ * ε²)⌉
use Nat.ceil (Fintype.card (↥C) / (δ * ε ^ 2))
intro D hD c m hm
-- For m ≥ m₀: Fintype.card C / (m * ε²) ≤ δ
-- By chebyshev_union_bound: Pr[bad] ≤ |C|/(m*ε²) ≤ δ
-- So Pr[good] ≥ 1 - δ
```

---

## 4. UK Universe

| # | Pressure | Impact |
|---|----------|--------|
| UK_1 | Exact statement of `efronStein_general` — does it use conditional expectation? What type? | HIGH for KU_1 |
| UK_2 | Whether `EmpiricalError` is stated as a function of `xs : Fin m → X` or as a random variable | MEDIUM for KU_2 |
| UK_3 | Whether `mcdiarmid_inequality` (line 112) should also be closed while we're here | LOW — skip |
| UK_4 | Whether `Fintype (↥C)` compiles — `C : ConceptClass X Bool = Set (Concept X Bool)` may not have a coercion to Type that admits Fintype | HIGH — CHECK |

**UK_4 is critical**: If `↥C` (coercion of `C : Set (X → Bool)` to a subtype) doesn't admit `[Fintype]` cleanly, we may need `(hfin : Set.Finite C)` instead and use `hfin.toFinset`.

---

## 5. UU Boundary

| # | Region |
|---|--------|
| UU_1 | Whether the ESChebyshev file, once closed, provides any value not already covered by the main Generalization.lean UC proof |
| UU_2 | Whether the `efronStein_general` sorry can be closed by porting Zhang's Efron-Stein proof (~60 LOC) |

---

## 6. Route Elimination

### Route B (Close efronStein_general too): ELIMINATED for this task
~200 LOC of ANOVA decomposition. Out of scope. The chain sorrys are independently valuable.

### Route C (Skip [Fintype], use GrowthFunction): ELIMINATED
Gamma_92 blocks this. The GrowthFunction union bound requires symmetrization for uncountable C.

### Route D (Rewrite to use Rademacher complexity): ELIMINATED
Would duplicate work from Rademacher.lean. Not the purpose of this file.

---

## 7. Action Space (Restricted)

| Step | Target | LOC | Pl |
|------|--------|-----|-----|
| 1 | Read exact statements of all sorrys | 0 | — |
| 2 | Add `[Fintype (↥C)]` or `(hfin : Set.Finite C)` to relevant theorems | 5 | 0.90 |
| 3 | Close `efronStein_bounded_diff` (KU_1) | 15 | 0.80 |
| 4 | Close `chebyshev_single_hypothesis` (KU_2) | 20 | 0.85 |
| 5 | Close `chebyshev_union_bound` (KU_3) | 20 | 0.90 |
| 6 | Close `chebyshev_uc` (KU_4) | 15 | 0.85 |

**Total**: ~75 LOC.

---

## 8. Termination Protocol

**Comp** = (closed chain sorrys) / 4 chain sorrys
- Target: 4/4 = 1.0

**Inv** = 0.85 (the [Fintype] addition is correct but narrows scope)

**Axiom sorrys remaining**: `efronStein_general`, `mcdiarmid_via_zhang` — these are ACCEPTABLE and documented.

**Termination conditions**:
1. `lake build` passes
2. All 4 chain sorrys closed
3. The 2 axiom sorrys remain with clear documentation
4. A4/A5 check passes (especially the [Fintype] addition)
5. `chebyshev_uc` type-checks with `HasUniformConvergence`

---

## 9. Exclusive File Access

**WRITE**: `FLT_Proofs/Complexity/ESChebyshev.lean` — FULL exclusive access
**READ**: Any file
**DO NOT TOUCH**: Any other .lean file
