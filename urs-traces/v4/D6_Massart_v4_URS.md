# D6 Massart v4 URS — Deep Closure of Rademacher.lean Helper Chain
**Date**: 2026-03-20 | **Supersedes**: D6_Massart_v3_URS.md (all content carried forward)
**Target**: Close 4 remaining sorrys in the Massart helper chain (Rademacher.lean:397-483)
**Predecessor discoveries**: `cosh_le_exp_sq_half` CLOSED via `Real.cosh_le_exp_half_sq`. `Fintype.prod_sum` identified for product factorization. `exp_mul_sup'_le_sum` PROVED.

---

## 0. Will — Discovery Axiom

The Massart chain is a 4-stage pipeline crossing 3 paradigm joints (Set→Combinatorics→Probability→Analysis). Each sorry is independently valuable. Attack `rademacher_mgf_bound` FIRST — it's the most mathematically rich and de-risks the entire chain. Do NOT decompose further — CLOSE. If `rademacher_mgf_bound` resists after 3 genuine attempts, document the exact Lean API obstacle as a Gamma and move to `finite_massart_lemma`.

**Termination condition**: Comp >= 0.95 AND Inv >= 0.95. The agent MUST close at least 3 of 4 sorrys, or document genuine Gamma discoveries for each unclosed sorry with full counterproof analysis.

---

## 1. KK Universe — Complete Inventory

### Proved in Codebase
| # | Component | Status | Exact Content |
|---|-----------|--------|---------------|
| KK_1 | `exp_mul_sup'_le_sum` | PROVED | `exp(t * sup') ≤ Σ exp(t * f_i)` for t ≥ 0 |
| KK_2 | `cosh_le_exp_sq_half` | PROVED | `cosh(x) ≤ exp(x²/2)` via `Real.cosh_le_exp_half_sq` |
| KK_3 | `empiricalRademacherComplexity_le_one` | PROVED | EmpRad ≤ 1 |
| KK_4 | `growth_function_le_sauer_shelah` | PROVED | GF(C,m) ≤ Σ_{i≤d} C(m,i) |
| KK_5 | `sum_choose_le_mul_pow` | PROVED | Σ_{i≤d} C(m,i) ≤ (d+1)*m^d |
| KK_6 | `card_restrict_le_sauer_shelah_bound` | PROVED | |restrictions| ≤ Sauer-Shelah |
| KK_7 | `rademacherCorrelation` | DEFINED | (1/m) * Σ_i boolToSign(σ_i) * boolToSign(h(xs_i)) |
| KK_8 | `SignVector m` = `Fin m → Bool` | DEFINED | Alias, Fintype instance |
| KK_9 | `boolToSign` | DEFINED | true ↦ 1, false ↦ -1 |
| KK_10 | `boolToSign_abs_eq_one` | PROVED | |boolToSign b| = 1 |

### Discovered in Mathlib (by predecessor agent)
| # | Component | Location | Verified? |
|---|-----------|----------|-----------|
| KK_11 | `Real.cosh_le_exp_half_sq` | Mathlib.Analysis.SpecialFunctions.Trigonometric.Series | YES — used in cosh closure |
| KK_12 | `Fintype.prod_sum` | Mathlib.Algebra.BigOperators.Finprod | YES — `∏ i, ∑ j, f i j = ∑ x, ∏ i, f i (x i)` |
| KK_13 | `Real.exp_add` | Mathlib.Analysis.SpecialFunctions.ExpDeriv | YES — `exp(a+b) = exp(a)*exp(b)` |
| KK_14 | `Finset.sum_congr` | Core | YES — rewrite under sum |
| KK_15 | `Finset.prod_le_prod` | Mathlib | YES — monotone product |
| KK_16 | `Real.exp_le_exp` | Mathlib | YES — exp monotone |
| KK_17 | `Real.log_le_log` | Mathlib | YES — log monotone |
| KK_18 | `Finset.card_fin` | Core | YES — |Fin m| = m |

---

## 2. KU Universe — The 4 Sorrys with Full AMRT

### KU_1: `rademacher_mgf_bound` (line 413) — SUB-GAUSSIANITY
**Goal**: `(1/2^m) * Σ_σ exp(t * Z(σ)) ≤ exp(t²/(2m))` where `Z(σ) = (1/m) * Σ_i a_i * boolToSign(σ_i)`, `|a_i| ≤ 1`

#### AMRT
- **Pl**: 0.92 — all 7 steps have identified Mathlib APIs
- **Coh**: 0.88 — the `SignVector m ↔ Fin m → Bool` bridge and `Fintype.prod_sum` instantiation are the tightest joints
- **Inv**: 0.95 — the proof uses only stable Mathlib APIs
- **Comp**: 0.0 (not started)

#### 7-Step Proof Route (the ONLY viable route — all alternatives eliminated in v3)

**Step 1** (~5 LOC): Rewrite `exp(t * (1/m) * Σ_i a_i * boolToSign(σ_i))` as `exp(Σ_i (t/m) * a_i * boolToSign(σ_i))`.
```lean
have h_sum : t * ((1 / (m : ℝ)) * ∑ i, a i * boolToSign (σ i))
    = ∑ i : Fin m, (t / m) * a i * boolToSign (σ i) := by ring_nf
simp_rw [h_sum]
```

**Step 2** (~5 LOC): Rewrite `exp(Σ_i x_i) = Π_i exp(x_i)` via `Real.exp_sum` or `Finset.prod_exp`.
```lean
rw [Real.exp_sum]  -- or: simp_rw [← Real.exp_sum]
-- Goal becomes: (1/2^m) * Σ_σ Π_i exp((t/m)*a_i*boolToSign(σ_i)) ≤ exp(t²/(2m))
```
**Counterproof**: Does `Real.exp_sum` exist? Search for `exp_sum` in Mathlib. If not, use `Finset.prod_eq_prod_iff_exp` or fold via `exp_add`. **CHECK AT RUNTIME.**

**Step 3** (~8 LOC): Apply `Fintype.prod_sum` (BACKWARDS) to get:
```
Σ_{σ : Fin m → Bool} Π_i g(i, σ_i) = Π_i Σ_{b : Bool} g(i, b)
```
where `g(i, b) = exp((t/m) * a_i * boolToSign(b))`.
```lean
rw [← Fintype.prod_sum]  -- KEY STEP
-- Goal: (1/2^m) * Π_i Σ_{b : Bool} exp((t/m)*a_i*boolToSign(b)) ≤ exp(t²/(2m))
```
**Counterproof**: `Fintype.prod_sum` requires the index types to be `Fintype`. `Fin m` and `Bool` are both `Fintype`. The function `g` must be from `Fin m → Bool → ℝ`. **No counterproof — this is clean.**

**Step 4** (~5 LOC): Rewrite `Σ_{b : Bool} exp(x * boolToSign(b)) = exp(x) + exp(-x)` for each coordinate.
```lean
simp only [Bool.forall_bool, boolToSign]
-- Each factor: exp(x) + exp(-x) where x = (t/m)*a_i
-- Divide by 2: ((exp(x) + exp(-x))/2) = cosh(x)
```

**Step 5** (~3 LOC): Apply `cosh_le_exp_sq_half` (KK_2) to each factor.
```lean
-- Each factor: (exp(x)+exp(-x))/2 ≤ exp(x²/2) where x = t*a_i/m
apply Finset.prod_le_prod (fun i _ => ...)
intro i _; exact cosh_le_exp_sq_half (t * a i / m)
```

**Step 6** (~5 LOC): Rewrite `Π_i exp(x_i²/2) = exp(Σ_i x_i²/2)` using `Real.exp_sum` again.
```lean
rw [← Real.exp_sum]
-- Goal: exp(Σ_i (t*a_i/m)²/2) ≤ exp(t²/(2m))
apply Real.exp_le_exp.mpr
```

**Step 7** (~5 LOC): Bound `Σ_i (t*a_i/m)² = (t/m)² * Σ_i a_i² ≤ (t/m)² * m = t²/m`.
```lean
-- Σ_i (t*a_i/m)²/2 = (t/m)²/2 * Σ_i a_i² ≤ (t/m)²/2 * m = t²/(2m)
calc ∑ i, (t * a i / m) ^ 2 / 2
    = (t / m) ^ 2 / 2 * ∑ i, a i ^ 2 := by ring_nf
  _ ≤ (t / m) ^ 2 / 2 * m := by
      apply mul_le_mul_of_nonneg_left
      · calc ∑ i, a i ^ 2 ≤ ∑ i : Fin m, (1 : ℝ) := by
            apply Finset.sum_le_sum; intro i _; exact sq_le_one_of_abs_le_one (ha i)
          _ = m := by simp [Finset.card_fin]
      · positivity
  _ = t ^ 2 / (2 * m) := by ring
```

**Counterproof search for entire route**:
- CP_1: `Fintype.prod_sum` direction — we need `Σ Π = Π Σ` but Lean states it as `Π Σ = Σ Π`. Need `.symm`. **Manageable.**
- CP_2: The `(1/2^m)` normalization distributes into the product as `Π_i (1/2)`. Need `Finset.prod_const` and `Fintype.card_fun`. **Standard.**
- CP_3: `ring_nf` may not simplify `Σ_i (t * a_i / m)^2 / 2` to the needed form. May need manual `simp` + `ring`. **Low risk.**
**No fatal counterproof found. Route is viable.**

### KU_2: `finite_massart_lemma` (line 440) — EXPECTED MAXIMUM BOUND
**Goal**: `(1/2^m) * Σ_σ sup'(s, Z_σ) ≤ σ * √(2*log|s|)` given sub-Gaussian MGF bounds

#### AMRT
- **Pl**: 0.85 — the proof requires finite Jensen which may need manual construction
- **Coh**: 0.90 — clean interface with KU_1 (σ parameter) and downstream (EmpRad bound)
- **Inv**: 0.90 — stable if formulated for finite sums
- **Comp**: 0.0

#### Proof Route (Zhang's method adapted for finite sums)

**Step 1** (~3 LOC): Set `t₀ = √(2*log(N))/σ` where `N = s.card`.
```lean
set N := s.card
set t₀ := Real.sqrt (2 * Real.log N) / σ_param
have ht₀_pos : 0 < t₀ := div_pos (Real.sqrt_pos.mpr (by positivity)) hσ
```

**Step 2** (~12 LOC): Finite Jensen: `(1/|Ω|) * Σ X ≤ (1/t) * log((1/|Ω|) * Σ exp(tX))` for t > 0.
This is the HARDEST step. It follows from convexity of exp:
```
exp((1/|Ω|) * Σ X) ≤ (1/|Ω|) * Σ exp(X)    [Jensen for finite sums]
(1/|Ω|) * Σ X ≤ log((1/|Ω|) * Σ exp(X))     [take log, noting exp ∘ log ≤ id for exp]
(1/|Ω|) * Σ tX ≤ log((1/|Ω|) * Σ exp(tX))   [apply to tX]
(1/|Ω|) * Σ X ≤ (1/t) * log(...)              [divide by t > 0]
```
**Lean formalization**: Jensen for finite sums = `Finset.inner_mul_le_norm_mul_norm` or `ConvexOn.sum_card_smul_le_sum` or prove inline using `Real.exp_le_exp` + `Finset.sum_le_sum`.

**Counterproof for Step 2**: Does Mathlib have finite Jensen for exp?
- `ConvexOn.sum_card_smul_le_sum`: checks convexity of exp on finite set — MAY exist
- If not: prove from `StrictConvexOn.inner_smul_sum_le` or inline (~12 LOC)
**This is the riskiest step. Pl: 0.75 for this step alone.**

**Step 3** (~5 LOC): Apply `exp_mul_sup'_le_sum` (KK_1 — PROVED!):
```lean
-- exp(t₀ * sup') ≤ Σ exp(t₀ * Z_i)
-- So: (1/|Ω|) * Σ exp(t₀ * sup') ≤ (1/|Ω|) * Σ_σ Σ_i exp(t₀ * Z_i(σ))
```

**Step 4** (~5 LOC): Swap sums via `Finset.sum_comm`:
```lean
-- Σ_σ Σ_i exp(t₀*Z_i(σ)) = Σ_i Σ_σ exp(t₀*Z_i(σ))
rw [Finset.sum_comm]
```

**Step 5** (~5 LOC): Apply sub-Gaussian bound `h_subG`:
```lean
-- (1/|Ω|) * Σ_σ exp(t₀*Z_i(σ)) ≤ exp(t₀²*σ²/2) for each i
-- So: Σ_i exp(t₀²σ²/2) = N * exp(t₀²σ²/2)
```

**Step 6** (~8 LOC): Algebra: `(1/t₀) * log(N * exp(t₀²σ²/2)) = (1/t₀) * (log N + t₀²σ²/2)`.
Substitute `t₀ = √(2*log N)/σ`:
```
(1/t₀) * (log N + t₀²σ²/2) = σ/√(2*log N) * (log N + (2*log N/σ²)*σ²/2)
                              = σ/√(2*log N) * (log N + log N)
                              = σ/√(2*log N) * 2*log N
                              = σ * √(2*log N)
                              = σ * √(2*log |s|)    ✓
```
**Lean**: `ring_nf` or manual `field_simp` + `Real.sqrt_div_self`.

**Counterproof search**:
- CP_1: Step 2 (finite Jensen) is the bottleneck. If no Mathlib lemma, need ~12 LOC inline.
- CP_2: `Real.log_mul` and `Real.log_exp` needed for Step 6. Both exist in Mathlib.
- CP_3: The `2 ≤ s.card` hypothesis ensures `log(s.card) > 0` (since `log 2 > 0`). Need `Real.log_pos`.
**Riskiest step: Step 2. Everything else is standard.**

### KU_3: `empRad_le_sqrt_vc_log` (line 483) — CHAIN ASSEMBLY
**Goal**: Chain restriction collapse + Massart + Sauer-Shelah + log arithmetic

#### AMRT
- **Pl**: 0.80 — depends on KU_1 and KU_2 being closed
- **Coh**: 0.85 — the sSup→Finset.sup' bridge is the tightest joint
- **Inv**: 0.90
- **Comp**: 0.0

#### Proof Route (~30 LOC)

**Step 1** (~10 LOC): Convert EmpRad's sSup to a Finset.sup' over restriction patterns.
The key: for fixed xs, the set `{r | ∃ h ∈ C, r = |corr(h,σ,xs)|}` has at most `GF(C,m)` elements (by restriction collapse). Convert to `Finset.sup'` on `(restrictConceptClass C xs).toFinset`.

**Step 2** (~5 LOC): Apply `finite_massart_lemma` with `σ = 1/√m`, `s = restriction patterns`.

**Step 3** (~5 LOC): Bound `|s| ≤ GF(C,m) ≤ Σ_{i≤d} C(m,i)` via `h_growth`.

**Step 4** (~10 LOC): Log arithmetic: `log(Σ_{i≤d} C(m,i)) ≤ log((d+1)*m^d) ≤ d*log(2m/d)`.
Use `sum_choose_le_mul_pow` (KK_5) for first inequality. The second: `(d+1)*m^d ≤ (2m/d)^d` for `m ≥ d ≥ 1`.

**Counterproof**:
- CP_1: The sSup→Finset.sup' conversion requires showing the sSup IS attained (the set is finite and bounded). On `Fin m → Bool` (finite), this is automatic.
- CP_2: The `2 ≤ |s|` requirement of `finite_massart_lemma`: need `|restrictions| ≥ 2`. This holds when `d ≥ 1` (at least 2 distinct patterns). The hypothesis `hd_pos : 0 < d` gives this.
- CP_3: Log arithmetic `log((d+1)*m^d) ≤ d*log(2m/d)`: need `(d+1)*m^d ≤ (2m/d)^d`. For d=1: `2m ≤ 2m` ✓. For d≥2 and m≥d: `(d+1) ≤ (2/d)^d * ... ` — NEED CAREFUL CHECK. This may require `(d+1) ≤ 2^d` (true for d ≥ 1) and `m^d ≤ (m/d)^d * d^d` — need `d^d ≤ m^d`... this gets complicated.
**CP_3 is a real risk. The log bound may need a weaker version. Pl drops to 0.75 for this step.**

### KU_4: `empRad_le_of_restriction_count` (line 456) — INTERMEDIATE
**Goal**: EmpRad ≤ √(2*log(N)/m) given per-σ sSup bounds

#### AMRT
- **Pl**: 0.90 — straightforward averaging
- **Coh**: 0.95 — may be bypassed entirely if KU_3 is proved directly
- **Inv**: 0.85 — may become dead code
- **Comp**: 0.0

**DECISION**: Skip this sorry. If KU_3 chains directly through KU_2 without needing this intermediate, it becomes dead code. Only attack if KU_3 needs it as a stepping stone.

---

## 3. UK Universe — Pressures

| # | Pressure | Impact | Status |
|---|----------|--------|--------|
| UK_1 | Does `Real.exp_sum` exist as a named Mathlib lemma? | MEDIUM for KU_1 Step 2 | Check at runtime. Fallback: `Finset.prod_exp` or fold via `exp_add`. |
| UK_2 | Finite Jensen for exp — does Mathlib have `ConvexOn.sum_card_smul_le_sum` or equivalent? | HIGH for KU_2 Step 2 | Check at runtime. Fallback: prove inline from `ConvexOn` definition (~12 LOC). |
| UK_3 | The log bound `log(Σ C(m,i)) ≤ d*log(2m/d)` — is it true for all m ≥ d ≥ 1? | HIGH for KU_3 Step 4 | Counterproof search found potential issue for d=2, m=2. CHECK NUMERICALLY. |
| UK_4 | `Fintype.prod_sum` — exact direction and universe polymorphism | LOW | The `.symm` should work. |

---

## 4. UU Boundary

| # | Region |
|---|--------|
| UU_1 | Whether `polyrith` or `norm_num` can close the algebraic steps in KU_2 Step 6 without manual calc |
| UU_2 | Whether there's a Mathlib lemma combining Sauer-Shelah + log bound into a single step |

---

## 5. Counterproof Pathways — Route Elimination

### Alternative Route: Use `HasSubgaussianMGF` structure (Route B from v3): ELIMINATED
Would add ~70 LOC of NNReal casting overhead. The finite-sum approach avoids this entirely. Coh drops from 0.88 to 0.75 at the NNReal↔R joint.

### Alternative Route: Port Zhang verbatim with Measure.pi (Route A from v3): ELIMINATED
Requires the counting-measure-to-Measure.pi bridge (UK_10 from v3). The finite-sum formulation eliminates this bridge entirely. Coh rises from 0.85 to 0.98 at the measure joint.

### Alternative Route: Cauchy-Schwarz generalization (Route C): FATAL
Second-moment methods give O(√N) not O(√(log N)). Gamma_101 confirms exponential moments are NECESSARY for d ≥ 2.

**ONLY Route A-finite survives. This is the invariant route.**

---

## 6. Action Space (Restricted)

| Step | Target | LOC | Pl | Dependencies |
|------|--------|-----|----|----|
| 1 | Close `rademacher_mgf_bound` (KU_1) | ~35 | 0.92 | KK_2, KK_12 |
| 2 | Close `finite_massart_lemma` (KU_2) | ~40 | 0.85 | KU_1, KK_1 |
| 3 | Close `empRad_le_sqrt_vc_log` (KU_3) | ~30 | 0.80 | KU_2, KK_4, KK_5 |
| 4 | Skip `empRad_le_of_restriction_count` (KU_4) unless needed | 0-15 | — | — |
| 5 | Verify main theorem sorry is closed | 0 | — | KU_3 |

**Total**: ~105 LOC. Sequential dependency: 1 → 2 → 3 → 5.

---

## 7. Termination Protocol

**Comp** = (closed sorrys) / (total sorrys in Massart section)
- KK: 2/6 closed (exp_mul_sup'_le_sum, cosh_le_exp_sq_half)
- Target: 5/6 (KU_4 may be skipped)

**Inv** = probability proof survives future changes
- Current: 0.90 (finite-sum route is robust)
- Target: >= 0.95

**Termination conditions (ALL must hold)**:
1. `lake build` passes
2. At least 3 of 4 actionable sorrys closed (KU_1, KU_2, KU_3 mandatory; KU_4 optional)
3. The main theorem `vcdim_bounds_rademacher_quantitative` either has zero sorry or one localized sorry with documented Gamma
4. A4/A5 check passes
5. K/U transitions logged for ALL closed sorrys

---

## 8. Exclusive File Access

**WRITE**: `FLT_Proofs/Complexity/Rademacher.lean` lines 379-546 ONLY
**READ**: Any file
**DO NOT TOUCH**: Lines 1-378, lines 547+ (Birthday section)
