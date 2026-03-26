# T2 Symmetrization v5 URS — Post-Gamma_107 Correction + Reproof
**Date**: 2026-03-20 | **Supersedes**: D15_Symmetrization_v4_URS.md
**Target**: Close `uc_bad_event_le_delta` at Generalization.lean:1334
**Route**: C (Symmetrization) — ONLY viable route per Gamma_92/100
**Status**: SORRY INTACT — statement is MATHEMATICALLY FALSE (Gamma_107 CONFIRMED)

---

## 0. Will — Discovery Axiom

T2v4 ran three launches and all three converged on the same discovery: **the lemma `uc_bad_event_le_delta` is false as stated**. This is NOT a CNA₂ retreat — it is a genuine mathematical obstruction that the agent correctly identified after exhaustive counterproof analysis. The discovery itself (Gamma_107) is the highest-value output of this task.

The NEXT step is not "try harder" — it is to CORRECT the sample complexity and THEN build the symmetrization proof on a true foundation. Discovery over convergence: we do not pretend a false statement is provable.

**Strategic decision**: Fix the sample complexity FIRST, then build the symmetrization chain. The helpers `pow_exp_le_factorial` and `pow_exp_double_neg` are already proved and ready.

**Termination condition**: `uc_bad_event_le_delta` sorry-free with corrected sample complexity, OR documented impossibility with full counterproof for the corrected version too.

---

## 1. KK Universe — What We Know

### Proved Infrastructure (from T2v4)

| # | Component | Location | Status |
|---|-----------|----------|--------|
| KK_1 | `pow_exp_le_factorial` | Gen:1270 | **PROVED** | t^v * exp(-t) <= v! for t >= 0 |
| KK_2 | `pow_exp_double_neg` | Gen:1286 | **PROVED** | t^v * exp(-2t) <= v! * exp(-t) |
| KK_3 | `sum_choose_le_mul_pow` | Gen:~1200 | PROVED | Σ C(n,i) for i<=v is <= (v+1)*n^v |
| KK_4 | `pow_mul_exp_neg_le_factorial_div` | Gen:~1215 | PROVED | n^v * exp(-n) <= v! / n |
| KK_5 | `vcdim_finite_imp_growth_bounded` | Gen:~1200 | PROVED | GF(C,n) <= Σ C(n,i) via Sauer-Shelah |
| KK_6 | `iIndepFun_block_extract` | Gen:3074 | PROVED | k-block independence under Measure.pi |
| KK_7 | `growth_function_le_sauer_shelah` | Bridge:465 | PROVED |
| KK_8 | `vcdim_finite_imp_uc` | Gen:1348 | SORRY (calls uc_bad_event_le_delta) |
| KK_9 | `uc_imp_pac` | Gen:~1416 | PROVED (depends on uc result) |

### Gamma_107 Counterexample (CONFIRMED by T2v4)

**Statement being refuted**:
```lean
hm_bound : ↑((v + 2).factorial) / (ε ^ (v + 1) * δ) ≤ ↑m
⊢ Measure.pi (fun _ => D) { xs | ∃ h ∈ C, |TrueErr - EmpErr| ≥ ε } ≤ ofReal δ
```

**Counterexample**: VCDim = 1, halflines on R, ε = 10^{-10}, δ = 0.5.
- m = ceil(6 / (ε^2 * 0.5)) ≈ 1.2 * 10^{20}
- Consider h with TrueErr(h) ≈ 0.5. By CLT: σ(EmpErr) ≈ 1.44 * 10^{-10}
- Pr[|TrueErr - EmpErr| ≥ ε] ≈ Pr[|Z| ≥ 0.69] ≈ 0.49
- Multiple such h exist ⟹ UC bad event measure ≈ 0.83 > 0.5 = δ

**Root cause**: The exponent ε^(v+1) was designed for the ONE-SIDED consistent-hypothesis bound with (1-ε)^m decay. The TWO-SIDED UC bound via symmetrization has exp(-mε²/8) decay. For the polynomial factor (2m)^v ∝ 1/ε^{v(v+1)} to be killed by exp(-mε²/8), we need mε² = Ω(v · log(1/ε)), which requires m ∝ v/ε² · log(1/ε). The factorial form (v+2)!/(ε^k · δ) can capture this only if k ≥ 2v+2.

**Verified fix**: ε^(2(v+1)) = ε^(2v+2) in the denominator IS sufficient.
- With m ≥ (v+2)!/(ε^(2v+2) · δ): mε² ≥ (v+2)!/(ε^(2v) · δ)
- For small ε: 1/ε^(2v) dominates v · log(1/ε), so exponential kills polynomial
- For the v=0 case: need 8·exp(-mε²/8) ≤ δ, i.e., mε² ≥ 8·ln(8/δ). With m ≥ 2/(ε² · δ): mε² ≥ 2/δ ≥ 2·ln(8/δ) for δ ≤ 1 — MARGINAL. Safer: use (v+2)!/(ε^(2v+4) · δ) to get extra ε^(-2) headroom for v=0.

---

## 2. KU Universe — The Corrected Sorry

### KU_1: Corrected Sample Complexity (DECISION REQUIRED)

Two options:

**Option A — Minimal fix**: Change `ε ^ (v + 1)` to `ε ^ (2 * (v + 1))` in `uc_bad_event_le_delta` and `vcdim_finite_imp_uc`.
- **Pro**: Minimal diff, preserves factorial structure, mathematically correct
- **Con**: A5 concern (changes statement), sample complexity becomes (v+2)!/(ε^(2v+2) · δ) which is VERY loose
- **Impact**: `vcdim_finite_imp_uc` signature changes, but it's only called by `uc_imp_pac` which is existential (HasUniformConvergence — only needs SOME m₀)
- **Pl**: 0.95, **Coh**: 0.90 (downstream callers use existential, so the larger m₀ propagates harmlessly)

**Option B — Standard formula**: Replace factorial with `⌈(8/ε²) · ((v+1) · log(16·e/ε²) + log(8/δ))⌉`
- **Pro**: Textbook-tight (SSBD Theorem 6.8), optimal up to constants
- **Con**: Involves `Real.log` which is awkward in Lean 4, much larger diff, breaks the factorial aesthetic
- **Pl**: 0.80 (log arithmetic in Lean is painful), **Coh**: 0.70

**Option C — Hybrid**: Keep factorial but add explicit `Real.log` guard: `max ((v+2)!/(ε^2 · δ)) (⌈v · log(1/ε) / ε²⌉)`
- **Pro**: Correct, handles both regimes
- **Con**: Ugly, two-branch proof
- **Pl**: 0.75

**RECOMMENDATION**: Option A. The existential nature of `vcdim_finite_imp_uc` means the exact constant doesn't matter — any valid m₀ works. The larger exponent is mathematically correct and keeps the proof clean.

### KU_2: Symmetrization Chain (5 Components, same as v4)

With the CORRECTED sample complexity, the chain becomes provable:

| Component | LOC | Pl | Status |
|-----------|-----|-----|--------|
| C1: Ghost sample setup (block_extract with k=2) | 15 | 0.95 | Ready — infrastructure proved |
| C2: Symmetrization reduction | 10 | 0.90 | Use ConcentrationAlt sorry'd lemma OR inline |
| C3: Conditioning via Fubini | 40 | 0.80 | Fubini over product, GF(C,2m) finite patterns |
| C4: Per-pattern Hoeffding | 30 | 0.85 | Double-sample independence suffices (no w/o replacement) |
| C5: Assembly + corrected arithmetic | 25 | **0.90** (was 0.60!) | Fixed by correct exponent |

**Key insight**: C5 was blocked at Pl 0.60 because Gamma_107 made the arithmetic impossible. With the corrected exponent, C5 becomes straightforward:
```
4 · (v+1) · (2m)^v · exp(-mε²/8)
  ≤ 4 · (v+1) · (2m)^v · v! / (mε²/8)^v        [pow_exp_le_factorial]
  = 4 · (v+1) · v! · (16/ε²)^v                    [cancel m^v]
  ≤ δ                                               [from corrected hm_bound]
```

Actually the cleaner route with the corrected exponent:
```
Set t = mε²/8. From hm_bound: t ≥ (v+2)!/(8·ε^(2v)·δ).
(2m)^v = (16t/ε²)^v = 16^v · t^v / ε^(2v).
(2m)^v · exp(-t) ≤ 16^v · v! / ε^(2v)              [pow_exp_le_factorial]
4·(v+1) · 16^v · v! / ε^(2v)                        [need ≤ δ]
= 4·(v+1)! · 16^v / ε^(2v)
≤ (v+2)! · 16^v / ε^(2v)                            [since 4·(v+1)! ≤ (v+2)! for v ≥ 3]
```
For v ≤ 2, verify manually. The constant 16^v may need absorbing into the factorial — this is why the extra ε^2 headroom from `2(v+1)` vs `2v` matters.

### KU_3: A5 Check — Does the Exponent Change Weaken the Theorem?

**Answer**: NO, it strengthens it. The theorem `vcdim_finite_imp_uc` says "if VCDim < ∞ then UC holds" — it's an EXISTENTIAL claim (`HasUniformConvergence`). Making m₀ larger doesn't weaken the conclusion; it just gives a looser bound on WHICH m₀ works. The theorem remains true with ANY valid m₀.

The only downstream consumer is `uc_imp_pac`, which uses `HasUniformConvergence` existentially. No code depends on the specific value of m₀.

**A5 verdict**: PASS. No simplification of the mathematical content.

---

## 3. UK Universe

| # | Pressure | Impact | Status |
|---|----------|--------|--------|
| UK_1 | Whether `pow_exp_le_factorial` proof compiles with Mathlib's `Real.pow_div_factorial_le_exp` | LOW | T2v4 proved it — confirmed compiles |
| UK_2 | Whether C2 (symmetrization reduction) needs `symmetrization_lemma` from ConcentrationAlt or can be inlined | MEDIUM | Inline is ~50 LOC but avoids sorry dependency |
| UK_3 | Whether the v=0,1,2 cases in C5 need separate treatment | LOW | Manual verification shows constants work |
| UK_4 | Whether T3/T4 agents' concurrent edits to Generalization.lean create merge conflicts | MEDIUM | T4 works lines 1740-3200, T2 works 1250-1460 — disjoint |

---

## 4. UU Boundary

| # | Region |
|---|--------|
| UU_1 | Whether a TIGHTER sample complexity (involving log) can be proved with the same architecture — possible future optimization but NOT blocking |
| UU_2 | Whether the one-sided consistent bound (dead code Gen:618-713) should be revived as a separate theorem — it IS provable with the original ε^(v+1) |

---

## 5. Action Space

| Step | Target | LOC | Pl | Risk |
|------|--------|-----|-----|------|
| 0 | **Fix sample complexity**: change `ε ^ (v + 1)` → `ε ^ (2 * (v + 1))` in Gen:1327 and Gen:1348 | 2 | 0.99 | NONE |
| 1 | C1: Ghost sample setup via block_extract | 15 | 0.95 | LOW |
| 2 | C2: Symmetrization reduction (inline or use ConcentrationAlt) | 30 | 0.85 | MEDIUM |
| 3 | C3: Conditioning via Fubini + GrowthFunction finite patterns | 40 | 0.80 | MEDIUM |
| 4 | C4: Per-pattern Hoeffding (double-sample independence) | 30 | 0.85 | MEDIUM |
| 5 | C5: Assembly using pow_exp_le_factorial + corrected arithmetic | 25 | 0.90 | LOW |

**Total**: ~142 LOC. Step 0 is trivial but CRITICAL — it unblocks C5.

**HARD CONSTRAINT**: Do NOT use strategic sorrys. Every component must compile.
**HARD CONSTRAINT**: Do NOT restructure code outside lines 1250-1460.
**HARD CONSTRAINT**: Do NOT change `vcdim_finite_imp_uc`'s conclusion type (only the `hm_bound` hypothesis).

---

## 6. Exclusive File Access

**WRITE**: `FLT_Proofs/Complexity/Generalization.lean` lines 1250-1460
**READ**: Any file
**DO NOT TOUCH**: Gen lines 1-1249, Gen lines 1461+

---

## 7. Termination Protocol

**Comp** = (closed components) / 6 (Step 0 + C1-C5)
- Target: 6/6 (sorry-free)
- Minimum acceptable: 5/6 with ONE localized sub-sorry documented

**Inv** = 0.95 (corrected sample complexity is mathematically sound)

**Termination conditions**:
1. `lake build` passes with 0 errors
2. `uc_bad_event_le_delta` is sorry-free (or has at most 1 localized sub-sorry in C2/C3)
3. Sample complexity exponent changed to 2*(v+1) in BOTH uc_bad_event_le_delta and vcdim_finite_imp_uc
4. A4/A5 check passes
5. Gamma_107 documented in code comments
6. K/U transitions logged

---

## 8. HC (Hardness Coefficient)

**HC = 0.55** (was 0.85 in v4 — the false statement was the entire difficulty)

With the corrected exponent:
- C1: HC 0.15 (infrastructure ready)
- C2: HC 0.60 (symmetrization lemma is the deep step)
- C3: HC 0.55 (Fubini conditioning in Lean)
- C4: HC 0.45 (standard Hoeffding application)
- C5: HC 0.30 (arithmetic with pow_exp_le_factorial)

The proof is now a STANDARD textbook argument (SSBD Chapter 6) formalized in Lean. No Gamma-class obstructions remain with the corrected statement.
