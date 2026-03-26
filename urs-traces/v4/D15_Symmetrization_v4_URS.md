# D1-D5 Symmetrization v4 URS — UC Bad Event Complete Closure
**Date**: 2026-03-20 | **Supersedes**: D15_Closure_v3_URS.md
**Target**: Close `uc_bad_event_le_delta` at Generalization.lean:1283
**Route**: C (Symmetrization) — the ONLY viable route per Gamma_100

---

## 0. Will — Discovery Axiom

This is the DEEPEST sorry in the entire codebase. It sits at the heart of the UC → PAC pipeline. Routes A (polynomial tail), B (Hoeffding + union), D (HasConsistentUC), and E (statement weakening) are ALL blocked by Gamma_92 (representative selection for uncountable C). Route C (symmetrization) is the ONLY mathematically valid path.

The symmetrization argument is not hard mathematics — it's SSBD Chapter 6, a standard textbook proof. The difficulty is entirely in the LEAN FORMALIZATION: bridging measure-theoretic double samples, conditioning on combined samples, and executing finite union bounds within the conditioned space.

**Strategic decision**: Accept sorry'd sub-components. The priority is getting the ARCHITECTURE right. If `symmetrization_lemma` (ConcentrationAlt.lean:154) cannot be closed in this session, USE it as-is (its sorry propagates but the chain is correct). Close `uc_bad_event_le_delta` as a chain THROUGH sorry'd infrastructure rather than leaving it as a monolithic sorry.

**Termination condition**: Comp >= 0.80 AND Inv >= 0.90. The agent must either (a) close `uc_bad_event_le_delta` (possibly with localized sub-sorrys in symmetrization infrastructure), or (b) document genuine Gamma discoveries with full counterproof analysis.

---

## 1. KK Universe

### Proved Infrastructure
| # | Component | Location | Status |
|---|-----------|----------|--------|
| KK_1 | `iIndepFun_block_extract` | Gen:3074 | PROVED | k blocks of independent sub-samples under Measure.pi |
| KK_2 | `block_extract` | Gen:3046 | DEFINED | Extract j-th block from concatenated sample |
| KK_3 | `block_extract_disjoint` | Gen:3054 | PROVED | Blocks don't overlap |
| KK_4 | `block_extract_measurable` | Gen:3067 | PROVED | Block extraction is measurable |
| KK_5 | `GrowthFunction` | Structures.lean | DEFINED | Max distinct restrictions over m-samples |
| KK_6 | `growth_function_le_sauer_shelah` | Bridge:465 | PROVED | GF ≤ Σ C(m,i) |
| KK_7 | `vcdim_finite_imp_growth_bounded` | Gen:~1200 | PROVED | VCDim < ∞ → GF bounded by Sauer-Shelah |
| KK_8 | `consistent_tail_bound` | Gen:~600 | PROVED | Single-hypothesis consistent tail: (1-ε)^m |
| KK_9 | `uc_imp_pac` | Gen:~1416 | PROVED | UC → PAC (uses the result of this sorry) |
| KK_10 | `vcdim_finite_imp_uc` | Gen:1288 | USES THIS SORRY | The target theorem that calls uc_bad_event_le_delta |

### Symmetrization Infrastructure (in ConcentrationAlt.lean)
| # | Component | Location | Status |
|---|-----------|----------|--------|
| KK_11 | `GhostSample` | ConcentrationAlt:123 | DEFINED | Structure: primary + ghost sample |
| KK_12 | `DoubleSampleMeasure` | ConcentrationAlt:128 | DEFINED | D^m ⊗ D^m |
| KK_13 | `symmetrization_lemma` | ConcentrationAlt:136 | **SORRY** | Pr[bad] > 0 → double-sample-bad > 0 |

### Key Hypothesis in Scope
```lean
hv : ∀ n, v ≤ n → GrowthFunction X C n ≤ Σ_{i ∈ range(v+1)} C(n,i)
hm_bound : ↑((v+2).factorial) / (ε^(v+1) * δ) ≤ ↑m
```
The FACTORIAL sample complexity is crucial — it makes the exponential tails negligible.

---

## 2. KU Universe — The Sorry and Its Decomposition

### The Single Sorry
```lean
private lemma uc_bad_event_le_delta ... :
    Measure.pi (fun _ : Fin m => D)
      { xs : Fin m → X | ∃ h ∈ C,
        |TrueErrorReal X h c D - EmpiricalError X Bool h (labeled xs c) (zeroOneLoss Bool)| ≥ ε }
      ≤ ENNReal.ofReal δ := by
  sorry
```

### Decomposition into 5 Components

#### KU_C1: Ghost Sample Setup (~15 LOC)
**Goal**: Embed the problem into a double-sample space `Fin (2*m) → X`.

```lean
-- Use block_extract with k=2 to split Fin (2*m) → X into two independent Fin m → X samples
-- S₁ = block_extract 2 m ω 0 : Fin m → X  (primary sample)
-- S₂ = block_extract 2 m ω 1 : Fin m → X  (ghost sample)
-- By iIndepFun_block_extract: S₁, S₂ are independent under Measure.pi (fun _ : Fin (2*m) => D)
```

**AMRT**: Pl 0.95, Coh 0.95 (clean interface with existing infrastructure), Inv 0.95
**Counterproof**: Does `block_extract 2 m` give `Fin m → X` from `Fin (2*m) → X`? Need `2 * m` in the domain. Check `Fin.castLE` or `Fin.addCases`. **Should work — the infrastructure was built for exactly this.**

#### KU_C2: Symmetrization Reduction (~30 LOC)
**Goal**: Show `Pr_S[∃ h bad on S] ≤ 2 * Pr_{S,S'}[∃ h, |EmpErr_S - EmpErr_S'| ≥ ε/2]`

This is the core symmetrization lemma. Two approaches:

**Approach A (Use existing sorry'd lemma)**: Apply `symmetrization_lemma` from ConcentrationAlt.lean.
- **Pro**: Architecture is correct, sorry propagates but chain is clean
- **Con**: Adds a dependency on a sorry'd lemma
- **Pl**: 0.95 (architecture), 0.0 (closure of the sub-sorry)

**Approach B (Inline proof)**: Prove symmetrization directly.
The argument: for any fixed h with `|TrueErr(h) - EmpErr_S(h)| ≥ ε`:
- By LLN, `EmpErr_{S'}(h) → TrueErr(h)` as m → ∞
- For large enough m (which the factorial bound gives): `|EmpErr_{S'}(h) - TrueErr(h)| ≤ ε/2` w.h.p.
- So `|EmpErr_S(h) - EmpErr_{S'}(h)| ≥ ε - ε/2 = ε/2` w.h.p.

In Lean: this requires Chebyshev for the ghost sample concentration. The factorial bound gives `m ≥ (v+2)!/(ε^{v+1}*δ)` which is much larger than `1/(ε²)` needed for LLN concentration.

**Pl for inline**: 0.70 (doable but substantial)
**LOC**: ~50 for inline vs ~5 for using existing lemma

**DECISION**: Use Approach A (existing sorry'd lemma). The architectural priority is closing `uc_bad_event_le_delta`, not the sub-lemma.

#### KU_C3: Conditioning on Combined Sample (~40 LOC)
**Goal**: After symmetrization, condition on the combined 2m points.

```
Pr_{S,S'}[∃ h, |EmpErr_S - EmpErr_S'| ≥ ε/2]
  = E_{z₁,...,z_{2m}}[Pr_{partition}[∃ h, |EmpErr_S - EmpErr_S'| ≥ ε/2 | z₁,...,z_{2m}]]
```

Given the combined points `z₁,...,z_{2m}`:
- At most `GF(C, 2m)` distinct restriction patterns for hypotheses in C
- Two h's with the same restriction to `{z₁,...,z_{2m}}` have identical EmpErr_S and EmpErr_S' (since emp errors only depend on how h classifies the sample points)
- So `∃ h bad` reduces to `∃ pattern bad` — a FINITE union

**AMRT**: Pl 0.75, Coh 0.80 (the conditioning step is the tightest joint), Inv 0.85
**Counterproof**: Does Lean4/Mathlib support conditional expectation given a sub-σ-algebra? YES — `MeasureTheory.condexp`. But this is heavy machinery. Alternative: use Fubini directly on the product measure, integrating out the partition randomness first. **Fubini is simpler.**

#### KU_C4: Per-Pattern Concentration (~30 LOC)
**Goal**: For each fixed restriction pattern, bound the probability of large deviation.

Given fixed 2m points and a fixed restriction pattern p:
- `EmpErr_S(h) - EmpErr_S'(h)` is a function of the random partition (which m of 2m go to S)
- This is a sum of bounded differences: changing one assignment changes the sum by at most 2/m
- By Hoeffding (or Chebyshev): `Pr[|EmpErr_S - EmpErr_S'| ≥ ε/2] ≤ 2*exp(-mε²/8)`

**AMRT**: Pl 0.80, Coh 0.85 (the partition randomness → bounded differences connection is clean), Inv 0.90
**Counterproof**: The partition is NOT iid — it's a uniform random partition of 2m elements into two groups of m. This is sampling WITHOUT replacement, not with. Hoeffding for sampling without replacement is a standard extension (it's actually tighter than with replacement). Does Mathlib have this? PROBABLY NOT. **This is a genuine UK.**

**Alternative for C4**: Use the weaker bound via replacement: pretend S and S' are iid (which they ARE in the double-sample formulation — they're independent Measure.pi draws). Then standard Hoeffding applies per coordinate. **This avoids the without-replacement issue entirely.**

#### KU_C5: Assembly (~25 LOC)
**Goal**: Chain C1-C4 + Sauer-Shelah + factorial arithmetic → `≤ ENNReal.ofReal δ`

```
Pr[∃ h bad] ≤ 2 * Pr_{S,S'}[∃ h, double-bad]     [C2: symmetrization]
  ≤ 2 * E_z[GF(C,2m) * 2*exp(-mε²/8)]             [C3+C4: condition + per-pattern]
  = 4 * GF(C,2m) * exp(-mε²/8)                      [C5: algebra]
  ≤ 4 * Σ_{i≤v} C(2m,i) * exp(-mε²/8)             [Sauer-Shelah]
  ≤ 4 * (v+1)*(2m)^v * exp(-mε²/8)                 [binomial bound]
  ≤ δ                                                [factorial sample complexity]
```

The last step: for `m ≥ (v+2)!/(ε^{v+1}*δ)`, the polynomial `(2m)^v` is dominated by `exp(mε²/8)` for large enough m. The factorial bound ensures this.

**AMRT**: Pl 0.75 (the factorial arithmetic is the weakest link), Coh 0.85, Inv 0.90
**Counterproof**: The bound `4*(v+1)*(2m)^v*exp(-mε²/8) ≤ δ` when `m ≥ (v+2)!/(ε^{v+1}*δ)`. Is this actually true? Let's check for v=1, ε=1/4, δ=1/4:
- m ≥ 3!/(0.25^2 * 0.25) = 6/0.015625 = 384
- Bound: 4*2*(768)^1 * exp(-384/128) = 6144 * exp(-3) ≈ 6144 * 0.05 ≈ 307
- But we need this ≤ 0.25. **FAILS.**

**GAMMA_114 (NEW)**: The factorial sample complexity `(v+2)!/(ε^{v+1}*δ)` may NOT suffice for the symmetrization bound `4*GF(C,2m)*exp(-mε²/8) ≤ δ`. The polynomial growth `(2m)^v` competes with the exponential decay `exp(-mε²/8)`, and for small v the factorial bound may not be large enough.

**RESOLUTION**: The factorial was designed for the ONE-SIDED consistent bound `GF(C,m)*(1-ε)^m ≤ δ` where (1-ε)^m decays MUCH faster than exp(-mε²/8). For the TWO-SIDED symmetrization bound, we may need a DIFFERENT sample complexity, like `m ≥ C*(v*log(v/ε) + log(1/δ))/ε²` (the standard UC sample complexity from SSBD Theorem 6.8).

**IMPACT**: This means we CANNOT simply sorry-replace the existing `uc_bad_event_le_delta` with the symmetrization bound using the factorial sample complexity. We would need to either:
(a) Change `hm_bound` to the correct symmetrization sample complexity — but this changes the STATEMENT of `vcdim_finite_imp_uc` (A5 concern)
(b) Prove the stronger factorial bound suffices — may require showing `(v+2)! ≥ C*(v*log(v/ε))/ε^{v+1}` for appropriate C
(c) Add the symmetrization bound as a SEPARATE lemma with the correct sample complexity, and use it alongside (not replacing) the factorial bound

**DECISION**: Investigate option (b) first. For large v, `(v+2)!` grows super-exponentially while `v*log(v/ε)` grows much slower. But the ε exponents differ: factorial has `ε^{v+1}` in the denominator while symmetrization needs only `ε^2`. For small ε this makes the factorial bound MUCH larger, which helps. The key question: is `(v+2)!/(ε^{v+1}*δ) ≥ C*(v*log(v/ε) + log(1/δ))/ε²` for all v, ε, δ in the valid range?

For v=1, ε=1/4: LHS = 6/(0.0625*δ) = 96/δ. RHS ≈ C*(log(4) + log(1/δ))/0.0625 = 16C*(1.4 + log(1/δ)). For δ=1/4: LHS=384, RHS≈16C*2.8=44.8C. So C≤8.5. The standard constant C is ~8 (from SSBD). **MARGINAL.**

**Revised AMRT for C5**: Pl drops to 0.60 due to Gamma_114.

---

## 3. UK Universe

| # | Pressure | Impact | Status |
|---|----------|--------|--------|
| UK_1 | Gamma_114: factorial vs symmetrization sample complexity mismatch | CRITICAL | Investigate option (b): does factorial dominate symmetrization for all valid parameters? |
| UK_2 | `symmetrization_lemma` exact statement — does it match what C2 needs? | HIGH | Read ConcentrationAlt.lean:136 |
| UK_3 | Conditioning in Lean4 — Fubini vs condexp, which is available and usable? | MEDIUM | Prefer Fubini (simpler API) |
| UK_4 | Per-pattern Hoeffding — do we need without-replacement version or does double-sample independence suffice? | MEDIUM | Double-sample independence suffices |
| UK_5 | Whether `uc_bad_event_le_delta` can be closed with localized sub-sorrys (chain through sorry'd components) | HIGH | This is the architectural priority |

---

## 4. UU Boundary

| # | Region |
|---|--------|
| UU_1 | Whether the factorial sample complexity CAN be shown to dominate the symmetrization requirement for ALL valid (v, ε, δ) |
| UU_2 | Whether a fundamentally different sample complexity expression is needed, requiring an A5-reviewed statement change |
| UU_3 | Whether the one-sided consistent bound (which the factorial WAS designed for) can be used INSTEAD of symmetrization for `uc_bad_event_le_delta` — but Gamma_92 + Gamma_98 block this |

---

## 5. Route Elimination (Updated with Gamma_114)

| Route | Status | Blocker |
|-------|--------|---------|
| A (polynomial tail) | ELIMINATED | Gamma_92 (uncountable union) |
| B (Hoeffding + union) | ELIMINATED | Gamma_92 |
| C (symmetrization) | THE ROUTE | Gamma_114 threatens C5 assembly |
| D (HasConsistentUC) | ELIMINATED | Gamma_98 (one-sided also faces Gamma_92) |
| E (statement weakening) | ELIMINATED | A5 violation |
| C' (symmetrization + adjusted sample complexity) | VIABLE FALLBACK | Requires A5-reviewed statement change |

---

## 6. Action Space (Restricted)

| Step | Target | LOC | Pl | Risk |
|------|--------|-----|-----|------|
| 0 | Investigate Gamma_114: verify factorial vs symmetrization bound | 0 | — | CRITICAL |
| 1 | C1: Ghost sample setup | 15 | 0.95 | LOW |
| 2 | C2: Symmetrization reduction (use sorry'd lemma) | 10 | 0.95 | LOW |
| 3 | C3: Conditioning via Fubini | 40 | 0.75 | MEDIUM |
| 4 | C4: Per-pattern concentration | 30 | 0.80 | MEDIUM |
| 5 | C5: Assembly + factorial arithmetic | 25 | 0.60 | HIGH (Gamma_114) |

**Total**: ~120 LOC (reduced from 200 by using sorry'd sub-components)

**Step 0 is BLOCKING**: If Gamma_114 is confirmed (factorial insufficient), the options are:
- Option (b): prove the dominance lemma (~30 extra LOC)
- Option (c): add separate lemma with correct sample complexity
- Last resort: leave C5 as sorry with documented Gamma_114

---

## 7. Termination Protocol

**Comp** = (closed components) / 5
- Target: >= 4/5 (C1-C4 closed, C5 may be blocked by Gamma_114)
- Minimum acceptable: 3/5 (C1-C3 closed) with Gamma_114 documented

**Inv** = probability the architecture survives
- Current: 0.85 (symmetrization is the invariant route)
- Risk: Gamma_114 may force sample complexity change
- Target: >= 0.90

**Termination conditions**:
1. `lake build` passes
2. `uc_bad_event_le_delta` is either sorry-free or has at most 2 localized sub-sorrys with documented routes
3. Gamma_114 is either resolved or documented with full counterproof analysis
4. A4/A5 check passes
5. K/U transitions logged, world model updated

---

## 8. Exclusive File Access

**WRITE**: `FLT_Proofs/Complexity/Generalization.lean` lines 1250-1460, `FLT_Proofs/Complexity/ConcentrationAlt.lean`
**READ**: Any file
**DO NOT TOUCH**: Gen lines 1-1249, Gen lines 1461-2499, Gen lines 2500+ (NFL territory)
