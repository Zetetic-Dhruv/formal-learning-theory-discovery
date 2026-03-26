# Discovery Task: vc_characterization (#62)

**KEYSTONE** — resolving this unlocks #65, #56, #57, and all downstream PAC theory.

## Target

```lean
theorem vc_characterization (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) :
    PACLearnable X C ↔ VCDim X C < ⊤ := by sorry
```

**File:** `LimitsOfLearning/Theorem/PAC.lean`, line 30
**Cluster:** C2_vc_characterization
**Dependencies upstream:** #27 (GrowthFunction), #63 (sauer_shelah)
**Dependencies downstream:** #65 (fundamental_theorem), #56, #57 (separations)

## World Model

### Forward direction: VCDim X C < ⊤ → PACLearnable X C

**Method:** M₂ (Probabilistic) + M₃ (Combinatorial)

**Proof sketch (textbook: Shalev-Shwartz & Ben-David, Theorem 6.7):**
1. Assume `VCDim X C = d` for some `d : ℕ`
2. By Sauer-Shelah (#63): GrowthFunction X C m ≤ (em/d)^d for m ≥ d
3. By uniform convergence + finite growth function:
   For sample size m ≥ (8/ε²)(d·ln(2em/d) + ln(4/δ)):
   Pr_S[∃ h ∈ C : |gen_err(h) - emp_err(h)| > ε] ≤ δ
4. ERM on sample S returns h with emp_err(h) = 0 (realizable case)
5. Therefore gen_err(h) ≤ ε with probability ≥ 1-δ
6. Construct the BatchLearner as ERM with sample size mf(ε,δ) = ⌈(8/ε²)(d·ln(2em/d) + ln(4/δ))⌉

**Lean4 substeps:**
```
1. unfold PACLearnable
2. use ERM X Bool C     -- the learner (already defined, #34 must be resolved first)
3. use fun ε δ => ⌈(8/ε²)(d·ln(2e·⌈8/ε²⌉/d) + ln(4/δ))⌉  -- sample complexity
4. intro ε δ hε hδ D hD c hc
5. -- need: uniform convergence lemma
6. -- need: Sauer-Shelah growth bound
7. -- need: ERM achieves zero empirical error in realizable case
```

**Missing lemmas (KU):**
- Uniform convergence from bounded growth function (KEY — this is the substantive step)
- ERM achieves zero training error on realizable samples
- Sauer-Shelah growth bound in usable form (depends on #63)
- Ceil arithmetic lemmas for sample complexity

**Mathlib availability (UK):**
- `MeasureTheory.Measure.prod` — product measure for i.i.d. samples
- lean-rademacher: `uniform_deviation_tail_bound_countable_of_pos` — may provide uniform convergence
- `Real.log`, `Real.exp` — logarithm and exponential
- `Int.ceil` — ceiling function

### Backward direction: PACLearnable X C → VCDim X C < ⊤

**Method:** M₂ (Probabilistic) — contrapositive via No Free Lunch

**Proof sketch:**
1. Contrapositive: VCDim X C = ⊤ → ¬PACLearnable X C
2. VCDim = ⊤ means: for all d, there exists S with |S| ≥ d that C shatters
3. For any learner L and sample size m: construct distribution D supported on a shattered set of size 2m
4. By shattering: every labeling of S is realized by some c ∈ C
5. Learner sees m points; there are 2^m consistent labelings of the remaining m points
6. With probability ≥ 1/2 over random labeling of unseen points, learner makes error > 1/4
7. Therefore no learner achieves error < 1/4 with probability > 3/4 for sample size m — for ALL m

**Lean4 substeps:**
```
1. rw [show (PACLearnable X C ↔ VCDim X C < ⊤) ↔ ... from iff_def]
2. constructor
3. -- forward: done above
4. -- backward: by_contra h; push_neg at h; -- h : VCDim X C = ⊤
5. -- need: NFL-style argument restricted to shattered set
6. -- need: probability bound on random labeling
```

**Missing lemmas (KU):**
- Restricted NFL theorem on shattered sets
- Probability of error on unseen points under uniform labeling
- Sample size lower bound arithmetic

## Ignorance Profile

| Quadrant | Content |
|----------|---------|
| KK | Theorem statement types correctly. Both directions known in textbooks. ERM defined (#34 pending). |
| KU | 1. Can lean-rademacher's uniform convergence substitute for our own? 2. Does the backward direction need explicit product measure construction? 3. Exact constant in sample complexity formula — which formulation matches our types? |
| UK | lean-rademacher `uniform_deviation_tail_bound_countable_of_pos` — inspect whether it gives what we need |
| UU | Whether the realizable→agnostic reduction (via symmetrization) is needed or can be bypassed |

## Constraints

- **Requires #27 (GrowthFunction body) and #63 (sauer_shelah) BEFORE forward direction**
- **Requires #34 (ERM.learn body) for the existential witness**
- M₂+M₃ composition required — Sauer-Shelah (combinatorial) feeds into concentration (probabilistic)
- Measure-theoretic infrastructure: need product measure for i.i.d. samples

## Estimated Difficulty

**Forward:** Hard (requires substantial measure-theoretic formalization, ~200-400 lines)
**Backward:** Medium (NFL-style argument, ~100-200 lines)
**Total:** ~300-600 lines of Lean4 proof
**Method confidence:** High — both directions well-understood, just need careful formalization
