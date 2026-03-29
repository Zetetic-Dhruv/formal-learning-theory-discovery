---
session: 8
date: 2026-03-29
title: "HC-Measurability Conjecture: Interpolation Failure and the Borel/Analytic Gap"
type: research-urs
status: open
domain: descriptive-set-theory × statistical-learning-theory × information-theory
principal_investigator: Dhruv Gupta
---

# HC-Measurability Research URS

## 0. The Conjecture (stated precisely)

**Conjecture (HC-Measurability).** Let X be a Polish space with vocabulary partition (S, P₁, P₂). Let C be a concept class over X.

1. If HC(C) = 0 (interpolation holds, fibers are rectangular), then the uniform convergence bad event `{xs | ∃ h ∈ C, gap(h, xs) ≥ ε}` is MeasurableSet (Borel).
2. If HC(C) > 0 (interpolation fails, some fiber is non-rectangular), then the bad event may be only NullMeasurableSet (universally measurable but not Borel).
3. The separation is strict: there exists a concept class with HC > 0 whose bad event is analytic (Σ₁¹) but not Borel.

**Origin**: Discovered during Session 8 of a Lean4 formalization of the Fundamental Theorem of Statistical Learning. The formalization forced the weakening MeasurableSet → NullMeasurableSet for uncountable concept classes. The question "when is this weakening strict?" led to connecting HC (from Gupta's KU-Factored Abduction monograph) with descriptive set theory.

---

## 1. KK — What Is Known

### 1.1 Descriptive Set Theory

- **Suslin's theorem (1917)**: The projection of a Borel set in a product of Polish spaces is analytic (Σ₁¹).
- **Suslin separation**: Analytic sets in uncountable Polish spaces need not be Borel. The inclusion Borel ⊊ Σ₁¹ is strict for any uncountable Polish space.
- **Measurability hierarchy**: NullMeasurableSet (under any probability measure) ⊇ universally measurable ⊇ analytic (Σ₁¹) ⊇ Borel, with all inclusions strict in uncountable Polish spaces.
- **Mathlib infrastructure**: `MeasureTheory.AnalyticSet`, universally measurable sets, and the Borel σ-algebra over Polish spaces are all available.
- **Projection complexity**: If A ⊆ X × Y is Borel and X, Y are Polish, then π_X(A) is Σ₁¹. The existential quantifier over a Polish space adds exactly one level of projective complexity.

### 1.2 HC Theory (Gupta, KU-Factored Abduction)

- **Definition**: HC(κ) = max_s I(P₁; P₂ | S = s) under uniform distribution on fibers, where (S, P₁, P₂) is the vocabulary partition and κ is the specification (concept class).
- **Five-way equivalence (Theorem 5.4/6.2)**: For finite structures, interpolation ↔ amalgamation ↔ rectangular fibers ↔ conditional independence ↔ fiber-product surjectivity. HC = 0 iff any of these hold.
- **Oscillation theorem (Theorem 7.7)**: Cross-domain discovery necessarily passes through non-rectangular states (HC > 0). There is no path from domain-separated knowledge to synthesized knowledge that avoids interpolation failure.
- **Scope**: All definitions and theorems are for FINITE structures (σ finite, κ ⊆ {T,F}^σ finite). No infinite extension has been developed.

### 1.3 Learning Theory (Krapp-Wirth + this kernel)

- **Krapp-Wirth (2024)**: Identified V-measurability and U-measurability conditions (both MeasurableSet-level) as sufficient for the Fundamental Theorem of Statistical Learning. Their Theorem 4.7 shows o-minimal definable classes satisfy these conditions.
- **This kernel**: Introduced WellBehavedVC (NullMeasurableSet) — strictly weaker than Krapp-Wirth conditions.
- **KrappWirthWellBehaved → WellBehavedVC**: Proved sorry-free. The implication is strict (conjectured).
- **KrappWirth_separation**: Stated as an open question in the kernel. Asks whether there exists a concept class satisfying WellBehavedVC but not KrappWirthWellBehaved.
- **O-minimal classes**: Krapp-Wirth Theorem 4.7 establishes that o-minimally definable classes satisfy MeasurableSet conditions. These classes have HC = 0 in the finite restriction (conjecture).

### 1.4 What Connects Them

The bridge between HC theory and learning theory measurability is the observation that a concept class C with a vocabulary partition IS a KU-specification on a potentially infinite vocabulary:

| HC Theory (finite)          | Learning Theory (infinite)              |
|-----------------------------|-----------------------------------------|
| Vocabulary σ (finite)       | Feature space X (Polish)                |
| Valuations κ ⊆ {T,F}^σ     | Concept class C ⊆ {X → Bool}           |
| Shared type s ∈ S           | Projection to shared features           |
| Fiber over s                | {(p₁, p₂) completions consistent with C} |
| Rectangular fiber           | Product structure in fiber              |
| Fiber-product surjectivity  | Projection preserves Borel              |
| Non-rectangular fiber       | Non-product structure in fiber          |
| (no analogue)               | Projection may exit Borel              |

The key structural insight: rectangular fibers correspond to product structure, and projection from a Borel set in a product of Polish spaces preserves Borel-ness when the fibers factor as products (because the projection decomposes into coordinate projections, each of which preserves Borel). Non-rectangular fibers break this factorization, potentially allowing the projection to produce a genuinely analytic (non-Borel) set.

---

## 2. KU — Articulated Unknowns

### 2.1 Does HC = 0 imply the bad event is Borel?

The argument sketch: rectangular fibers → product projection → stays Borel. But the bad event involves a SUPREMUM over all h ∈ C, not just a fiber projection:

```
BadEvent(ε) = {xs ∈ X^m | ∃ h ∈ C, |empirical_risk(h, xs) - true_risk(h)| ≥ ε}
```

Even with rectangular fibers, the supremum over uncountable Borel functions need not be Borel. The relationship between fiber rectangularity and supremum measurability is not direct.

**Sub-question 2.1a**: Does rectangular fiber structure imply the sup map `xs ↦ sup_{h ∈ C} gap(h, xs)` is Borel measurable? This would require C to have additional regularity — e.g., that the evaluation map (h, x) ↦ h(x) is jointly Borel on C × X, and that C with its natural topology is a standard Borel space.

**Sub-question 2.1b**: Is there a concept class with HC = 0 (rectangular fibers) whose bad event is analytic but not Borel? If yes, HC = 0 is necessary but not sufficient for Borel measurability, and the conjecture Part 1 is FALSE as stated. A third condition beyond HC would be needed.

**Sub-question 2.1c**: If C is additionally assumed to be a standard Borel space and the evaluation map is jointly measurable, does HC = 0 then suffice? This would give a refined version of Part 1.

### 2.2 Does HC > 0 produce a concrete non-Borel bad event?

The construction strategy: take two Borel-measurable concept classes C₁, C₂ on a Polish space, form their interpolation C₁₂ = {patch(c₁, c₂, A) | c₁ ∈ C₁, c₂ ∈ C₂, A measurable}, and show the bad event for C₁₂ is Σ₁¹ \ Borel.

**Sub-question 2.2a**: What is the simplest C₁, C₂ that produce a non-Borel bad event? Candidates in order of complexity:
- Threshold functions on ℝ (VC dimension 1)
- Half-spaces in ℝ² (VC dimension 3)
- Linear classifiers in ℝ^d
- Neural networks with one hidden layer

**Sub-question 2.2b**: Is the existential over A (the partition set) the source of non-Borelness? The interpolation C₁₂ involves an existential quantifier over all measurable partitions A of X. This existential ranges over an uncountable family, and existential quantification over uncountable families is exactly what creates analytic sets. If A is restricted to a countable sub-σ-algebra (e.g., generated by a countable partition), does the bad event become Borel?

**Sub-question 2.2c**: Is the non-Borelness "robust" (survives small perturbations of C₁, C₂) or "fragile" (requires exact construction)?

### 2.3 How does HC extend to infinite structures?

HC is defined for finite σ. For infinite σ (Polish X), we need:
- A σ-algebra on the fiber space (the set of completions consistent with C over a fiber)
- A measure on the shared types (to take the supremum over s in the HC definition)
- Conditional mutual information I(P₁; P₂ | S = s) well-defined (requires a probability model on the fiber)

**Sub-question 2.3a**: Is the extension unique? If we take an increasing sequence of finite sub-vocabularies σ_n ↑ σ and compute HC(C|_{σ_n}), does the limit exist? Is it independent of the sequence?

**Sub-question 2.3b**: Can HC be defined intrinsically (without a vocabulary partition) as a property of the concept class? For example, as a supremum over all possible vocabulary partitions: HC_intrinsic(C) = sup_{(S,P₁,P₂)} HC(C, (S,P₁,P₂))? This would remove the dependence on auxiliary structure.

**Sub-question 2.3c**: For the learning theory application, do we need the full HC value, or just the dichotomy HC = 0 vs HC > 0? The dichotomy might extend more cleanly than the quantitative value.

### 2.4 Does the oscillation theorem lift?

The oscillation theorem (Theorem 7.7): cross-domain discovery necessarily passes through HC > 0 states. A learning-theoretic reading: transfer learning across feature partitions passes through states where MeasurableSet fails.

**Sub-question 2.4a**: Is there a dynamic version — a learner that starts with HC = 0 (on each domain separately) and must pass through HC > 0 (combined domain) before converging? This would be a formal version of "synthesis requires passing through uncertainty."

**Sub-question 2.4b**: Does the "measurability gap" (NullMeasurable but not Borel) have a duration/cost in sample complexity? That is, does the learner need MORE samples during the HC > 0 phase than during the HC = 0 phases?

**Sub-question 2.4c**: Is the oscillation theorem an artifact of the finite setting, or does it reflect a topological/measure-theoretic obstruction in the infinite setting?

---

## 3. UK — Discovered Pressures (things we didn't know we didn't know)

### 3.1 The supremum problem

**Kill check**: This is the most dangerous threat to the conjecture.

HC = 0 controls FIBER structure but the bad event involves a SUPREMUM over all h ∈ C. The relationship between fiber rectangularity and supremum measurability is NOT the same as the relationship between fiber rectangularity and individual fiber projection measurability.

Concretely: even if every individual set `{xs | gap(h, xs) ≥ ε}` is Borel (for each fixed h), the union `⋃_{h ∈ C} {xs | gap(h, xs) ≥ ε}` over uncountably many h need not be Borel. The existential quantifier over C is the source of potential non-Borelness, INDEPENDENT of fiber structure.

**Pressure**: If the supremum over uncountable rectangular products can exit Borel, then HC = 0 is necessary but not sufficient. The conjecture Part 1 needs either: (a) an additional regularity condition on C, or (b) a proof that rectangular fiber structure implies the right kind of regularity. If (b) is true, it would be a genuinely new result connecting information-theoretic structure to descriptive set-theoretic structure.

**Resolution path**: Study the map C × X^m → ℝ given by (h, xs) ↦ gap(h, xs). If C is standard Borel and this map is jointly Borel, then {(h, xs) | gap(h, xs) ≥ ε} is Borel in C × X^m, and projection to X^m gives an analytic set. For it to be Borel, we need C to be countable (trivial) or the map to have special structure (e.g., the fibers {h | gap(h, xs) ≥ ε} are σ-compact in C).

### 3.2 The topology on C

For Suslin's theorem to apply, we need C to have a Polish topology (or at least be analytic as a subset of a Polish space). The space of all functions {X → Bool} with product topology is:
- Polish when X is countable (it's a Cantor space or similar)
- Compact (Tychonoff) but NOT second-countable when X is uncountable, hence NOT Polish

This means the descriptive set theory machinery does not apply directly to arbitrary concept classes over uncountable Polish spaces.

**Pressure**: For uncountable X, we need C to be a SUBSET of {X → Bool} with additional structure. Options:
- C consists of Borel-measurable functions, and we topologize C by pointwise convergence on a countable dense subset D ⊂ X. This gives a Polish topology on C (as a subset of {0,1}^D).
- C is parametrized by a Polish space Θ (e.g., C = {h_θ | θ ∈ Θ}) and the parametrisation is Borel.
- C is a closed (or analytic) subset of a Polish function space.

The choice of topology on C may ITSELF depend on the vocabulary partition, creating a circularity.

### 3.3 The role of the partition

The conjecture requires a vocabulary partition (S, P₁, P₂) of X. But WellBehavedVC and KrappWirthWellBehaved are defined WITHOUT a partition. This creates a mismatch.

**Pressure**: Is the partition auxiliary or essential?

- **Auxiliary**: For every concept class C, there exists a vocabulary partition such that HC(C, partition) controls the measurability type. Then HC is a derived quantity that diagnoses an intrinsic property of C.
- **Essential**: The same C can have HC = 0 under one partition and HC > 0 under another. Then HC is a RELATIONAL property of (C, partition), and the conjecture says something about concept classes equipped with additional structure.

If essential, the conjecture weakens to: "There exists a partition such that HC = 0 iff the bad event is Borel." This is weaker but still interesting, as it says the measurability type is detectable by an information-theoretic quantity (under the right partition).

**Resolution path**: Check whether, for the simplest non-trivial examples, the HC = 0 / HC > 0 dichotomy is partition-independent. If threshold functions on ℝ have HC = 0 under every partition, and some interpolated class has HC > 0 under every partition, the partition is likely auxiliary.

### 3.4 Analytic vs co-analytic: which side matters?

The bad event `BadEvent(ε) = {xs | ∃ h ∈ C, gap(h, xs) ≥ ε}` is an existential projection → Σ₁¹ (analytic).
The good event `GoodEvent(ε) = {xs | ∀ h ∈ C, gap(h, xs) < ε}` is a universal → Π₁¹ (co-analytic).

For the PAC bound, we need: P(GoodEvent(ε)) ≥ 1 - δ. The probability of the good event must be well-defined and satisfy the bound.

**Pressure**: Under NullMeasurableSet, both analytic and co-analytic sets are universally measurable, hence NullMeasurableSet under any probability measure. So the NullMeasurableSet route handles both sides. But under MeasurableSet (Borel), we need BOTH the bad event and good event to be Borel. Since a set is Borel iff its complement is Borel, this reduces to: the bad event is Borel iff the good event is Borel.

The real question is: does the Borel-ness of the bad event carry additional mathematical information beyond what NullMeasurableSet already gives? Answer: yes, because Borel sets have EFFECTIVE properties (computable in the Borel hierarchy) that NullMeasurableSet sets lack. For example, Borel sets have a definite Borel rank, and the rank controls the complexity of computing probabilities.

### 3.5 The finite/infinite gap in conditional independence

HC = 0 ↔ conditional independence (in the finite case). But conditional independence in the measure-theoretic setting is much more delicate than in the finite setting. Conditional independence given a sub-σ-algebra (as opposed to given a discrete random variable) involves regular conditional probabilities, which exist for Polish spaces but have known pathologies for non-standard spaces.

**Pressure**: Even if we extend HC to infinite structures and prove HC = 0 ↔ conditional independence, the measure-theoretic conditional independence may not have the same geometric consequences (rectangular fibers) as the finite version. The Borel structure of conditional independence sets is itself a non-trivial problem.

---

## 4. UU — Boundary of Askability

### 4.1 Is HC definable for the learning theory setting?

HC requires a finite vocabulary and a finite set of valuations. Learning theory has infinite vocabularies (continuous X) and infinite valuation sets (uncountable C). The extension is NOT obvious and may not be unique. We may need a DIFFERENT quantity that:
- Reduces to HC in the finite case
- Is well-defined for Polish X and standard Borel C
- Controls the Borel/analytic dichotomy

We cannot currently formulate this as a precise question because we don't know what properties the "right" extension should have beyond reducing to HC.

### 4.2 Does the non-Borel analytic set actually arise from natural concept classes?

Suslin's theorem guarantees EXISTENCE of non-Borel analytic sets. All known explicit examples are constructed via diagonalization or coding arguments. The question: does the interpolation of NATURAL concept classes (linear classifiers, neural networks, decision trees) produce such sets?

Possibilities:
- **Natural classes always stay Borel**: The separation exists but is vacuous for practice. HC > 0 for natural classes produces analytic-but-still-Borel bad events. The conjecture Part 3 requires pathological classes.
- **Natural classes CAN produce non-Borel events**: The separation is practically relevant. There exist standard ML model classes whose combined bad events genuinely exit the Borel σ-algebra.
- **The answer is independent of ZFC**: The Borel/analytic status of specific bad events might be undecidable in standard set theory. This is not impossible — Suslin's hypothesis is independent of ZFC.

We currently lack the tools to determine which possibility holds. This is genuinely at the boundary of askability.

### 4.3 What is the RIGHT generalization of HC to infinite structures?

Candidate definitions:

| Approach | Definition | Pros | Cons |
|----------|-----------|------|------|
| Information-theoretic | I(P₁; P₂ \| S) under reference measure | Direct analogue of finite HC | Requires choice of reference measure |
| Approximation | sup over finite sub-vocabularies HC(C\|_{σ_n}) | No new machinery needed | Limit may not exist or may be trivial |
| Category-theoretic | Failure of fiber product = pushout in Meas | Structurally clean | Requires heavy categorical machinery |
| Topological | Non-trivial fundamental group of fiber space | Captures "twist" in fibers | Only detects topological non-rectangularity |
| Descriptive set-theoretic | Projective complexity of the fiber map | Directly connects to the conjecture | Circular (defines HC via what it's supposed to predict) |

We cannot currently determine which approach is "right" because we don't have enough examples to test them against. The FIRST research task must be to produce concrete examples (Phase 1) that can discriminate between these approaches.

### 4.4 Is there a deeper unity?

The conjecture connects three apparently unrelated phenomena:
- **Information theory**: HC = conditional mutual information = interpolation failure
- **Descriptive set theory**: Borel vs analytic = projective complexity = quantifier complexity
- **Learning theory**: MeasurableSet vs NullMeasurableSet = effective vs non-effective measurability

Is there a deeper mathematical structure that explains WHY these three coincide? Or is the coincidence superficial (they happen to align in simple cases but diverge in general)?

This question is currently unaskable in a precise sense. It would become askable if we could exhibit the conjecture as a special case of a more general principle.

---

## 5. Research Programme

### Phase 1: Concrete examples (2-4 weeks)

**Goal**: Produce explicit concept classes where the measurability type can be computed.

1. Take C₁ = C₂ = threshold functions on ℝ (h_t(x) = 1_{x ≥ t}, t ∈ ℝ).
2. Form C₁₂ = interpolation over measurable partitions: {x ↦ h_{t₁}(x) · 1_A(x) + h_{t₂}(x) · 1_{Aᶜ}(x) | t₁, t₂ ∈ ℝ, A ∈ Borel(ℝ)}.
3. Compute: is the bad event for C₁₂ Borel? Analytic but not Borel? Neither?
4. If Borel: escalate to C₁ = half-spaces in ℝ², C₂ = threshold functions on ℝ. Repeat.
5. If analytic non-Borel: we have a witness for Part 3. Characterize the HC of C₁₂.

**Key technical step**: Show that the existential quantifier over A ∈ Borel(ℝ) in the definition of C₁₂ produces genuine projective complexity. The space Borel(ℝ) with the Effros Borel structure is a standard Borel space, so the existential is a projection from a standard Borel space, giving Σ₁¹.

### Phase 2: HC extension (2-4 weeks)

**Goal**: Define HC for concept classes over Polish spaces and prove the five-way equivalence lifts.

1. Define: HC(C, (S, P₁, P₂)) for C ⊆ {X → Bool}, X Polish, via conditional mutual information under a reference measure.
2. Prove: HC = 0 ↔ interpolation ↔ rectangular fibers (lifting Theorem 5.4 to the measure-theoretic setting).
3. Prove or disprove: HC = 0 → bad event Borel (Part 1 of the conjecture, possibly with additional regularity conditions from Section 3.1).
4. If Part 1 needs additional conditions, characterize them precisely.

### Phase 3: Formalization in Lean4 (4-8 weeks)

**Goal**: Formally state the conjecture and prove whatever directions are accessible.

1. Add `AnalyticSet` infrastructure to the kernel (connect to Mathlib's `MeasureTheory.AnalyticSet`).
2. Prove: analytic → universally measurable → NullMeasurableSet (the chain that justifies our WellBehavedVC approach).
3. Define HC for finite concept classes in Lean4 (as a warmup / bridge to infinite).
4. Formally state the HC-Measurability conjecture.
5. Prove Part 1 (HC = 0 → Borel) or Part 3 (separation witness), whichever is accessible.

### Phase 4: Publication

**Target venues (in order of ambition)**:
- *Annals of Statistics* (if the result is a complete theorem with both directions)
- *COLT 2027* (if the result is a separation theorem with algorithmic implications)
- *Journal of Symbolic Logic* (if the result is primarily descriptive set-theoretic)
- *Transactions of the AMS* (if the result connects to broader questions in descriptive set theory)

**Paper title**: "Heterogeneity Coefficient and the Measurability Gap in Statistical Learning Theory"

**Core content**: The conjecture, proved direction(s), the connection to descriptive set theory, implications for when NullMeasurableSet is strictly necessary.

---

## 6. Key References

1. Krapp & Wirth (2024), "Measurability in the Fundamental Theorem of Statistical Learning", arXiv:2410.10243.
2. Gupta (2024), "KU-Factored Abduction" (monograph; defines HC, five-way equivalence, oscillation theorem).
3. Suslin (1917), "Sur une definition des ensembles mesurables B sans nombres transfinis", *Comptes Rendus Acad. Sci. Paris* 164, 88-91.
4. Kechris (1995), *Classical Descriptive Set Theory*, Springer GTM 156.
5. Shalev-Shwartz & Ben-David (2014), *Understanding Machine Learning: From Theory to Algorithms*, Cambridge University Press.
6. Moschovakis (1980), *Descriptive Set Theory*, North-Holland (reprinted AMS 2009). [For projective hierarchy and determinacy.]
7. This kernel: formal-learning-theory-kernel (GitHub: Zetetic-Dhruv). [WellBehavedVC, KrappWirthWellBehaved, NullMeasurableSet infrastructure.]

---

## 7. Connection to URT

The conjecture, if true, would be the first instance where URT's structured ignorance framework (K/U partition, HC measurement) produces a genuinely new theorem in mathematics — not merely a methodology for discovery, but a mathematical object (HC) that has independent meaning in a field (descriptive set theory / measure theory) where it was not originally defined.

### 7.1 HC as a bridge concept

HC was defined in the context of finite abductive inference. It measures the failure of interpolation — the inability to decompose a specification into independent components over a vocabulary partition. The conjecture says this same quantity, when extended to infinite structures, controls a fundamental distinction in measure theory: whether the σ-algebra of events you can reason about probabilistically must be extended beyond the Borel σ-algebra.

This is a bridge between epistemology (what can be known via interpolation) and measure theory (what can be measured). If the bridge holds, it vindicates the URT thesis that the K/U structure is not merely a heuristic but a mathematical invariant with cross-domain meaning.

### 7.2 The oscillation theorem as a learning-theoretic obstruction

The oscillation theorem's learning-theoretic reading: the act of combining knowledge from two domains (transfer learning) necessarily passes through a state where the standard measure-theoretic framework (Borel σ-algebra) is insufficient, and the extended framework (NullMeasurableSet / universally measurable) is required.

This is a formal version of "synthesis requires passing through uncertainty" — not just epistemic uncertainty (we don't know the answer yet) but measure-theoretic uncertainty (the event we need to measure is not in the σ-algebra we started with).

### 7.3 Structured ignorance generating mathematics

The research URS itself exemplifies the URT method: by carefully articulating what is known (KK), what we know we don't know (KU), what we discovered we don't know (UK), and what lies at the boundary of askability (UU), the structure of the ignorance POINTS to the key mathematical questions. The supremum problem (UK 3.1) was not visible before the KU analysis forced it into view. The topology problem (UK 3.2) was not visible before the UK analysis of the supremum problem. The structured ignorance is generative — it produces questions that would not have been asked without the systematic articulation.

---

## 8. URS State Summary

| Quadrant | Count | Key items |
|----------|-------|-----------|
| KK (Known) | 4 sections | Suslin, HC five-way equivalence, Krapp-Wirth, fiber-projection bridge |
| KU (Known unknowns) | 4 questions, 12 sub-questions | HC=0→Borel?, HC>0→witness?, infinite extension?, oscillation lift? |
| UK (Discovered pressures) | 5 pressures | supremum problem, topology on C, partition role, Σ₁¹/Π₁¹ asymmetry, finite/infinite CI gap |
| UU (Boundary) | 4 items | HC definability, natural class pathology, right generalization, deeper unity |

**Current ignorance ratio**: KK : KU : UK : UU ≈ 1 : 3 : 5 : 4

The ignorance is heavily loaded toward UK (discovered pressures) and UU (boundary), indicating this is a GENUINELY OPEN problem where the difficulty has been underestimated. The supremum problem (UK 3.1) is the single most dangerous threat to the conjecture as stated.

**Next action**: Phase 1 — compute the measurability type of the bad event for interpolated threshold functions on ℝ. This is the simplest concrete example and will either provide a witness (if non-Borel) or reveal that the conjecture needs refinement (if Borel despite HC > 0).
