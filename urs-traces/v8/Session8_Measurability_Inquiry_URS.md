---
session: 8
date: 2026-03-29
title: "Measurability Infrastructure: Inquiry State and Discovery Frontiers"
status: open
type: research-urs
---

# Session 8 — Measurability Infrastructure: Inquiry State and Discovery Frontiers

## 0. Will -- Discovery Direction

The measurability problem is the central obstruction in the Formal Learning Theory kernel. Every major proof closure in Sessions 7-8 hit a measurability wall: uncountable concept classes breaking MeasurableSet (Session 7 symmetrization), Classical.choose making success events non-measurable (Session 8 advice elimination), learner evaluation needing joint measurability (Session 8 boosting), independence of block events requiring both hypothesis and learner regularity simultaneously.

The will of this inquiry is threefold:

1. **Build reusable infrastructure**: Typeclasses (`MeasurableBatchLearner`, `MeasurableConceptClass`, `UniversallyMeasurableSpace`) that replace ad hoc measurability threading and make future theorems (PAC-Bayes, stability, transfer learning) statable without re-deriving regularity conditions.

2. **Understand the structural fracture**: Why formal learning theory (PAC), deep learning (SGD), quantum learning, and causal learning cannot talk to each other -- and whether the fracture is at the computation layer (L0) where each paradigm defines uncertainty differently.

3. **Chart the genuine new mathematics**: Distinguish formalization hygiene (making implicit assumptions explicit) from genuinely new results (NullMeasurableSet weakening, the learner measurability axis that Krapp-Wirth does not address, the DeepLearner segregation theorem).

User's framing:

> "Measurability is the key blocker in this entire repo. Should we not looking into settling it once and for all and creating the correct infrastructure for it?"

> "I am actually not even asking you to build the L(-1) layer. I am asking you to understand it's existence and setup computation and everything else downstream in a manner which understands the INQUIRY state - not just the current discovery state."

> "We're going to operate under learning theory and focus on producing cool new measurability infrastructure which is reusable across mathlib - while understanding generalizations above and specifications (as already discovered in use) below"

---

## 1. KK -- What Is Known

### 1.1 Infrastructure Built

Three typeclasses were added to the kernel during Session 8:

**MeasurableBatchLearner** (`Learner/Core.lean`):
```lean
class MeasurableBatchLearner (X : Type u) [MeasurableSpace X]
    (L : BatchLearner X Bool) : Prop where
  eval_measurable : forall (m : N),
    Measurable (fun p : (Fin m -> X * Bool) * X => L.learn p.1 p.2)
```
The minimal regularity that makes the PAC success event `{S | D{L(S) != c} <= eps}` a MeasurableSet via `measurable_measure_prod_mk_left`. Replaces `LearnEvalMeasurable` (Separation.lean) and `AdviceEvalMeasurable` (Extended.lean).

**MeasurableConceptClass** (`Complexity/Measurability.lean`):
```lean
class MeasurableConceptClass (X : Type u) [MeasurableSpace X]
    (C : ConceptClass X Bool) : Prop where
  mem_measurable : forall h in C, Measurable h
  all_measurable : forall c : Concept X Bool, Measurable c
  wellBehaved : WellBehavedVC X C
```
Bundles three explicit hypotheses (`hmeas_C`, `hc_meas`, `hWB`) that were threaded through every theorem signature.

**UniversallyMeasurableSpace** (`Complexity/Measurability.lean`):
```lean
class UniversallyMeasurableSpace (X : Type u) [MeasurableSpace X] : Prop where
  all_concepts_measurable : forall c : Concept X Bool, Measurable c
  all_classes_wellBehaved : forall C : ConceptClass X Bool, WellBehavedVC X C
```
Domain-level property: "X is nice enough that measurability of learning events is never an issue." Implies `MeasurableConceptClass X C` for every C via a priority-50 instance.

**Bridge lemmas**: `MeasurableBatchLearner.learn_measurable`, `MeasurableConceptClass.hmeas_C`, `.hc_meas`, `.hWB`, `UniversallyMeasurableSpace.concept_measurable`, `.class_wellBehaved`.

**Typeclass hierarchy**:
```
UniversallyMeasurableSpace X
         | (instance, priority 50)
MeasurableConceptClass X C    MeasurableBatchLearner X L
         | (bridges)                    | (bridge)
    hmeas_C, hc_meas, hWB        LearnEvalMeasurable L
```

**Primed theorem variants**: 4 theorems in `GeneralizationResults.lean` now have typeclass-enabled versions (`uc_bound'`, `erm_consistent_realizable'`, `pac_sample_complexity_sandwich'`, `uc_does_not_imply_online'`) that take `[UniversallyMeasurableSpace X]` instead of explicit hypotheses.

### 1.2 Session 7-8 Discoveries (D1-D15)

#### Tier 1: Formalization-driven mathematical contributions (gaps that don't exist on paper)

**D1: NullMeasurableSet resolution for uncountable concept classes (Session 7, propagated Session 8)**
The symmetrization bad event `{exists h in C, |TrueErr - EmpErr| >= eps}` is NOT MeasurableSet for uncountable C. This nearly forced `[Finite X]` on `fundamental_theorem`, which would have been mathematically wrong. Resolution: NullMeasurableSet suffices for integration (`lintegral_indicator_one_0`, `AEMeasurable.indicator_0`), with `WellBehavedVC` as explicit regularity assumption. Pen-and-paper proofs silently assume sigma-algebras are rich enough.

**D2: `[Infinite X]` containment via `rcases finite_or_infinite X`**
An agent propagated `[Infinite X]` all the way to `fundamental_theorem`. The fix: `rcases finite_or_infinite X` INSIDE `vcdim_finite_imp_uc'`, with both branches sorry-free. The finite branch is trivial (finite X -> finite C -> direct enumeration). The infinite branch uses the full symmetrization chain. Result: `fundamental_theorem` holds for ALL measurable spaces X, not just infinite ones.

**D3: `finite_exchangeability_bound` -- generic NullMeasurableSet Tonelli lemma**
A new lemma extracted during SL3 closure: a version of Tonelli/Fubini for indicator sums over NullMeasurableSets. Bridges the gap between the standard (MeasurableSet-assuming) integration API and the reality that uncountable concept class events are only NullMeasurable. Not in Mathlib; potentially contributable.

**D4: Measurable inner event pattern (two instances)**
- Session 7: uncountable union over C -> NullMeasurableSet + monotonicity
- Session 8: `Classical.choose` in `bestAdvice` -> GoodPair (measurable) subset of SuccessProd (non-measurable) + transport GoodPair + monotonicity

General principle: when the target event is non-measurable, find a measurable inner event with the same probability bound and conclude by monotonicity. This pattern has no pen-and-paper analogue because measurability is invisible on paper.

#### Tier 2: New proof techniques for formalization

**D5: 7/12-fraction argument for boosting**
Standard majority-of-blocks uses "more than half good" but `k * rate(n)` diverges. Fix: demand 7/12 good fraction. Majority error <= 7*rho (worst case `2g/(2g-k)` at `g = 7k/12` = 7). Concentration constant 36/delta (from gap k/12). Cleanly separates confidence from accuracy.

**D6: Doubled-count trick for N-arithmetic Markov**
Threshold `g - k/2` has half-integer problem in Lean's N. Fix: `G(x) = 2*Y(x)`, threshold `2g - k` (always N). Markov applies without division.

**D7: Three-step pullback chain for product-space transport**
For advice elimination: `D^N -> D^{m1+m2} -> D^{m1} x D^{m2}` via `usedPrefix -> splitUsedEquiv`. Each step is one MeasurePreserving application. Pull back one map at a time, never try to transport the full success event in one shot.

**D8: Set-equality bridge (Route E) for binder-type gaps**
`Nat.unpair(Nat.pair m1 m2)` in lambda binder types resists `simp_rw`. Fix: name both sets, prove equality by `ext xs; simp [Nat.unpair_pair]`, then `change` + `rw`. Unit of rewriting is the event set, not the inequality.

**D9: `Nat.pair`/`Nat.unpair` encoding for sample splitting**
Encode training size m1 and validation size m2 into a single sample complexity `Nat.pair m1 m2`. The extra "junk" coordinates integrate out via `pi_cylinder_set_eq`.

#### Tier 3: Lean4/Mathlib API discoveries

**D10: `measurable_measure_prod_mk_left` chain**
For section measure measurability: `AdviceEvalMeasurable` -> labeling map -> `measurableSet_eq_fun` + `.compl` -> `measurable_measure_prod_mk_left` -> preimage of `Iic`. Used 4 times (T0, T2, T4, T5). The alternative `Kernel.measurable_kernel_prodMk_left_of_finite` is a hallucination.

**D11: `iIndepFun` -> `iIndepSet` via `iIndep_of_iIndep_of_le`**
Converting block-function independence to block-event independence via sigma-algebra containment.

**D12: `ENNReal.div_le_iff (Or.inl ...) (Or.inl ...)` for Markov ratio bounds**
Combined with `Nat.cast_sub (by omega)` for the `cast(2g-k) = 2*cast(g) - cast(k)` cast.

**D13: `MeasurePreserving.measure_preimage_equiv` doesn't need MeasurableSet**
Unlike `Measure.map_apply` for general functions, the equiv version works for ALL sets.

#### Tier 4: Process/methodology

**D14: EmpiricalRademacherComplexity definition fix (|*| removal)**
One-sided (Bartlett-Mendelson 2002), not two-sided. Cascading fix through 8 downstream consumers.

**D15: Sample complexity constant changes**
`2m/d -> em/d` (Sauer-Shelah), `9/delta -> 36/delta` (7/12 fraction), `eps/kmin -> eps/7`.

### 1.3 Krapp-Wirth Comparison

Krapp & Wirth (2024, arXiv:2410.10243) is the definitive pen-and-paper treatment of measurability in the FTSL. They did NOT formalize their work -- no Lean, no Coq, no Isabelle.

**What they found (pen-and-paper):**
- Definition 3.2 "well-behaved" has two conditions: (V) the symmetrization map is measurable, (U) the UC map is measurable, plus a base condition that all hypothesis graphs are sigma-measurable
- Standard textbook proofs (SSBD, Anthony-Bartlett) tacitly assume these conditions
- O-minimal definable hypothesis classes satisfy well-behavedness (Theorem 4.7)
- Permissibility (Pollard) is strictly stronger than well-behavedness
- NIP connection: NIP formulas have finite VC dimension, so definable classes in NIP structures are PAC learnable

**What we found (formalization-driven):**
- `NullMeasurableSet` suffices where they require `MeasurableSet` -- our condition is WEAKER (D1)
- The measurable inner event pattern for non-measurable algorithmic events (D4) -- they don't address this because they don't formalize algorithms
- The `[Infinite X]` containment (D2) -- they don't address this because pen-and-paper implicitly assumes infinite X
- `MeasurableBatchLearner` as a regularity condition on the LEARNER -- they explicitly state "we place no restrictions on the learning function A" (footnote 7, page 8)

**Honest comparison:**

> "Their work is DEEPER on the mathematical side. They connect to model theory (NIP, o-minimality), identify the exact boundary between well-behaved and non-well-behaved classes, and show that neural networks with standard activations are well-behaved via o-minimality. We don't have any of that."

> "Our work is DEEPER on the formalization side. We discovered that: 1. Their V condition can be weakened to NullMeasurableSet and the proof still goes through 2. There's a THIRD measurability axis they don't address: the learner's evaluation map 3. The UniversallyMeasurableSpace abstraction is architecturally necessary for theorems quantifying over all concept classes"

**Relationship between conditions:**
```
Krapp-Wirth well-behaved -> MeasurableConceptClass (strictly stronger)
MeasurableConceptClass -/-> Krapp-Wirth well-behaved (we're weaker)
```

The weaker condition allows a broader hypothesis class. The learner measurability axis (`MeasurableBatchLearner`) is entirely absent from their analysis.

---

## 2. KU -- Articulated Unknowns

### 2.1 Tier 1-3 Refactoring Plan

The propagation plan through the codebase:

**Tier 1 -- High-traffic sites** (threaded through every major theorem):
- `Theorem/PAC.lean`: `fundamental_theorem` + 8 helpers take `hmeas_C`, `hc_meas`, `hWB` (~20 sites)
- `Bridge.lean`: threading `hmeas_C`, `hc_meas` everywhere

**Tier 2 -- Separation theorems**:
- `Theorem/Separation.lean`: `boost_two_thirds_to_pac` takes `hc_meas`, `hL_meas : LearnEvalMeasurable L`
- `Theorem/Extended.lean`: `advice_elimination` takes `hc_meas` + `AdviceEvalMeasurable`

**Tier 3 -- Generalization results** (COMPLETED):
- `GeneralizationResults.lean`: 4 primed theorems added using `[UniversallyMeasurableSpace X]`

**Tier 3a -- UniversallyMeasurableSpace** (COMPLETED):
- Added to kernel's `Measurability.lean` with instance deriving `MeasurableConceptClass`

The pressure point discovered during Tier 2 planning: `hL_meas : forall (L : BatchLearner X Bool), LearnEvalMeasurable L` says "every learner on X is jointly measurable" -- a property of the SPACE X, not any learner. This led to the expansion of `UniversallyMeasurableSpace` to potentially include `all_learners_measurable`.

### 2.2 OP1-OP6 Assessment

Six open problems were identified where the measurability infrastructure creates a bridge. Each received an honest kill check:

**OP1: Uniform convergence for overparameterized models (double descent)**
Bridge: `MeasurableBatchLearner` formalizes which learners are admissible. The image of a measurable learner is an analytic set with well-defined capacity. The gap between VC dim of the full class and capacity of the learner's image IS the double descent gap.
Kill check: **Not new math.** "The 'effective hypothesis class' idea is NOT new -- Arora et al. 2019, Bartlett et al. 2020 already formalize compression-based effective capacity. What's missing is the measure-theoretic grounding, but that's a formalization contribution, not new math."

**OP2: Distribution-dependent bounds (Rademacher vs VC)**
Bridge: If `D -> RademacherComplexity(C, D, m)` is measurable/continuous, Bayesian averaging over D yields distribution-averaged Rademacher bounds. Requires `MeasurableConceptClass` composed with topology on `Measure X`.
Kill check: **Not new math.** "The continuity of Rademacher complexity in the distribution is known -- it follows from standard uniform convergence of empirical processes (van der Vaart & Wellner 1996)."

**OP3: Transfer learning generalization bounds**
Bridge: H-divergence `d_H(D_source, D_target) = sup_{h in H} |D_source(h=1) - D_target(h=1)|` is a supremum over H -- same measurability pattern as UC event. `WellBehavedVC`/`NullMeasurableSet` infrastructure applies directly.
Kill check: **Not new math.** "Ben-David et al. 2010 already implicitly assume measurability. Making it explicit is a formalization contribution."

**OP4: PAC-Bayes with data-dependent priors**
Bridge: Extension from `pac_bayes_finite` requires prior P to be a MEASURABLE function of held-out data: `P : (Fin k -> X * Bool) -> FinitePMF H`. This is exactly `MeasurableBatchLearner` applied to the prior-selection algorithm.
Kill check: **Not new math.** "Catoni 2007 and Lever et al. 2013 already handle data-dependent priors via sample splitting. The measurability of the prior-selection map is implicitly assumed."

**OP5: Online-to-batch conversion with measurability**
Bridge: Adding `MeasurableOnlineLearner` would require `Measurable (fun (s, x) => predict s x)` and `Measurable (fun (s, x, y) => update s x y)`. Then `universal_imp_pac` could produce a `MeasurableBatchLearner`.
Kill check: **Not new math.** "The conversion is standard (Cesa-Bianchi et al. 2004). Adding measurability conditions is formalization hygiene."

**OP6: Algorithmic stability -> generalization**
Bridge: `MeasurableBatchLearner` gives exactly the joint measurability needed for the coupling argument in Bousquet-Elisseeff (2002).
Kill check: **Not new math.** "Bousquet-Elisseeff 2002 assumes measurability implicitly. Making it explicit strengthens nothing."

**Summary:**

> "The honest answer: None of these are open problems in the research sense. They are all KNOWN results with IMPLICIT measurability assumptions. Making the assumptions explicit is valuable for formalization but is not new mathematics."

> "What WOULD be new math: The genuinely new thing we discovered is that NullMeasurableSet suffices where the literature requires MeasurableSet (or assumes measurability silently). If there exists a concept class that is: WellBehavedVC (NullMeasurable UC events) but NOT Krapp-Wirth well-behaved (MeasurableSet UC events), PAC learnable under our weaker condition, NOT provably PAC learnable under their stronger condition -- THAT would be a separation theorem with genuine mathematical content."

### 2.3 DeepLearner Definition

The proposed `DeepLearner` structure exposes the optimization trajectory that `BatchLearner` hides:

```lean
structure DeepLearner (X : Type u) [MeasurableSpace X] where
  Params : Type
  [measParams : MeasurableSpace Params]
  forward : Params -> X -> Bool
  forward_measurable : Measurable (fun p : Params * X => forward p.1 p.2)
  loss : Bool -> Bool -> R
  step : Params -> X * Bool -> Params
  step_measurable : Measurable (fun p : Params * (X * Bool) => step p.1 p.2)
  init : Params
```

Key properties:
- `DeepLearner.toBatchLearner` converts to `BatchLearner` by iterating gradient steps
- `DeepLearner.measurable`: the induced BatchLearner is AUTOMATICALLY `MeasurableBatchLearner` (because constructive, finite composition of measurable functions)
- This is the formal segregation: deep learners are always measurable; general BatchLearners (which can use `Classical.choose`) may not be

The typed divergence between FLT and DL:

```
FLT types:                          DL types:
ConceptClass X Bool                 Architecture : N -> N -> Type
  (set of hypotheses)                 (layer dims -> parameter space)
BatchLearner X Bool                 Optimizer : ParamSpace -> Grad -> ParamSpace
  (sample -> hypothesis)               (SGD, Adam, etc.)
Measure X                           DataLoader : N -> Batch
  (distribution)                      (stochastic, ordered)
SampleComplexity                    ConvergenceRate
  (how many samples)                  (how many steps)
TrueError : ENNReal                 Loss : ParamSpace -> R
  (population risk)                   (empirical, on batch)
```

> "FLT types are DECLARATIVE: a BatchLearner maps a sample to a hypothesis. It says nothing about HOW."
> "DL types are PROCEDURAL: an Optimizer iteratively updates parameters. The trajectory through parameter space IS the learning algorithm."

The three disconnections:
1. **Expressiveness != Learnability**: Universal Approximation says C is rich. VC theory says rich C needs many samples. These pull in OPPOSITE directions.
2. **Existential != Constructive**: FLT's `exists L` is non-constructive. DL's SGD is specific.
3. **Population != Empirical**: FLT measures TrueError (population). DL minimizes EmpLoss (empirical). The gap is EXACTLY generalization error, requiring measurability of `S -> h_theta(S)`.

At L0-L2, PAC and DL are the SAME type. The divergence starts at L3:
- PAC (L3): learner is a BLACK BOX, only existence matters, non-constructive learners allowed
- DL (L3): learner is a SPECIFIC ALGORITHM, the process IS the object of study, must be constructive (hence measurable)

---

## 3. UK -- Discovered Pressures

### 3.1 The NullMeasurableSet Separation Question

The central open mathematical question:

Does there exist a concept class C such that:
- The UC event `{exists h in C, |TrueErr - EmpErr| >= eps}` is NullMeasurableSet (our `WellBehavedVC`)
- But NOT MeasurableSet (Krapp-Wirth's stronger condition)
- C is PAC learnable under our weaker condition
- C is NOT provably PAC learnable under their stronger condition

If yes: our weakening is STRICT and constitutes a publishable separation theorem.
If no: the weakening is vacuous and Krapp-Wirth's condition loses nothing.

> "I don't know if such a class exists. That's a real UK."

### 3.2 The Learner Measurability Axis

Krapp-Wirth explicitly state "we place no restrictions on the learning function A" (footnote 7, page 8). Our `MeasurableBatchLearner` IS a restriction on the learner. Why it matters:

The GoodPair discovery (D4) showed that `Classical.choose`-based learners produce success events that are not provably MeasurableSet. The learner's algorithmic structure (constructive vs non-constructive) determines whether PAC-Bayes and information-theoretic bounds are even STATABLE.

This axis is orthogonal to hypothesis class measurability:
- Hypothesis class regularity (Krapp-Wirth): which CLASSES admit well-defined UC events?
- Learner regularity (our contribution): which ALGORITHMS produce well-defined success events?

User's insight:

> "The weaker criteria definitely works in our favor as it allows a broader hypothesis class. The learner definition as well. I would like to double click on the learner definition for a bit and see if our learner definitions if developed can imply strong bounds on deep learners"

### 3.3 L(-1): Admissible sigma-algebras per Paradigm

Each learning paradigm defines uncertainty differently, and these definitions are incompatible at the TYPE level:

```
PAC:      uncertainty = P_S[error > eps] <= delta       (frequentist, over samples)
Bayesian: uncertainty = E_Q[error]                       (posterior expectation)
Quantum:  uncertainty = Tr(rho * O)                      (density matrix, observable)
Causal:   uncertainty = P(Y | do(X))                     (interventional distribution)
Online:   uncertainty = sum(mistakes) <= f(d)            (worst-case, no probability)
```

These are not different MEASURES of the same thing -- they are different TYPES. You cannot cast `P_S[error > eps]` to `Tr(rho * O)`.

In HC terms, each paradigm has a DIFFERENT vocabulary partition:

| Paradigm | S (shared) | P1 (left-private) | P2 (right-private) | Uncertainty type |
|----------|-----------|-------------------|-------------------|-----------------|
| PAC | Instance space X | Training sample S | Test point x | Probabilistic (measure) |
| Deep learning | Parameter space Theta | Training trajectory | Test input | Implicit (SGD dynamics) |
| Quantum | Hilbert space H | Measurement basis | Observable | Amplitude (complex) |
| Causal | Variable space V | Intervention do(X) | Outcome Y | Counterfactual (structural) |

The structural fracture: these four vocabulary partitions are INCOMPATIBLE. There's no common (S, P1, P2) that subsumes all four.

> "The most interesting implication is that the uncertainty definitions themselves need to be well defined and proved in computation and they inherit their type structure from the missing L(-1) -- the layer which connects the Ignorance structures of Deep learning, Quantum learning/computation, etc. That layer literally is the URT formalization of limits of learning and initializes learning theories"

> "I am actually not even asking you to build the L(-1) layer. I am asking you to understand its existence and setup computation and everything else downstream in a manner which understands the INQUIRY state - not just the current discovery state."

The measurability infrastructure we built IS a piece of L(-1) for PAC learning. `MeasurableConceptClass`, `MeasurableBatchLearner`, `UniversallyMeasurableSpace` formalize the UK quadrant of PAC's ignorance structure. The analogous infrastructure for other paradigms:
- Bayesian: under what conditions is the posterior well-defined as a measure? (Doob's theorem)
- Quantum: under what conditions does a POVM give a well-defined outcome distribution?
- Causal: under what conditions is the interventional distribution well-defined? (positivity, faithfulness)

Each is the UK quadrant of its paradigm. L(-1) would be the type that parameterizes over all of them.

### 3.4 MeasurabilityDefect as K/U Transition Cost

Inspired by HC (Hidden Channel Capacity): `MeasurabilityDefect` should be defined as a K/U transition cost, not as a number.

Concrete definition:
```
MeasurabilityDefect(L, m) := inf { k : N | exists L' : BatchLearner,
  MeasurableBatchLearner X L' and
  forall D, IsProbabilityMeasure D -> forall c,
    |TrueError(L, D, c) - TrueError(L', D, c)| <= k/m }
```

This says: how many bits of regularization (expressed as 1/m accuracy loss) do you need to approximate L by a measurable learner L'?

- ERM on finite class: defect = 0 (already measurable)
- SGD with fixed steps: defect = 0 (measurable -- finite composition of measurable functions)
- SGD with early stopping: defect = O(log(1/delta)) (validation-based stopping adds log(1/delta)/m excess risk)
- Architecture search over k architectures: defect = O(log(k)) (union bound)

Kill check on the definition:

> "Is this genuinely new? The 'approximation by measurable functions' idea is classical in measure theory (Lusin's theorem). But applying it specifically to learning algorithms with the 1/m accuracy scale is new -- I haven't seen it in the literature."

> "Is it USEFUL? It would give concrete bounds: 'SGD with early stopping on architecture class of size k has measurability defect O(log(k)),' which means the PAC-Bayes bound applies with an additive O(log(k)/m) penalty."

HC connection: `MeasurableBatchLearner` is equivalent to "the learner's fiber structure is measurable." HC measures the degree to which fibers FAIL to be products. The fiber at shared instance x is `Fib(x) = {(S, y) | L.learn(S)(x) = y}`. Measurability of this fiber is exactly `MeasurableBatchLearner`.

---

## 4. UU -- Boundary of Askability

### 4.1 Can Classical.choose Learners Be Measurable?

The GoodPair discovery (D4) showed that `bestAdvice` using `Classical.choose` makes `SuccessProd` not provably MeasurableSet. The question: is this a FUNDAMENTAL obstruction or just a Lean artifact?

> "Classical.choose is not concrete. Measurability is a property of concrete functions, and Classical.choose is not concrete. This is exactly the GoodPair discovery: we couldn't prove MeasurableSet SuccessProd because bestAdvice used Classical.choose. The question wasn't hard -- it was UNASKABLE in the current grammar."

The measurability of `Classical.choose` depends on the Axiom of Choice in a way that cannot be resolved within the current type theory. In ZFC, the Axiom of Choice produces non-measurable sets (Vitali sets). In Lean4, `Classical.choose` is an opaque term -- you cannot prove it measurable because you cannot inspect its definition.

This means: the gap between existential PAC (some learner works) and certifiable PAC (some MEASURABLE learner works) is NOT an artifact. It reflects a genuine mathematical distinction between constructive and non-constructive selection.

### 4.2 Does UniversallyMeasurableSpace Hold for Standard Borel?

`UniversallyMeasurableSpace X` requires `forall f : X -> Bool, Measurable f`. For R^n with Borel sigma-algebra, this FAILS -- not every function R^n -> Bool is Borel measurable.

> "So UniversallyMeasurableSpace is actually a STRONG condition that essentially says 'X has the discrete sigma-algebra or something close to it.' For standard Borel R^n, it does NOT hold."

This means the correct hierarchy is:
- `UniversallyMeasurableSpace` -- for discrete/countable spaces (N, Fin n, etc.)
- `MeasurableConceptClass X C` -- for specific well-behaved classes on general spaces
- `MeasurableBatchLearner X L` -- for specific well-behaved learners

For the kernel's current theorems (which operate over generic `[MeasurableSpace X]`), `UniversallyMeasurableSpace` is the right assumption for theorems quantifying over ALL concept classes. For theorems about specific classes on R^n, the per-class `MeasurableConceptClass` is needed.

### 4.3 The Grammar Expansion Problem

User's insight:

> "The very act of definition changes ignorance which changes what can be known, which changes the definitions. The grammar expands under its own operation."

In the session's context: adding `MeasurableBatchLearner` to the type system made the question "is this learner measurable?" ASKABLE. Before the typeclass existed, the measurability condition was an ad hoc hypothesis threaded through proofs -- it wasn't a first-class concept. After adding it, new questions become formulable:
- Is every `DeepLearner` automatically `MeasurableBatchLearner`? (Yes, provable.)
- Is every `Classical.choose` learner `MeasurableBatchLearner`? (No, but the proof is in UU.)
- Does `MeasurableBatchLearner` compose? (If L1, L2 are measurable, is their boosted combination measurable?)

The grammar expansion is: adding a definition changes what's provable. This is standard in mathematics (new definitions enable new theorems), but the URT framing highlights that WHICH definitions to add is itself an inquiry -- guided by the K/U partition of the current state.

---

## 5. Action Space

### 5.1 Concrete Next Steps (this session or next)

1. **Complete Tier 1-2 refactoring**: Migrate `fundamental_theorem`, `boost_two_thirds_to_pac`, `advice_elimination` to use typeclass infrastructure. Estimated ~200 LOC of signature changes across 5 files.

2. **Expand `UniversallyMeasurableSpace`**: Add `all_learners_measurable` field. Prove `instance : UniversallyMeasurableSpace N`. This resolves `pac_not_implies_online` which constructs measurability concretely for the threshold class on N.

3. **Add `DeepLearner` structure**: 10 LOC definition + `toBatchLearner` + proof that induced learner is automatically `MeasurableBatchLearner` (~40 LOC).

4. **Add `KrappWirthWellBehaved` typeclass**: Formalizes their Definition 3.2 (V + U conditions). Prove `KrappWirthWellBehaved -> MeasurableConceptClass` (~50 LOC definitions + ~30 LOC implication proof). First formalization to explicitly engage with their 2024 analysis.

5. **MeasurabilityDefect definition**: Ground the definition with `MeasurabilityDefect = 0 <-> MeasurableBatchLearner` (~20 LOC).

### 5.2 Research Directions (future sessions)

1. **NullMeasurableSet separation**: Construct (or prove non-existence of) a concept class where the UC event is NullMeasurableSet but not MeasurableSet. This is the genuine new-math question at the center of the measurability investigation.

2. **SGD measurability theorem**: Prove that fixed-step SGD with Borel-measurable activation functions satisfies `MeasurableBatchLearner`. Needs the o-minimal connection from Krapp-Wirth.

3. **PAC-Bayes with random posteriors**: Extend `pac_bayes_finite` to data-dependent Q where Q is a measurable function of a held-out subset. This is where `MeasurableBatchLearner` pays off for the posterior-selection algorithm.

4. **MeasurableOnlineLearner**: Define the typeclass and prove `universal_imp_pac` produces a `MeasurableBatchLearner` from a `MeasurableOnlineLearner`.

5. **L(-1) inquiry state charting**: Thoroughly map the structural fracture between PAC/Bayesian/quantum/causal at the measurement level. Define `Paradigm -> MeasurableSpace Omega -> Prop` as the type of admissible sigma-algebras per paradigm. This is exploratory/philosophical, not formalization.

6. **Mathlib contribution**: The `measurable_measure_prod_mk_left` chain and `NullMeasurableSet` sufficiency for integration are general patterns. Package them as clean Mathlib API.

### 5.3 Potential Publications

1. **Formalization paper**: "Measurability in Lean4: The First Formalization of the Fundamental Theorem of Statistical Learning with Explicit Regularity Conditions"
   - Content: the NullMeasurableSet weakening, `MeasurableBatchLearner` as a third axis, the typeclass hierarchy, comparison to Krapp-Wirth
   - Venue: ITP 2026 or CPP 2027
   - Strength: first formalization to engage with Krapp-Wirth 2024; the NullMeasurableSet weakening is provably novel

2. **Separation paper** (contingent on 5.2.1): "NullMeasurableSet vs MeasurableSet in PAC Learning: A Strict Separation"
   - Content: construct a concept class that is PAC learnable under NullMeasurableSet but not under MeasurableSet
   - Venue: COLT or ALT
   - Strength: genuine new mathematics; risk is that no such class exists

3. **Textbook chapter**: "Chapter 19: The Measurability Barrier -- Why VC Theory Cannot Explain Deep Learning"
   - Content: formalize the gap between existential PAC (VC) and certifiable PAC (information-theoretic) as a complexity measure; show this measure explains why engineers find VC bounds useless while PAC-Bayes bounds are useful
   - Strength: genuinely original chapter no existing textbook has
   - Kill check caveat: "VC bounds are loose because they're distribution-free and uniform over the entire hypothesis class. The looseness comes from the supremum over all distributions and all concepts in C, not from non-measurable learners." The chapter must be honest about this.
