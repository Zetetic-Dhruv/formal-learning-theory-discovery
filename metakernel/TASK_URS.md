# Task URS: Lean4 Type Architecture for Formal Learning Theory

## PROBLEM

Produce a complete, coherent Lean4 type architecture for ALL of formal learning theory — a skeleton where every definition compiles, every theorem is stated with correct types, and every proof is `sorry`. The architecture must: (1) be consistent with existing Mathlib/lean-rademacher types where they exist, (2) cover all 133 kernel nodes from the concept graph, (3) make the type-level JOINTS between paradigms (PAC/Online/Gold/Universal/Bayesian) explicit and inspectable, and (4) compile as a single `lake build` with zero errors (only `sorry` warnings).

**What this task IS:** Grammar design (R in URT terms). Choosing the right types, typeclasses, structures, and their relationships. The output is a `.lean` file tree that defines the VOCABULARY of formal learning theory in Lean4.

**What this task is NOT:** Proving theorems (Step (b) Phase 1–4). Not URT retyping (Path B). Not writing a paper.

**A₄ check:** A type signature is not a theorem. But a BAD type signature makes theorems unprovable or trivially provable. The quality of the typing shows in whether the STATED theorems (with `sorry`) have the right hypotheses — not too many (decorative), not too few (false).

**Quality test:** Can someone ELSE pick up the skeleton and fill in proofs without rewriting the types? If yes, the grammar is good.

---

## KK — What Is Established

### K₁: Mathlib's combinatorial VCdim types
```lean
-- Mathlib.Combinatorics.SetFamily.Shatter
def Finset.Shatters (𝒜 : Finset (Finset α)) (s : Finset α) : Prop
def Finset.vcDim (𝒜 : Finset (Finset α)) : ℕ
def Finset.shatterer (𝒜 : Finset (Finset α)) : Finset (Finset α)
theorem Finset.card_shatterer_le_sum_vcDim  -- Sauer-Shelah
```
**Constraint:** Our function-class VCdim must reduce to this when the domain is finite. We WRAP Mathlib, not duplicate it.

### K₂: lean-rademacher's probabilistic types
```lean
-- auto-res/lean-rademacher
def empiricalRademacherComplexity
def rademacherComplexity
theorem symmetrization
theorem mcdiarmid_pos
theorem uniform_deviation_tail_bound_countable_of_pos
```
**Constraint:** Our generalization error framework must compose with these.

### K₃: Mathlib's probability infrastructure
```lean
MeasureTheory.Measure, MeasureTheory.ProbabilityMeasure
MeasureTheory.integral, MeasureTheory.Measurable
```
**Constraint:** Use Mathlib's measure theory for all probabilistic concepts. No custom probability.

### K₄: Mathlib's ordinal/cardinal infrastructure
```lean
Ordinal, WithTop ℕ (= ℕ∞), Cardinal
```
**Constraint:** VCdim : ℕ∞, LittlestoneDim : ℕ∞, MindChangeComplexity : Ordinal. Different types for different paradigms — this is a TYPE BREAK the architecture must make visible.

### K₅: Concept graph layer structure (from Step (a))
| Layer | Content | Node Count |
|-------|---------|------------|
| L0–1 | Base types (Domain, Label, Concept, ConceptClass, HypothesisSpace) | ~15 |
| L2 | Data presentations (Text, Informant, IIDSample, Oracle) | ~12 |
| L3 | Learners (Learner typeclass + specializations) | ~15 |
| L4 | Success criteria (PAC, Online, Gold, Universal, Bayesian) | ~20 |
| L5 | Complexity measures (VCdim, Ldim, Rademacher, etc.) | ~33 |
| L6 | Theorems (Fundamental theorem, Gold's theorem, separations) | ~16 proved |

### K₆: Concept graph edge structure (260 edges, 13 typed relations)
- 99 `defined_using` → prerequisite DAG (determines import order)
- 28 `characterizes` → equivalence theorems (type signatures must allow biconditional)
- 9 `does_not_imply` + 4 `strictly_stronger` → separations (same H, different Prop conclusions)
- 32 `analogy` with obstruction types → type-level parallels that FAIL (Break Points)
- 15 `extends_grammar` → where new type primitives are needed (grammar expansion signals)
- 12 `used_in_proof` → lemma dependencies
- 8 `upper_bounds` + 4 `lower_bounds` → inequality theorems

### K₇: Design decisions (pre-locked from problem statement)
| Decision | Choice | Reason |
|----------|--------|--------|
| ConceptClass type | `Set (X → Y)` | Simplest, closest to math, bridges to Mathlib |
| Label type | `Y : Type*` with `[Fintype Y]` default | Supports multiclass (Natarajan, DS) |
| Learner types | Per-paradigm (separate types) | Makes breaks visible for Path B |
| VCdim type | `ℕ∞` (`WithTop ℕ`) | Handles infinite VCdim |
| Success criteria | Individual `Prop`-valued defs | Different quantifier structures |
| Complexity measures | Individual defs | Different type signatures |
| Ordinals | Mathlib `Ordinal` | For mind-change, ordinal Ldim |
| Measure theory | Mathlib `MeasureTheory` | For PAC, Rademacher, all probabilistic |

---

## KU — Active Design Questions

### KU₁: The ConceptClass → Finset bridge
The decision to use `Set (X → Y)` is locked. But Mathlib's `Finset.vcDim` works over `Finset (Finset α)`. The bridge function `restrict : Set (X → Bool) → Finset X → Finset (Finset X)` (restricting each function in H to a finite subset S) must:
- Be computable when H is finite
- Produce exactly the set family Mathlib expects
- Make the statement "our VCdim = Mathlib's vcDim on finite instances" a THEOREM, not a definition

**Open:** Does this require `[DecidableEq X]`? Does it require `[Fintype H]` or just `[Finite H]`? What universe level does `Set (X → Y)` live in?

### KU₂: Loss function abstraction level
All generalization bounds need a loss function `ℓ : Y → Y → ℝ`. Options:
- (a) Bake 0-1 loss into PAC definitions, separate `LossFunction` for generalization bounds
- (b) Parameterize everything by loss from the start
- (c) Two layers: `PAC` with implicit 0-1 loss, `AgnosticPAC` with explicit loss

The concept graph suggests (c): `pac_learning` uses 0-1 loss implicitly; `agnostic_pac_learning` introduces explicit loss; `generalization_error` parameterizes by loss. The `extends_grammar` edge from `agnostic_pac_learning` to `pac_learning` confirms: agnostic = grammar expansion, not just parameter change.

### KU₃: How to type the Online learning game
Online learning is a GAME between learner and adversary. Two typing options:
- (a) `OnlineLearner : Type` = function `X → Y` at each round, with state updated by feedback. The adversary is implicit (universally quantified).
- (b) Explicit game tree type with alternating moves.
- (c) State monad: `OnlineLearner S := S → X → (Y × S)` where S is internal state.

The Littlestone dimension definition requires TREES (mistake trees). The characterization theorem says `OnlineLearnable H M ↔ LittlestoneDim H ≤ M`. This means the learner type must be compatible with tree-based arguments. Option (c) with explicit state seems most natural for stating the characterization.

### KU₄: Gold model computability requirements
Gold's model involves computable learners and computably enumerable concept classes. Options:
- (a) Use Lean4's `Computable` attribute / Mathlib's computability library
- (b) Use `ℕ → ℕ` (Gödel-numbered) representations
- (c) Ignore computability in type signatures, state it as hypotheses on theorems

The concept graph has `partial_computable`, `limiting_recursion`, `delta_02_class`, `godel_numbering` as nodes. These are ALL L0 base types feeding into the Gold paradigm. Option (c) loses too much — the computability IS the point of Gold's model vs PAC. Option (a) is ideal but may not compose well with the set-theoretic `Set (X → Y)` choice for ConceptClass.

**Predicted tension:** `Set (X → Y)` is great for PAC/Online. For Gold, we need `Set (X → Y)` where members are partial computable. This requires either a subtype `{f : X → Y // Computable f}` or a predicate `IsComputable : (X → Y) → Prop`. The concept graph's `extends_grammar` edge from `ex_learning` to `pac_learning` predicts exactly this friction.

### KU₅: Universal learning rate typing
Universal learning's trichotomy produces three possible RATES:
- Exponential: `e^{-n}` (finite Littlestone tree)
- Polynomial: `1/n` (infinite Littlestone tree, finite VCL tree)
- Arbitrarily slow (infinite VCL tree)

The rate is a FUNCTION `ℕ → ℝ` up to constants. How to type:
- (a) `UniversalRate := ℕ → ℝ` with `O(·)` comparison
- (b) Enum `{exponential, polynomial, arbitrarilySlow}`
- (c) The trichotomy as three separate Props

Option (c) is cleanest for stating the trichotomy theorem. The rate function matters for sample complexity bounds, which are separate theorems.

### KU₆: PAC-Bayes output type
Standard PAC learner outputs a hypothesis `h : X → Y`. PAC-Bayes learner outputs a DISTRIBUTION `Q : Measure (X → Y)`. This is a genuine type change, not a parameter. The `extends_grammar` edge from `pac_bayes_bound` to `pac_learning` in the concept graph confirms this.

How to handle:
- (a) Separate `PACBayesLearner` type that outputs `MeasureTheory.Measure H`
- (b) Generalize all learners to output distributions (PAC = point mass)
- (c) PAC-Bayes as a bound framework, not a learner type

The concept graph lists `pac_bayes_bound` as a success_criterion (L4), not a complexity_measure (L5). This suggests it's a learning paradigm, not just a bound. Option (a) seems right — separate type, with a bridge showing PAC-Bayes with point-mass prior recovers PAC.

### KU₇: Multiclass dimension type universe
Natarajan dim needs `Set (X → Y)` with `|Y| ≥ 2`. DS dim needs the same but with a fundamentally different combinatorial structure (one-inclusion hypergraphs, pseudo-cubes). Both are `ℕ∞`-valued.

Key constraint from concept graph: DS dim characterizes multiclass PAC learnability for ALL Y (including infinite). Natarajan dim characterizes only for finite Y. The type signatures must ALLOW stating this distinction — i.e., the DS characterization theorem should NOT have `[Fintype Y]` in its hypotheses, while the Natarajan characterization SHOULD.

### KU₈: File dependency order
The concept graph's `defined_using` edges give a DAG. The file structure must respect this DAG — no circular imports. The 99 `defined_using` edges determine which files can import which.

**Constraint:** Lean4/Mathlib convention is that files import upward. `Theorem/Fundamental.lean` imports `Complexity/VCDim.lean` which imports `Basic.lean`. Circular dependencies are a compile error.

---

## UK — What Likely Exists But Hasn't Been Checked

### UK₁: Existing Lean4 formalizations of learning theory
There may be partial Lean4 formalizations of PAC learning, VCdim, or online learning beyond Mathlib's `Finset.Shatters` and lean-rademacher. A literature/GitHub search would reveal whether anyone has typed `PACLearnable` in Lean4 before.

### UK₂: Mathlib's `FunLike` pattern
Mathlib uses `FunLike` extensively for function-like structures. Whether `ConceptClass` should be a `FunLike` instance (giving us coercion to `X → Y` for free) is a UK that becomes KK upon reading Mathlib source.

### UK₃: lean-rademacher's actual import structure
The exact types and universe levels used by lean-rademacher determine how our generalization bound types compose. Haven't inspected the source.

### UK₄: How Mathlib handles `WithTop ℕ` arithmetic
Our VCdim and Ldim are `ℕ∞ = WithTop ℕ`. Theorems like "VCdim H ≤ Ldim H" need `ℕ∞` arithmetic. Mathlib's `WithTop` API may or may not have the lemmas we need (e.g., `WithTop.add_le_add`).

### UK₅: Universe polymorphism requirements
`Set (X → Y)` lives in `Type (max u v)` when `X : Type u` and `Y : Type v`. Whether this creates universe issues when composing with Mathlib's measure theory (which may fix universes) is a UK.

---

## UU — Boundary of Current Askability

### UU₁: Whether the 5 predicted Break Points are real
BP₁–BP₅ (three learner types with no common parent, VCdim vs OrdinalVCdim type break, PAC vs Online universal quantifier difference, function-class → set-family information loss, five generalization bound signatures) are PREDICTED structural observations. Whether they're genuine type-theoretic obstructions or artifacts of our design choices is unknowable until someone (Path B) attempts a principled unification.

### UU₂: Whether `Set (X → Y)` is the right universe
The choice `Set (X → Y)` means ConceptClass is `Type 1` (a set of functions). An alternative universe where ConceptClass is a `Type 0` (a concrete structure with a finite description) might be more natural for computability-theoretic concepts. We can't know which universe is "right" without trying both.

### UU₃: Whether the type skeleton predicts which theorems are hard to prove
If the type architecture is good, the `sorry`-marked theorems should fall into two categories: (a) those whose types obviously constrain the proof strategy, and (b) those whose types leave the proof strategy open. The ratio of (a) to (b) would measure typing quality. But we can't compute this ratio without attempting the proofs (Step (b) Phase 1–4).

---

## Measurements: Applying Task-URS-Manuscript to Type Architecture Clusters

Unlike a textbook where each concept gets its own profile, a type architecture has CLUSTERS of definitions that must be designed together. The measurement applies at cluster level.

### Cluster 1: Base Types (L0–1) — 15 nodes
**M = (g_Pl=0.15, g_Coh=0.05, Inv=0.95, Comp=0.90)**
- g_Pl=0.15: `concept_class` has contested typing (Set vs typeclass vs structure). All other base types are crisp.
- g_Coh=0.05: These are dependency sinks — everything points TO them, they compose trivially downward.
- Inv=0.95: Base types are maximally robust across paradigms.
- Comp=0.90: All 15 have clear definitions. Only `concept_class` needs design attention.
- **Profile: A (Vocabulary)** — except `concept_class` which is **G (Framework Bridge)**: the hub node that every paradigm measures differently.
- **Centerpiece:** The `concept_class` definition and its coercion to Mathlib's `Finset (Finset α)`.
- **Design effort:** Low (2–3 days). Write once, shouldn't need revision.

### Cluster 2: Data Presentations (L2) — 12 nodes
**M = (g_Pl=0.10, g_Coh=0.35, Inv=0.30, Comp=0.85)**
- g_Pl=0.10: Each data model has one clear definition.
- g_Coh=0.35: HIGH Coh_fail — the data models are INCOMPATIBLE with each other. `IIDSample` is a `Fin n → X × Y`; `Text` is `ℕ → X`; `Informant` is `ℕ → X × Y`; `Oracle` is a function `X → Y`. These don't compose.
- Inv=0.30: LOW — each data model is specific to its paradigm. IIDSample only makes sense for PAC.
- Comp=0.85: All have clear typing.
- **Profile: D (Negative Result)** — the incompatibilities ARE the content. The type system makes paradigm boundaries VISIBLE.
- **Centerpiece:** The THREE separate data types and why they CAN'T be unified.
- **Design effort:** Medium. Must resist the urge to force a common `DataModel` typeclass.

### Cluster 3: Learner Types (L3) — 15 nodes
**M = (g_Pl=0.40, g_Coh=0.45, Inv=0.25, Comp=0.70)**
- g_Pl=0.40: HIGH — the BatchLearner vs OnlineLearner vs GoldLearner typing is genuinely contested. Per-paradigm is locked but the INTERNAL structure of each learner type has multiple defensible options (state monad, function type, structure).
- g_Coh=0.45: HIGH Coh_fail — the three learner types share nothing in the type system. This is predicted Break Point BP₁.
- Inv=0.25: LOW — each learner type is fragile outside its paradigm.
- Comp=0.70: The 15 learner specializations (conservative, consistent, set-driven, etc.) are modifiers on the base types. Some may not need their own type.
- **Profile: E (Obstruction/Analogy)** — three parallel types with the SAME informal meaning ("learner") but incompatible formal types. The obstruction analysis IS the design content.
- **Centerpiece:** Why three separate types, and what each loses by not having a parent.
- **Design effort:** HIGH. This is the hardest cluster. BP₁ lives here.

### Cluster 4: Success Criteria (L4) — 20 nodes
**M = (g_Pl=0.20, g_Coh=0.50, Inv=0.20, Comp=0.85)**
- g_Pl=0.20: Each criterion has a clear mathematical definition (PAC, Online, Gold, Universal, Bayesian). Minor ambiguity in agnostic vs realizable PAC.
- g_Coh=0.50: HIGHEST Coh_fail — the criteria quantify over DIFFERENT things (distributions, adversaries, streams, rates). This is predicted BP₃.
- Inv=0.20: LOW — each criterion is specific to its paradigm.
- Comp=0.85: All 20 have clear formal definitions in the concept graph.
- **Profile: G (Framework Bridge)** — the criteria are the PAC-Online-Gold JOINT. The parallels AND the divergences are the content.
- **Centerpiece:** The five `*Learnable` Props on the same `H : Set (X → Bool)` — same input, different questions.
- **Design effort:** Medium-high. The joint structure requires careful theorem statement design.

### Cluster 5: Complexity Measures (L5) — 33 nodes
**M = (g_Pl=0.10, g_Coh=0.30, Inv=0.40, Comp=0.75)**
- g_Pl=0.10: Each measure has a crisp definition.
- g_Coh=0.30: Moderate Coh_surprise — measures from different paradigms have SURPRISING relationships (VCdim ≤ Ldim, Rademacher ≤ f(VCdim)).
- Inv=0.40: Moderate — measures extend across settings (binary → multiclass, combinatorial → probabilistic) but change type signature when they do.
- Comp=0.75: All defined, but open problems exist (compression conjecture, exact constants).
- **Profile: C (Revelation)** — the surprise is that so many different-looking measures are CONNECTED.
- **Centerpiece:** The inequality web connecting VCdim, Ldim, Rademacher, sample complexity. And the type-break between `ℕ∞`-valued and `Ordinal`-valued measures (BP₂).
- **Design effort:** Medium. Many definitions, but each is individually simple. The challenge is the BRIDGE theorems between measures.

### Cluster 6: Theorems (L6) — 16 proved nodes
**M = (g_Pl=0.05, g_Coh=0.15, Inv=0.50, Comp=0.60)**
- g_Pl=0.05: Theorem statements are crisp.
- g_Coh=0.15: Theorems compose cleanly via `used_in_proof` edges.
- Inv=0.50: Some theorems (fundamental theorem) break when extended beyond binary 0-1 loss.
- Comp=0.60: Theorems are STATED (this task) but not proved (that's Step (b)).
- **Profile: B (Load-Bearing Theorem)** — but with all proofs as `sorry`. The type signatures must PREDICT the right proof structure.
- **Centerpiece:** The fundamental theorem's 9-way equivalence — stating it with the right type is the hardest theorem-level design task.
- **Design effort:** Medium-high for statement design. The hypotheses must be neither too many (decorative) nor too few (false statement).

### Cluster 7: Generalization Bounds — 5 bound frameworks
**M = (g_Pl=0.15, g_Coh=0.55, Inv=0.35, Comp=0.80)**
- g_Pl=0.15: Each bound has a clear statement.
- g_Coh=0.55: HIGHEST Coh_surprise — five different-looking bounds all bound the SAME quantity (generalization error). This is BP₅.
- Inv=0.35: Each bound requires its own framework-specific objects (prior P, stability β, mutual information I).
- Comp=0.80: All bounds well-established.
- **Profile: G (Framework Bridge)** — five frameworks converging on one quantity.
- **Centerpiece:** Common `LossFunction`, `EmpiricalRisk`, `TrueRisk` infrastructure shared by all five bounds.
- **Design effort:** Medium. The common infrastructure is straightforward; the framework-specific types are each simple.

---

## Break Points (Predicted, for Path B documentation)

| BP | Location | Nature | Why It's a Break |
|----|----------|--------|------------------|
| BP₁ | `Learner/` directory | Three learner types, no common parent | BatchLearner, OnlineLearner, GoldLearner share nothing in the type system. In learning theory they're all "learners." |
| BP₂ | `Complexity/` directory | VCdim = ℕ∞ but OrdinalVCdim = Ordinal | Same conceptual measure at different types. No typeclass unifies them. |
| BP₃ | `Criterion/` directory | PAC quantifies over measures, Online over adversaries | Both ask "does H support learning?" but ∀ ranges over different categories. |
| BP₄ | `Bridge/FunctionToSet.lean` | Function-class → set-family bridge is lossy | Converting `Set (X → Bool)` to `Finset (Finset X)` loses function structure. |
| BP₅ | `Bound/` directory | Five generalization bounds, five signatures | No common interface without losing each bound's content. |

---

## File Structure (locked)

```
LimitsOfLearning/
├── Basic.lean              -- L0-1: ConceptClass, HypothesisSpace, Loss
├── Data/
│   ├── IID.lean            -- L2: IIDSample, Distribution
│   ├── Stream.lean         -- L2: DataStream, Text, Informant
│   └── Oracle.lean         -- L2: MembershipOracle, EquivalenceOracle
├── Learner/
│   ├── Batch.lean          -- L3: BatchLearner (PAC)
│   ├── Online.lean         -- L3: OnlineLearner (adversarial)
│   └── Gold.lean           -- L3: GoldLearner (identification)
├── Criterion/
│   ├── PAC.lean            -- L4: PACLearnable, AgnosticPACLearnable
│   ├── Online.lean         -- L4: MistakeBounded, RegretBounded
│   ├── Gold.lean           -- L4: ExLearnable, BCLearnable, FINLearnable
│   ├── Universal.lean      -- L4: UniversalLearnable, Trichotomy
│   └── Bayes.lean          -- L4: PACBayesBound, PosteriorConsistency
├── Complexity/
│   ├── VCDim.lean          -- L5: Bridge to Mathlib's Finset.vcDim
│   ├── Littlestone.lean    -- L5: MistakeTree, LDim
│   ├── Rademacher.lean     -- L5: Bridge to lean-rademacher
│   ├── Compression.lean    -- L5: CompressionScheme
│   ├── SQ.lean             -- L5: SQDim
│   ├── Multiclass.lean     -- L5: NatarajanDim, DSDim
│   ├── RealValued.lean     -- L5: PseudoDim, FatShatDim
│   ├── MindChange.lean     -- L5: MindChangeCount, MindChangeOrd
│   └── Ordinal.lean        -- L5: OrdinalLDim, OrdinalVCDim, VCLTree
├── Theorem/
│   ├── Fundamental.lean    -- L6: VCDim ↔ PAC (9-way equiv)
│   ├── SauerShelah.lean    -- L6: Bridge to Mathlib's Sauer-Shelah
│   ├── Gold.lean           -- L6: Gold's theorem
│   ├── NFL.lean            -- L6: No Free Lunch
│   ├── Trichotomy.lean     -- L6: Universal learning trichotomy
│   ├── Hardness.lean       -- L6: Computational hardness
│   └── Separation.lean     -- L6: All does_not_imply + strictly_stronger
├── Bound/
│   ├── Rademacher.lean     -- Rademacher gen bound
│   ├── PACBayes.lean       -- PAC-Bayes bound
│   ├── Stability.lean      -- Stability bound
│   ├── InfoTheoretic.lean  -- Info-theoretic bound
│   └── Margin.lean         -- Margin bound
└── Bridge/
    ├── VCtoRademacher.lean -- VC-to-Rademacher reduction
    ├── PACtoOnline.lean    -- VCdim ≤ Ldim
    └── FunctionToSet.lean  -- Function class → Finset set family
```

---

## γ — Discovery Targets

1. **Resolve KU₁–KU₈** by writing code and checking compilation
2. **Discover which concept graph nodes DON'T need their own Lean4 definition** (many L3 learner variants may be predicates on a base type rather than separate types)
3. **Discover the minimal typeclass hierarchy** — what NEEDS to be a typeclass vs what's just a `def`
4. **Discover whether BP₁–BP₅ are genuine** by attempting to state cross-paradigm theorems (separations) and checking whether the types fight back
5. **Discover the import DAG** — which files can import which without circularity

## Γ — Inquiry Actions

- Write `Basic.lean` first (foundation types) → compile → iterate
- Write each cluster in dependency order (L0→L1→L2→L3→L4→L5→L6)
- For each cluster, write definitions first, then theorem STATEMENTS
- After all files compile, attempt to state one cross-paradigm theorem (separation) to test whether the types compose across paradigm boundaries
- Document every ad-hoc design choice in `BREAKS.md`

## η — Efficiency Assessment

**Predicted η = moderate.** A well-designed type grammar for all of formal learning theory in a single Lean4 project doesn't exist. The grammar IS the contribution — but only if the types are right (theorems provable without type rewrites). If we force artificial unification or miss genuine structure, η drops to zero because every proof requires ad-hoc type coercions.

**Verification:** After skeleton compiles, pick 3 theorems from different paradigms (1 PAC, 1 Online, 1 separation) and attempt proof. If the proof attempt reveals type friction (needing coercions, missing instances, wrong universe levels), the typing is bad. If the proof attempt flows naturally from the types, the typing is good.

---

## Homogeneity Warning Protocol

For this task, the homogeneity risk is: treating every concept graph node as "write a definition, state a theorem, sorry the proof." The measurements above show that clusters have DIFFERENT profiles:
- L0–1 base types → Profile A (minimal ceremony, just write the def)
- L2 data types → Profile D (the incompatibility is the content)
- L3 learner types → Profile E (the obstruction analysis drives the design)
- L4 success criteria → Profile G (the parallels AND divergences matter)
- L5 complexity measures → Profile C (the surprising connections are the content)
- L6 theorems → Profile B (statement design is the work)
- Bounds → Profile G (five frameworks, one target)

If I find myself writing the same `structure Foo where ... sorry` pattern for every node, that's the homogeneity alarm. Each cluster demands a different design approach.
