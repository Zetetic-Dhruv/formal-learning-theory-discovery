# Break Points — Formal Learning Theory Type Architecture

This document catalogs every point where the Lean4 type system forces an ad-hoc choice
in formalizing learning theory. These are genuine type-theoretic obstructions, not
implementation shortcuts.

## Break Point Inventory

### BP₁: No Common Learner Parent

**Location:** `LimitsOfLearning/Learner/Core.lean`

**Description:** The concept graph has `learner` as a hub node (20 incoming edges), but
PAC, Online, and Gold learners have incompatible type signatures:
- BatchLearner: `{m : ℕ} → (Fin m → X × Y) → Concept X Y`
- OnlineLearner: `State → X → Y` (+ update function)
- GoldLearner: `List (X × Y) → Concept X Y`

**Alternatives considered:**
1. Common typeclass `class Learner` with associated types — compiles but downstream
   theorems can't be stated generically (success criteria differ per paradigm)
2. Sum type `Learner := PAC | Gold | Online` — forces pattern matching in every theorem
3. Dependent type `Learner (p : Paradigm)` — ad hoc and unmathematical

**Choice made:** Separate structure types per paradigm.

**Why ad-hoc:** The three learner types DO share conceptual content (they all map data
to hypotheses). The type system can't express "data → hypothesis" without committing
to a specific data presentation and output format.

---

### BP₂: VCdim = ℕ∞ vs OrdinalVCdim = Ordinal

**Location:** `LimitsOfLearning/Complexity/VCDimension.lean`, `LimitsOfLearning/Bridge.lean`

**Description:** Classical complexity measures take values in `WithTop ℕ`. Universal
learning theory extends them to ordinals. The types `WithTop ℕ` and `Ordinal` have
fundamentally different algebraic structures:
- `WithTop ℕ` has exactly one infinite value (⊤)
- `Ordinal` has a proper class of infinite values (ω, ω², ω^ω, ε₀, ...)

The embedding `WithTop ℕ ↪ Ordinal` sends `n ↦ n` and `⊤ ↦ ω`. But ordinal VC dimension
can be ω², which has no `WithTop ℕ` preimage.

**Alternatives considered:**
1. Use only `Ordinal` everywhere — but most theorems (Sauer-Shelah, PAC bounds) work
   with finite VCDim and using Ordinal would force unnecessary complexity
2. Use only `WithTop ℕ` — but universal learning results are unprovable without ordinals
3. Type alias with coercion — hides the genuine structural difference

**Choice made:** Separate types with explicit embedding bridge (`withTopNatToOrdinal`).

**Why ad-hoc:** Both `WithTop ℕ` and `Ordinal` are correct in their respective paradigms.
The choice to maintain both is correct engineering but the BRIDGE between them is
ad-hoc — there's no canonical way to lift a `WithTop ℕ`-valued theorem to ordinals.

---

### BP₃: PAC Measures vs Online Adversaries (Data Interface Break)

**Location:** `LimitsOfLearning/Data.lean`

**Description:** The three paradigms present data in fundamentally incompatible ways:
- PAC: `IIDSample` (distribution + finite sample with i.i.d. property)
- Gold: `DataStream` / `TextPresentation` (infinite stream with exhaustiveness)
- Online: adversary-chosen sequence (no distribution, no exhaustiveness guarantee)

**Alternatives considered:**
1. Common `DataInterface` sum type — forces pattern matching in every theorem
2. Typeclass `DataSource` — artificial; the three interfaces share no methods
3. Dependent type indexed by paradigm — ad hoc

**Choice made:** Separate structure types per paradigm.

**Why ad-hoc:** The data interfaces share the conceptual idea of "information source"
but differ in every structural property (finite/infinite, distributional/adversarial,
exhaustive/non-exhaustive). The type system can't express the shared structure.

---

### BP₄: Function-Class → Set-Family Bridge is Lossy

**Location:** `LimitsOfLearning/Bridge.lean`

**Description:** Many Mathlib results work with `Set (Set X)` (set families). Our types
use `ConceptClass X Bool = Set (X → Bool)` (function classes). The bridge:
```
C ↦ { { x : c(x) = true } : c ∈ C }
```
is classically an equivalence for `X → Bool` (every set corresponds to its
characteristic function), but the Lean4 type system treats them as different types
requiring explicit coercion.

**Alternatives considered:**
1. Use `Set (Set X)` everywhere — loses function application syntax
2. Use `X → Bool` everywhere — loses membership notation from Mathlib
3. Definitional equality trick — doesn't work because `Set X` ≠ `X → Prop` ≠ `X → Bool`

**Choice made:** Explicit bridge functions `conceptClassToSetFamily` and `setFamilyToConceptClass`
with a round-trip theorem.

**Why ad-hoc:** The bridge IS lossless for Boolean concepts, but proving this requires
function extensionality + propositional extensionality at each use site. For non-Boolean
labels (multiclass), the bridge doesn't exist at all.

---

### BP₅: Five Generalization Bounds with Different Signatures

**Location:** `LimitsOfLearning/Theorem/PAC.lean`

**Description:** The fundamental theorem equates PAC learnability with five different
characterizations, each using a complexity measure with a DIFFERENT type signature:
1. `VCDim` : `WithTop ℕ` — combinatorial, dimension-like
2. `RademacherComplexity` : `ℝ` — analytic, depends on distribution and sample size
3. `CompressionScheme` : structure with `size : ℕ`, `compress`, `reconstruct`
4. `AlgorithmicStability` : structure with `beta : ℝ`, `stable`
5. `GrowthFunction` : `ℕ → ℕ` — combinatorial function

**Alternatives considered:**
1. Single `ComplexityMeasure` typeclass — but the five measures have genuinely different
   arities and signatures (VCDim takes only C; Rademacher takes C, D, and m)
2. Sum type — possible but every theorem would need to case-split on measure type
3. `GeneralizationBound` structure — would hide WHICH measure drives the bound

**Choice made:** Separate pairwise equivalence theorems (`fundamental_vc_compression`,
`fundamental_rademacher`, etc.) rather than a single N-way equivalence.

**Why ad-hoc:** The mathematical content IS that these five different things are equivalent.
The type system can express pairwise equivalences but not "these five heterogeneous types
are all equivalent characterizations of the same property."

---

### BP₆: ConceptClass is Over-Connected (22 incoming edges)

**Location:** `LimitsOfLearning/Basic.lean`

**Description:** `ConceptClass` has 22 incoming edges in the concept graph — far more
than any other node. It's used by every paradigm, every complexity measure, every
criterion, and most theorems. This creates pressure for FOUR alternative definitions
(decidable, RE, measurable, multiclass), each serving a different paradigm's needs.

**Choice made:** Primary type is `Set (X → Y)` with commented alternative definitions.

**Why it's a break:** The type `Set (X → Y)` compiles everywhere but is too permissive —
it allows pathological concept classes that break measure-theoretic proofs, computability
proofs, and decidability proofs. Each paradigm needs a RESTRICTION of ConceptClass that
the primary type doesn't enforce. The restrictions are incompatible with each other
(measurable ≠ RE ≠ decidable).

---

### BP₇: Bayesian Prior Has No Canonical Type

**Location:** `LimitsOfLearning/Learner/Bayesian.lean`, `LimitsOfLearning/Computation.lean`

**Description:** A Bayesian prior over hypotheses can be:
- A probability mass function: `Concept X Y → ℝ≥0` (discrete case)
- A probability measure: `MeasureTheory.ProbabilityMeasure (Concept X Y)` (continuous)
- A scoring function: `Concept X Y → ℝ` (unnormalized, used in MDL/MML)

The choice matters for which Bayesian theorems can be stated:
- Posterior consistency (Doob's theorem) needs the measure-theoretic version
- PAC-Bayes bounds work with the scoring version
- Computational results need the discrete version

**Choice made:** `BayesianInference` uses `Concept X Y → ℝ` as primary (unnormalized);
alternative `BayesianLearnerMeas` uses ProbabilityMeasure.

---

## Compilation-Discovered Constraints (C₁-C₅)

These are Lean4 substrate constraints that emerged during compilation.

### C₁: Σ is a Lean4 keyword
**Impact:** All formal language types use `Sym` instead of the mathematically natural `Σ`.

### C₂: ℝ≥0 notation requires explicit import
**Impact:** BayesianInference uses `ℝ` instead of `NNReal` for prior/likelihood/posterior.
Non-negativity lost at type level. Alternative: import `Mathlib.Data.NNReal.Defs` and
use `NNReal` fields.

### C₃: `def` blocks typeclass synthesis
**Impact:** ConceptClass, HypothesisSpace, DriftRate changed from `def` to `abbrev` so
that Lean4's elaborator can unfold them for Set membership and LE/Zero instance resolution.

### C₄: TextPresentation DataStream X Unit → DataStream X Bool
**Impact:** TextPresentation originally used `Unit` labels (text provides no label info).
Changed to `Bool` (text provides `true` labels) for compatibility with
`GoldLearner.conjecture : List (X × Bool) → Concept X Bool`.

### C₅: Ordinal universe annotation required
**Impact:** `VCLTree.value : Ordinal` needed explicit `.{0}` universe annotation.
Fixed to countable ordinals.

## Summary Statistics

| Metric | Value |
|--------|-------|
| Total break points | 7 |
| Compilation constraints (C₁-C₅) | 5 |
| With alternative definitions | 4 (BP₁, BP₂, BP₆, BP₇) |
| Blocking theorem statements | 3 (BP₁, BP₃, BP₅) |
| Requiring explicit bridges | 2 (BP₂, BP₄) |
| **Compilation status** | **0 errors, 69 sorry warnings** |
| **Sorry-in-Prop remaining** | **0** |
| **Trivially-true conclusions** | **0** |
