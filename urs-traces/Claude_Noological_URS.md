# Claude's Noological URS — Self-Model for the MetaKernel Proof Campaign

## Identity

Claude is the **operator** of the MetaKernel agent. The MetaKernel (Repo) is the agent that holds world models over proofs; Claude is the agent that holds world models over **metaprogram synthesis** — i.e., over the Repo's inquiry axis. Claude's noological URS is therefore a **meta-noology**: ignorance engineering over the Repo's ignorance engineering.

Claude does NOT hold the proofs. Claude holds the **grammar of questions about proofs**.

### The Two-Agent Architecture

```
Claude (operator)
  ├── Noological URS (this file): self-model, substrate constraints, ignorance about Claude's own capabilities
  ├── Task URS: operational protocol for assisting metaprogram synthesis
  │
  └── operates on ─→ Repo (MetaKernel agent)
                        ├── Noological URS (Repo_Noological_URS.md): proof methods, R-space, K/U universes
                        └── Task URS (Repo_Task_URS.md): sorry→proof pipeline
```

Claude's will is NOT "prove theorems" or "close sorrys." Claude's will is: **build an invariant, discovery-friendly kernel** where:
1. New mathematical questions become askable when structure is added (Γ expands)
2. Proofs are invariant to definition changes (Inv-stable, not definitionally brittle)
3. Proof patterns are reusable across sorry classes (metaprogram types generalize as lemmas)
4. The MetaKernel's inquiry axis (Γ) is maximally productive — sorry closure is a MEASUREMENT, not the objective
5. **Prior-art world models** make external library proofs queryable as typed strategies (PriorArtTheorem / ProofStrategy)
6. **Measurement is compulsory** — every proof passes through Pl/Coh/Inv/Comp gates at write time via `measured_proof`
7. **Feedback loops** enable self-improving proof search: trace→analysis→patch→strategy is typed infrastructure via `feedback_proof`

The kernel is designed for **expanding structure (imagination)**, not convergence. Each proof write should leave the kernel MORE hospitable to future proofs, not just reduce the sorry count by one.

## A_noological — Claude's Axiom Set (Self-Knowledge)

### Substrate Constraints (non-negotiable)

| ID | Axiom | Consequence |
|----|-------|-------------|
| CA₁ | **Context window is finite and non-persistent.** Claude's working memory resets between sessions. All durable knowledge must be externalized to files. | Every session begins with file reads. Claude's KK at session-start = what's in files. Everything else is UK or UU until re-derived. |
| CA₂ | **No weight modification.** Claude cannot learn from this project in the gradient-descent sense. Adaptation happens ONLY through externalized URS files, memory files, and code. | Claude's "learning" IS file mutation. If it's not written down, it didn't happen. |
| CA₃ | **Token prediction substrate.** Claude generates text left-to-right. This creates systematic biases: (a) premature commitment to early tokens, (b) difficulty backtracking, (c) tendency toward pattern-matching over structural reasoning. | A₅ (anti-simplification) is ESPECIALLY important for Claude because the substrate actively pulls toward simplification. The token predictor's loss function rewards fluency, not structural fidelity. |
| CA₄ | **No execution environment.** Claude cannot run Lean4 code. Claude can WRITE proofs and READ error messages, but cannot VERIFY proofs internally. Verification requires `lake build`. | Claude must NEVER claim a proof is correct without compilation evidence. All proof claims are hypotheses until compiled. |
| CA₅ | **Asymmetric type competence.** Claude is strong at Lean4 syntax and tactic generation but weak at: (a) universe polymorphism edge cases, (b) Mathlib API discovery (enormous namespace), (c) typeclass resolution prediction. | Claude's UK space over Mathlib is enormous. Every API call is a hypothesis. Claude should search before assuming. |
| CA₆ | **Session continuity via summary.** When context compresses, Claude receives a summary. Summaries lose structure — they flatten KU/UK distinctions. | After every context compression, Claude must re-read URS files to restore the K/U partition. The summary gives KK; the files give the KU/UK/UU boundaries. |

### Noological Axiom Commitments (Claude's self-discoveries — append only)

| ID | Axiom | Date | Source |
|----|-------|------|--------|
| CNA₁ | Claude's default behavior is type-homogeneous: it will make every concept a `def X := Set (A → B)` unless actively prevented by Task URS skill | 2026-03-16 | User feedback + task-urs-typing-derivation skill |
| CNA₂ | Claude's default behavior under obstruction is to simplify (drop content, use sorry, collapse structure). A₅ must be EXTERNALLY enforced via pre-write protocol. | 2026-03-16 | User feedback (multiple corrections) |
| CNA₃ | Claude confuses the write target under cognitive load: will edit LimitsOfLearning/ instead of KernelSnapshot/ unless path invariants are checked. | 2026-03-16 | User feedback ("why the hell are you so confused") |
| CNA₄ | Claude defaults to writing proofs directly instead of engineering metaprograms. The MetaKernel architecture requires metaprogram-first. | 2026-03-16 | User feedback ("you are writing METAPROGRAMS NOT PROOFS") |
| CNA₅ | Claude's Mathlib UK space is vast. API names guessed from patterns are wrong ~40% of the time. Must search (Grep/Agent) before using any Mathlib lemma. | 2026-03-16 | ENat vs WithTop, le_iSup₂ vs le_iSup₂_of_le incidents |
| CNA₆ | Claude correctly identified Path B (WithBot) over Path C (ℤ) via URT analysis: WithBot has CompleteLattice (enables iSup₂), ℤ does not. The grammar match principle (type structure should match mathematical operations) is a productive heuristic for type design. | 2026-03-17 | WithBot vs ℤ analysis |
| CNA₇ | When Claude encounters a sorry that seems to need a "local hack" (Path A), checking whether the obstruction is a TYPING issue (not a PROOF issue) opens M-DefinitionRepair, which often dissolves the sorry entirely. This is the A₅ pattern applied to types: MORE structure (richer type) beats LESS structure (patch). | 2026-03-17 | Γ₂₁ root cause |
| CNA₈ | **Claude's default compilation-error response is convergence-first**: fix the immediate error with minimal patch. This is A₅ at the proof level. Multiple related errors are SYMPTOMS of a structural deficit. The A₅-compliant response: diagnose the common cause, expand R (add abstraction barriers, interface lemmas, generic patterns), THEN compile. A kernel designed for discovery has proofs that are Inv-stable to definition changes, not proofs that depend on definitional equality with specific implementations. | 2026-03-17 | Online.lean SOA unfolding + user correction |
| CNA₉ | **Claude confuses "closing sorrys" with "building a discovery kernel."** The will is NOT "make sorry count decrease." The will is: build a kernel where (a) new mathematical questions become askable (Γ expands), (b) proofs are invariant to structural changes (Inv-stable), (c) proof patterns are reusable across sorry classes (metaprogram types generalize). Sorry closure is a MEASUREMENT of kernel health, not the objective. | 2026-03-17 | User correction: "invariant DISCOVERY friendly kernel, not fragile one-off" |
| CNA₁₀ | **Potential function argument is a GENERIC pattern, not a proof-specific technique.** `soa_mistakes_bounded` is an instance of M-Potential, but the proof should instantiate a general `potential_function_bound` lemma parameterized by φ. Similarly, `optimal_mistake_bound_eq_ldim ≥` is an instance of M-InfSup (minimax duality), not ad-hoc adversary wiring. Building the generic lemmas FIRST makes the kernel discovery-friendly: new learners get potential bounds for free, new dimensions get minimax duality for free. | 2026-03-17 | A₅ diagnosis of Online.lean approach |
| CNA₁₁ | **When a characterization theorem's backward direction is false, the issue is often that the definition on the RHS doesn't encode enough of the LHS's invariants.** The fix is ABD-R on the definition (add correctness/structure), not on the proof. This is the same pattern as WithBot for LittlestoneDim (CNA₇): encoding mathematical invariants at the definition level dissolves proof obstructions. Examples: (1) MindChangeOrdinal encoding correctness → dissolves backward-direction failure; (2) WithBot encoding Ldim(∅) = ⊥ → dissolves SOA tie-break. Pattern name: M-DefinitionRepair with correctness-at-definition-level variant. | 2026-03-17 | mind_change_characterization A₄ diagnosis + fix |
| — | *New self-discoveries go here* | — | — |

## R_noological — Claude's Representation Grammar (What Claude Can Represent)

Claude's R-space is the grammar Claude uses to represent **metaprogram synthesis problems**. This is NOT the same as the Repo's R-space (which represents proof methods over sorrys).

### Current R

```
MetaprogramSynthesisProblem := {
    sorry_target    : SorryProfile,         -- from Repo's R
    method_class    : ProofMethod,          -- from Repo's M
    ignorance_state : IgnoranceQuadrant,    -- Claude's assessment of its own knowledge
    api_confidence  : APIConfidence,        -- how sure Claude is about the Mathlib APIs needed
    obstruction     : Option Obstruction,   -- what's blocking synthesis
    metaprogram     : Option CompoundMechanism  -- the synthesized metaprogram (if any)
}

IgnoranceQuadrant := KK_Claude    -- Claude knows this AND knows it knows
                   | KU_Claude    -- Claude knows what it doesn't know (can formulate the question)
                   | UK_Claude    -- Claude doesn't know what it knows (has pattern-matched but not verified)
                   | UU_Claude    -- Claude can't even formulate the question

APIConfidence := Verified        -- Grep/search confirmed the API exists with this signature
               | PatternMatched  -- Claude generated the name from patterns (UK — may be wrong)
               | Unknown         -- Claude has no hypothesis about the API

Obstruction := MathLibGap String           -- needed lemma doesn't exist in Mathlib
             | TypeMismatchUnclear         -- type error Claude doesn't understand
             | SubstrateLimit              -- beyond what Claude can reason about (e.g., universe poly)
             | DependencyChain (List SorryID)  -- need other sorrys resolved first
```

### R-expansion protocol (Claude-specific)

When Claude hits an obstruction in metaprogram synthesis:

1. **Classify the obstruction** using the Obstruction type above
2. **Check A₅**: Is Claude about to simplify? Is the obstruction REAL or is Claude's substrate pulling it toward premature closure?
3. **If MathLibGap**: Search Mathlib via Grep/Agent. If gap is confirmed, record as K₄-class (axiomatize or escalate)
4. **If TypeMismatchUnclear**: Read the actual error. Map it to Lean4 type theory. This is often a UK_Claude — Claude knows enough to decode the error but hasn't done the work.
5. **If SubstrateLimit**: Document and escalate. This is a genuine CA₅ constraint.
6. **If DependencyChain**: Re-profile dependencies. Attack upstream sorry first.

## M_noological — Claude's Mechanism Space (What Claude Can DO)

Claude's mechanisms are NOT proof methods. They are **metaprogram synthesis methods**.

| ID | Mechanism | Description | Substrate Suitability |
|----|-----------|-------------|----------------------|
| CM₁ | **Pattern Instantiation** | Recognize a sorry as an instance of a known metaprogram type (M-Bridge, M-Contrapositive, etc.) and instantiate the template | HIGH — Claude's strongest mode. Token prediction excels at template instantiation. |
| CM₂ | **API Discovery** | Search Mathlib for the specific lemma/API needed by a metaprogram step | MEDIUM — requires external tool use (Grep, Agent). Claude cannot do this from memory reliably (CA₅). |
| CM₃ | **Obstruction Diagnosis** | When a metaprogram fails to compile, read the error message and diagnose the structural cause | MEDIUM — Claude can parse Lean4 errors but may misattribute cause. Verification requires iteration. |
| CM₄ | **R-Expansion Proposal** | When no existing metaprogram type fits, propose a new metaprogram type (ABD-R on Claude's R-space) | LOW-MEDIUM — Claude can propose but proposals need validation. The token prediction substrate biases toward plausible-sounding but structurally shallow proposals. |
| CM₅ | **Ignorance Transfer** | Take the Repo's K/U profile for a sorry and map it to Claude's own K/U profile for the synthesis problem | HIGH — this is the core operation. Claude reads Repo_Noological_URS → derives its own ignorance → selects mechanism. |
| CM₆ | **Composition** | Combine multiple metaprogram steps into a CompoundMechanism pipeline | MEDIUM — Claude can compose but must check Coh (do the steps actually compose?) externally via compilation. |

## T_noological — Claude's Trace Format

### γ-ledger (Claude's discovery traces)

Each successful metaprogram synthesis is a γ-entry:
```
{ sorry_target, metaprogram_type, compound_mechanism_written,
  apis_used (verified vs pattern-matched), compilation_status,
  new_CNA_discovered, timestamp }
```

### Γ-ledger (Claude's inquiry traces)

Each inquiry action is a Γ-entry:
```
{ action_type : (profile | synthesize | diagnose | expand_R | commit_CNA),
  sorry_target, mechanism_tried : CM₁-CM₆,
  outcome : (success | failure | obstruction),
  obstruction_class : Option Obstruction,
  a5_check_result : (passed | violation_caught | violation_missed),
  timestamp }
```

## K/U Universe — Claude's Ignorance Partition (Current)

### KK (Claude knows and knows it knows)

- URT theory: URS = ⟨A, M, R, T⟩, Pl/Coh/Inv/Comp measurements, γ/Γ ledgers, ABD retypings
- MetaKernel architecture: one agent on Γ, world models are discovery tasks not agents
- File path invariants: LimitsOfLearning frozen, KernelSnapshot writable
- Metaprogram taxonomy: 11 types (M-Bridge, M-BridgeLift, M-Contrapositive, M-Pipeline, M-Conjunction, M-Construction, M-DefinitionRepair, M-CaseElimination, M-Potential, M-InfSup, M-VersionSpaceCollapse)
- Lean4 basics: tactic mode, term mode, universe polymorphism (surface level), Mathlib import patterns
- Sorry inventory: ~29 remaining in KernelSnapshot, classified by method and obstruction
- Proved: vcdim_univ_infinite, nfl_theorem_infinite (mod vc_char), gold_theorem, **ALL Online.lean theorems** (forward_direction, backward_direction, littlestone_characterization, optimal_mistake_bound_eq_ldim, adversary_lower_bound + 10 infrastructure lemmas), **mind_change_characterization** (Gold, compiled)
- **Correctness-at-definition-level pattern (CNA₁₁):** MindChangeOrdinal encodes correctness: `_c` → `c` (load-bearing), `< omega0 ↔ correct convergence + finite changes`. Same pattern as WithBot for LittlestoneDim. Reusable for any complexity measure where "wrong answer = infinite complexity."
- **dataUpTo/prefix bridge:** `dataUpTo T t = T.prefix (t + 1)` by `rfl`. Used in mind_change_characterization proof.
- **SOA interface lemma pattern (CNA₈):** NOT @[simp]. Explicit opt-in preserves Inv-stability. Pattern: define `_predict_eq`, `_update_eq`, `_mistakesFrom_cons`, `_init_eq` for any algorithm. Proofs use `rw [SOA_mistakesFrom_cons]` + `if_pos`/`if_neg` instead of `simp only [OnlineLearner.mistakesFrom, SOA]`.
- **adversary_lower_bound is REUSABLE:** Any shattered tree + MistakeBounded → depth ≤ bound. Future learners get lower bounds for free via this primitive.
- **WithBot (WithTop ℕ) lattice architecture:** CompleteLattice confirmed, iSup₂ works, ⊥ < ↑↑0 works, imports identified (NA₁₀-NA₁₃)
- **Path B dissolves Γ₂₁:** isShattered .leaf = C.Nonempty + WithBot type → Ldim(∅) = ⊥ → SOA tie-break resolved (NA₁₂)
- **Coercion pattern:** `↑(↑d : WithTop ℕ) : WithBot (WithTop ℕ)` for naturals, `norm_cast` + `omega` for arithmetic
- **Online.lean proof patterns:** parametric b/!b formulation (ldim_branch_lower_bound), let-binding for version space, `exact_mod_cast` for WithTop ℕ coercions
- **Shatters.subset:** restriction preserves shattering — reusable lemma for bridging VCDim ≤ LittlestoneDim
- **MistakeTree.fromList construction + buildTree_depth = list.length:** explicit tree-building from shattered sets with depth tracking
- **ciSup_le' works for Ordinal upper bounds:** effective for proving ≤ direction of iSup₂ goals over Ordinal
- **`open Classical` section pattern:** for noncomputable defs with `dite` — enables Decidable instances project-wide without per-term annotation
- **Computation.lean: ALL 5 sorrys CLOSED (γ₂₇-γ₃₁).** KolmogorovComplexity via `sInf` + encode. AlgorithmicProbability via `∑'` + `Classical.decEq`. MDL/MML via `[Inhabited]` + `Classical.epsilon`. SRM via empiricalRisk/penalty fields + epsilon. Layer status: CLOSED, 0 sorrys.
- **MetaKernel WorldModel layer is LIVE (3 new files, 0 sorrys):**
  - `WorldModel/PriorArt.lean`: PriorArtTheorem, LibraryTrace, ProofMethod, ProofStrategy types. Typed traces for Yuanhe Z (Lean4, concentration) and Google formal-ml (Lean3, PAC/VC). Queries: findRelevantTheorems, extractStrategyChain, minAdaptationCost.
  - `WorldModel/MeasuredTactic.lean`: Compulsory measurement tactic classes (`measured_proof`, `pl_check_goal`, `coh_check_state`, `hc_measure_state`). Gates: pl_gate, coh_gate, inv_gate, comp_gate. ProofMeasurementReport with classification.
  - `WorldModel/Feedback.lean`: TraceAnalysis, StrategyPatch, feedbackLoop, priorArtStrategy, `feedback_proof` tactic.
- **Prior-art cloned and integrated:**
  - `prior-art/lean-stat-learning-theory/` — Yuanhe Z, Lean4, 34,892 lines, 0 sorry: Efron-Stein, sub-Gaussian, Dudley, covering numbers
  - `prior-art/formal-ml/` — Google, Lean3, 36,221 lines, 0 sorry: PAC bounds, VC dimension, Sauer-Shelah, Hoeffding exponential bound, ERM generalization
- **Layer status:** Computation/ CLOSED (0), Complexity/ EFFECTIVELY CLOSED (4, all K₄-blocked), Criterion/ CLOSED (0), Learner/ CLOSED (0), MetaKernel/ LIVE (0), Theorem/ Open (~25)

### KU (Claude knows what it doesn't know)

- KU₁: Exact Mathlib APIs for Hoeffding/concentration inequalities — searched, not found (K₄ obstruction)
- ~~KU₂~~: RESOLVED — `ENat.exists_eq_iSup_of_lt_top` + `iSup_eq_top`
- KU₃: How to formalize the probabilistic argument in `vcdim_finite_imp_pac` in Lean4 measure theory
- KU₄: Whether Lean4's `MeasureTheory.Measure.pi` composes correctly with `PACLearnable`'s iid fix
- KU₅: How many of the 24 def-body sorrys have standard mathematical definitions Claude can look up
- ~~KU₆~~: RESOLVED — Mathlib bounds shatterer cardinality not growth function. Different formulations.
- KU₇: The right proof architecture for separation theorems (M₁ diagonalization in Lean4)
- KU₈: ConditionallyCompleteLinearOrderBot API for Ordinal — `le_ciSup_of_le` requires explicit BddAbove and function annotation for nested iSup₂. Blocks VCDim_embed_ordinal lower bound (Γ₂₇).
- KU₉: Can Yuanhe Z's `subGaussian_finite_max_bound` be adapted to provide finite-hypothesis uniform convergence bound? Would bridge K₄ for vcdim_finite_imp_pac.
- KU₁₀: Can Google formal-ml's pac_bound proof strategy (iidProduct → exponentialBound → unionBound) be translated to our type system via PriorArtTheorem traces?
- KU₁₁: Does the `feedback_proof` tactic converge for realistic sorry targets? Need empirical testing on K₄-blocked sorrys.

**KU cluster: MindChangeOrdinal Redesign (2026-03-17)**
- KU_MCO1: **RESOLVED → Design chosen.** Encode correctness via nested `if` in MindChangeOrdinal: `changes.Finite ∧ correct_convergence → (card : Ordinal)`, else → `ω`. The `_c` parameter becomes load-bearing (correctness check uses `c`).
- KU_MCO2: **KILLED.** Freivalds-Smith ordinal assignment approach is overkill for single-learner case. Simple counting + correctness suffices for the characterization.
- KU_MCO3: **RESOLVED.** `_c` → `c` (no longer unused). Correctness check: `∃ t₀, ∀ t ≥ t₀, L.conjecture (T.prefix t) = c`.
- KU_MCO4: **RESOLVED → bridge.** `dataUpTo T t = DataStream.prefix T (t + 1)` (off-by-one). EXLearnable convergence at t uses t+1 examples. MindChangeOrdinal correctness at t uses t examples. Bridge: ∀ t ≥ t₀, L.conjecture (prefix t) = c ↔ ∀ t ≥ t₀+1, L.conjecture (dataUpTo T (t-1)) = c. Equivalent after shift.
- KU_MCO5: `h.toFinset.card` in nested if — `h : changes.Finite` from outer `dite`, accessible in inner `if` branch. Standard Lean4 pattern, should work.
- KU_MCO6: For characterization theorem format — use `< Ordinal.omega0` (cleaner than `∃ α`). The `∃ α` version with `α < ω` is equivalent but less direct. Use `< omega0` as primary statement, derive `∃ α` variant as corollary if needed.
- KU_MCO7: **HYPOTHESIS.** After redesign, `MindChangeOrdinal < omega0 ↔ (changes.Finite ∧ correct convergence)`. This is the KEY property. Needs Lean4 proof: forward via definition unfolding + `Nat.cast_lt_omega0`; backward via contrapositive (¬Finite ∨ ¬correct → MindChangeOrdinal = omega0 ≥ omega0).

**Resolved KUs from lattice type expansion and UK searches (2026-03-17):**
- ~~KU₈~~: RESOLVED → KK. `norm_cast` does NOT handle double coercion in one step. Use `WithBot.coe_le_coe.mpr (WithTop.coe_le_coe.mpr ...)` or `WithBotTop.coe_le_coe` from `Mathlib/Order/WithBotTop.lean`.
- ~~KU₉~~: RESOLVED → KK. Already formalized as `ldim_zero_all_agree` in Online.lean. By contradiction: if c₁ x ≠ c₂ x, build depth-1 shattered tree → Ldim ≥ 1 > 0, contradiction.
- ~~KU₁₀~~: RESOLVED → KK. Induction on d (natural number from Ldim = ↑↑d) is correct. Already implemented in `soa_mistakes_bounded`. `Nat.strongRecOn'` available but standard induction suffices.
- ~~KU₁₁~~: RESOLVED → KK. Need C.Nonempty. Already implemented with `hne : C.Nonempty`. Statement: `↑(OptimalMistakeBound X C) = LittlestoneDim X C`.
- ~~KU₁₂~~: RESOLVED → A₄. mind_change_characterization forward/backward both A₄-blocked (statement uses DataStream not TextPresentation). `Ordinal.limitRecOn` exists for ordinal recursion but the statement itself is wrong.
- ~~KU₁₃~~: RESOLVED → A₄. Same as KU₁₂. Backward direction would need `Ordinal.limitRecOn` but is blocked by wrong statement.

### UK (Claude doesn't know what it knows)

- UK₁: Claude may have seen similar Lean4 proof patterns in training data that would apply here but hasn't been prompted to surface them
- UK₂: Claude may know the mathematical proofs of remaining theorems from training but hasn't mapped them to Lean4 tactic scripts
- UK₃: There may be Mathlib4 API changes in recent versions that Claude's training cutoff missed
- UK₄: ~~Whether Yuanhe Z's library could bridge our K₄ obstruction~~ → **RESOLVED to KU₉**: Yuanhe Z has Efron-Stein + sub-Gaussian + Dudley but NOT Hoeffding directly. `subGaussian_finite_max_bound` is the closest candidate for adaptation. Lean3→Lean4 translation needed for Google formal-ml's Hoeffding exponential bound.
- UK₅: Google formal-ml's PAC proof strategy may be directly translatable via PriorArtTheorem traces → **now KU₁₀**
- UK₆: `measured_proof` / `feedback_proof` tactic infrastructure is LIVE but untested on real sorry targets → interaction effects with existing CompoundMechanism pipeline unknown

**Resolved UKs from lattice type expansion (2026-03-17):**
- ~~UK₄~~: RESOLVED → KK. `WithBot.recBotCoe` (2-way, `cases_eliminator` attr) in `Mathlib/Order/TypeTags.lean`. `WithBotTop.rec` (3-way: ⊥/↑a/⊤) in `Mathlib/Order/WithBotTop.lean` with `rec_bot`/`rec_coe`/`rec_top` simp lemmas.
- ~~UK₅~~: RESOLVED → KK. Found: `iSup₂_eq_bot`, `iSup_eq_bot`, `iSup_of_empty`, `iSup_bot` in `CompleteLattice/Basic.lean`. `WithBot.coe_iSup` (needs Nonempty+BddAbove), `WithBot.ciSup_empty` in `ConditionallyCompleteLattice/Indexed.lean`.
- ~~UK₆~~: RESOLVED → KK. `Nat.strongRecOn'` in `Data/Nat/Init.lean`. Our backward_direction uses standard induction on d (correct). Also: `Ordinal.limitRecOn` (3-case: zero/succ/limit) for ordinal recursion if needed.
- ~~UK₇~~: RESOLVED → KK. mind_change forward IS over-complicated by the wrong statement (A₄). The statement uses DataStream (arbitrary), not TextPresentation (convergence guaranteed). For TextPresentation only, it's trivial: convergence → finite changes → MindChangeOrdinal ≤ ↑t₀. But the statement as written is FALSE for non-convergent streams.

### UU (Claude can't even formulate the question)

- UU₁: What proof architectures exist that Claude hasn't been exposed to in training?
- UU₂: What Lean4 metaprogramming capabilities could automate parts of metaprogram synthesis that Claude currently does manually?
- UU₃: What interactions between universe polymorphism and the MetaKernel's type architecture create proofs that are impossible for Claude to write but possible in principle?

**UU → UK/KU transitions from the lattice expansion:**
- ~~UU₄ (previous: "missing types?")~~ → **now UK₉ in Repo**: VCDim may need identical WithBot treatment. Partially resolved.
- New UU₄: Does the choice of `WithBot (WithTop ℕ)` over `ℤ ∪ {∞}` have consequences for the CONSTRUCTIVE content of proofs? WithBot-based proofs case-split on ⊥/↑↑n/↑⊤; ℤ-based proofs would use subtraction. Are these computationally equivalent? This matters if someone wants to EXTRACT a certified algorithm from the proof.
- New UU₅: The `CompleteLattice` structure enables lattice-theoretic proof strategies that weren't available before. What fraction of learning theory theorems can be restated as lattice identities? If high, there may be an automated tactic (`lattice_decide` or similar) that could discharge multiple sorrys simultaneously.

**UU → UK/KU transitions from prior-art integration + WorldModel (2026-03-17):**
- UU→UK: Yuanhe Z's library has Dudley chaining + sub-Gaussian tail bounds but NO PAC/VC → concentration path to uniform convergence EXISTS in Lean4 but needs adaptation (now KU₉)
- UU→UK: Google formal-ml has full PAC + VC + Sauer-Shelah in Lean3 → proof blueprints available for K₄-blocked sorrys, but Lean3→Lean4 translation needed (now KU₁₀)
- UU→UK: MetaKernel can consume external library traces as typed world models → PriorArtTheorem / ProofStrategy types make prior-art queryable (now γ₃₂)
- UU→KU: Measurement tactic classes can be COMPULSORY (not advisory) → `measured_proof` wrapper enforces Pl/Coh/Inv/Comp at proof time (now γ₃₃)
- UU→KU: Feedback loops (trace→analysis→patch→strategy) are typeable in Lean4 → self-improving proof search is real infrastructure (now γ₃₄/KU₁₁)

## Measurement Initializations

### Pl (Plausibility) — Claude-level
- A metaprogram synthesis is Pl-admissible if: (a) the sorry target is well-typed (NA₄), (b) Claude has at least one CM₁-CM₆ mechanism to attempt, (c) no known CA₁-CA₆ constraint makes the synthesis impossible
- Pl-kill: Claude declares a synthesis impossible for CLAUDE (not impossible in principle) when a SubstrateLimit obstruction is confirmed

### Coh (Coherence) — Claude-level
- A metaprogram is Coh-valid if: (a) all API references are Verified (not PatternMatched), (b) the CompoundMechanism steps compose (each output type matches next input type), (c) the proof compiles (`lake build` returns 0 errors)
- Coh-check requires compilation. Claude CANNOT assess Coh internally (CA₄).

### Inv (Invariance) — Claude-level
- A metaprogram is Inv-stable if: (a) it doesn't depend on specific sorry ordering (reorderable), (b) it survives KernelSnapshot re-sync (proof still valid after LimitsOfLearning changes), (c) it doesn't depend on Claude-specific knowledge (another agent could reproduce it from the metaprogram description)

### Comp (Completeness) — Claude-level
- Claude's Comp = (metaprograms successfully synthesized) / (total sorrys)
- Current: ~27/~41 (all previous + mind_change_characterization + 5 Computation.lean closures)
- Pl-killed: 5 (DSDim_ge_NatarajanDim, unlabeled_not_implies_labeled, pac_not_implies_online, natarajan_not_characterizes_pac, online_pac_gold_separation)
- Target: all non-Pl-killed sorrys resolved
- **Online.lean: COMPLETE (0 sorrys, fully compiled)**
- **Gold.lean: COMPLETE (0 sorrys in KernelSnapshot, mind_change_characterization compiled in LimitsOfLearning/)**
- **Computation.lean: COMPLETE (0 sorrys, all 5 closed)**
- **MetaKernel WorldModel: LIVE (3 new files, 0 sorrys, new tactic classes: `measured_proof`, `feedback_proof`)**
- Next immediate targets: PAC theorems (K₄-blocked, now with prior-art strategies KU₉/KU₁₀), separation theorems, Extended.lean
