---
session: 10
date: 2026-04-02
title: "Proof Operad Phase 1: Core Structures for TPG_FLT"
type: formalization-urs
status: awaiting-verification
target_file: FLT_Proofs/Meta/ProofOperad.lean (NEW)
theorem_count: 3 core judgments + 2 soundness theorems
sorry_budget: 2 (generator_sound, plan_sound — these require MetaM execution)
M-type: M-Construction (new mathematical structure)
HC: 0.40
---

# Proof Operad Phase 1: Core Structures

## What This File Is

A Lean4 formalization of the THEORY of proof generation for formal learning theory.
Not a tactic automation tool. A typed calculus whose terms are proof plans, whose
types are proof interfaces, and whose typing rules enforce admissibility.

The calculus is:

    TPG_FLT = (Interfaces, Generators, Plans, FailureRules, Extensions)

with a typing judgment `Σ ⊢ p : I ⇒ O⃗` meaning: under theory Σ, plan p transforms
an obligation of interface I into sub-obligations O⃗.

## Lean4 Metaprogramming Substrate

From the Lean4 Metaprogramming Book (Chapters 4-8):

### The monad stack
```
CoreM → MetaM → TermElabM → TacticM
```
Each adds capabilities: environment → metavar context → elaboration → goal list.

### Proof state = metavariable
A goal is an `MVarId` carrying:
- `target : Expr` (the proposition to prove)
- `lctx : LocalContext` (available hypotheses)

Key operations:
- `mkFreshExprMVar` : create new goal (subobligation)
- `MVarId.assign` : close goal with proof term
- `isDefEq` : unification (may assign mvars as side effect)
- `forallMetaTelescopeReducing` : open binders as new goals

### Composition in the substrate
- **Sequential**: monadic `do`-bind in `TacticM`
- **Parallel**: `Array.mapM` over independent goals
- **Backtracking**: `saveState`/`restoreState`, `observing?`
- **Macro chaining**: `macro_rules` tries handlers in sequence, `throwUnsupported` passes to next

### Why operad, not category
A tactic sends one `MVarId` to `List MVarId` — one obligation to MANY sub-obligations.
This is operadic (multi-output) data, not categorical (unary morphism) data.

## File: `FLT_Proofs/Meta/ProofOperad.lean` (NEW)

### Imports

```lean
import Lean.Meta.Basic
import Lean.Elab.Tactic.Basic
```

Minimal: only the Lean4 metaprogramming substrate. Zero Mathlib, zero FLT_Proofs.
This file is PURE proof theory — it describes proof methods, not learning theory.

---

## Core Structures

### 1. Paradigm (the coarse lock)

```lean
/-- Mathematical universes that lock proof methods to type families.
    A generator carrying paradigm lock `pac` can only apply when the goal
    mentions measure-theoretic types. -/
inductive Paradigm where
  | structural   -- paradigm-agnostic (intro, cases, calc)
  | pac          -- MeasureTheory.Measure, ENNReal, Measure.pi
  | online       -- OnlineLearner.State, versionSpace, LTree
  | gold         -- DataStream, TextPresentation, MindChangeOrdinal
  | dst          -- AnalyticSet, NullMeasurableSet, PolishSpace
  | bayes        -- FinitePMF, klDiv
  | separation   -- WellBehavedVCMeasTarget, KrappWirthWellBehaved
  deriving DecidableEq, Repr, BEq, Hashable
```

### 2. Interface (the typed obligation)

```lean
/-- An abstract proof interface: the type of obligation flowing between generators.
    This is NOT a raw Lean Expr — it is a proof-theoretic abstraction over goal shapes.

    An interface captures: what paradigm the goal lives in, what hypotheses are
    required, what the target obligation is named, and how many sub-obligations
    the generator produces. -/
structure Interface where
  /-- Human-readable name (e.g., `GrowthBound`, `HasUC`, `PACLearnable`) -/
  name : String
  /-- Which paradigm(s) this interface belongs to -/
  locks : List Paradigm
  /-- Required hypothesis names in the local context -/
  premises : List String
  /-- Tag identifying the target type family -/
  targetTag : String
  deriving DecidableEq, Repr, BEq
```

### 3. GenLevel (the stratification)

```lean
/-- The three levels of the stratified operad.
    Structural combinators operate on proof-state form.
    Domain generators are the mathematically meaningful kernels.
    Strategic policies choose plans from goal profiles. -/
inductive GenLevel where
  | structural  -- operates on proof-state form, independent of math content
  | domain      -- mathematically meaningful proof kernel
  | strategic   -- high-level approach selection
  deriving DecidableEq, Repr
```

### 4. Generator (the primitive operation)

```lean
/-- A primitive proof generator in the operad.
    One input interface, finitely many output interfaces.
    This is the operadic arity: `input ⇒ [output₁, output₂, ...]`.

    The `tacticPattern` field records the TacticM skeleton from the
    empirical extraction (tactic_pattern in proof_world_model.json).
    The `guard` field is a decidable predicate on goal profiles that
    determines applicability. -/
structure Generator where
  /-- Unique identifier (e.g., `MeasureBridge`, `TreePotential`) -/
  name : String
  /-- Stratification level -/
  level : GenLevel
  /-- Input interface (the obligation this generator consumes) -/
  input : Interface
  /-- Output interfaces (the sub-obligations this generator produces) -/
  outputs : List Interface
  /-- The tactic skeleton, as a string (for display/matching) -/
  tacticPattern : String
  /-- Paradigm locks inherited from input -/
  paradigm : List Paradigm
  deriving Repr
```

**Design note**: The `guard` and `realize` fields from the guidance are omitted in
Phase 1. They require `MetaM` execution, which is Phase 3. Phase 1 is the pure
typed calculus — no monadic effects, no goal inspection.

### 5. Plan (the composition syntax)

```lean
/-- A proof plan: the syntax of proof generation.
    Plans compose generators via sequential, parallel, guarded,
    nondeterministic, and extension operators.

    This is the FREE operad generated by the primitive generators,
    before quotienting by failure rules. -/
inductive Plan where
  /-- Apply a primitive generator by name -/
  | atom (g : String)
  /-- Sequential composition: apply p, then q to ALL resulting subgoals -/
  | seq (p q : Plan)
  /-- Parallel composition: apply plans to independent subgoals -/
  | par (ps : List Plan)
  /-- Guarded plan: only attempt if paradigm lock matches -/
  | guard (lock : Paradigm) (p : Plan)
  /-- Nondeterministic choice: try alternatives until one succeeds -/
  | choose (alts : List Plan)
  /-- Extension placeholder: marks a typed gap where the theory needs growth -/
  | extend (gapName : String)
  deriving Repr
```

**Lean4 substrate connection**: `Plan.seq` corresponds to monadic `do`-bind in
`TacticM`. `Plan.par` corresponds to `Array.mapM` over independent goals.
`Plan.choose` corresponds to `observing?` + backtracking via `saveState`/`restoreState`.
`Plan.guard` corresponds to pattern-matching on `Expr` in the goal's target type.
`Plan.extend` has NO substrate analogue — it is the theory's prediction mechanism.

### 6. RejectReason (negative typing)

```lean
/-- Reasons a generator application is rejected.
    These are the NEGATIVE typing rules of the calculus.
    Each corresponds to an empirically observed failure diagnostic. -/
inductive RejectReason where
  /-- Goal's paradigm types don't match generator's lock -/
  | paradigmMismatch (needed : List Paradigm) (found : List Paradigm)
  /-- A required hypothesis is missing from the local context -/
  | missingPremise (name : String)
  /-- A type in context makes this generator inadmissible
      (e.g., [Fintype X] blocks symmetrization) -/
  | forbiddenInstance (tag : String)
  /-- Classical.choose over uncountable set loses measurability -/
  | nonconstructiveSelection
  /-- No bridge exists between source and target interfaces -/
  | missingBridge (source target : String)
  /-- Lean4 elaboration fails (unification, instance synthesis) -/
  | elaborationDeadEnd (msg : String)
  deriving Repr
```

### 7. FailureRule (the admissibility constraint)

```lean
/-- A failure rule: a negative typing judgment.
    If `onInput` matches the current interface and `blocks` matches the
    generator name, the application is rejected with `reason`.

    The 7 empirical failure diagnostics (FD1-FD7) become instances of this. -/
structure FailureRule where
  /-- Unique identifier (e.g., `FD1_fintype_blocks_symmetrization`) -/
  name : String
  /-- Predicate on the input interface -/
  onInput : Interface → Bool
  /-- Predicate on the generator name -/
  blocks : String → Bool
  /-- The rejection reason -/
  reason : RejectReason
  deriving Repr
```

### 8. GapSpec (the extension object)

```lean
/-- A typed gap: what the theory needs but doesn't have.
    When a goal cannot be decomposed by any existing generator,
    the system produces a GapSpec describing the missing generator. -/
structure GapSpec where
  /-- What interface the gap starts from -/
  source : Interface
  /-- What interface is needed -/
  needed : Interface
  /-- Why it's missing -/
  because : RejectReason
  deriving Repr
```

### 9. Theory (the full operad)

```lean
/-- The proof operad: a collection of generators, failure rules,
    and known gaps. This is the complete theory state. -/
structure Theory where
  /-- The primitive generators -/
  generators : List Generator
  /-- The failure rules (negative typing) -/
  failures : List FailureRule
  /-- Known gaps (extension objects) -/
  gaps : List GapSpec
  deriving Repr
```

---

## Core Judgments

### 10. Admissibility

```lean
/-- Check that a generator is admissible for an interface under a theory.
    Returns `Except RejectReason Unit`. -/
def Theory.admissible (Σ : Theory) (I : Interface) (g : Generator) :
    Except RejectReason Unit :=
  -- Check paradigm lock
  if g.paradigm.any (fun p => !I.locks.contains p) && !g.paradigm.isEmpty then
    .error (.paradigmMismatch g.paradigm I.locks)
  -- Check premises
  else if g.input.premises.any (fun p => !I.premises.contains p) then
    .error (.missingPremise (g.input.premises.filter (fun p => !I.premises.contains p)).head!)
  -- Check failure rules
  else match Σ.failures.find? (fun fd => fd.onInput I && fd.blocks g.name) with
    | some fd => .error fd.reason
    | none => .ok ()
```

### 11. HasType (the typing judgment)

```lean
/-- The typing judgment: `Σ ⊢ p : I ⇒ Os`.
    Under theory Σ, plan p transforms obligation I into sub-obligations Os. -/
inductive HasType (Σ : Theory) : Plan → Interface → List Interface → Prop where
  /-- Atom: apply a generator -/
  | atom (g : Generator)
      (hg : g ∈ Σ.generators)
      (hadm : Σ.admissible I g = .ok ()) :
      HasType Σ (.atom g.name) g.input g.outputs

  /-- Sequential composition: p produces Js, q consumes each J and produces Ks -/
  | seq {p q : Plan} {I : Interface} {Js : List Interface}
      (hp : HasType Σ p I Js)
      (hq : ∀ J ∈ Js, ∃ Ks, HasType Σ q J Ks) :
      HasType Σ (.seq p q) I (Js.bind (fun J =>
        (hq J (by assumption)).choose))

  /-- Parallel: independent plans for independent subgoals -/
  | par {ps : List Plan} {Is Os : List (List Interface)}
      (hlen : ps.length = Is.length)
      (hpar : ∀ i (hi : i < ps.length),
        HasType Σ (ps.get ⟨i, hi⟩) (Is.get ⟨i, by omega⟩) (Os.get ⟨i, by omega⟩)) :
      HasType Σ (.par ps) ⟨"bundle", [], [], "bundle"⟩ Os.join

  /-- Guard: plan is well-typed if the paradigm matches -/
  | guard {lock : Paradigm} {p : Plan} {I : Interface} {Os : List Interface}
      (hmatch : lock ∈ I.locks)
      (hp : HasType Σ p I Os) :
      HasType Σ (.guard lock p) I Os

  /-- Choose: at least one alternative is well-typed -/
  | choose {alts : List Plan} {I : Interface} {Os : List Interface}
      (halt : ∃ p ∈ alts, HasType Σ p I Os) :
      HasType Σ (.choose alts) I Os

  /-- Extend: marks a gap — always well-typed but produces an unresolved gap -/
  | extend {gapName : String} {I : Interface} :
      HasType Σ (.extend gapName) I
        [⟨gapName, I.locks, I.premises, gapName⟩]
```

**Lean4 substrate connection**:
- `HasType.atom` corresponds to applying a single tactic (the generator's `realize`)
- `HasType.seq` corresponds to monadic bind: `p >>= fun goals => goals.mapM q`
- `HasType.par` corresponds to `goals.zip plans |>.mapM (fun (g, p) => p g)`
- `HasType.choose` corresponds to `observing?` with `saveState`/`restoreState` backtracking
- `HasType.extend` has no substrate analogue — it's the theory's growth mechanism

---

## Core Theorems

### 12. Failure as negative typing

```lean
/-- Every failure rule produces a rejection.
    This is the soundness of negative typing: if a failure rule applies,
    the generator is inadmissible. -/
theorem failure_as_negative_typing
    (Σ : Theory) (fd : FailureRule) (I : Interface) (g : Generator)
    (hfd : fd ∈ Σ.failures)
    (honInput : fd.onInput I = true)
    (hblocks : fd.blocks g.name = true) :
    ∃ r : RejectReason, Σ.admissible I g = .error r := by
  -- The failure check in admissible finds fd and returns .error fd.reason
  sorry -- Phase 1 target: close this
```

**Route**: Unfold `Theory.admissible`, case-split on the paradigm/premise checks.
The `List.find?` will find `fd` because `honInput` and `hblocks` hold. The key
lemma is `List.find?_some` with the witness `fd`.

### 13. Typed openness

```lean
/-- When no plan types, a gap exists.
    This is the PREDICTION mechanism: the theory produces structured ignorance. -/
theorem typed_openness
    (Σ : Theory) (I : Interface)
    (hno : ¬ ∃ p Os, HasType Σ p I Os) :
    ∃ gap : GapSpec, gap.source = I := by
  exact ⟨⟨I, ⟨"unknown", I.locks, I.premises, "unknown"⟩, .missingBridge I.name "unknown"⟩, rfl⟩
```

**Route**: Trivial — construct the gap from the input interface. The content is in
the SPECIFICATION of the gap (what interface is missing), not the proof.

### 14. Extension soundness

```lean
/-- Adding a generator that solves a gap extends the theory.
    If g.input = gap.source and g.outputs = [gap.needed],
    then inserting g into Σ makes the previously untypable plan typable. -/
theorem extension_sound
    (Σ : Theory) (gap : GapSpec)
    (g : Generator) (hsolve : g.input = gap.source ∧ g.outputs = [gap.needed])
    (hadm : Σ.admissible gap.source g = .ok ()) :
    HasType ⟨g :: Σ.generators, Σ.failures, Σ.gaps⟩
      (.atom g.name) gap.source [gap.needed] := by
  exact .atom g ⟨List.Mem.head _⟩ (by
    -- admissibility in extended theory: same failures, g is now in generators
    sorry -- Phase 1 target: close this
  )
```

**Route**: The extended theory has `g` at the head of `generators`. Admissibility
needs to be shown for the extended theory's failure rules (same as Σ's). The
hypothesis `hadm` gives admissibility under Σ; since failures don't change,
admissibility under the extended theory is the same.

---

## KK/KU/UK/UU Partition

| Quadrant | Content |
|----------|---------|
| **KK** | Lean4's `inductive`, `structure`, `Prop` are the right tools. `deriving Repr` gives display. `List` for finite collections. `Except` for error-or-success. The Plan inductive is well-founded (structural recursion). |
| **KU** | (1) Should `HasType` use `List Interface` or `Array Interface` for outputs? List is simpler for inductive proofs but Array is what Lean4 actually uses. Decision: List for Phase 1 (pure theory). (2) The `seq` case of `HasType` uses `List.bind` with `Exists.choose` — this is noncomputable. Is that acceptable for a Prop-valued judgment? Yes — `HasType` is a `Prop`, not data. (3) Does `Interface` need a `DecidableEq` instance? Yes, for `List.contains` in `admissible`. Added via `deriving`. |
| **UK** | The `HasType.par` case needs a "bundle" interface for grouping. This is ad hoc. A cleaner version would use a context/environment of interfaces rather than a single input. Phase 2 can refine this. |
| **UU** | Whether the typing judgment is DECIDABLE. Can we write `Decidable (HasType Σ p I Os)`? Probably not in general (the `seq` case quantifies over all J ∈ Js). But we can write a CHECKER for specific plans, which is the practical use case. |

---

## Execution Plan

### Phase 1a: Structure definitions (~80 LOC)

Write `Paradigm`, `Interface`, `GenLevel`, `Generator`, `Plan`, `RejectReason`,
`FailureRule`, `GapSpec`, `Theory`. Build after.

### Phase 1b: Admissibility function (~20 LOC)

Write `Theory.admissible`. Build after.

### Phase 1c: HasType inductive (~40 LOC)

Write the typing judgment. Build after.

### Phase 1d: Core theorems (~30 LOC)

Write `failure_as_negative_typing`, `typed_openness`, `extension_sound`.
`typed_openness` should be sorry-free (trivial construction).
`failure_as_negative_typing` target: sorry-free.
`extension_sound` target: sorry-free if admissibility under extended theory = same.

### Phase 1e: Verify

Build `lake build FLT_Proofs.Meta.ProofOperad`. Zero errors. Target: 0 sorrys.

---

## LOC Estimate: ~170

## Sorry Budget: 0 (all three theorems should close)

## Agent Guardrails

1. NEVER run `git checkout`, `git restore`, or any working-tree discard
2. Build after every phase (1a, 1b, 1c, 1d)
3. Zero sorrys target
4. The file imports ONLY from Lean core — no Mathlib, no FLT_Proofs
5. This is a THEORY file, not a tactic file — it defines structures and judgments,
   it does NOT execute MetaM or inspect actual proof states
6. `open Lean` at the top if needed for `Name`, but prefer `String` for simplicity
   in Phase 1 (avoid depending on Lean internals that may change)
7. All structures must `deriving Repr` for inspectability
8. The `HasType` inductive is in `Prop` — it is a typing judgment, not data
