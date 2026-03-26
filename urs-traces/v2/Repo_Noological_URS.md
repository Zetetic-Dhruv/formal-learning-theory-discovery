# Repo Noological URS — FLT_Proofs Agent Ontology (v2, 2026-03-18)

## Identity

The FLT_Proofs repository is a formal learning theory codebase in Lean4. This URS
describes its noological structure: what it knows, what mechanisms it supports,
how its representations are organized, and what traces it has accumulated.

**State:** 0 errors, 31 sorrys. Library: `FLT_Proofs`.

---

## A — Axiom Set (Identity + Scoping)

### Domain Constraints (A₁-A₆)
- **A₁:** Formal learning theory in Lean4 v4.29.0-rc6
- **A₂:** All Mathlib types are treated as ground truth
- **A₃:** Compilation monotonicity (lake build must succeed after every edit)
- **A₄:** No sorry may prove a trivially true or vacuously satisfiable statement
- **A₅:** No edit may simplify a statement to make it provable
- **A₆:** Break points are documented, not hidden

### Noological Axiom Commitments (NA₁-NA₁₃ + NA₁₄)

- **NA₁:** PAC, Online, Gold learners have incompatible type signatures (BP₁)
- **NA₂:** WithTop ℕ ↪ Ordinal is injective but not surjective (BP₂)
- **NA₃:** PAC (distribution), Online (adversary), Gold (stream) data are incompatible (BP₃)
- **NA₄:** Function-class ↔ set-family bridge is classically lossless for Bool, type-theoretically requires proof (BP₄)
- **NA₅:** Five generalization bounds have genuinely different type signatures (BP₅)
- **NA₆:** ConceptClass is over-connected (22 edges) with 4 alternative definitions (BP₆)
- **NA₇:** Bayesian prior has no canonical type (BP₇)
- **NA₈:** Ordinal lacks CompleteLattice; BddAbove must be proved explicitly
- **NA₉:** CompleteLattice for LittlestoneDim via WithBot(WithTop ℕ)
- **NA₁₀:** Ldim(∅) = ⊥ ≠ Ldim({c}) = 0 (the distinction is non-trivial)
- **NA₁₁:** M-DefinitionRepair pattern: typing issues → type expansion (not proof tricks)
- **NA₁₂:** Correctness-at-definition-level: MindChangeOrdinal and WithBot both encode invariants at type level
- **NA₁₃:** SOA (Standard of Accuracy) interface lemmas: explicit opt-in, not @[simp]
- **NA₁₄ (NEW):** ENNReal/ℝ error joint is a genuine break point (BP₈). The coercion ENNReal.toReal loses ⊤ → 0.

---

## M — Mechanism Space (Proof Methods)

### Primary Methods (M₁-M₈)
- **M₁:** Diagonalization (Gold's theorem, separation theorems)
- **M₂:** Probabilistic (PAC bounds, concentration inequalities)
- **M₃:** Combinatorial (Sauer-Shelah, growth function bounds)
- **M₄:** Game-Theoretic (online learning, mistake bounds)
- **M₅:** Convergence (identification in the limit, Bayesian consistency)
- **M₆:** Construction (witness building for existentials)
- **M₇:** Reduction (reducing one learning problem to another)
- **M₈:** Category-Theoretic (structure-preserving maps between paradigms)

### Metaprogram Types (11 + 1 new)
- **M-Bridge:** Connecting two type regimes (e.g., ENNReal ↔ ℝ)
- **M-BridgeLift:** Lifting a theorem across a bridge
- **M-Contrapositive:** Proving P → Q via ¬Q → ¬P
- **M-Pipeline:** Chaining through infrastructure (VCDim → UC → PAC)
- **M-Conjunction:** Proving P₁ ∧ ... ∧ Pₙ by factoring
- **M-Construction:** Building a witness for ∃
- **M-DefinitionRepair:** Fixing a definition to dissolve a proof obstruction
- **M-CaseElimination:** Exhaustive case analysis
- **M-Potential:** Potential function argument (online learning)
- **M-InfSup:** Infimum/supremum argument
- **M-VersionSpaceCollapse:** Version space shrinking argument
- **M-InfrastructureGap (NEW):** Identifying and building missing definitional infrastructure between type layers (discovered via K4 dissolution — the obstruction was not a missing lemma but a missing definition layer)

### Mechanism Incompatibilities (V₁-V₄)
- **V₁:** M₂ (probabilistic) requires measure theory; M₃ (combinatorial) avoids it
- **V₂:** M₁ (diagonalization) is non-constructive; M₆ (construction) is constructive
- **V₃:** M₄ (game-theoretic) uses adversarial quantifiers; M₂ uses distributional
- **V₄:** M-Pipeline requires intermediate types to exist; M-InfrastructureGap creates them

---

## R — Representation Grammar

### Core Types
```
SorryProfile := {
  id : String,
  file : FilePath,
  line : ℕ,
  paradigm : PAC | Online | Gold | Universal | Cross,
  method_candidates : List Method,
  metaprogram_type : MetaprogramType,
  dependencies : List SorryId,
  tractability : Immediate | Conditional | Blocked | Deep,
  ignorance_class : IgnoranceClass
}

IgnoranceClass :=
  | KU_standard    -- known unknown, articulable
  | KU_mathlib     -- blocked on Mathlib API
  | UK_pattern     -- suspected regularity, not verified
  | UK_construction -- know-how gap (can't build the witness)
  | UU_open        -- genuinely open mathematical problem
  | UU_undecidable -- may be undecidable from current axioms
```

### R-Expansion Protocol
When a proof attempt reveals missing infrastructure:
1. Diagnose: is the gap a LEMMA (provable from existing defs) or a DEFINITION (new concept needed)?
2. If DEFINITION → use M-InfrastructureGap: design, type-check, add to Generalization.lean
3. If LEMMA → use appropriate M-* template
4. Record the R-expansion in the Γ-ledger

---

## T — Traces

### γ-ledger (Discovery — 39+ entries)

**Completed layers:**
| Layer | File | Sorrys Closed | Session |
|-------|------|--------------|---------|
| L0 | Computation.lean | 5 (γ₂₇-γ₃₁) | 2026-03-17 |
| L4 | Theorem/Online.lean | 10 (γ₁₂-γ₂₀) | 2026-03-17 |
| L4 | Theorem/Gold.lean | 1 (γ₁₁) + mind_change (γ₂₁) | 2026-03-17 |
| L5 | Bridge.lean (ordinal) | 2 (γ₃₅: Γ₂₇ resolution) | 2026-03-18 |
| L5 | Generalization.lean | Infrastructure layer (γ₃₆) | 2026-03-18 |
| L6 | Theorem/PAC.lean | A4 repairs (γ₃₇-γ₃₈), factoring (γ₃₉) | 2026-03-18 |

**Open layers:**
| Layer | File | Remaining Sorrys | Primary Method |
|-------|------|-----------------|----------------|
| L5 | Generalization.lean | 10 | M-Bridge, M-Pipeline |
| L5 | Rademacher.lean | 1 | M-InfrastructureGap |
| L6 | Theorem/PAC.lean | 9 | M-Pipeline, M-Contrapositive |
| L6 | Theorem/Separation.lean | 5 | M-Construction, M-Diagonalization |
| L6 | Theorem/Extended.lean | 5 | Mixed |
| L5→L6 | Bridge.lean | 1 | M-Bridge |

### Γ-ledger (Inquiry — 34+ entries)

**Key resolved entries:**
| ID | Entry | Resolution |
|----|-------|-----------|
| Γ₂₇ | VCDim_embed_ordinal blocked (BddAbove) | RESOLVED via uniform ω-bound (γ₃₅) |
| Γ₃₁ | K4 obstruction (Hoeffding) | DISSOLVED — Mathlib has APIs; obstruction was infrastructure |
| Γ₃₃ | A4 violations (pac_lower_bound, nfl) | RESOLVED (γ₃₇-γ₃₈) |

**Key open entries:**
| ID | Entry | Status |
|----|-------|--------|
| Γ₃₂ | BP₈ discovery (ENNReal/ℝ joint) | OPEN — bridge theorems are sorry |
| Γ₃₄ | Sorry DAG dependency structure | OPEN — documented but not verified |

---

## K/U Universes — Ignorance Partition (v2)

### KK (Established — 175+ entries)

**Infrastructure (NEW):**
- TrueError, TrueErrorReal, EmpiricalMeasure, EmpiricalMeasureError defined
- HasUniformConvergence defined with correct Measure.pi quantification
- GhostSample, DoubleSampleMeasure defined
- PACsampleComplexity defined
- vc_characterization = ⟨pac_imp_vcdim_finite, vcdim_finite_imp_pac⟩
- K4 dissolved: `Real.one_sub_le_exp_neg`, `one_sub_div_pow_le_exp_neg` in Mathlib
- Γ₂₇ resolved: BddAbove via uniform ω-bound
- 2 A4 violations repaired

**Architecture:**
- All v1 KK entries preserved (CompleteLattice, dataUpTo bridge, SOA pattern, etc.)
- FLT_Proofs is sole build target
- 0 errors, 31 sorrys

### KU (Active — 15 entries)

| ID | Question | Scope |
|----|----------|-------|
| KU₁ | Measurability hypotheses for trueError_eq_genError | Generalization.lean |
| KU₆ | ERM minimizer existence for infinite H | Generalization.lean |
| KU₈ | Pure-ENNReal formulation of UC | Generalization.lean |
| KU₁₁ | Measure.prod vs Measure.pi for DoubleSampleMeasure | Generalization.lean |
| KU₁₅ | Simplest VCDim < ∞, Ldim = ∞ separation example | Separation.lean |
| KU₁₈ | C.Nonempty gap in vcdim_finite_imp_pac | PAC.lean |
| KU₁₉ | Mathlib uniform probability on finite set | PAC.lean |
| KU₂₀ | Exact constant in PAC lower bound | PAC.lean |
| KU₂₁ | Constructing uniform measure on T for NFL | PAC.lean |

**Resolved KUs (since v1):**
- ~~K₄ (Hoeffding)~~ → DISSOLVED
- ~~KU₂ (vcdim_to_ordinal_vcdim BddAbove)~~ → RESOLVED (Γ₂₇)

### UK (Active — 6 entries)

| ID | Pressure | Scope |
|----|----------|-------|
| UK₃ | Measurability of sup_{h∈H} over uncountable H | symmetrization_lemma |
| UK₈ | Constructive ← vs non-constructive → in vc_characterization | PAC.lean |
| UK_P1 | Sorry-dependency DAG cascading structure | Cross-file |
| UK_P2 | Shatters → Finset.Shatters bridge | Bridge.lean |

### UU (Boundary — 6 regions)

- UU₁: Whether BP₁-BP₈ are genuine or artifacts
- UU₂: Proof methods beyond M₁-M₈
- UU₃: Whether sorry DAG structure is an invariant of the math
- UU₄: Constructive content of WithBot vs ℤ proofs
- UU₅: Lattice-theoretic automation potential
- UU₆: Whether 31 sorrys is a natural stopping point or arbitrary

---

## Measurement Initializations

### HC at Paradigm Joints (v2)

| Joint | HC (v1) | HC (v2) | Change |
|-------|---------|---------|--------|
| Finite/Ordinal | 0.7 | 0.2 | Γ₂₇ resolution |
| ENNReal/ℝ error | — | 0.5 | NEW (BP₈) |
| Combinatorial/Measure | 1.0 | 0.7 | Infrastructure layer |
| PAC/Online | 1.0 | 1.0 | Unchanged |
| PAC/Gold | 0.8 | 0.8 | Unchanged |

### Sorry Tractability Distribution (v2)

| Tractability | Count | Percentage |
|-------------|-------|------------|
| Immediately Provable | 5 | 16% |
| Conditionally Provable | 14 | 45% |
| Blocked | 4 | 13% |
| Deep Structure | 2 | 6% |
| Keystone (critical path) | 3 | 10% |
| Assembly (depends on others) | 3 | 10% |
