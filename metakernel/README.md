# Axioms — Immutable Research Program Record

This folder contains the **axiomatic commitments** of the LimitsOfLearning formalization project: the type grammar decisions, break point documentation, paradigm joint analysis, and novelty assessment that define the project's identity.

## Why Isolated

These documents are separated from both the **Kernel** (the Lean4 proof files in `LimitsOfLearning/`) and the **MetaKernel** (the meta-programs in `MetaKernel/`) to prevent accidental overwrite during proof-filling or meta-program generation sweeps.

The Axioms folder is the `A` (identity/axiom set) of this project's URS. It changes only by deliberate noological commitment — discovering a new break point, closing a KU question, or revising a type decision — never as a side effect of proof work.

## Contents

| Document | Role | URS Position |
|----------|------|-------------|
| `BREAKS.md` | 7 break points (BP₁–BP₇) + 5 compilation constraints (C₁–C₅) | R (grammar obstructions) |
| `TASK_URS.md` | Full Task URS: KK/KU/UK/UU tracking for the type architecture | Full URS |
| `TYPE_DERIVATION_STATE.json` | Machine-readable concept graph: paradigm joints, break points, typing profiles, η checks | R + γ (structured state) |
| `DAG_ASSESSMENT.md` | Module/concept DAG, novelty assessment, completeness analysis, Mathlib coherence | γ (discovery record) |
| `novelty.md` | Prior art comparison, 4 novelty claims, usage guide | Γ (positioning) |
| `CHANGELOG.md` | Version history with semantic detail | T (trace record) |
| `VERSION` | Semantic version number | — |

## Editing Protocol

1. **Read before edit.** Always read the full document before modifying.
2. **Append, don't replace.** New discoveries go into new sections; old content is preserved as historical record.
3. **Date all changes.** Every modification includes a date stamp.
4. **Cross-reference.** If a change here affects Kernel or MetaKernel, note the dependency explicitly.

## Relationship to Kernel and MetaKernel

```
Axioms/  ─── defines the grammar (R), identity (A), and constraints ───┐
                                                                        │
Kernel/  ─── LimitsOfLearning/*.lean: the proof record (γ-ledger)      │
              69 sorry → proof transitions                              │
              Changes here are KU→KK transitions                       │
                                                                        │
MetaKernel/ ─ Meta-programs: the inquiry apparatus (Γ-ledger)          │
              World models over proof methods                           │
              Discovery tasks generating proofs                         │
              Validated AGAINST Axioms/ ◄──────────────────────────────┘
```

The MetaKernel's world model is initialized FROM Axioms/ (break points constrain which meta-programs are writable; paradigm joints constrain which methods compose). The Kernel's proofs are validated BY compilation against the type grammar recorded here.
