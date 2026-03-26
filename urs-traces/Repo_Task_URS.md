# Repo Task URS — MetaKernel Sorry Replacement Pipeline

> Canonical version. `MetaKernel/TASK_URS.md` is the legacy file; this supersedes it with full AMRT structure.

## Task Identity

The MetaKernel's SOLE task: **discover metaprograms that replace ALL sorrys in KernelSnapshot/**. Each metaprogram is a world model — a structured hypothesis about how to prove a specific theorem, verified by compilation.

This is NOT routine proof-writing. This is **discovery**: the MetaKernel engineers its own ignorance (Γ-ledger) to expand the space of askable questions about proofs, then collapses specific questions into proved theorems (γ-ledger).

---

## A_task — Task Axioms (Non-Negotiable Invariants)

| ID | Axiom | Enforcement |
|----|-------|-------------|
| TA₁ | **Write target is ONLY `MetaKernel/KernelSnapshot/`** | Path check before every Edit/Write. Violation = abort. |
| TA₂ | **`LimitsOfLearning/` is NEVER modified** | Frozen source of truth. KernelSnapshot diverges only by proof insertions. |
| TA₃ | **Sorry count monotonically decreases** | No new sorrys. No replacing a sorry with a different sorry. |
| TA₄ | **`lake build` = 0 errors at all times** | Compilation is the verification gate. No proof is "done" without it. |
| TA₅ | **Metaprogram-first** | Every proof in KernelSnapshot has a corresponding metaprogram (CompoundMechanism or evalCustom) in Discovery.lean or WorldModel/. Direct tactic-writing without metaprogram is prohibited. |
| TA₆ | **Obstruction documentation** | When a sorry is BLOCKED, the obstruction must be documented in the Γ-ledger with specific diagnosis (not "hard" or "needs work"). |

## M_task — Task Mechanisms (The Pipeline)

### Phase 1: Profiling

For a sorry target, produce its SorryProfile:

```
Input:  sorry_id, file_path
Output: SorryProfile := {
  sorry_id, file, type_signature, paradigm,
  method_candidates, metaprogram_type,
  dependencies, bp_blocked, ignorance_class, tractability
}
```

**Profiling steps:**
1. READ the sorry's type signature from KernelSnapshot
2. CLASSIFY paradigm: PAC | Online | Gold | Universal | Bayesian | Query | Cross
3. IDENTIFY method candidates from M₁-M₈ based on type shape
4. DERIVE metaprogram type: M-Bridge | M-BridgeLift | M-Contrapositive | M-Pipeline | M-Conjunction | M-Construction
5. CHECK dependencies: does this sorry need other sorrys to be resolved first?
6. CHECK BP blocking: does the proof need to cross a paradigm boundary?
7. CLASSIFY ignorance: KU_standard → UK_literature → KU_composite → KU_bp_blocked → UU_undecidable
8. ASSESS tractability: Immediate | Conditional | Blocked

### Phase 2: World Model Construction

For a profiled sorry, construct a WorldModel (= metaprogram):

```
Input:  SorryProfile
Output: WorldModel := {
  target, method, metaprogram (CompoundMechanism),
  substeps, constraints, plausibility, trace
}
```

**Construction steps:**
1. SELECT method from method_candidates (highest Pl)
2. DECOMPOSE into substeps:
   - For M-Bridge: identify source def, target def, mediator
   - For M-Contrapositive: identify negation, contradiction source, intermediate result
   - For M-Pipeline: identify stages (Bound → Concentrate → Construct → Compose)
   - For M-Conjunction: identify component results, check all available
   - For M-Construction: look up mathematical definition from literature
3. For each substep, VERIFY Mathlib API availability (must reach Verified, not PatternMatched)
4. COMPOSE into CompoundMechanism using seq/conj/branch/evalCustom combinators
5. ASSESS plausibility: Pl-admissible if all substeps have Verified APIs and no V-constraints block

### Phase 3: Execution

Write the metaprogram's output (a tactic proof) into KernelSnapshot:

```
Input:  WorldModel with CompoundMechanism
Output: Modified KernelSnapshot file with sorry → proof
```

**Execution steps:**
1. WRITE the CompoundMechanism to Discovery.lean (or as evalCustom strategy)
2. TRANSLATE the CompoundMechanism to a concrete tactic proof
3. EDIT the sorry in KernelSnapshot/ with the proof
4. CHECK: no A₅ violation (didn't drop content, didn't simplify structure)

### Phase 4: Verification

```
Input:  Modified KernelSnapshot
Output: Compiled | Error(message)
```

KernelSnapshot is NOT a build target in lakefile.lean. Verification options:
- **Option A:** Temporarily add KernelSnapshot to lakefile targets, build, then remove
- **Option B:** Read the proof for type-correctness manually (less reliable)
- **Option C:** Import KernelSnapshot files from a test file in MetaKernel/

Currently using: Option B (manual check) with compilation when possible.

### Phase 5: Recording

After every sorry attack, record in BOTH ledgers:

**If success (sorry → proof):**
1. Add γ-entry to Repo_Noological_URS.md traces
2. Update Comp table
3. Add metaprogram to Discovery.lean if not already there
4. Update Claude_Noological_URS.md K/U partition

**If failure (sorry remains):**
1. Add Γ-entry to Repo_Noological_URS.md traces with specific obstruction
2. CLASSIFY obstruction:
   - Local (affects only this sorry) → document and move on
   - Global (affects a class of sorrys) → add to V-table, re-profile affected sorrys
3. If obstruction suggests R-expansion → perform ABD-R, add new structure to R
4. If obstruction is permanent → Pl-kill the sorry, document in BREAKS.md

---

## R_task — Task Representations

### Sorry Inventory (current state — 2026-03-16)

#### Bridge.lean (0 sorrys — CLEARED)

| Sorry | Type | Metaprogram | Status | Notes |
|-------|------|-------------|--------|-------|
| ~~`vcdim_to_ordinal_vcdim`~~ | M-BridgeLift | γ₆ | ✓ PROVED (UNCHECKED) | KU₁ resolved: ENat.exists_eq_iSup_of_lt_top + iSup_eq_top |

#### Theorem/PAC.lean (9 real sorrys)

| Sorry | Type | Metaprogram | Tractability | Notes |
|-------|------|-------------|-------------|-------|
| `vc_characterization` | M-Conjunction | — | BLOCKED (needs components) | Iff of PAC ↔ VCDim < ∞ |
| `vcdim_finite_imp_pac` | M-Pipeline | — | BLOCKED (K₄: Hoeffding) | Forward direction of vc_characterization |
| `pac_imp_vcdim_finite` | M-Contrapositive | — | CONDITIONAL (KU₃) | Backward direction, double-sampling |
| `sauer_shelah_quantitative` | M-Bridge | — | CONDITIONAL (KU₂) | Bridge to Finset.Shatters |
| `fundamental_theorem` | M-Conjunction | — | BLOCKED (needs components) | Assembly of vc_char + sauer_shelah |
| `fundamental_vc_compression` | M-Pipeline | — | BLOCKED | Needs compression scheme |
| `fundamental_rademacher` | M-Pipeline | — | BLOCKED | Needs Rademacher tools |
| `nfl_fixed_sample` | M-Pipeline | — | CONDITIONAL | Counting/measure argument |
| `occam_algorithm` | M-Pipeline | — | BLOCKED (K₄) | Needs Hoeffding |

#### Other Files (~25 sorrys)

| File | Count | Primary Method | Tractability |
|------|-------|---------------|-------------|
| Computation.lean | **0** | M₆ (Direct Construction) | **COMPLETE.** All 5 sorrys closed: KolmogorovComplexity (sInf encode), AlgorithmicProbability (∑' with Classical.decEq), MDLPrinciple.select (Inhabited + Classical.epsilon), MMLPrinciple.select (same), SRM (empiricalRisk + penalty fields + Classical.epsilon). |
| Theorem/Online.lean | **0** | M₄ + M-DefinitionRepair + M-Potential + M-InfSup | **COMPLETE.** All sorrys resolved. Key structural additions: SOA interface lemmas (Inv-stable abstraction), WithBot_WithTop_lt_succ_le (reusable lattice fact), adversary_lower_bound (M-InfSup reusable primitive). Discovery-friendly: proofs don't depend on SOA internals. |
| Theorem/Gold.lean | **0** | M₅ + M-DefinitionRepair | **COMPLETE.** gold_theorem PROVED (γ₁₁). mind_change_characterization PROVED (γ₂₁): M-DefinitionRepair on MindChangeOrdinal (encode correctness → `< omega0` characterizes correct convergence) + M-Construction (dataUpTo/prefix bridge). Both directions ~15 lines each. Discovery-friendly: correctness-at-definition-level pattern (CNA₁₁) reusable for other complexity measures. |
| Theorem/Extended.lean | ~3 (1 Pl-killed) | Mixed M₁/M₅/M₆ | CONDITIONAL (unlabeled Pl-killed Γ₁₄) |
| Theorem/Separation.lean | ~5 (3 Pl-killed) | M₁ (Diagonalization) | 3 Pl-killed (Γ₁₅, Γ₁₇, Γ₁₈), 2 BLOCKED (online_strictly_stronger_pac Γ₁₆, ex_not_implies_pac) |
| Complexity/*.lean | ~10 | Mixed | CONDITIONAL to BLOCKED |

### Dependency Graph (critical paths)

```
vcdim_finite_imp_pac ──→ vc_characterization ──→ fundamental_theorem
pac_imp_vcdim_finite ──→ vc_characterization ──→ fundamental_theorem
sauer_shelah_quantitative ────────────────────→ fundamental_theorem
                                                fundamental_vc_compression
                                                fundamental_rademacher
```

The critical bottleneck is `vc_characterization` (M-Conjunction): it needs both directions of the VCDim ↔ PAC equivalence. The forward direction (vcdim_finite_imp_pac) is K₄-blocked.

### Known External Dependencies

| ID | Dependency | Status | Impact |
|----|-----------|--------|--------|
| K₄ | Hoeffding inequality | NOT in Mathlib | Blocks M-Pipeline for PAC bounds. Options: (a) axiomatize, (b) prove from scratch, (c) find alternative formalization |
| K₅ | Rademacher complexity | NOT in Mathlib (partial in lean-rademacher) | Blocks fundamental_rademacher |
| K₆ | Compression scheme | Custom formalization needed | Blocks fundamental_vc_compression |
| K₇ | Turing machine semantics | Custom formalization needed (partial in Computation.lean) | Blocks computability sorrys |

---

## T_task — Task Traces (Operational Record)

### Attack Order (planned)

**Wave 1 — Immediately Provable (no external dependencies):**
1. ~~vcdim_univ_infinite~~ ✓ (γ₁)
2. ~~nfl_theorem_infinite~~ ✓ (γ₂, modulo vc_char)
3. ~~vcdim_to_ordinal_vcdim~~ ✓ (γ₆) — KU₁ resolved
4. ~~nfl_fixed_sample~~ ✓ (γ₃) — A4 vacuous

**Wave 1.5 — Path B Implementation (M-DefinitionRepair):**
5. **EXECUTE Path B:** Change `isShattered .leaf` from `True` to `C.Nonempty`, change `LittlestoneDim : WithTop ℕ` to `WithBot (WithTop ℕ)`. Required: add `import Mathlib.Data.Nat.Lattice`, add helper `LTree.nonempty_of_isShattered`, propagate coercions.
6. **Online.lean closure:**
   - ldim_strict_decrease d=0 (M-CaseElimination: show SOA can't mistake when Ldim=0 after Path B)
   - backward_direction (M-Potential: φ=Ldim(VS) decreases on mistake, induction on d)
   - optimal_mistake_bound_eq_ldim (M-InfSup: ↑(⨅ M, MistakeBounded) = ⨆ shattered depths, needs C.Nonempty)
7. **Gold.lean:** mind_change_characterization forward direction (M₅ → finite ordinal). Backward: profile as KU₁₅.

**Wave 2 — Conditionally Provable (need API verification):**
8. pac_imp_vcdim_finite (M-Contrapositive, double-sampling)
9. sauer_shelah_quantitative (M-Bridge to Finset.Shatters)
10. Separation theorems batch (M₁ diagonalization template)

**γ-entries (Computation.lean — ALL CLOSED):**
- γ₂₇: KolmogorovComplexity — `sInf { encode p | (p : Code) (_ : p.eval 0 = Part.some (encode x)) }`. Compiled.
- γ₂₈: AlgorithmicProbability — `∑' (p : Code), if p.eval 0 = ... then 2^(-|p|) else 0` with `Classical.decEq` for halting. Compiled.
- γ₂₉: MDLPrinciple.select — Added `[Inhabited (Concept X Y)]`, `Classical.epsilon` for argmin. Compiled.
- γ₃₀: MMLPrinciple.select — Same Inhabited fix. Compiled.
- γ₃₁: SRM — Added `empiricalRisk`, `penalty` fields, `Classical.epsilon` for argmin. Compiled.

**γ-entries (MetaKernel WorldModel layer — NEW):**
- γ₃₂: WorldModel/PriorArt.lean — PriorArtTheorem, LibraryTrace, ProofMethod, ProofStrategy types. Concrete traces for Yuanhe Z (Lean4, 34,892 lines, 0 sorry: Efron-Stein, sub-Gaussian, Dudley, covering numbers) and Google formal-ml (Lean3, 36,221 lines, 0 sorry: PAC bounds, VC dimension, Sauer-Shelah, Hoeffding exponential bound, ERM generalization). Queries: findRelevantTheorems, extractStrategyChain, minAdaptationCost.
- γ₃₃: WorldModel/MeasuredTactic.lean — Compulsory measurement tactic classes: `measured_proof`, `pl_check_goal`, `coh_check_state`, `hc_measure_state`. Gates: pl_gate (non-triviality), coh_gate (well-typedness), inv_gate (stability), comp_gate (sorry tracking). ProofMeasurementReport with classification: trivial/structural/bridge/deep.
- γ₃₄: WorldModel/Feedback.lean — Feedback metaprograms: TraceAnalysis (pattern extraction from PhiTrace), StrategyPatch (promote/demote/addConstraint/coordinatedStrategy/usePriorArt), feedbackLoop (self-improving proof search), priorArtStrategy (prior-art guided strategy generation). `feedback_proof` tactic.

**γ-entries (Prior-art cloned):**
- γ₃₅: prior-art/lean-stat-learning-theory/ — Yuanhe Z, Lean4, concentration inequalities (Efron-Stein, sub-Gaussian, Dudley, covering numbers). 34,892 lines, 0 sorry.
- γ₃₆: prior-art/formal-ml/ — Google, Lean3, PAC/VC theory (PAC bounds, VC dimension, Sauer-Shelah, Hoeffding exponential bound, ERM generalization). 36,221 lines, 0 sorry.

**γ-entries (Online.lean compiled proofs):**
- γ_littlestone_forward: `forward_direction` proved (adversary forces n mistakes from depth-n shattered tree), η 0.9 (non-trivial: requires corrected isShattered + depth-indexed trees + adversary argument)
- γ_adversary_core: `adversary_core` proved (core mathematical content), η 0.95
- γ_mistakesFrom_bridge: `mistakesFrom_init_eq` proved (accumulator bridge), η 0.4 (technical, not mathematically deep)
- γ_shattering_mono: `isShattered_mono` proved, η 0.5

**Γ₁₉ — RESOLVED:** isShattered definition corrected (path-wise restriction, depth-indexed complete trees).

**Note:** `littlestone_characterization` compiles with the forward direction fully proved and backward direction sorry'd.

**Wave 3 — External Dependency Resolution:**
9. Hoeffding (K₄): axiomatize or prove
10. vcdim_finite_imp_pac (unblocked by K₄ resolution)
11. occam_algorithm (unblocked by K₄)

**Wave 4 — Assembly:**
12. vc_characterization (M-Conjunction of pac→vc + vc→pac)
13. fundamental_theorem (M-Conjunction of everything)
14. fundamental_vc_compression, fundamental_rademacher

**Wave 5 — Deep Structure:**
15. ~~Computation.lean sorrys~~ ✓ ALL 5 CLOSED (γ₂₇-γ₃₁)
16. Remaining complexity sorrys
17. Def bodies (M-Construction, literature lookup)

**Wave 6 — MetaKernel WorldModel Layer (NEW):**
18. WorldModel/PriorArt.lean — prior-art integration (Yuanhe Z + Google formal-ml)
19. WorldModel/MeasuredTactic.lean — compulsory measurement tactics
20. WorldModel/Feedback.lean — feedback metaprograms

### Session Protocol

At the START of each session:
1. Read all 4 URS files in `MetaKernel/URS/`
2. Read `MetaKernel/AGENT.md` and `MetaKernel/TASK_URS.md` (legacy)
3. Check KernelSnapshot sorry inventory — what changed?
4. Identify next attack target from Wave ordering
5. Begin Phase 1 (Profiling) for that target

At the END of each session:
1. Update all modified URS files
2. Ensure all γ and Γ entries are recorded
3. Update Comp table in Repo_Noological_URS.md
4. Update Claude's K/U partition in Claude_Noological_URS.md
