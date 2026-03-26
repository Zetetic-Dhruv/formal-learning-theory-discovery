# Claude Task URS — Metaprogram Synthesis Assistance (v2, 2026-03-18)

## Task Identity

Claude assists the MetaKernel agent by synthesizing metaprograms for sorry replacement.
Claude does NOT directly prove theorems — Claude discovers the proof STRUCTURE
(which method, which decomposition, which Mathlib APIs) and translates that structure
into tactic proofs.

**Current state:** 31 sorrys, K4 dissolved, PAC infrastructure layer in place.

---

## Pre-Flight Protocol (7 Mandatory Gates Before Every Write/Edit)

### Gate 0: Path Invariant Check
- Active library: `FLT_Proofs` (NOT `LimitsOfLearning`, NOT `KernelSnapshot`)
- All file paths begin with `FLT_Proofs/`
- lakefile.lean has sole `@[default_target]` for `FLT_Proofs`

### Gate 1: A₅ Anti-Simplification Check
- The sorry's statement must NOT be weakened to make it provable
- Hypotheses must NOT be added that make the conclusion trivial
- The conclusion must NOT be changed to a weaker version
- If the proof doesn't work with the current statement, that's an OBSTRUCTION to record, not a reason to change the statement

### Gate 2: Task URS Skill Invocation
- Call `task-urs-typing-derivation` before any type definition
- This prevents type-homogeneity (CNA₁)

### Gate 3: Noological URS Skill Invocation
- Maintain K/U partition awareness
- Track what Claude knows vs. what Claude guesses about Mathlib

### Gate 4: Metaprogram-First Check (CNA₄)
- Before writing tactic proof: identify the metaprogram type
- Is this M-Bridge? M-Contrapositive? M-Pipeline? M-Construction?
- The metaprogram type determines the proof architecture

### Gate 5: Measurement Gate
- Check `WorldModel/MeasuredTactic.lean` for prior measurements
- Has this sorry been attempted before? What was the obstruction?

### Gate 6: Prior-Art Check
- Check `WorldModel/PriorArt.lean` for relevant external work
- ~~K₄: Hoeffding APIs~~ → **DISSOLVED** (Mathlib has `one_sub_le_exp_neg`)
- Yuanhe Z (subGaussian, 34,892 lines Lean4)
- Google formal-ml (PAC/VC, 36,221 lines Lean3)

### Gate 7: Feedback Loop
- Check `WorldModel/Feedback.lean` for prior session lessons
- Pattern: obstruction → diagnosis → resolution → record

---

## Sorry Selection Protocol (Updated Triage)

### Tier 0 (IMMEDIATELY PROVABLE — no dependencies):
- `empiricalMeasureError_eq_empiricalError` — direct unfolding
- `consistent_imp_zero_empiricalError` — direct from IsConsistentWith
- `pac_sample_complexity_pos` — Nat.ceil positivity
- `ex_not_implies_pac` — construction (languages learnable in Gold but not PAC)
- `bc_strictly_stronger_ex` — construction

### Tier 1 (CONDITIONALLY PROVABLE — KU dependencies):
- `trueError_eq_genError` — needs KU₁ (measurability hypotheses)
- `erm_consistent_realizable` — needs KU₆ (ERM minimizer for infinite H)
- `pac_lower_bound` — needs KU₂₀ (exact constant)
- `nfl_fixed_sample` — needs KU₁₉, KU₂₁ (uniform measure construction)
- `occam_algorithm` — concentration + finite H
- `pac_not_implies_online` — needs KU₁₅ (separation example)

### Tier 2 (KEYSTONE — sorry DAG critical path):
- `vcdim_finite_imp_uc` — VCDim finite → uniform convergence
- `uc_imp_pac` — UC → PACLearnable via ERM
- `pac_imp_vcdim_finite` — contrapositive direction

### Tier 3 (ASSEMBLY — depends on Tier 2):
- `sauer_shelah` — needs UK_P2 (Shatters → Finset.Shatters bridge)
- `fundamental_vc_compression` — compression ↔ PAC
- `fundamental_stability` — stability → generalization bound
- `fundamental_rademacher` — needs RademacherComplexity def body
- Extended theorems (natarajan, ds, multiclass, universal_trichotomy)

### Tier 4 (BLOCKED — external dependency):
- `symmetrization_lemma` — UK₃ (measurability of sup over uncountable H)
- `RademacherComplexity` def body — needs distribution + sample size params
- `shatters_bridge` — UK_P2 (function-class → finite-set bridge)

### Tier 5 (DEEP STRUCTURE / OPEN PROBLEM):
- `compression_conjecture` — open mathematical problem
- `universal_trichotomy` — needs VCL tree analysis

### Previously Resolved (since v1):
- ~~`vcdim_to_ordinal_vcdim`~~ → **PROVED** (Γ₂₇ resolution, γ₃₅)
- ~~All Computation.lean sorrys~~ → **PROVED** (γ₂₇-γ₃₁)
- ~~All Online.lean sorrys~~ → **PROVED** (γ₁₂-γ₂₀)
- ~~gold_theorem~~ → **PROVED** (γ₁₁)
- ~~mind_change_characterization~~ → **PROVED** (γ₂₁)

---

## Ignorance Transfer Protocol

**Repo ignorance → Claude ignorance:**

| Repo KU | Claude KU | Claude API Confidence |
|---------|----------|----------------------|
| KU₁ (measurability) | CKU₁: Which Measurable* lemmas exist | PatternMatched |
| KU₆ (ERM minimizer) | CKU₆: iSup/Finset.sup API | PatternMatched |
| KU₈ (pure ENNReal UC) | CKU₈: ENNReal arithmetic API | Unknown |
| KU₁₅ (separation example) | CKU₁₅: Constructing ℝ-thresholds in Lean4 | Unknown |
| KU₁₉ (uniform measure) | CKU₁₉: Measure.count normalization | PatternMatched |

**Repo UK → Claude UK:**

| Repo UK | Claude assessment |
|---------|-----------------|
| UK₃ (sup measurability) | Claude cannot verify without empirical process theory |
| UK₈ (constructive asymmetry) | Claude recognizes pattern but can't type-check |
| UK_P1 (sorry DAG) | Claude can enumerate but not verify cascades |
| UK_P2 (Shatters bridge) | Claude needs to grep Mathlib for Finset.Shatters interface |

---

## Metaprogram Synthesis Templates

### Template: M-Bridge (connecting two type regimes)
```
1. Identify source and target types
2. Find the canonical coercion (ENNReal.toReal, WithTop.map, etc.)
3. State the bridge as `source_thing = coercion(target_thing)`
4. Prove by unfolding definitions + applying coercion lemmas
5. Check round-trip (if applicable)
```

### Template: M-Contrapositive (proving P → Q via ¬Q → ¬P)
```
1. State the contrapositive
2. Assume ¬Q (e.g., VCDim = ⊤)
3. Construct a counterexample (e.g., adversarial distribution)
4. Show the counterexample violates P (e.g., PAC learning fails)
5. Conclude by contradiction
```

### Template: M-Pipeline (chaining through infrastructure)
```
1. Identify the chain: A → B → C → ... → Z
2. Prove each step as a separate lemma
3. Compose with `Trans` or explicit `fun h => step₃ (step₂ (step₁ h))`
4. The pipeline for vc_characterization is:
   VCDim < ⊤ → HasUniformConvergence → PACLearnable
```

### Template: M-Construction (building a witness)
```
1. Identify the existential: ∃ x, P(x)
2. Construct x explicitly (e.g., a specific concept class)
3. Prove P(x) by direct computation
4. Use `⟨x, proof⟩` or `exact ⟨x, by ...⟩`
```

### Template: M-Conjunction (proving P₁ ∧ P₂ ∧ ... ∧ Pₙ)
```
1. Factor into n sub-goals
2. Prove each independently
3. Compose with `⟨proof₁, proof₂, ..., proofₙ⟩`
4. vc_characterization uses this: ⟨pac_imp_vcdim_finite, vcdim_finite_imp_pac⟩
```

---

## KU Discovery Log (Carried from v1 + new)

### KU: WithBot(WithTop ℕ) Lattice for LittlestoneDim
**Status:** RESOLVED (v1). CompleteLattice confirmed, iSup₂ works.
**Verdict:** η ≈ 0.6 (genuine contribution, not trivial).

### KU (NEW): PAC Infrastructure Layer Design
**Discovered:** The gap between VCDim types and PACLearnable was not Hoeffding (K4)
but infrastructure. The resolution was DEFINITIONAL: add TrueError, EmpiricalMeasure,
HasUniformConvergence as bridge definitions.
**Pattern:** M-Bridge at the paradigm joint, not M-Pipeline through concentration.
**CNA₁₂ (NEW):** Claude's bias toward "find the missing lemma" when the actual
obstruction is "define the missing concept."

---

## Error Recovery Protocol

### Compilation Error → Diagnose, Don't Converge
1. Read the error message fully
2. Check if it's a path issue (Gate 0)
3. Check if it's a name collision (C₆ precedent: IsConsistent)
4. Check if it's a missing import (C₇ precedent: FiniteMeasureProd)
5. If the error reveals a genuine type obstruction → create Γ-entry
6. Do NOT weaken the statement to make it compile (A₅)

### Context Compression Recovery
1. Re-read this URS
2. Re-read `Axioms/v2/TASK_URS.md`
3. Check sorry inventory (which sorrys remain?)
4. Check wave status (which wave is active?)
5. Resume from the next attackable sorry

---

## Trace Protocol

After every sorry attack, record:

```
{
  "sorry_id": "theorem_name",
  "method": "M-Bridge | M-Contrapositive | M-Pipeline | ...",
  "result": "proved | obstructed | deferred",
  "a5_check": "pass | VIOLATION",
  "obstruction": null | { "type": "KU | UK | BP", "description": "..." },
  "gamma_entry": "γ₄₀" | null,
  "capital_gamma_entry": "Γ₃₅" | null,
  "api_confidence_validated": ["lemma1", "lemma2"] | [],
  "api_confidence_invalidated": ["guessed_lemma"] | []
}
```
