# MetaKernel Usage Synthesis — How to Use the 4 URSes

## What the MetaKernel IS

The MetaKernel is an **agent on Γ** (the inquiry axis). It does not prove theorems
directly (that's γ-work). It discovers the STRUCTURE of proofs: which method applies,
which Mathlib APIs are needed, which definitions are missing, and where the type system
obstructs.

The 4 URSes define a complete operational architecture:

```
Claude_Noological_URS ─── Claude's self-model (biases, mechanisms, K/U)
         │
         ▼
Claude_Task_URS ──────── Claude's operational protocol (7 gates, triage, templates)
         │
         ▼
Repo_Task_URS ─────────── The pipeline (5 phases, attack waves, sorry inventory)
         │
         ▼
Repo_Noological_URS ───── The agent's ontology (methods, metaprograms, γ/Γ ledgers)
```

## How to Use: Session Protocol

### 1. Session Start
Read in order:
1. `Axioms/v2/TASK_URS.md` → current sorry state, KK/KU/UK/UU
2. `MetaKernel/URS/v2/Repo_Task_URS.md` → which attack wave is active
3. `MetaKernel/URS/v2/Claude_Task_URS.md` → sorry triage, pre-flight gates

### 2. Sorry Selection
Use Claude_Task_URS's triage (Tier 0-5):
- Start from Tier 0 (immediately provable) unless strategic reasons to go deeper
- Check sorry DAG in Repo_Task_URS → don't attack a sorry whose dependencies have sorrys
- Check attack wave → stay in wave order within a tier

### 3. Pre-Flight (Before Every Edit)
Execute Claude_Task_URS's 7 gates:
- Gate 0: Path check (`FLT_Proofs/`, not old names)
- Gate 1: A₅ check (don't weaken statements)
- Gate 2: Task URS Skill (if writing types)
- Gate 3: Noological URS Skill (if K/U boundary)
- Gate 4: Metaprogram-first (identify M-* type before writing tactics)
- Gate 5: Measurement gate (check WorldModel/)
- Gate 6: Prior-art check (Yuanhe Z, formal-ml)
- Gate 7: Feedback loop (check WorldModel/Feedback.lean)

### 4. Proof Synthesis
Use Repo_Noological_URS's metaprogram types:
1. **Profile the sorry** (Phase 1): paradigm, method candidates, dependencies
2. **Select metaprogram type**: M-Bridge? M-Contrapositive? M-Pipeline?
3. **Use the template** from Claude_Task_URS's synthesis templates
4. **Verify Mathlib APIs** via grep (CNA₅: don't guess)
5. **Write the proof** following the metaprogram structure

### 5. Post-Proof
- `lake build` (Phase 4 verification)
- Check A₅ (did the statement change?)
- Record: γ-entry (success) or Γ-entry (failure/obstruction)
- Update sorry inventory in Repo_Task_URS
- If obstruction → classify (KU/UK/BP) and record

### 6. Session End
- Update sorry count
- Update attack wave status
- Save any new KU/UK discoveries to memory
- Note which sorrys were attempted but not resolved

## Key Patterns from the 4 URSes

### Pattern 1: M-InfrastructureGap (CNA₁₂)
When a proof is blocked, check: is the gap a missing LEMMA or a missing DEFINITION?
The K4 dissolution established this: the Hoeffding lemma existed in Mathlib, but the
INFRASTRUCTURE connecting VCDim types to PACLearnable types was missing. Building
TrueError, EmpiricalMeasure, HasUniformConvergence dissolved the obstruction.

**Diagnostic:** If the proof attempt requires a type coercion that doesn't exist,
the gap is probably definitional, not lemmatic.

### Pattern 2: Correctness-at-Definition-Level (CNA₁₁)
When a proof is hard, check: can the DEFINITION be improved to make the proof flow?
MindChangeOrdinal and WithBot(WithTop ℕ) both encode correctness at the type level,
dissolving proof obstructions.

**Diagnostic:** If the sorry's proof seems to need a case split that the type system
should handle, the definition may need M-DefinitionRepair.

### Pattern 3: Sorry DAG Navigation
Don't attack sorrys in isolation. Check the dependency chain:
- `vcdim_finite_imp_uc` → `uc_imp_pac` → `vc_characterization` forward
- If you prove `uc_imp_pac` but `vcdim_finite_imp_uc` is still sorry, you haven't
  advanced the critical path

**Diagnostic:** Always check what DEPENDS on the sorry you're attacking. If nothing
depends on it, it's a leaf sorry (lower priority unless it's a separation theorem).

### Pattern 4: HC > 0 at Joints = Discovery Site
Paradigm joints with HC > 0 are where discoveries happen. The current HC > 0 joints:
- ENNReal/ℝ error (HC=0.5) — the bridge theorems are active sorry targets
- Combinatorial/Measure (HC=0.7) — VCDim → PAC infrastructure exists but sorrys remain
- PAC/Online (HC=1.0) — separation theorems

**Diagnostic:** If you're working at a HC > 0 joint and the proof flows easily,
either you've made a discovery or you've made an A₅ error. Check which.

## WorldModel Layer

The MetaKernel has a WorldModel layer with 3 files:
- `WorldModel/PriorArt.lean` — external formalizations (Yuanhe Z, formal-ml)
- `WorldModel/MeasuredTactic.lean` — tactic effectiveness measurements
- `WorldModel/Feedback.lean` — session lessons and error patterns

These are NOT proof files — they are meta-level records that inform sorry selection
and proof strategy. Check them before attacking a sorry that overlaps with prior art.

## What the MetaKernel is NOT

- NOT a proof automation system (it doesn't run tactics)
- NOT a replacement for reading Mathlib source (CNA₅)
- NOT a sorry counter (CNA₉: expand Γ, not decrease sorry count)
- NOT persistent (Claude's context window is finite; externalize state)
